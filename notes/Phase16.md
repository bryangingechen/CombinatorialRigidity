# Phase 16 — Body-hinge Tay–Whiteley theorem (existence form) (work log)

**Status:** in progress (`def:edge-multiply`, `def:body-hinge-framework` landed).

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
blueprint chapter `body-hinge.tex` (§`sec:body-hinge`). Nodes `def:edge-multiply`
and `def:body-hinge-framework` are now green: `Graph.edgeMultiply` (+3 transport
facts) and `Graph.BodyHingeFramework` (+ `toBodyBar`, `IsIndependent`,
`IsInfinitesimallyRigid`) live in `BodyBar/BodyHinge.lean` (in the
`CombinatorialRigidity.lean` aggregator). Next concrete step is
`lem:edge-multiply-sparse` — independent/isostatic body-hinge ⇔
`(δ,δ)`-sparse/tight `(δ-1)·G`, the count `(δ-1)|E| = δ(|V|-1)`.

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
- [x] `def:body-hinge-framework` — body-hinge framework as the induced body-bar
  framework on `(δ-1)·G` (`Graph.BodyHingeFramework`, `.toBodyBar`,
  `.IsIndependent`, `.IsInfinitesimallyRigid`); rigidity / independence inherited
  verbatim (one-line wrappers, no glue). In `BodyBar/BodyHinge.lean`.
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

- **Body-hinge framework = thin wrapper over the induced body-bar framework; no
  glue.** `Graph.BodyHingeFramework n α β` stores `graph : Graph α β` and
  `placement : E((δ-1)·G) → ℝᵈ` (= the placement on the multiplied multigraph);
  `toBodyBar` is the `Graph.BodyBarFramework n α (β × Fin (δ-1))` on `(δ-1)·G`
  carrying that placement (`graph := edgeMultiply …; placement := F.placement`,
  no transport). `IsIndependent` / `IsInfinitesimallyRigid` are one-line
  `F.toBodyBar.Is…` wrappers at an orientation `D` of `(δ-1)·G`. This **resolves
  the Blockers spike** (degree of `tay_witness` reuse): the standard-basis witness
  on `(δ-1)·G` routes through verbatim — the dual-space-basis bookkeeping the
  blueprint describes is the *content* of `lem:edge-multiply-sparse`'s generic
  realization, not of the framework definition. `δ-1` factored out as
  `bodyHingeMult n` for the downstream `[NeZero]` hypothesis.

- **Tay 1989 title vs body terminology — do not "harmonize".** The
  `tay1989` bib `title` is verbatim the published title, which reads
  *"…(n−2,2)-frameworks…"*. The paper's *abstract and body* instead define
  and use *"(n−1,2)-framework"* (63× vs 1×) with *(n−2)-dimensional panels*.
  So `body-hinge.tex`'s panel-hinge aside says *"(n−2)-dimensional panels, the
  (n−1,2)-frameworks of Tay"* (the self-consistent in-text name) while the bib
  keeps the verbatim title. This mismatch is Tay's, not ours; bib = verbatim
  title, prose = in-text term — neither should be edited to match the other.

### Promoted to TACTICS-GOLF / TACTICS-QUIRKS / FRICTION / DESIGN

- *Bare `\lean{}` in blueprint prose poisons `lean_decls` / fails `checkdecls`*
  → `blueprint/SETUP-AND-PITFALLS.md` *Pitfalls* (hit on this commit: the
  phase-opening chapter preamble's "gains a `\lean{}` pointer" prose silently
  injected a blank decl that only failed once real `\lean{}` entries landed
  after it).

## Blockers / open questions

- **Degree of reuse of `tay_witness` — RESOLVED for the framework definition.**
  `def:body-hinge-framework` routes through `tay_witness`/the body-bar predicates
  verbatim: `BodyHingeFramework.IsIndependent` / `IsInfinitesimallyRigid` are
  one-line `toBodyBar.Is…` wrappers, no orientation transport or basis
  bookkeeping at the *definition* layer (see Decisions). The remaining content is
  the count `(δ-1)|E| = δ(|V|-1)` and the generic-realization claim, both inside
  `lem:edge-multiply-sparse`; `thm:body-hinge-tay` should then be a near-`rw` of
  `tay_witness` on `(δ-1)·G`. Re-assess whether the sparse-side count needs a new
  `edgeMultiply_edgeSet_ncard`-backed arithmetic lemma once that node opens.

## Hand-off / next phase

**Smallest next commit:** formalize `lem:edge-multiply-sparse` — that an
independent (resp. isostatic) body-hinge framework on `G` corresponds to
`(δ,δ)`-sparse (resp. tight) `(δ-1)·G`, with the count
`(δ-1)|E(G)| = δ(|V(G)|-1)`. The count side should follow from
`edgeMultiply_edgeSet_ncard` (`|E((δ-1)·G)| = (δ-1)|E(G)|`, already green) plus
`Graph.IsSparse`/tightness arithmetic (Phase 13 `Sparsity.lean`); the rigidity
side from the `BodyHingeFramework.Is…` wrappers (now green) composed with the
body-bar independence/sparsity correspondence used by `tay_witness`. Decide
whether the count needs a small standalone `ℕ`-arithmetic lemma or folds into the
sparse predicate directly. Land it in `BodyBar/BodyHinge.lean` and flip
`lem:edge-multiply-sparse` green in `body-hinge.tex` in the same commit.

`def:edge-multiply` (`Graph.edgeMultiply` + 3 transport facts) and
`def:body-hinge-framework` (`Graph.BodyHingeFramework` + `toBodyBar` +
`IsIndependent` + `IsInfinitesimallyRigid`) are done.

Follow-on after Phase 16: the **molecular conjecture** (panel-and-hinge with
concurrent hinges; Tay–Whiteley conjecture, proved by Katoh–Tanigawa 2011) — a
longer-horizon **Phase 17** target, not opened. Whiteley's "almost all
realizations are rigid" irreducible-variety lift remains deferred.
