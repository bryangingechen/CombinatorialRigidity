# Phase 16 — Body-hinge Tay–Whiteley theorem (existence form) (work log)

**Status:** ✓ Complete (all `body-hinge.tex` nodes green).

## Current state

The **body-hinge / panel-hinge Tay–Whiteley theorem** in `n`-space (Tay 1989,
Whiteley 1988), existence-of-realization form, landed **via the matroid-union
reduction to Phase 15's body-bar theorem**: a multigraph `G` carries an
independent (resp. isostatic) body-hinge framework in `ℝⁿ` iff `(δ-1)·G` is
`(δ,δ)`-sparse (resp. tight), where `δ = bodyBarDim n = n(n+1)/2` and `(δ-1)·G`
replaces each hinge by `δ-1` parallel bars. This reduces node-for-node to
`Graph.BodyBarFramework.tay_witness` (Phase 15).

Forward-mode phase; the authoritative dep-graph and lemma index is the blueprint
chapter `body-hinge.tex` (§`sec:body-hinge`), now fully green. All declarations
live in `BodyBar/BodyHinge.lean` (in the `CombinatorialRigidity.lean`
aggregator): `Graph.edgeMultiply` (+3 transport facts), `Graph.BodyHingeFramework`
(+ `toBodyBar`, `IsIndependent`, `IsInfinitesimallyRigid`), the sparsity
correspondence `edgeMultiply_isSparse_iff` (+ helper `exists_toBodyBar_iff`), and
the chapter target `Graph.BodyHingeFramework.body_hinge_tay`. The target conjoins
`edgeMultiply_isSparse_iff` with the forest-packing reformulation
(`tutte_nash_williams` on `(δ-1)·G`); the connected-tight spanning-tree
refinement is `isSpanningTreePacking_of_isTight` at the call site (one-directional,
needs `((δ-1)·G).Connected`), so it is not folded into the iff.

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
- [x] `lem:edge-multiply-sparse` — independent/isostatic body-hinge ⇔
  `(δ,δ)`-sparse/tight `(δ-1)·G` (`edgeMultiply_isSparse_iff`). Routed through
  `tay_witness` on `(δ-1)·G` + the existential bijection `exists_toBodyBar_iff`;
  the count `(δ-1)|E| = δ(|V|-1)` is left as the blueprint-prose consequence of
  `edgeMultiply_edgeSet_ncard` + tightness (no standalone ℕ-lemma needed — see
  Decisions). In `BodyBar/BodyHinge.lean`.
- [x] `thm:body-hinge-tay` — the chapter target
  (`Graph.BodyHingeFramework.body_hinge_tay`): independent body-hinge framework
  iff `(δ-1)·G` is `(δ,δ)`-sparse / forest-packing of `δ` forests; isostatic iff
  `(δ,δ)`-tight. `edgeMultiply_isSparse_iff` composed (`.trans
  tutte_nash_williams.symm`) with the forest-packing reformulation. The
  spanning-tree leg stays a call-site application of `isSpanningTreePacking_of_isTight`
  (needs connectivity; one-directional) rather than a third iff conjunct.

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

- **`lem:edge-multiply-sparse` = `tay_witness` on `(δ-1)·G` + an existential
  bijection; no new count lemma.** `edgeMultiply_isSparse_iff` mirrors
  `tay_witness`'s iff-pair shape with the body-hinge existential on the LHS and
  `((δ-1)·G).IsSparse/IsTight δ δ` on the RHS. The proof `rw`s `tay_witness`'s
  RHS (`IsSparse`/`IsTight` match syntactically), then bridges the body-hinge ⇔
  body-bar existentials with the new helper `exists_toBodyBar_iff` (a bijection:
  a body-hinge framework on `G` *is* a body-bar framework on `(δ-1)·G`, same
  placement data). The count `(δ-1)|E| = δ(|V|-1)` is **not** a separate Lean
  lemma — it falls out of `edgeMultiply_edgeSet_ncard` + the additive tightness
  equation, so it stays a blueprint-prose consequence (answers the Blockers
  re-assess: no `edgeMultiply_edgeSet_ncard`-backed arithmetic lemma needed).

### Promoted to TACTICS-GOLF / TACTICS-QUIRKS / FRICTION / DESIGN

- *`Iff.trans` / `refine h.trans ?_` needs a syntactic side-match, not just
  defeq; bridge with `constructor` + `.mp`/`.mpr`* → TACTICS-QUIRKS § 25 /
  FRICTION [resolved] *`refine h.trans ?_` over a defeq-but-not-syntactic iff
  side* (hit landing `edgeMultiply_isSparse_iff`).
- *Bare `\lean{}` in blueprint prose poisons `lean_decls` / fails `checkdecls`*
  → `blueprint/SETUP-AND-PITFALLS.md` *Pitfalls* (hit on this commit: the
  phase-opening chapter preamble's "gains a `\lean{}` pointer" prose silently
  injected a blank decl that only failed once real `\lean{}` entries landed
  after it).

## Blockers / open questions

- **Tree-packing reformulation for `thm:body-hinge-tay` (resolved).** Chosen
  phrasing: `thm:body-hinge-tay` restates the *forest-packing* leg explicitly as
  the RHS of the independent/sparse iff (`((δ-1)·G).IsForestPacking δ`, via
  `.trans tutte_nash_williams.symm`) and keeps the isostatic iff on
  `IsTight`. The spanning-tree leg (`cor:k-spanning-trees`) is *not* a third iff
  conjunct: `isSpanningTreePacking_of_isTight` is one-directional and needs
  `((δ-1)·G).Connected`, so it is applied at the call site, matching the
  blueprint proof's "applied to `(δ-1)·G`" phrasing. The count
  `(δ-1)|E| = δ(|V|-1)` needs no Lean lemma — `edgeMultiply_edgeSet_ncard` + the
  additive tightness equation (resolved during `lem:edge-multiply-sparse`).

## Hand-off / next phase

Phase 16 is **complete**: all `body-hinge.tex` nodes are green, build + lint +
`blueprint/verify.sh` clean. The chapter target `Graph.BodyHingeFramework.body_hinge_tay`
landed as `edgeMultiply_isSparse_iff` (sparse/tight) composed with the forest-packing
reformulation (`tutte_nash_williams`).

Follow-on after Phase 16: the **molecular conjecture** (panel-and-hinge with
concurrent hinges; Tay–Whiteley conjecture, proved by Katoh–Tanigawa 2011) — a
longer-horizon **Phase 17** target, not opened. Whiteley's "almost all
realizations are rigid" irreducible-variety lift remains deferred. Opening
Phase 17 would start (forward mode) by drafting a new `molecular.tex` chapter
dep-graph and `notes/Phase17.md`; the concurrency constraint is genuinely new
mathematics (not a reduction to existing phases), so expect a multi-session
formalization rather than a re-export.
