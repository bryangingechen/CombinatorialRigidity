# Phase 22 — Realization layer (Case I + Case III at `d=3`) (work log)

**Status:** in progress (opened 2026-06-04).

Stratum 5 of the molecular-conjecture program, continued: the Theorem-5.5 *case
producers* that the Phase-21b genericity device feeds. Phase 21b closed the
genericity-free reductions (the accounting iffs, the `V(G)`-relative count
bridges, the device, the reusable row/glue infra) and re-scoped the realization
*producers* here after a math-first feasibility pass. The KT math for both
producers is worked out in `notes/Phase21b.md` *Finding A/B* + *Hand-off to
Phases 22–23* — **Phase 22 formalizes it, it does not re-derive it.**

Forward-mode / **structural-edit** discipline (`blueprint/CLAUDE.md`): Phase 22
does *not* open a new blueprint chapter. Its producers (N4/N5/N6, the Case II/III
producer) **extend the existing `algebraic-induction.tex`** — their nodes are
already stubbed red there. Program plan / reuse map / citations:
`notes/MolecularConjecture.md` *Phase 22*. Lean lands in
`Molecular/{Induction,AlgebraicInduction}.lean`. Cross-cutting rationale:
`DESIGN.md` *Realization motive must be V(G)-relative*, *Constructibility recon
before a producer build*, *Phase Case-naming vs. KT's k-bookkeeping*.

## Current state

Phase opened; no Lean landed yet. The first content commit is **N4**
(`lem:rigidContract-isMinimalKDof`, the graph↔matroid contraction-minimality
bridge). **A constructibility recon (below) reclassified N4 from "build-shaped"
to a genuine, multi-step matroid-correspondence build** — start there, but
budget for it accordingly. The matroid-side fact it transports
(`contraction_isMinimalKDof`, `Induction.lean:1998`) is green; what N4 adds is
the bridge from `M(G̃)／E(H̃)` to the contracted *graph*'s own matroid
`matroidMG (G.rigidContract H r)`.

## Architectural choices made up front

- **Two tracks; Track A first.** Track A (Case I producer, full-rank, KT §6.2) is
  the tractable entry point and independent of Case III. Track B (Case II/III
  reducible-vertex producer at `d=3`, KT §6.3 + §6.4.1) is the crux (Lemma 6.10,
  ~12 pages, the single largest proof in KT). See `notes/MolecularConjecture.md`
  *Phase 22* for the node-by-node plan.
- **The motive is `V(G)`-relative** (`DESIGN.md` *Realization motive must be
  V(G)-relative*; carried from Phase 21b). `HasFullRankRealization` is the
  `V(G)`-relative rank `D(|V(G)|−1)`; the absolute null-space form is
  unsatisfiable for non-spanning inductive subgraphs.

## Lemma checklist

**Track A — Case I producer (full-rank, KT §6.2).**
- [ ] **N4** `lem:rigidContract-isMinimalKDof` — graph↔matroid contraction-
  minimality bridge: `G.IsMinimalKDof n 0 ∧ H proper rigid ⟹ (G.rigidContract H
  r).IsMinimalKDof n 0`. Matroid side (`contraction_isMinimalKDof`) green; the
  content is the `matroidMG`-of-`(map ∘ deleteEdges)` correspondence. **See the
  N4 recon below — heavier than the launch-plan label suggested.**
- [ ] **N5** `lem:case-I-splice-placement` — splice the inductive legs `(H,p₁)`,
  `(G/E',p₂)` along boundary hinges at panel intersections (eq. 6.6); needs a
  *panel-transversality* lemma + block-triangular independence (Lemma 5.1). Three
  KT sub-cases (6.2/6.3/6.5). Research-shaped — decompose math-first.
- [ ] **N6** `lem:case-I-realization` — compose N4 + N5 + the green glue
  (`isInfinitesimallyRigidOn_union_of_inter`) + device ⇒ discharges
  `theorem_55.hcontract`.

**Track B — Case II/III producer at `d=3` (the crux, KT §6.3 + §6.4.1).**
- [ ] eq. (6.12) degenerate placement (`p1(vb)=q(ab)` reproduces the `e₀` row;
  the green N7b-0/1/2/3 + glue feed it) — gives `+(D−1)`, one short.
- [ ] **Lemma 6.10** (`d=3`, 3 candidates): Claim 6.11 (combinatorial↔linear,
  redundant `ab`-row), Claim 6.12 (extensor-span genericity via Lemma 2.1).

**Assembly (may defer to Phase 23 with Thm 5.5's completion).**
- [ ] `prop:rigidity-matrix-prop11` `hub` brick (Phase-19 partition count).
- [ ] `thm:theorem-55` flips green once the producers land.

## Decisions made during this phase

### Phase-local choices and proof techniques
- **N4 constructibility recon (2026-06-04, before any build).** Ran the producer
  recon (`blueprint/CLAUDE.md` *the honesty gate*, second half) on N4. **Finding:
  N4 is the graph↔matroid correspondence Phase 20 deliberately deferred, and the
  underlying matroid fact is non-trivial — not the one-commit "build-shaped" node
  the launch plan implied.** The target equality is
  `matroidMG (G.rigidContract H r) = matroidMG G ／ E(H̃)`. Edge-set check: both
  grounds equal `(E(G) \ E(H)) × Fin D`, so the ground sets *do* match. But:
  - `M(G̃)` is the `D`-fold *union* of cycle matroids restricted to `E(G̃)`
    (`Deficiency.lean:141`). **`Matroid.Union` does not commute with contraction**
    in general (`Union Mᵢ ／ C ≠ Union (Mᵢ ／ C)`), so the per-cycle-matroid fact
    `cycleMatroid_contract` (vendored `Matroid/Graphic.lean:177`,
    `(G/[E(H),φ]).cycleMatroid = G.cycleMatroid ／ E(H)`) does **not** push
    through the union to give the whole-`matroidMG` equality directly.
  - The whole green substrate (`contract_matroidMG_deficiency_eq`,
    `contract_minimality_transport`, `contraction_isMinimalKDof`) reasons
    *directly on the matroid contraction* `M(G̃)／E(H̃)` and explicitly says "No
    graph↔matroid `map` correspondence is needed" — precisely because the
    correspondence is the deferred hard part.
  - The viable route is **independence-level** (`Matroid.ext_indep`), mirroring
    how `matroidMG_restrict_mulTilde` (`Deficiency.lean:212`) handled *restriction*
    via the sparsity characterization `matroidMG_indep_iff` rather than a union
    identity. The graph side is favorable: `rigidContract = (G.deleteEdges
    E(H)).map (collapseTo r V(H))`, and `contract_eq_map_of_disjoint`
    (`Matroid/Graph/GraphLike/Contract.lean:78`) gives `G/[C,φ] = φ ''ᴳ G` when
    `Disjoint E(G) C` — which holds after `deleteEdges E(H)`. So the *graph*
    contraction matches mathlib's `/[·,·]`; the open work is the
    **union-of-contracted-cycle-matroids ↔ contraction-of-union** independence
    correspondence (likely a new vendored-`Matroid` lemma, or a direct
    `ext_indep` against `matroidMG_indep_iff` + the contraction independence
    characterization). Budget N4 as a several-node sub-build, not one commit; or
    pivot to **Track A's N5 / Track B** if N4 stalls (N4 gates only N6, the
    Case-I composer).

### Promoted to TACTICS-GOLF / TACTICS-QUIRKS / FRICTION / DESIGN
- *(none yet — the N4 recon lesson is already captured by `DESIGN.md`
  *Constructibility recon before a producer build*; this is its first
  application post-21b.)*

## Blockers / open questions

- **N4 difficulty (above).** The matroid union↔contraction correspondence is the
  real obstruction; the launch-plan "build-shaped, the natural first commit"
  framing was optimistic. Re-cut on contact: either build the independence-level
  bridge, or sequence N5/Track B first (N4 only gates N6).

## Hand-off / next phase

**Next concrete commit:** **N4** `lem:rigidContract-isMinimalKDof` in
`Molecular/Induction.lean` (it owns `rigidContract` + the matroid substrate), via
the independence-level `Matroid.ext_indep` route sketched in the recon above —
*or*, if N4's union↔contraction lemma proves too large for one session, **N5**
`lem:case-I-splice-placement` (decompose math-first: the panel-transversality
lemma is the one genuinely new geometry) since N4 gates only N6. Flip the
corresponding red node in `algebraic-induction.tex` (`\lean{...}` + `\leanok`) in
the same commit, and run `blueprint/verify.sh`. The KT math is in
`notes/Phase21b.md` *Finding A/B*.
