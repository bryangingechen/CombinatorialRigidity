# Phase 40b — PENCIL-X0 / CARRIER: planar pictures, the lifting space, `X₀`, and "the general point attains" (work log)

**Status:** in progress (opened design-first 2026-09-26). CARRIER is the geometric layer the whole
`X₀` argument rests on. This commit is design-only (blueprint red nodes + this log + status
surfaces); the definitions land next (C1a). Plan: `notes/Phase40-design.md` §3 CARRIER.

## Current state

**Next concrete step: C1a — land the four CARRIER definitions** (a Lean slice, no proofs beyond the
submodule closure): the admissible planar picture, the lifting space `L(q)`, the picture→normal map,
and the single `X0Attains` predicate. All four elaborated as compiler-checked candidate signatures in
the design recon (scratch, EXIT 0). This commit opened CARRIER: the accepted design is recorded
below, the forward-mode blueprint section `blueprint/src/chapter/main-component.tex` carries the four
red nodes ((MC-1),(MC-2),(MC-3),(MC-10)(a)) wired toward `def:pencil-main-component-statements`, and
the status surfaces say 40b/CARRIER in progress. Nothing of the Lean is landed yet.

## Architectural choices made up front

The coordinator's adjudication (2026-09-26), settling the design recon:

- **Uncurried picture coordinates `q : α × Fin 2 → K`** (not curried `α → Fin 2 → K`).
  `PanelHingeFramework.ofNormals` takes `q : α × Fin (k+2) → K` and the rank polynomial lives in
  `MvPolynomial (α × Fin 2) K`, so uncurried composes directly with the landed machinery.
- **A single `X0Attains` predicate** carrying a nonzero `MvPolynomial (α × Fin 2) K`, with
  fibre-genericity/semicontinuity proved once in a mirror lemma `x0Attains_of_exists` (NOT two defs
  `X0Attains` + `X0GenericAttains`). MOTIVES consumes only the existential half.
- **The picture→normal map is `cross₃` of homogeneous config points** — polynomial, denominator-free.
  "Rational parametrization" collapses to a fibre polynomial at a fixed admissible `q`; the Cramer
  chart lives in the proof, not the def.
- **β-headroom fix: an additive-successor `_of_card` triple** (`x0Dist_of_card`, `x0Gen_of_card`,
  `pencil_conjecture_of_card`) concluding the UNCHANGED L0 predicates `X0Dist`/`X0Gen` and reusing the
  protected `pencil_conjecture_of_X0` verbatim. L0 is protected: not edited, not made
  unprovable-as-stated. These are MOTIVES leaves — the planned signatures are recorded, they do not
  land here. Mirrors `molecular_conjecture_multigraph`'s `hcard`+`hspan` shape (type-checked in the
  recon, only the MOTIVES bodies sorried).

## Lemma checklist

Leaf plan in dependency order (from the recon; rungs and fragility flags noted). Fragility zone =
anything touching `ScrewSpace`/the opaque carrier or `rigidityRows` rank arithmetic → opus minimum.

- [ ] **C1a — the four definitions** (next commit; sonnet, defs only): `Graph.IsAdmissiblePicture`
  (uncurried) + the homogeneous-triple form `IsAdmissiblePicture'` + their `↔`; `Graph.liftAtVertex`
  (submodule, closure proofs trivial) and `Graph.liftingSpace`; `pencilConfigPoint` /
  `pencilNormalOfPicture` (via `cross₃`); the single `Graph.X0Attains` (carrying the nonzero
  `MvPolynomial (α × Fin 2) K` + target-rank clause). X0Attains references `ofNormals`/`rigidityRows`
  but is a def — no proof — so still sonnet-landable.
- [ ] **C1b/C6 — the mirror lemma `x0Attains_of_exists`** (opus, fragility): the semicontinuity
  engine, proved once — one witness config at the target rank ⟹ `X0Attains` — reusing
  `PanelHingeFramework.exists_rankPolynomial_of_rigidOn` (`GenericityDevice.lean`) and
  `MvPolynomial.exists_eval_ne_zero`.
- [ ] **C2 ∥ C3 ∥ C4** (parallelizable once C1a lands):
  - [ ] **C2 — lifting-space API** (sonnet): `Aff(q) ⊆ L(q)`, `3 ≤ dim L(q)` at admissible `q`, the
    codim bound `dim L(q) ≥ 3|V| − 2|E|` (MC-1 tail).
  - [ ] **C3 — picture→normal API** (sonnet/opus): `pencilNormalOfPicture ≠ 0 ↔ admissible-at-v`
    (via `cross₃_ne_zero_iff_linearIndependent`); selector-independence of the normal at `z ∈ L(q)`.
  - [ ] **C4 — the config as a pencil framework** (opus, fragility): the `ofNormals … .toBodyHinge`
    support extensor `≠ 0 ↔ q_u ≠ q_v`; the hinge extensor `C_e = p_u ∧ p_v` affine in `z` (MC-3
    Plücker). Touches `ScrewSpace`/extensor.
- [ ] **C5 — `X0Attains` at the flat witness** (opus, fragility): `X0Attains` holds at a flat config
  `(q, 0)` from a single seed; rank arithmetic on `rigidityRows`. The entry point STEPS extends.

Blueprint red nodes for the four MC labels are opened in `main-component.tex`; each flips to `\lean{}`
+ `\leanok` in the commit that lands its Lean.

## Blockers / open questions

Two questions are recorded for the **MOTIVES pre-build recon**, deliberately NOT resolved now (both
recons disagreed; settle against the landed SPINE2 threading at MOTIVES, not now):

- **(a) The exact `hcard` constant.** The opus recon read it as `bodyBarDim 3 · (|α|−1)` (= `6·`,
  matching `molecular_conjecture_multigraph` and `freshEdgeSupply_of_card_lt_of_noRigid_of_degree_two`,
  `Molecule/Pencil/Escape.lean`); the fable recon read `3 · (|α|−1)`. Pin against the SPINE2
  producer's actual `hfresh`/`hcard` threading when MOTIVES builds the `_of_card` triple.
- **(b) The headroom root cause.** The opus recon attributed the fresh-edge need to the split-off's
  `e₀ ∉ E(G)` (the `hK`/`hbareSplit` slots in `Escape.lean`); the fable recon read `splitOff`'s body
  (`Induction/Operations.lean:770`) and argued split-off can reuse a freed label, locating the real
  source in BRIDGE consuming SPINE2's `hfresh`. Plus the opus recon's sub-gap: the landed fresh-edge
  supply lemma keys on *sparsity* (no proper rigid subgraph), while the X₀ split-off step is applied
  at `δ ≥ 5` — MOTIVES settles which supply lemma discharges `e₀ ∉ E(G)`.

## Hand-off / next phase

**Next commit: C1a — the four CARRIER definitions** (a Lean slice, at the rung C1a maps to — sonnet
for the pure defs; escalate if X0Attains's def elaboration fights the carrier). It flips the
`main-component.tex` red nodes it realizes to `\lean{}`/`\leanok`. Do NOT open FLAT or any successor
layer; CARRIER runs C1a → C1b/C6 → C2∥C3∥C4 → C5 first.

## Decisions made during this phase

- **2026-09-26 — opened design-first.** The design recon (opus, adopted as session rung; a parallel
  fable recon ran too) settled the four new mirror definitions and the β-headroom fix; the coordinator
  adjudication above is the accepted design. Verbatim recon findings compressed into *Architectural
  choices*; the cross-phase plan stays `notes/Phase40-design.md` §3.
