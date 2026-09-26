# Phase 40b — PENCIL-X0 / CARRIER: planar pictures, the lifting space, `X₀`, and "the general point attains" (work log)

**Status:** in progress (opened design-first 2026-09-26). C1a (the definitions) and C1b (the
one-witness upgrade `Graph.x0Attains_of_exists`) landed 2026-09-26 in
`Molecule/Pencil/MainComponent/Carrier.lean`. **Next: C2 ∥ C3 ∥ C4**; *Hand-off* names C2's
`U`-open lemma first. Plan: `notes/Phase40-design.md` §3.

## Current state

**Next concrete step: C2's `U`-open lemma** (*Hand-off*); C3 and C4 may run in parallel. C1a landed
seven definitions and `Graph.mem_liftingSpace`, C1b the one-witness upgrade
`Graph.x0Attains_of_exists` at the pinned signature, both in
`CombinatorialRigidity/Molecular/Molecule/Pencil/MainComponent/Carrier.lean` (signatures and the C1b
API in the checklist). `blueprint/src/chapter/main-component.tex` carries five green definition
nodes and the green lemma `lem:pencil-x0-one-witness` (C1b, split out of
`thm:pencil-x0-main-component`); the four MC nodes stay red.

## Architectural choices made up front

The coordinator's adjudication (2026-09-26), settling the design recon:

- **Uncurried picture coordinates `q : α × Fin 2 → K`** (not curried `α → Fin 2 → K`).
  `PanelHingeFramework.ofNormals` takes `q : α × Fin (k+2) → K` and the rank polynomial lives in
  `MvPolynomial (α × Fin 2) K`, so uncurried composes directly with the landed machinery.
- **A single `X0Attains` predicate** carrying a nonzero `MvPolynomial (α × Fin 2) K`, with
  fibre-genericity/semicontinuity proved once in a mirror lemma `x0Attains_of_exists` (NOT two defs
  `X0Attains` + `X0GenericAttains`). `X0Dist` consumes one attaining `(q, z)`; `X0Gen` consumes the
  fibre-open clause (C1a verdict, *Decisions*).
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

- [x] **C1a — the definitions** (landed 2026-09-26). Namespace `CombinatorialRigidity.Molecular`,
  `Graph.*` via `_root_`; bodies abbreviated except `X0Attains`, the contract C1b must meet:
  ```
  def pencilPicturePoint (q : α × Fin 2 → K) (w : α) : Fin 3 → K            -- ![x_w, y_w, 1]
  def Graph.IsAdmissiblePicture (G : Graph α β) (q : α × Fin 2 → K) : Prop  -- links: picture pts differ;
    -- ∀ v ∈ V(G), ∃ t : Fin 3 → α, (∀ i, t i ∈ G.closedNbhd v) ∧ LinearIndependent K (pencilPicturePoint q ∘ t)
  def Graph.liftingSpace (G : Graph α β) (q : α × Fin 2 → K) : Submodule K (α → K)  -- z = 0 off V(G) ∧
    -- ∀ v ∈ V(G), ∃ h : Fin 3 → K, ∀ w ∈ G.closedNbhd v, z w = h ⬝ᵥ pencilPicturePoint q w
  theorem Graph.mem_liftingSpace : z ∈ G.liftingSpace q ↔ … := Iff.rfl
  def Graph.IsMainPicture (G) (q) : Prop  -- admissible ∧ ∀ q' admissible, finrank L(q) ≤ finrank L(q')
  def pencilConfigPoint (q : α × Fin 2 → K) (z : α → K) (w : α) : Fin 4 → K    -- ![x_w, y_w, z w, 1]
  def pencilNormalOfPicture (q) (z) (sel : α → Fin 3 → α) (v : α) : Fin 4 → K  -- cross₃ of sel v's points
  def Graph.X0Attains (K : Type*) [Field K] (G : Graph α β) : Prop :=
    ∃ (ends : β → α × α) (P : MvPolynomial (α × Fin 2) K),
      (∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2) ∧ P ≠ 0 ∧
      ∀ q, MvPolynomial.eval q P ≠ 0 → G.IsAdmissiblePicture q ∧
        ∃ R : MvPolynomial α K, (∃ z ∈ G.liftingSpace q, MvPolynomial.eval z R ≠ 0) ∧
          ∀ z ∈ G.liftingSpace q, MvPolynomial.eval z R ≠ 0 →
            (Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := 2) G ends
                (fun p => pencilConfigPoint q z p.1 p.2)).toBodyHinge.rigidityRows) : ℤ)
              = screwDim 2 * ((V(G).ncard : ℤ) - 1) - G.deficiency 3
  ```
- [x] **C1b/C6 — `Graph.x0Attains_of_exists`** (landed 2026-09-26 at the signature C1a pinned,
  unchanged; no `[Infinite K]`). API for C2–C5, all in `Carrier.lean` unless noted:
  `Graph.IsAdmissiblePicture.exists_mvPolynomial` (admissibility is open; `[Finite α]` only);
  `Graph.IsAdmissiblePicture.supportExtensor_ne_zero` (hinges nonzero at every height over an
  admissible `q`) via `linearIndependent_pencilConfigPoint_pair`; `Graph.liftingMatrix K G` (`M(q)`,
  rows `α ⊕ (α × α) ⊕ (α × Fin 3)`, columns `α ⊕ (α × Fin 3)`) with
  `Graph.liftingMatrix_mulVec_eq_zero_iff`, `Graph.map_ker_liftingMatrix` (height projection of
  `ker M(q)` is `L(q)`, any `q`), `Graph.finrank_ker_liftingMatrix` (equal finrank, admissible `q`);
  the mirror `Matrix.exists_mvPolynomial_section_mulVec_eq_zero`
  (`Mathlib/LinearAlgebra/Matrix/MvPolynomial.lean`: `D`, `Z` with `D(q₀) ≠ 0`, `Z(q₀) = z₀`,
  `D(q) ≠ 0 → dim ker M(q) ≤ dim ker M(q₀)`, and the section in `ker M(q)` where also
  `dim ker M(q₀) ≤ dim ker M(q)`); mirrors `MvPolynomial.eval_bind₁`,
  `Matrix.linearIndependent_rows_iff_det_ne_zero`.
- [ ] **C2 ∥ C3 ∥ C4** (parallelizable; each needs only C1a):
  - [ ] **C2 — lifting-space API** (sonnet): `Aff(q)` (restricted to `V(G)`) `⊆ L(q)`,
    `3 ≤ dim L(q)` at admissible `q`, the codim bound `dim L(q) ≥ 3|V| − 2|E|` (MC-1 tail), and
    **`U` nonempty open**: `∃ P ≠ 0, ∀ q, eval q P ≠ 0 → G.IsMainPicture q` (`[Infinite K]`; STEPS
    uses it to put its witnesses over `U`). Route for the last, from C1b's API: an admissible
    picture exists (the only new work; needs every closed neighbourhood of a body to have three
    members, and `K` infinite, e.g. points `(t, t²)` at distinct `t`); take an admissible `q₀`
    minimizing `finrank L` (`Nat.find`); then `P := Padm · D` from
    `IsAdmissiblePicture.exists_mvPolynomial` and the mirror's third conjunct (at `z₀ = 0`), with
    `finrank_ker_liftingMatrix` at both ends.
  - [ ] **C3 — picture→normal API** (sonnet/opus): `pencilNormalOfPicture ≠ 0 ↔` the selected
    triple is independent (via `cross₃_ne_zero_iff_linearIndependent`; picture-triple independence
    gives config-triple independence); selector-independence up to scalar at `z ∈ L(q)`; a
    `…Poly`/`…Poly_eval` mirror via `cross₃Poly` (X0Gen's nondegeneracy is polynomial in `z`).
  - [ ] **C4 — the config as a pencil framework** (opus, fragility): the `ofNormals … (config
    points) .toBodyHinge` support extensor `≠ 0 ↔ q_u ≠ q_v` (`←` landed in C1b, at every height:
    `Graph.IsAdmissiblePicture.supportExtensor_ne_zero`; `→` needs `z ∈ L(q)`, since distinct
    heights over one picture point still give independent points); the hinge extensor `C_e = p_u ∧ p_v`
    affine in `z` (MC-3 Plücker); **the polar/primal rank equality**: a point-join framework
    (hinges `p_u ∧ p_v`, endpoints from `ends`, no `[Inhabited α]`) has the rank of `ofNormals` at
    the config points — `panelSupportExtensor = complementIso ∘ normalsJoin`, then
    `BodyHingeFramework.finrank_span_rigidityRows_mapSupport` (general `K`; the ℝ-only
    `Molecule/Duality.lean` polarity is not needed). Touches `ScrewSpace`/extensor.
- [ ] **C5 — `X0Attains` at the flat witness** (opus, fragility): `X0Attains` holds at a flat config
  `(q, 0)` from a single seed; rank arithmetic on `rigidityRows`. Enters through C1b (`0 ∈ L(q)`,
  `q` main). The entry point STEPS extends.

Blueprint red nodes for the four MC labels stay in `main-component.tex`; each flips to `\lean{}` +
`\leanok` in the commit that lands its Lean.

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

**Next commit: C2's `U`-open lemma** (sonnet/opus) in `Carrier.lean`, route in the C2 bullet:
`∃ P ≠ 0, ∀ q, eval q P ≠ 0 → G.IsMainPicture q` over an infinite `K`. Its one new sub-step is an
admissible picture's existence; if that alone is a commit, land it first (under a hypothesis that
every body's closed neighbourhood has three members) and re-aim here. C3 and C4 need only C1a and
may run in parallel; the rest of C2 (`Aff(q) ⊆ L(q)`, `3 ≤ dim L(q)`, the codim bound) is separate.
Blueprint: the `U`-open content is `thm:pencil-x0-main-component`'s first clause, which stays red
until the bundle/irreducibility clauses are settled; give the `U`-open lemma its own node when it
lands. Do NOT open FLAT or any successor layer; CARRIER runs C2∥C3∥C4 → C5 first.

## Decisions made during this phase

- **2026-09-26 — C1b: the Cramer section uses a left inverse, not a maximal minor.** Stacking a
  projection onto `ker M(q₀)` under `M(q₀)` and left-multiplying by a constant left inverse gives a
  square polynomial `S(q)` with `S(q₀) = 1`; `adj S(q) z₀` is the section, no minor or rank-minor
  lemma needed (TACTICS-GOLF § 25). `M(q)` carries per-body coefficient columns, so `L(q)` is its
  kernel's height projection by definition; `IsMainPicture` enters once, as
  `dim ker M(q₀) ≤ dim ker M(q)` at admissible `q`. The blueprint's `lem:pencil-condition-linear`
  (red) is not used: the Lean route needs only the projection lemmas above.
- **2026-09-26 — opened design-first.** The design recon (opus, adopted as session rung; a parallel
  fable recon ran too) settled the new mirror definitions and the β-headroom fix; the coordinator
  adjudication above is the accepted design. The cross-phase plan stays `notes/Phase40-design.md` §3.
- **2026-09-26 — C1a: the rank is read at `ofNormals` of the config points, not of the plane
  normals** (the recon's scratch candidate fed `pencilNormalOfPicture` to `ofNormals`). From the
  bodies: a zero hinge welds its bodies (`hingeRowBlock` of `0` is `⊤`), `panelSupportExtensor n n = 0`,
  and adjacent planes coincide on the whole fibre inside a def₂-rigid subgraph ((MC-13)(c): every
  triangle edge) and everywhere at a flat `(q, 0)`, where that rank is `6(|V|−1)`, not (MC-4)'s
  `6|V|−3−dim L(q)`. At the points the hinge is the polar of `p_u ∧ p_v`, `≠ 0 ↔ q_u ≠ q_v` (C4's
  line already assumed this); the rank device applies verbatim; C4 converts to the point-join rank.
- **2026-09-26 — C1a, hypothesis 1 CONFIRMED: `U` is a def (`Graph.IsMainPicture`).** C1b's
  Cramer transport of `z₀` to nearby fibres needs `rank M(q)` locally constant at `q₀`, i.e.
  `dim L(q₀)` minimal; over a picture of larger fibre dimension `z₀` may lie off `X₀`. A def, not a
  C1b-only hypothesis, since STEPS must also place witnesses over `U` (C2's openness lemma). `ℓ₀` is
  not a def: finranks are compared directly, no `sInf`.
- **2026-09-26 — C1a, hypothesis 2 CONFIRMED: `X0Attains` carries fibre-openness.** (MC-133)(ii)
  needs one point both attaining and nondegenerate; (MC-14) gives nondegeneracy only at the general
  point of `L(q)`, so the two sets must meet in one fibre. One attaining `z` per picture forces
  MOTIVES to re-prove semicontinuity; the per-picture `R` (C1b gets it from the same device call)
  does not. Trace: X0Dist uses one attaining `(q, z)`; X0Gen intersects `R` with a nondegeneracy
  polynomial on `L(q)` (a MOTIVES fibre-intersection lemma); C5's `(q, 0)` enters via C1b. None blocked.
- **2026-09-26 — C1a shape details.** `L(q)` vanishes off `V(G)` (honest dimension for non-spanning
  `G`, which FLAT's `6|V|−3−dim L(q)` needs); `ends` is link-relative (a total selector forces
  `E(G) = β`); the planned `IsAdmissiblePicture'` + `↔` (one triple form suffices) and
  `Graph.liftAtVertex` (`L(q)` states the per-vertex condition itself) were dropped; the normal's
  selector is a plain `α → Fin 3 → α`, since `IsFin3SelectorOf` is unsatisfiable at
  `|closedNbhd v| > 3` and padding would detach the normal from the picture.
