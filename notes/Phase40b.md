# Phase 40b — PENCIL-X0 / CARRIER: planar pictures, the lifting space, `X₀`, and "the general point attains" (work log)

**Status:** in progress (opened design-first 2026-09-26). C1a, C1b, C2 (both the `U`-open
lemma and the lifting-space API), and DUAL-K (the polarity over every field) landed 2026-09-26.
**C2 and DUAL-K are DONE.** **Next: C3 (picture→normal API), then C4.** Plan:
`notes/Phase40-design.md` §3.

## Current state

**Next concrete step: C3 (picture→normal API)** (*Hand-off*) — needs only C1a. C4 needs both C3 and
DUAL-K (now landed).
C1a landed seven definitions and `Graph.mem_liftingSpace`, C1b the one-witness upgrade
`Graph.x0Attains_of_exists` at the pinned signature, and C2 landed the `U`-open lemma (existence of
an admissible picture, a main-picture minimizer, and the openness polynomial) plus the lifting-space
API (`Graph.affineLiftMap`/`Graph.affineLifts`, `Graph.affineLifts_le_liftingSpace`,
`Graph.finrank_affineLifts`) — full checklist below — all in
`CombinatorialRigidity/Molecular/Molecule/Pencil/MainComponent/Carrier.lean`. The codim bound
`dim L(q) ≥ 3|V| − 2|E|` originally on C2's checklist is **dropped** (*Decisions made*): FLAT's
(MC-4)(b) subsumes it and it has no consumer on the route. `blueprint/src/chapter/main-component.tex`
carries five green definition nodes, the green lemma `lem:pencil-lifting-space-affine` (C2's
`Aff(q)` containment/dimension), the green lemma `lem:pencil-x0-one-witness` (C1b), and the green
lemma `lem:pencil-x0-main-picture-open` (C2's `U`-open landing), all split out of
`thm:pencil-x0-main-component`, which stays red.

DUAL-K landed the field-general polarity `screwComplementIso` (`Molecule/Duality.lean`),
`ProjectiveInvariance.lean`'s `mapExtensor`/`scaleExtensor` family, and the field-general forms of
`screwComplementIso_mk_extensor` and both predicate transports (`Pencil/Statement.lean`), all at
`[Field K]` with names unchanged, so C4's polar/primal rank equality (`ofNormals … = (pointJoin …
).mapSupport screwComplementIso`) is unblocked and needs no further duality work. Blueprint and the
`notes/pencil/workbook/K-clos.md` (AC-1) annotation restated in step; no new dep-graph node (the
existing `lem:pencil-self-dual` pin stays green, now honestly over every field).

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
  `Graph.IsAdmissiblePicture.exists_mvPolynomial`, `Graph.IsAdmissiblePicture.supportExtensor_ne_zero`
  (hinges nonzero at every height over an admissible `q`), `Graph.liftingMatrix K G` (`M(q)`) with
  `Graph.map_ker_liftingMatrix` (height projection of `ker M(q)` is `L(q)`, any `q`) and
  `Graph.finrank_ker_liftingMatrix` (equal finrank, admissible `q`), via the mirror
  `Matrix.exists_mvPolynomial_section_mulVec_eq_zero`
  (`Mathlib/LinearAlgebra/Matrix/MvPolynomial.lean`).
- [x] **C2 — lifting-space API** (landed 2026-09-26, sonnet). `Aff(q)` (restricted to `V(G)`)
  `⊆ L(q)`, at every picture, and `3 ≤ dim L(q)` at an admissible `q` with `V(G).Nonempty`.
  **The codim bound `dim L(q) ≥ 3|V| − 2|E|` (MC-1 tail) is dropped from the checklist**: FLAT's
  (MC-4)(b), `dim L(q) ≥ 3 + def₂`, subsumes it (take the singleton partition in `def₂`), it has no
  consumer on the route, and it is not proved here — FLAT's pre-build recon may reinstate it if its
  route needs it.
  - [x] **`U` nonempty open** (landed 2026-09-26): `∃ P ≠ 0, ∀ q, eval q P ≠ 0 →
    G.IsMainPicture q` (`[Infinite K]`; STEPS uses it) — `Graph.exists_mvPolynomial_isMainPicture`,
    from `Graph.exists_isMainPicture` (`Nat.sInf`-minimizing) and `Graph.exists_isAdmissiblePicture`
    (moment curve), both taking `hloop : G.Loopless`, `h3 : ∀ v ∈ V(G), 3 ≤ (G.closedNbhd v).ncard`.
    Blueprint: `lem:pencil-x0-main-picture-open`.
  - [x] **`Aff(q) ⊆ L(q)`, `3 ≤ dim L(q)`** (landed 2026-09-26): `Graph.affineLiftMap G q : (Fin 3
    → K) →ₗ[K] (α → K)`, `h ↦ fun w => if w ∈ V(G) then h ⬝ᵥ pencilPicturePoint q w else 0`;
    `Graph.affineLifts G q := LinearMap.range (G.affineLiftMap q)` is `Aff(q)` restricted to `V(G)`,
    `≤ L(q)` at every `q` (`Graph.affineLifts_le_liftingSpace`); `Graph.finrank_affineLifts`
    (admissible `q`, `V(G).Nonempty`, `[Finite α]`) gives `finrank = 3`. Blueprint:
    `lem:pencil-lifting-space-affine`.
- **C3, then C4** (DUAL-K, below, is DONE — C4 no longer waits on it):
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
    the config points. After DUAL-K this is `ofNormals (k := 2) G ends p = (pointJoin G ends
    p).mapSupport screwComplementIso` (a `funext` on support extensors through
    `screwComplementIso_mk_extensor`), then `BodyHingeFramework.finrank_span_rigidityRows_mapSupport`,
    about 15 lines (duality recon, compiler-checked in scratch). The **X0Dist witness** must patch
    the hinges off `E(G)`: `HasCoplanarPanelRealization` needs `supportExtensor e ≠ 0` for every
    `e : β`, as `pencilChartFramework` does. Carry the rank across with
    `span_rigidityRows_eq_of_supportExtensor_agree` (`Arms.lean:670`). Touches `ScrewSpace`/extensor.
  - [x] **DUAL-K — the polarity over every field, in place** (landed 2026-09-26, sonnet;
    see *Decisions made* for the adjudication). `screwComplementIso`, `equivExteriorPower_
    mk_extensor`, `screwComplementIso_mk_extensor`, both transports, and
    `ProjectiveInvariance.lean` (`mapExtensor`/`scaleExtensor` + 18 lemmas) are all
    `[Field K]`-generic; the ℝ-specific molecular declarations stay `K := ℝ`. Blueprint
    (`lem:pencil-self-dual`, `sec:pencil-duality`, `thm:projective-invariance`,
    `pencil.tex:610`) and `K-clos.md` (AC-1, now `[PROVED]`) restated in step.
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

**C2 and DUAL-K are DONE.** **Next commit: C3 (picture→normal API)**, in `Carrier.lean`; needs only
C1a. C4 needs both C3 and DUAL-K (now landed). Do NOT open FLAT or any successor layer; CARRIER runs
C3 → C4 → C5 next.

## Decisions made during this phase

- **2026-09-26 — C2's `U`-open lemma: moment curve, `Nat.sInf` minimizer, reused mirror.** Any
  three distinct closed-neighbourhood members are non-collinear on the moment curve
  `v ↦ (φ v, (φ v)²)` (`det_moment_curve_triple`). The openness polynomial reuses
  `Matrix.exists_mvPolynomial_section_mulVec_eq_zero` at the trivial kernel vector `0`.
- **2026-09-26 — C1b: the Cramer section uses a left inverse, not a maximal minor** (TACTICS-GOLF
  § 25); the blueprint's `lem:pencil-condition-linear` (red) is not used, since the Lean route needs
  only the projection lemmas.
- **2026-09-26 — opened design-first** (opus recon; plan `Phase40-design.md` §3). **C1a: the rank
  is read at `ofNormals` of the config points**, not the plane normals (a zero hinge would weld a
  def₂-rigid subgraph at the wrong rank); the hinge there is the polar of `p_u ∧ p_v`,
  `≠ 0 ↔ q_u ≠ q_v`, and C4 converts to the point-join rank.
- **2026-09-26 — C1a hypotheses CONFIRMED and shape details.** `U` is a def
  (`Graph.IsMainPicture`, needed by both C1b's Cramer transport and STEPS); `X0Attains` carries
  fibre-openness via a per-picture `R`. `L(q)` vanishes off `V(G)`; `ends` is link-relative.
- **2026-09-26 — C2 closes: `Aff(q)` as a linear map's range, codim bound dropped.** Dimension count
  reuses the `finrank_ker_liftingMatrix` injectivity device; the codim bound is dropped per the
  coordinator's scope-pin, FLAT's (MC-4)(b) subsuming it with no route consumer.
- **2026-09-26 — duality recon (field-free, `Phase40-design.md` §4) and DUAL-K adjudication.** Its
  one route use is C4's rank equality; frozen-doc citations ruled out the planned `mapSupport`
  restatement for the self-duality, so `ProjectiveInvariance.lean` was generalized in place instead.
