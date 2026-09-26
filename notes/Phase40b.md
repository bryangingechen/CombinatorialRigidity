# Phase 40b — PENCIL-X0 / CARRIER: planar pictures, the lifting space, `X₀`, and "the general point attains" (work log)

**Status:** in progress (opened design-first 2026-09-26). C1a, C1b, and C2 (both the `U`-open
lemma and the lifting-space API) landed 2026-09-26 in `Molecule/Pencil/MainComponent/Carrier.lean`.
**C2 is DONE.** **Next: C3 ∥ DUAL-K → C4** (parallelizable; DUAL-K must land before C4 and never
builds in parallel with a `Carrier.lean` build). Plan: `notes/Phase40-design.md` §3.

## Current state

**Next concrete step: C3 (picture→normal API) or DUAL-K (the polarity over every field)** (*Hand-
off*) — both need only C1a; DUAL-K must land before C4 and never in parallel with a `Carrier.lean`
build.
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
- [x] **C2 — lifting-space API** (landed 2026-09-26, sonnet). `Aff(q)` (restricted to `V(G)`)
  `⊆ L(q)`, at every picture, and `3 ≤ dim L(q)` at an admissible `q` with `V(G).Nonempty`.
  **The codim bound `dim L(q) ≥ 3|V| − 2|E|` (MC-1 tail) is dropped from the checklist**: FLAT's
  (MC-4)(b), `dim L(q) ≥ 3 + def₂`, subsumes it (take the singleton partition in `def₂`), it has no
  consumer on the route, and it is not proved here — FLAT's pre-build recon may reinstate it if its
  route needs it.
  - [x] **`U` nonempty open** (landed 2026-09-26): `∃ P ≠ 0, ∀ q, eval q P ≠ 0 →
    G.IsMainPicture q` (`[Infinite K]`; STEPS uses it to put its witnesses over `U`) —
    `Graph.exists_mvPolynomial_isMainPicture`, from `Graph.exists_isMainPicture` (a
    `finrank L(q)`-minimizing admissible `q_min`, via `Nat.sInf` over the image set) and
    `Graph.exists_isAdmissiblePicture` (an admissible picture exists for loopless `G` whose closed
    neighbourhoods all have at least three members, via the moment curve `v ↦ (φ v, (φ v)²)` at
    an injective `φ : α → K`). All three take `hloop : G.Loopless` and
    `h3 : ∀ v ∈ V(G), 3 ≤ (G.closedNbhd v).ncard`. `P := Padm * D` from
    `IsAdmissiblePicture.exists_mvPolynomial` and the mirror's semicontinuity conjunct at the
    trivial kernel vector `0`, with `finrank_ker_liftingMatrix` at both ends. Blueprint:
    `lem:pencil-x0-main-picture-open`.
  - [x] **`Aff(q) ⊆ L(q)`, `3 ≤ dim L(q)`** (landed 2026-09-26): `Graph.affineLiftMap G q : (Fin 3
    → K) →ₗ[K] (α → K)` sends `h` to `fun w => if w ∈ V(G) then h ⬝ᵥ pencilPicturePoint q w else
    0`; `Graph.affineLifts G q := LinearMap.range (G.affineLiftMap q)` is `Aff(q)` restricted to
    `V(G)`. `Graph.affineLifts_le_liftingSpace` holds at every `q` (the same `h` at every body — no
    admissibility). `Graph.finrank_affineLifts` (admissible `q`, `V(G).Nonempty`, `[Finite α]`)
    gives `finrank = 3`: the map is injective since `IsAdmissiblePicture`'s second conjunct gives
    three closed-neighbourhood members with independent homogeneous picture points, forcing `h = 0`
    via `Matrix.mulVec_injective_iff_isUnit`. Blueprint: `lem:pencil-lifting-space-affine`.
- [ ] **C3 ∥ (DUAL-K → C4)** (parallelizable; each needs only C1a):
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
  - [ ] **DUAL-K — the polarity over every field, in place** (sonnet; a mechanical refactor, the
    bodies compile verbatim at `[Field K]`; upstream of `Carrier.lean`, so never in parallel with a
    Carrier build). Must land **before C4**. Design: `notes/Phase40-design.md` §4 *Duality*.
    - ℝ → `K`, same bodies:
      - `screwComplementIso` (`Molecule/Duality.lean:69`);
      - `equivExteriorPower_mk_extensor` (`Molecule/ScrewVelocity.lean:161`; HingeGeneric has a
        private K form, so reuse it rather than duplicate);
      - `screwComplementIso_mk_extensor` (`Pencil/Statement.lean:200`);
      - both transports, `extensorInPanel_screwComplementIso_of_extensorThroughPoint` and
        `extensorThroughPoint_screwComplementIso_of_extensorInPanel`.
    - The self-duality becomes
      `hasPencilPanelRealization_mapSupport_screwComplementIso {F : BodyHingeFramework K 2 α β} (h :
      HasPencilPanelRealization G F normal point) : HasPencilPanelRealization G (F.mapSupport
      screwComplementIso) point normal`. Prove it with `mapSupport_graph`,
      `mapSupport_supportExtensor` and `map_ne_zero_iff _ screwComplementIso.injective`.
      `mapExtensor = mapSupport` holds by `rfl` at ℝ.
    - Renaming triggers the deletion gate: repoint every live reference tree-wide. Statement.lean's
      docstrings carry four.
    - The ℝ³ molecular declarations (`screwComplementIso_lineExtensor`,
      `molecularOfCentres_mapExtensor_screwComplementIso`, `*_ofNormals_homogenize*`) stay ℝ and
      instantiate `K := ℝ`. Leave `ProjectiveInvariance.lean` alone; merging
      `mapExtensor`/`mapSupport` is a cleanup-round item.
    - Blueprint:
      - restate and repin `lem:pencil-self-dual` over every field;
      - replace `sec:pencil-duality`'s "Fix `K = ℝ`" with a field-generality remark stating only
        what is verified: the polarity transports rank, rigidity and pencil realizations over
        every field; field dependence enters only at self-dual configurations
        (`fmlnote:pencil-conditional-realization-pair-field`);
      - add the matching remark on `thm:projective-invariance`'s "ℝ³";
      - reword `pencil.tex:610` ("whose polarity is one such automorphism" is wrong: the polarity
        is a correlation, and that lemma is its collineation companion).
    - Workbook: annotate `K-clos.md` (AC-1) in place, with date and finder, as now
      compiler-witnessed (`notes/pencil/CLAUDE.md` discipline).
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

**C2 is DONE.** **Next commit: C3 (picture→normal API) or DUAL-K (the polarity over every field)**
in `Carrier.lean` (checklist for both). C3 and C4 need only C1a; DUAL-K must land before C4 and
never builds in parallel with a `Carrier.lean` build — so the two runnable-now leaves are C3 and
DUAL-K, either order. Do NOT open FLAT or any successor layer; CARRIER runs C3∥(DUAL-K → C4) → C5
next.

## Decisions made during this phase

- **2026-09-26 — C2's `U`-open lemma: moment curve, `Nat.sInf` minimizer, reused mirror.** Any
  three distinct closed-neighbourhood members are non-collinear on the moment curve
  `v ↦ (φ v, (φ v)²)` (`det_moment_curve_triple`, a permuted Vandermonde product). The openness
  polynomial reuses `Matrix.exists_mvPolynomial_section_mulVec_eq_zero` at the trivial kernel
  vector `0` — no new mirror lemma, no witness height to transport.
- **2026-09-26 — C1b: the Cramer section uses a left inverse, not a maximal minor.** Stacking a
  projection onto `ker M(q₀)` under `M(q₀)` and left-multiplying by a constant left inverse gives a
  square polynomial `S(q)` with `S(q₀) = 1`; `adj S(q) z₀` is the section (TACTICS-GOLF § 25); no
  minor lemma needed. The blueprint's `lem:pencil-condition-linear` (red) is not used: the Lean
  route needs only the projection lemmas.
- **2026-09-26 — opened design-first.** The design recon (opus, adopted as session rung) settled
  the new mirror definitions and the β-headroom fix; cross-phase plan stays `Phase40-design.md` §3.
- **2026-09-26 — C1a: the rank is read at `ofNormals` of the config points, not of the plane
  normals** (the recon's scratch candidate fed `pencilNormalOfPicture` to `ofNormals`). From the
  bodies: a zero hinge welds its bodies (`hingeRowBlock` of `0` is `⊤`), `panelSupportExtensor n n = 0`,
  and adjacent planes coincide on the whole fibre inside a def₂-rigid subgraph ((MC-13)(c): every
  triangle edge) and everywhere at a flat `(q, 0)`, where that rank is `6(|V|−1)`, not (MC-4)'s
  `6|V|−3−dim L(q)`. At the points the hinge is the polar of `p_u ∧ p_v`, `≠ 0 ↔ q_u ≠ q_v` (C4's
  line already assumed this); the rank device applies verbatim; C4 converts to the point-join rank.
- **2026-09-26 — C1a, hypothesis 1 CONFIRMED: `U` is a def (`Graph.IsMainPicture`).** C1b's
  Cramer transport needs `rank M(q)` locally constant at `q₀`; STEPS also places witnesses over `U`
  directly (C2's openness lemma), so it is a def, not a C1b-only hypothesis. `ℓ₀` is not a def.
- **2026-09-26 — C1a, hypothesis 2 CONFIRMED: `X0Attains` carries fibre-openness.** One attaining
  `z` per picture would force MOTIVES to re-prove semicontinuity; the per-picture `R` (C1b's device)
  does not. X0Dist uses one attaining `(q, z)`; X0Gen intersects `R` with a nondegeneracy polynomial
  on `L(q)`; C5's `(q, 0)` enters via C1b.
- **2026-09-26 — C1a shape details.** `L(q)` vanishes off `V(G)`; `ends` is link-relative; the
  planned `IsAdmissiblePicture'`/`Graph.liftAtVertex` were dropped as redundant; the normal's
  selector is a plain `α → Fin 3 → α` (no `IsFin3SelectorOf`, unsatisfiable at
  `|closedNbhd v| > 3`).
- **2026-09-26 — duality recon (PI-commissioned, opus, read-only; `Phase40-design.md` §4
  *Duality*).** The polarity is field-free over every field, as a transport of frameworks and
  pencil realizations; the ℝ scope of `Duality.lean`/the self-duality is historical. It never
  preserves adjacent-distinctness, nondegeneracy or `X₀`, so self-duality does not reach `X0Dist`.
  Its one use on the route is C4's rank equality, via the new slice DUAL-K. The rejected
  simplifications and the FLAT-recon questions are in the design doc.
- **2026-09-26 — C2 closes: `Aff(q)` as a linear map's range, and the codim bound is dropped.**
  `Graph.affineLiftMap` needs `open Classical in` (the `if w ∈ V(G)` body has no `Decidable`
  instance otherwise, matching `Graph.liftingMatrix`'s idiom); the dimension count reuses the
  `finrank_ker_liftingMatrix` injectivity device (`Matrix.mulVec_injective_iff_isUnit`) rather than
  a fresh argument. The codim bound is dropped per the coordinator's scope-pin: FLAT's (MC-4)(b)
  `dim L(q) ≥ 3 + def₂` subsumes it (singleton partition), with no route consumer.
