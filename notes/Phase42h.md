# Phase 42h — PD-STEPS: open ears with four or more interior bodies in every dimension (work log)

**Status:** all eight nodes green, close pending. Opened 2026-10-31 at the PI's word ("k ≥ 4 half
first (Recommended)", design doc §1), a sub-phase of Phase 42 and the third of PD-STEPS. Forward
mode, the Lean under `/coordinate-phase`: the eight nodes of `blueprint/src/chapter/pencil-d.tex`'s
`sec:pencil-d-short` for open ears with four or more interior bodies (`-short-four`), on the
`Pencil/Grade/` carrier (`Grade/Stars.lean`, `Grade/EarData.lean`, `Grade/Short.lean`). The last,
`thm:pencil-d-open-ear-four` (`Graph.X0AttainsGrade.of_openEar_four`), landed with its `hins`
discharge. The `-short-three` half (4 nodes) stays mapped by section in design doc §3. Next
(*Hand-off*): the sub-phase's close (`PHASE-BOUNDARIES.md`), dispatched by the coordinator.

## Current state

**Next: the close of 42h** (*Hand-off*). All eight nodes are green; `Pencil/Grade/Short.lean` has
the theorem `Graph.X0AttainsGrade.of_openEar_four`, no `sorry`. Its proof applies, in order,
`splitOff_ear_succAbove`, then `Graph.X0AttainsGrade.of_openEar_splitOff` with `hins` discharged by
`exists_mvPolynomial_starsFour` (at `Sa`, `Sb` the ranges of `gradeSigma la`, `gradeSigma lb`, `pa`,
`pb` the base points of `a`, `b`), `exists_mvPolynomial_earDataGrade_of_smul` (at
`v = x ∘ succAbove 1`, the stars condition as `C`), and `exists_insertion_of_starGrade_sup` at
`R = ρ ⊔` the `G″` joins but the one at `1`. Four new leaves in the file, unpinned:
`pathVertex_smul_comp` and `starsCond_of_smul` (the condition is scale invariant: the path scaled by
`1` at the ends and `c i` at body `i`, each join a nonzero multiple), `pathVertex_map` (a function
of the bodies commutes with the path sequence; it carries the `G″` joins at `s` to
`pathVertex pa Y pb`), and `span_joins_succAbove_two` (the joins of the path of `G` are those of
`G″` but the one at `1`, plus `P 1 ∨ P 2` and `P 2 ∨ P 3`), with `starGrade_smul` and
`span_range_smul_eq` beside them. The first residual, `G″`'s `IsLink (e 1) (x 0) (x 2)`, is
`hpath''` at `1`. `hza`, `hzb`, the admissibility hypothesis and the base-compatibility binders of
`hins` go unused, as the trace predicted. The theorem is pinned with `\lean` and `\leanok` on
statement and proof; its `\uses` already listed everything the Lean calls. Honesty gate: every
hypothesis of the Lean (`hG`, the cover and path data `hcover`, `hinj`, `hxV₁`, `hab`, `hpath`,
`hsep`, `h₁`, `h₂`) is the chapter's standing hypotheses, open ear and attaining assumptions; none
is added. The Lean's route differs from the chapter's order (stars-four through ear data (3)),
ledger R-12. `ShortBody.lean` in the gitignored `scratch/42h/` is spent.

## Architectural choices made up front

- **Scope** (the PI's, verbatim in design doc §1): the eight nodes above.
- **Naming the halves** (the open's choice): `-short` stays the section's code; its halves are
  `-short-four` (these eight) and `-short-three` (four nodes), stable codes (design doc §3).
- **Encoding** as 42b–42g: `m = d − 2` heights at grade `k = m + 1`, `D = screwDim (m + 1)`,
  `def_d` is `G.deficiency (m + 2)`, attaining is `Graph.X0AttainsGrade K m`. `σ_a`, `σ_b` are
  `gradeSigma la`, `gradeSigma lb`; `Π_a`, `Π_b` their ranges. Joins live in
  `⋀[K]^2 (Fin (k + 2) → K)` (`normalsJoin`); the relative screws in `ScrewSpace K k`.
- **The annihilator** (the recon's choice): `U°` is `U.dualAnnihilator` in
  `Module.Dual K (⋀[K]^2 V)`, the chapter's own perfect pairing (`wedgePairing k`, injective, from
  which `complementIso` is built) identifying `⋀^{d−1}` with the forms on `⋀²`. No exterior power
  past `⋀²` is used; `star y` is `starGrade y`, the span of `range (normalsJoin y)`. The chapter's
  section now defines `U°` so too (the PI, *Decisions*).

## Lemma checklist

Shorthand: every declaration is in `namespace CombinatorialRigidity.Molecular`, under
`@[expose] public section`; `V = Fin (k + 2) → K`; `Graph.` names are `_root_.Graph.…`.

- [x] **Pre-build recon** (`fe5baf0f`): the pins below.
- [x] `lem:pencil-d-two-stars`, `lem:pencil-d-insertion`, `lem:pencil-d-kernel-curve`,
  `lem:pencil-d-stars-four`: new `Pencil/Grade/Stars.lean` (this commit), the recon's signatures
  and routes, pinned and green. Two-stars pins its seven (`starGrade` and the six of parts
  (1)–(3)); the other three pin `exists_insertion_of_starGrade_sup`,
  `exists_mvPolynomial_kernel_curve` and `exists_mvPolynomial_starsFour`, their helpers
  (`exists_insertion_gain_grade`, the kernel curve's first-order step, rank-is-open and dual form,
  `eq_zero_of_starsFour_firstOrder`, `starsFamily`) in the file unpinned, as 42g's
  `-polygon-insert` helper.
- [x] `def:pencil-d-ear-data`, new `Pencil/Grade/EarData.lean` (this commit; imports `Grade.Stars`,
  `Grade.Chain`, `Grade.ConditionLinear`, `MainComponent.EarGen`). Pins
  `earPictureGrade`, `earHeightGrade` (column `i` is `earHeight` at `la i`, `lb i`),
  `earConfigGrade` (with `earPicturePolyGrade`, `earHeightPolyGrade`, `earPointPolyGrade`); ear data
  `s : (α × Fin 2) ⊕ (α × Fin m) → K`, base `z₁ : α × Fin m → K`, `la lb : Fin m → Fin 3 → K`.
- [x] `lem:pencil-d-ear-data`, `Grade/EarData.lean` (this commit; R-10 open). (1):
  `Graph.earHeightGrade_mem_liftingSpaceGrade`, `eval_earPointPolyGrade`, `earConfigGrade_of_mem`,
  `eval_bind₁_earPicturePolyGrade`; (2): `earConfigGrade_first` (`= gradeSigma la ![s₀, s₁, 1]`),
  `earConfigGrade_last`, `earConfigGrade_of_mem_X` (`= gradeMk … 1`), `exists_earConfigGrade_eq`
  (any points with last coordinate `1` on the planes are an ear datum, `s₀` kept elsewhere); (3):
  `exists_mvPolynomial_earDataGrade_of_smul` (`C` with `C (c • Y) → C Y` for nonzero `c`, `f`
  nonzero on the plane-constrained families → `∃ g`, nonzero, `g s ≠ 0 → C (points of s)`).
- [x] `lem:pencil-d-ear-data-open`, `Grade/EarData.lean` (this commit). Pins
  `exists_mvPolynomial_le_finrank_ofNormals_bind_grade` ((1), every `k`) and
  `exists_mvPolynomial_le_finrank_sup_span_normalsJoin` ((2)).
- [x] `thm:pencil-d-open-ear-four`, new `Pencil/Grade/Short.lean` (imports `Grade.EarData`,
  `MainComponent.Short`), green, both residuals discharged (R-12). Pin `Graph.X0AttainsGrade.of_openEar_four`:
  `Graph.X0Attains.of_openEar_four` verbatim with `{n} {x : Fin (n + 4) → α}`
  `{e : Fin (n + 5) → β}` (`k = n + 4`), `h₁` and `h₂` at `X0AttainsGrade K m`,
  `G″ = G.splitOff (x 1) (x 0) (x 2) (e 1)`. Leaves, in build order:
  - [x] `splitOff_ear_succAbove` (`x : Fin (k + 3) → α`: `G″` has the ear `a − x ∘ succAbove 1 − b`
    with labels `e ∘ succAbove 2`, and `x 1` has degree two): `splitOff_ear_four` at every length;
    `k = 0` serves `-short-three`.
  - [x] `Graph.exists_earBase_splitOff_grade`: `Graph.exists_earBase_splitOff` with `m` heights
    (`ρ : Submodule K (ScrewSpace K (m + 1))`); heights by
    `Graph.exists_liftingRestrict_preimage_fst_eq`; verbatim pin, no departure.
  - [x] `Graph.X0AttainsGrade.of_openEar_splitOff`: `Graph.X0Attains.of_openEar_splitOff` at grade
    `m + 1`, `D` for `6`, `hins`'s `ρ` in `⋀²`; with `complementScrew`,
    `span_supportExtensor_comp_eq_map_normalsJoin` and `finrank_sup_map_complementScrew`.
  - [x] Residual 1 (kernel-checked, discharged): `(G.splitOff (x 1) (x 0) (x 2) (e 1)).IsLink (e 1) (x 0) (x 2)`,
    from `hpath''` at `1`.
  - [x] Residual 2 (kernel-checked, discharged), `hins`: for base data `q z la lb ρ` with `hza`, `hzb`,
    `∃ Q ≠ 0, ∀ s, eval s Q ≠ 0 → G″.IsAdmissiblePicture (earPictureGrade V₁ q s) → ∃ x₂, x₂ last
    = 1 ∧ ∀ p, p (x 1) = x₂ → (∀ t ≠ x 1, p t = point of s at t) → min (finrank (ρ ⊔ span (G″'s
    ear joins at s)) + 1) D ≤ finrank (ρ ⊔ span (G's ear joins at p))`. Discharge:
    `exists_mvPolynomial_starsFour` at `Sa = range (gradeSigma la)`, `Sb = range (gradeSigma lb)`,
    `pa`, `pb` the points of `a`, `b`; `exists_mvPolynomial_earDataGrade_of_smul` at
    `v = x ∘ succAbove 1` (needs the condition's scale invariance, a leaf); then an
    `exists_insertion_four_grade`, `exists_insertion_of_starGrade_sup` at `R = ρ ⊔` the other
    joins, in the path-join form (a leaf: the index bookkeeping of `exists_insertion_four`), with a
    `pathVertex` composition lemma.
- [ ] **Close** 42h, an intermediate sub-phase close (`PHASE-BOUNDARIES.md`).

## Blockers / open questions

1. **`lem:pencil-d-two-stars` (2) and (3)** — settled by the PI, 2026-10-31 (*Decisions*; the
   questions as put, design doc §1): restated on the forms on `⋀²`, with the section's `U°`, and
   stars-four's proof on its Lean, this commit (ledger R-7, R-8 aligned).
2. **Every `m`** — resolved: all eight hold at every `m`; no `1 ≤ m` (the dual route never uses
   `d ≥ 3`; the theorem's composition type-checks at every `m`).
3. **The kernel curve** — resolved: the generic rank by `Nat.findGreatest` and a maximal minor; the
   first-order step without `K(t)`: if `M_wξ₀ ∉ range A`, then `r + 1` columns, independent at
   `t = 0`, stay independent at some `t ≠ 0` (`LinearIndependent.exists_notMem_of_polynomial_repr`),
   and `A + tM_w + t²M₂(t)` has rank `> r`. The matrix is over `MvPolynomial σ K`, the parameters a
   subspace `L` (stars-four's `Y 0 ∈ Sa`, `Y last ∈ Sb`). Ledger R-9.
4. **The grade ear data** — resolved (*Lemma checklist*); part (3) by a coefficient in the scalars
   of `f(λ_x y_x(s))` (`MvPolynomial.sumAlgEquiv`), not the multihomogeneous `f_α`. Ledger R-10.
5. **The factoring** — pinned, not spiked: `Graph.X0AttainsGrade.of_openEar_splitOff` keeps the
   `P³` shape (any `v u w e₀`, `G″`'s ear given, `2 ≤ k`), so `-short-three` reuses it with
   `splitOff_ear_succAbove` at `k = 0`, changing only `hins`. The `P³` sources check: both `P³`
   lemmas are `ScrewSpace K 2`, bound `6`, every ear length; `splitOff_ear_four` is at `k = 4`.
6. **The insertion gain** — resolved: `Lines.lean`'s route at grade `k`, no 42g join algebra.
- The files: three new `Grade/` files, no landed file edited (no deferral of design doc §3 fires).

## Hand-off / next phase

The next concrete commit is **the close of 42h** (an intermediate sub-phase close,
`PHASE-BOUNDARIES.md` *When this commit closes a phase*): all eight nodes are green. The close
re-thins the ROADMAP row and compresses its planning section, syncs the user-facing status
surfaces, re-reads the chapter's `sec:pencil-d-short` end to end for the `-short-four` nodes, and
writes the exposition ledger entry; the coordinator dispatches it, not this build.
- **The standing rule** (design doc §3): each build adds a row to `notes/Cleanup42.md` §2 where its
  Lean departs from the chapter's proof; R-7 to R-10 are this recon's, R-11 the Stars build's, R-12 the theorem's.
- **Deferred from 42g, where it lands** (design doc §3; two `[open]` FRICTION entries): the four
  `normalsJoin` lemmas of `Grade/Polygon.lean` join 42c's move to `PanelLayer.lean`, and
  `pencilConfigPointGrade_ofPoints` (`Grade/Chain.lean`) joins 42e's fold into
  `Grade/Carrier.lean`, each with the next commit that edits that file. `Grade/Stars.lean`'s
  `normalsJoin_sub_left`, `normalsJoin_zero_right`, `normalsJoinLin` and
  `normalsJoin_add_smul_add_smul` go with them, and its four `pathVertex` lemmas
  (`pathVertex_add_smul`, `pathVertex_succ_castSucc`, `pathVertex_eq_of_val_eq`,
  `pathVertex_zero_single`) to `MainComponent/Cut.lean`, which defines `pathVertex` (FRICTION, two
  `[open]` entries; design doc §3); `Grade/Short.lean`'s `pathVertex_comp_succAbove_one`, `pathVertex_smul_comp` and
  `pathVertex_map` go with them, and its two `Fin.succAbove` value lemmas (`coe_succAbove_one`, `coe_succAbove_two`) are
  the Mathlib-eligible ones beside them (not yet in a FRICTION entry).
- **After 42h:** `-short-three` (4 nodes) opens at the PI's word, its recon building on 42h's Lean:
  the dual route carries `lem:pencil-d-stars-three` (the radical then holds `Π_a + Π_b`, and
  `finrank_add_two_le_of_forall_ιMulti_eq_zero` gives `d + κ ≥ 7`).

## Decisions made during this phase

- **PI, 2026-10-31 (42h's open):** the PI answered "k ≥ 4 half first (Recommended)", whose option
  read: "8 nodes, Phase 40's open-ear factoring in Pᵈ at four or more interior bodies. Opus open
  commit, a pre-build recon against the carrier, then roughly 4–8 builds. The three-body case (4
  nodes) stays mapped by section for its own sub-phase, which lets its recon build on the landed
  k ≥ 4 Lean." The question as put, the other options and a note on them: design doc §1.
- **The question's attribution, corrected** (not the PI's text; design doc §1): "SHORT-CORE's hand
  proof, the coverage's only new mathematics" is SHORT-CORE's whole step. 42h carries S35 (every
  `ρ`, `k ≥ 4`, every `d`) with S20's factoring and the shared tools; `-short-three` carries `k = 3`
  at `d = 4` to `6` (S28–S33).
- **Consistency read at the open:** all eight PASS; no `-short-four` node uses a `-short-three`
  one; the 30 dependencies outside the eight are green, proofs too.
- **The pre-build recon (`fe5baf0f`):** the annihilator on the forms of `⋀²`, under which
  stars-four needs no `⋀^{d−3}`, no quotient and no independence of `y₁`, `y₃` (its statement keeps
  the independence, via one minor). Seven nodes spiked complete; the theorem's composition checks
  over three `P³` transcriptions. Departures R-7 to R-10 in the ledger.
- **PI, 2026-10-31 (42h, after the recon), two-stars:** the PI answered "Restate in forms
  (Recommended)", whose option read: "Edit the node's parts (2) and (3) to what the Lean proves
  (forms on ⋀², part (3) at the degree used), with one sentence keeping the ⋀^{d−1} reading through
  the section's pairing. Lands in the Stars.lean build commit; no extra Lean or commits. The citing
  proofs get matching wording." The question as put, the other option and a note: design doc §1.
- **PI, 2026-10-31 (42h, after the recon), the routes:** the PI answered "Stars-four only
  (Recommended)", whose option read: "Rewrite stars-four's chapter proof to the Lean's shorter forms
  route in the Stars.lean build, which keeps it consistent with a forms-worded two-stars. R-9 and
  R-10 stay in the ledger for the cleanup." The question as put, the other options: design doc §1.
- **`Grade/Stars.lean` (this commit):** both answers carried out (not the PI's text: both
  questions and their options are the coordinator's words, design doc §1). Two-stars' (2), (3) and
  the section's `U°` are on forms, the `⋀^{d−1}` reading in one sentence of its proof; stars-four's
  proof follows its Lean, `\uses` what it calls; stars-three (red) cites the restated parts through
  the pairing, its last step reading the radical in `K^{d+1}`. One shorter route:
  `eq_zero_of_forall_ιMulti_two_eq_zero`, any `V`, shared by part (3)'s bound and the stars-four
  helper. Part (1)'s chapter proof keeps its basis (R-11, open).
- **`Grade/EarData.lean` (this commit):** transcribed as spiked, docstrings written, no shorter route
  taken. Faithfulness gate: the definition has no hypotheses, so any `la`, `lb`, `z₁` is a datum
  (the chapter's compatibility of the base data with `σ_a`, `σ_b` enters as `hla`, `hlb`, `hz₁` of
  part (1), discharged by the node's own hypotheses); parts (2) and (3) need none. Part (3)'s
  `f` is nonzero on the plane-constrained families (the chapter's polynomial in that family).
  Ledger R-10 open.
