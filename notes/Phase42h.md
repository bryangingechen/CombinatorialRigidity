# Phase 42h — PD-STEPS: open ears with four or more interior bodies in every dimension (work log)

**Status:** in progress, opened 2026-10-31 at the PI's word ("k ≥ 4 half first (Recommended)",
design doc §1), a sub-phase of Phase 42 and the third of PD-STEPS. Forward mode, the Lean under
`/coordinate-phase`: the eight red nodes of `blueprint/src/chapter/pencil-d.tex`'s
`sec:pencil-d-short` for open ears with four or more interior bodies (`-short-four`: Phase 40's
short-ear step in `Pᵈ`, SHORT-CORE's S35 with S20's factoring), on the `Pencil/Grade/` carrier. The
section's other half, the three-body ear at `d = 4` to `6` (`-short-three`, 4 nodes), stays mapped
by section in design doc §3, no letter minted. The open's consistency read found every proof
routing through the argument its statement claims, and no `-short-four` node using a
`-short-three` one (*Decisions made*). Next (*Hand-off*): the pre-build recon of the eight
nodes.

## Current state

**Next: the pre-build recon** (*Hand-off*). Opened; no Lean yet. The eight targets, leaf-first:
`lem:pencil-d-two-stars`, `lem:pencil-d-insertion`, `lem:pencil-d-kernel-curve`,
`def:pencil-d-ear-data` and `lem:pencil-d-ear-data-open` have every dependency green;
`lem:pencil-d-ear-data` rests on the definition; `lem:pencil-d-stars-four` on the two stars and the
kernel curve; `thm:pencil-d-open-ear-four` on all seven, every other dependency green (42f's
`lem:pencil-d-lifting-restrict`, 42e's `lem:pencil-d-condition-linear`, 42b's configuration
realization and one witness, and Phase 40's ear, fibre and deficiency lemmas). The chapter is the
lemma index (forward mode).

## Architectural choices made up front

- **Scope** (the PI's, verbatim in design doc §1): the eight nodes above.
- **Naming the halves** (this open's choice): `-short` stays the section's code, and its halves
  are `-short-four` (these eight, 42h) and `-short-three` (the four three-body nodes), stable codes
  named after their theorems `thm:pencil-d-open-ear-four` and `-three`, so that the unopened half
  has a name before a letter (design doc §3).
- **Encoding** as 42b–42g: `m = d − 2` heights at grade `k = m + 1`, `D = screwDim (m + 1)`,
  `def_d` is `G.deficiency (m + 2)`, attaining is `Graph.X0AttainsGrade K m` (witness
  `Graph.x0AttainsGrade_of_exists`). A vector with last coordinate `1` is a configuration point
  (`gradeMk_eta`). The maps `σ_a`, `σ_b` of `def:pencil-d-ear-data` are `gradeSigma`
  (`Grade/ConditionLinear.lean`), and `Π_a`, `Π_b` their ranges. `⋀^{d−1}K^{d+1}`, where the
  annihilators of the section live, is `⋀^k K^{k+2}` at grade `k`: the screw space itself.

## Lemma checklist

- [ ] **Pre-build recon**: exact Lean signatures for the eight nodes, their files, and spikes of
  the questions under *Blockers*.
- [ ] `lem:pencil-d-two-stars`, a leaf.
- [ ] `lem:pencil-d-insertion`, a leaf.
- [ ] `lem:pencil-d-kernel-curve`, a leaf.
- [ ] `def:pencil-d-ear-data`, a leaf.
- [ ] `lem:pencil-d-ear-data-open`, a leaf.
- [ ] `lem:pencil-d-ear-data`, on the definition.
- [ ] `lem:pencil-d-stars-four`, on the two stars and the kernel curve.
- [ ] `thm:pencil-d-open-ear-four`, on the other seven.
- [ ] **Close** 42h, an intermediate sub-phase close (`PHASE-BOUNDARIES.md`).

## Blockers / open questions

- None blocking. For the recon:
  - **Past `⋀²`.** The two stars and the stars lemma compute in `⋀^{d−3}`, `⋀^{d−1}` and `⋀^d`,
    and with the pairing `⋀² × ⋀^{d−1} → ⋀^{d+1} ≅ K`: the first `Grade/` Lean past `⋀²` (42g used
    no basis even of `⋀²`). In hand: `Meet.lean`'s `wedgeProd`, `wedgePairing` and
    `wedgePairing_injective` (every `j ≤ k + 2`), mathlib's `exteriorPower.wedge` (any degrees),
    `exteriorPower.wedgePairing` (a perfect pairing) and `Module.Basis.exteriorPower`. The recon
    picks the annihilator's encoding and spikes part (3) of the two stars.
  - **Every `m`, or `1 ≤ m`.** `⋀^{d−3}` needs `d ≥ 3`; at `d = 2` the two stars span `⋀²K³` and
    the stars lemma is empty. Whether the Lean holds at every `m`, as 42e–42g's did, or carries
    `1 ≤ m` (the nodes say `d ≥ 3` either way).
  - **The kernel curve.** The chapter's proof runs over `K(t)` and power series; bordered minors
    (an adjugate) give the first-order vector as a polynomial identity, which may suit Lean better.
    And the encoding of a matrix polynomial on `Y` (as `lem:rank-polynomial-of-le-finrank`'s).
  - **The grade ear data.** Grade forms of `earPicture`, `earHeight`, `earConfig` with `m` heights
    through `gradeSigma`; part (3)'s multihomogeneous step, new in `Pᵈ`; and grade forms of the
    openness lemma's two `k := 2` pins. The theorem's third condition is scale-invariant and lives
    on part (2)'s space for `G″` (`x₁ ∈ Π_a`, `x₃, …, x_{k−1}` free, `x_k ∈ Π_b`), which is
    `lem:pencil-d-stars-four`'s, so part (3) carries it to the ear data.
  - **The factoring.** `Graph.X0Attains.of_openEar_splitOff` (its every-`ρ` antecedent `hins`,
    `ScrewSpace K 2`, the bound `6`) and `Graph.exists_earBase_splitOff` are `P³` at every ear
    length; the suppression of `x₂` is `splitOff_ear_four` at fixed `k` (`induce_splitOff_ear` is
    at every `k`). Needed: a grade factoring at `D`, a suppression at every `k ≥ 4`, and whether
    `-short-three`'s theorem can reuse the factoring (its proof changes only the first stage and
    the third condition). The count's lemmas hold at every `D` already
    (`BodyHingeFramework.finrank_span_rigidityRows_ear_eq`,
    `Graph.splitOff_deficiency_le_of_eq_left`, `Graph.deficiency_induce_add_le_of_ear`).
  - **The insertion.** `lem:pencil-insertion`'s proof reads no dimension (`exists_insertion_gain`
    picks `t` by `exists_ne_zero_add_smul_notMem`, any module), but its Lean is `⋀²K⁴`-only, so a
    grade insertion gain is a new lemma, on 42g's join algebra (*Hand-off*).
  - The files: new `Grade/` files, no landed file edited unless a deferral below triggers.

## Hand-off / next phase

The next concrete commit is the **pre-build recon** (a `recon-opus` dispatch, read-only or a
design-pass commit at the coordinator's choice): pin the exact Lean signatures of the eight nodes
against the landed `Pencil/Grade/` API and Phase 40's `MainComponent/Short.lean`, `EarGen.lean` and
`Lines.lean`; spike the exterior-algebra step of the stars, the kernel curve, the grade ear data
and the factoring under `lake lean`; settle *Blockers*; and record the signatures here. Then build
leaf-first, roughly 4–8 commits by the coordinator's estimate in the option the PI chose. Each
build adds its node's `\lean{}` and `\leanok`.
- **The standing rule** (design doc §3): the recon and every build add a row to
  `notes/Cleanup42.md` §2 wherever their Lean departs from the chapter's proof, in the same commit.
- **What 42g hands the insertion:** `eq_of_add_smul_mem_of_add_smul_mem` and the `normalsJoin`
  lemmas of `Grade/Polygon.lean`, which `lem:pencil-d-insertion` can share (a dimension gain at
  `[Infinite K]`, a different statement from `lem:pencil-d-polygon-insert`).
- **Deferred from 42g, where it lands** (design doc §3; two `[open]` FRICTION entries): the four
  `normalsJoin` lemmas of `Grade/Polygon.lean` join 42c's move to `PanelLayer.lean`, and
  `pencilConfigPointGrade_ofPoints` (`Grade/Chain.lean`) joins 42e's fold into
  `Grade/Carrier.lean`, each with the next commit that edits that file. The other deferrals of 42b,
  42c, 42e and 42f (design doc §3) ride the same way.
- **After 42h:** `-short-three` (4 nodes) opens at the PI's word, its recon building on 42h's Lean.
  It is the coverage's step at three interior bodies, needed at `d = 4` only
  (`thm:pencil-d-chain-or-core`).

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
- **Consistency read at the open:** all eight PASS (each node read against the `Grade/` carrier,
  its `P³` node where it has one, and its SHORT-CORE source): every proof routes through the
  argument its statement claims, and no wording needs a repair. With every `\uses` list parsed
  whole, no `-short-four` node uses a `-short-three` one; the 30 dependencies outside the eight are
  green, proofs too.
