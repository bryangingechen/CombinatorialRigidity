# Phase 22b — KT Claim 6.4 (Case-I green-modulo discharge) (work log)

**Status:** planning (opened 2026-06-05 as the coordinator's Close-C of Phase 22a).

Stratum 5 of the molecular-conjecture program, continued. **Scope: just KT
Claim 6.4** — the single deferred obligation Phase 22a left green-modulo. 22a's
Case-I realization composer `PanelHingeFramework.case_I_realization`
(`AlgebraicInduction.lean`) / blueprint `lem:case-I-realization` is green-modulo
one dischargeable hypothesis, `hclaim64`, tracked by the red blueprint node
`lem:claim-6-4`. 22b's target is to **discharge it** — flipping `lem:claim-6-4`
green and `lem:case-I-realization` to fully green.

This is the same green-modulo → discharge pattern as Phase 21 → 21b. The KT math
is **worked out** in `notes/Phase22-realization-design.md` §1.13–§1.16 and
`notes/Phase22a.md` *Hand-off* / *Blockers*; 22b **formalizes** it, it does not
re-derive it. Forward-mode / structural-edit (`blueprint/CLAUDE.md`): 22b opens no
new chapter — `lem:claim-6-4` is the existing red node in `algebraic-induction.tex`;
Lean lands in `Molecular/AlgebraicInduction.lean`.

## Current state

22b opens to **discharge KT Claim 6.4** (`lem:claim-6-4` / the composer's
`hclaim64` hypothesis). The green-modulo source is 22a's
`case_I_realization`: axiom-clean, build + lint green, honestly green-modulo this
one hypothesis + the KT Lemma-6.3 case hypothesis `hcSimple` (the latter is a case
hypothesis, not a 22b target). Nothing is mid-stream; the first concrete step is
the 22b opening recon (decompose-then-build the discharge path below, and settle the
sub-phase cut — see *Blockers*).

## The target

**Claim 6.4 in the `Qc`-non-root / exterior-projected-rank form (the form
`case_I_realization` carries as `hclaim64`).** Verified dischargeable in design-doc
§1.16; the over-quantified `∀`-GP form was the 4th over-claim and is NOT the target.

Precisely (design doc §1.16, the form the block-triangular coupling
`hasGenericFullRankRealization_of_couple_blockTriangular_ofNormals_set` consumes):
given the contraction's generic IH, produce

> `∃ Qc ≠ 0, ∀ q, eval q Qc ≠ 0 → ∃ rsc, (links in Gc) ∧ |rsc| ≥ D(|sc|−1) ∧`
> `LinearIndependent (D ∘ panelRow rsc)`

where `Gc = G ＼ E(H)` is the surviving-edge block, `sc = (V(G)∖V(H)) ∪ {r}` the
surviving body set, and `D = (extProj V(H)).dualMap` the **exterior-column
projection** onto the surviving body columns `V(G)∖V(H)`. I.e. the surviving block
attains independent rank `≥ D(|sc|−1)` at a Zariski-**open (generic) locus** (a
contraction rank-polynomial `Qc`-non-root), restricted/projected to the surviving
columns.

**KT grounding** (verified 2026-06-05; `notes/Phase22a.md` *Hand-off*): this IS KT
**Claim 6.4 / eq. (6.9)** — `D` is the restriction to `V∖V′ = V(G)∖V(H)` columns,
and Claim 6.4 gives the surviving block's `V∖V′`-restricted rank `= D(|sc|−1)` (full
exterior column rank) at the generic placement. KT §5.1 (p. 668) bundles
non-degeneracy + rank-maximality under the single "coefficients algebraically
independent over ℚ" hypothesis (footnote 4 flags this as a deliberate
simplification); Claim 6.4 (p. 675, inside Lemma 6.3) reads the Case-I rank-transport
off it. Source eqs.: (6.5)/(6.9).

**Why irreducible** (G3a finding; design doc §1.7). The green linking-edge brick
does not apply — `collapseTo r V(H)` redirects each surviving edge's endpoints, so
its support extensor uses *different* panel normals in `rigidContract` vs. `G ＼ E(H)`,
breaking the `hspan` span-equality. The 21b genericity device does **not** discharge
it either (a distinct obligation: the collapse-normal mismatch).

## Discharge path (verified, design doc §1.16)

22b = **(a) research content + (b) bounded packaging**:

- **(a) the genuine research content** — the **rank-transport across the collapse
  map** from the contraction's generic IH via **algebraic independence** (KT §5.1 /
  eq. (6.9)): `∃` one placement with full exterior-projected surviving rank. This is
  the irreducible analytic step (the relabel-induced normal mismatch); it lands the
  *existence at a generic placement*.
- **(b) bounded packaging** — a **`D ∘ panelRow` variant** of the existing
  `exists_rankPolynomial_of_rigidOn_linking_set` (which builds its polynomial via the
  generic mirror `exists_polynomial_ne_zero_of_linearIndependent_at` from full-space
  rows `panelRow`). The variant feeds `D ∘ panelRow` (a fixed linear map ∘ the rows,
  still polynomially coordinatized) + a witness placement, producing the `Qc ≠ 0` +
  `∀`-non-root row-independence packaging the coupling consumes. No new matrix-rank
  theory; bounded — "no wall" per §1.16.

This form **avoids all four traps** documented for 22a (false `hpinc`; `∀`-GP-rigid;
`∀`-GP-independent; consumer/false-equality) and restores leg-symmetry (both legs via
rank-poly non-roots). The recon rule + the `∀`-GP-vs-generic-locus sharpening are in
`DESIGN.md` *Match the source's argument structure, not just its conclusion*.

## Lemma checklist

Skeleton (settle the exact node cut in the 22b opening recon, math-first per
`DESIGN.md` *Constructibility recon …*):

- [ ] **(a) rank-transport lemma** (research-shaped) — the algebraic-independence
  rank-transport across the collapse map from the contraction's generic IH: `∃` one
  placement at which the surviving block attains full exterior-projected rank
  (KT §5.1 / eq. (6.9)).
- [ ] **(b) `D ∘ panelRow` producer variant** (bounded) — the `D ∘ panelRow` sibling
  of `exists_rankPolynomial_of_rigidOn_linking_set`: package (a)'s witness placement
  into `∃ Qc ≠ 0, ∀ q, eval q Qc ≠ 0 → ∃ rsc, … D-projected-independent`.
- [ ] **wire-up / flip** — discharge `case_I_realization`'s `hclaim64` from (a)+(b);
  flip `lem:claim-6-4` green and `lem:case-I-realization` to fully green (drop the
  green-modulo marker on each user-facing surface, à la 21b).

## Blockers / open questions

- **Sub-phase cut/ordering is NOT settled here.** 22b's scope in this scaffold is
  *just Claim 6.4*. Whether the parked Case-III-at-`d=3` + `d=3`-assembly territory
  (currently ROADMAP's "22b+" row) becomes 22c+ etc., and the detailed within-22b
  node cut, is settled in the **22b opening recon** — the owner deferred this to the
  `coordinate-phase 22b` session. Do not finalize it before that recon.
- **Recurring Lean traps** (FRICTION; `notes/Phase22a.md` *Hand-off*): the heavy
  `IsInfinitesimallyRigidOn` defeq across `ofNormals`/`withGraph` graph-swaps (state
  hypotheses pre-converted; transfer across an `infinitesimalMotions` equality needs
  a `mem_infinitesimalMotions` round-trip); a leading `|>.proj` on a wrapped
  continuation line can fail to parse (use prefix-application form).

## Hand-off / next phase

22b is a scaffold; the first concrete commit is the **22b opening recon** —
decompose the §1.16 discharge path (a)+(b) into nodes, settle the within-22b cut and
whether the Case-III/assembly territory renumbers to 22c+, then build the bounded
packaging brick (b) (the likely first buildable commit; (a) is research-shaped and
may itself decompose). Cross-references rather than re-derivation:
`notes/Phase22-realization-design.md` §1.13–§1.16 (the block-triangular reframe + the
`Qc`-non-root form), §1.7 (collapse-transport irreducibility); `notes/Phase22a.md`
*Hand-off* (*22b target — Claim 6.4*) + *Blockers*; `DESIGN.md` *Match the source's
argument structure, not just its conclusion* (incl. the `∀`-GP-vs-generic-locus
sharpening). Follow `CLAUDE.md` *When this commit closes a phase* when
`lem:claim-6-4` / `lem:case-I-realization` flip fully green.
