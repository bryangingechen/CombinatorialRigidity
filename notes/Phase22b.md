# Phase 22b — KT Claim 6.4 (Case-I green-modulo discharge) (work log)

**Status:** in progress (opened 2026-06-05 as the coordinator's Close-C of Phase 22a;
opening recon landed 2026-06-05).

Stratum 5 of the molecular-conjecture program, continued. **Scope: just KT
Claim 6.4** — the single deferred obligation Phase 22a left green-modulo. 22a's
Case-I realization composer `PanelHingeFramework.case_I_realization`
(`AlgebraicInduction/CaseI.lean`) / blueprint `lem:case-I-realization` is green-modulo
one dischargeable hypothesis, `hclaim64`, tracked by the red blueprint node
`lem:claim-6-4`. 22b's target is to **discharge it** — flipping `lem:claim-6-4`
green and `lem:case-I-realization` to fully green.

This is the same green-modulo → discharge pattern as Phase 21 → 21b. The KT math
is **worked out** in `notes/Phase22-realization-design.md` §1.13–§1.16 and
`notes/Phase22a.md` *Hand-off* / *Blockers*; 22b **formalizes** it, it does not
re-derive it. Forward-mode / structural-edit (`blueprint/CLAUDE.md`): 22b opens no
new chapter — `lem:claim-6-4` is the existing red node in `algebraic-induction.tex`;
Lean lands in `Molecular/AlgebraicInduction/CaseI.lean`.

## Current state

22b discharges **KT Claim 6.4** (`lem:claim-6-4` / the composer's `hclaim64`
hypothesis). The green-modulo source is 22a's `case_I_realization`: axiom-clean,
build + lint green, honestly green-modulo this one hypothesis + the KT Lemma-6.3 case
hypothesis `hcSimple` (the latter is a case hypothesis, not a 22b target). **The
opening recon (this commit) is landed:** the §1.16 discharge path (a)+(b) is
decomposed into the node cut below (N-22b-1 research / N-22b-2 bounded / N-22b-3
wire-up), the within-22b cut and the 22c+ renumbering are settled (see *Blockers /
settled*), and the feasibility of brick (b) is re-verified against the live engine.
**N-22b-2 (the bounded `D ∘ panelRow` producer variant) is landed** —
`PanelHingeFramework.exists_rankPolynomial_of_rigidOn_linking_set_proj` in
`AlgebraicInduction/CaseI.lean`, axiom-clean (`propext`/`Classical.choice`/`Quot.sound`
only), build + lint warning-clean. **N-22b-1 (the research-shaped rank-transport) is now
also landed** — `PanelHingeFramework.rigidContract_exterior_rank_transport` in
`AlgebraicInduction/CaseI.lean`: the §1.16 exterior-projected-row form of KT Claim 6.4
/ eq. (6.9), carrying the irreducible algebraic-independence content as the explicit
hypothesis `htransport` (the established Phase-21b green-modulo `h…` idiom — the
faithful exterior-projected analogue of G3a's superseded motion-space
`rigidContract_rigidity_transport`); the brick extracts the contraction's generic IH and
forwards the `(q₀, t, hsupp, hcount, hindep)` witness in N-22b-2's exact shape. The
math-first re-recon settled the layer (design doc §1.17: the analytic core admits no
green-brick reduction, so it is carried as `htransport`; the brick is plumbing only).
Axiom-clean, build + lint warning-clean. Nothing is mid-stream. **The next concrete
commit is the one-step wire-up N-22b-3** (compose N-22b-1 → N-22b-2 to discharge the
composer's `hclaim64`, then flip `lem:claim-6-4` + `lem:case-I-realization` fully green),
per the build order below.

### Opening recon — feasibility re-verification (this commit)

Confirmed against the live Lean before settling the cut:

- **Brick (b) has no wall (re-verified against the engine).** The bounded packaging
  variant feeds the engine `exists_polynomial_ne_zero_of_linearIndependent_at`
  (`Mathlib/LinearAlgebra/Matrix/Rank.lean`), which is fully generic in its target
  space: it takes `g : (σ → ℝ) → ι → W` into *any* `[Module.Finite ℝ W]` space with a
  polynomial coordinatization `hg : φ (g p i) j = eval p (c i j)` and produces the
  `Qc ≠ 0` + `∀`-non-root LI packaging. The existing
  `exists_rankPolynomial_of_rigidOn_linking_set`
  (`GenericityDevice.lean:1285`) instantiates it at `W = Module.Dual ℝ (α → ScrewSpace
  k)` with `g q i := panelRow ends i`. Brick (b) re-instantiates it at the
  **post-projection** family `g q i := (extProj sH).dualMap (panelRow ends i)` — a
  fixed linear map ∘ the rows, still polynomially coordinatized (`D` is `q`-independent
  and `D ∘ panelRow` is linear in the same panel coordinates), so the coordinatization
  `hg` survives as the `φ'`-pullback of `D ∘ g` for any basis `φ'` of the (finite-dim)
  codomain. **No new matrix-rank theory.** This is exactly the §1.16 "no wall" claim,
  now checked against the engine signature rather than asserted.
- **The composer's `hclaim64` shape is the discharge target verbatim.**
  `case_I_realization`'s `hbundle` third conjunct (CaseI.lean:1187–1198 after the N-22b-1
  insertion) is, for each
  `Q : PanelHingeFramework k α β` realizing `G.rigidContract H r` at its rank, exactly
  `∃ Qc ≠ 0, ∀ q, eval q Qc ≠ 0 → ∃ rsc, (links in G ＼ E(H)) ∧ |rsc| ≥ D(|sc|−1) ∧
  LinearIndependent ℝ (i ↦ (extProj V(H)).dualMap (panelRow ends i))`. N-22b-3 must
  produce *this* term from N-22b-1 (the witness placement) + N-22b-2 (the packaging).
  Both halves are present in the form the composer already consumes — the wire-up is
  a discharge of one existing hypothesis, not a re-statement.

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

**Node cut settled in the opening recon** (math-first per `DESIGN.md`
*Constructibility recon …*). Three nodes, in build order. **N-22b-2 is the first
buildable commit** (bounded); N-22b-1 is research-shaped and may itself decompose;
N-22b-3 is the one-step wire-up + flip.

- [x] **N-22b-2 — `D ∘ panelRow` producer variant** (bounded; *first buildable*) —
  **LANDED.** `PanelHingeFramework.exists_rankPolynomial_of_rigidOn_linking_set_proj`
  in `AlgebraicInduction/CaseI.lean` (sibling of the un-projected
  `exists_rankPolynomial_of_rigidOn_linking_set` in `GenericityDevice.lean`). Takes the
  **already-witnessed subfamily `t`** with its support `hsupp`, count `hcount : m ≤
  Nat.card t`, and the **projected independence at `q₀`** `hindep` (the N-22b-1 output)
  as hypotheses, and produces
  `∃ Qc ≠ 0, ∀ q, eval q Qc ≠ 0 → ∃ rsc, (links) ∧ m ≤ Nat.card rsc ∧
  LinearIndependent ℝ (i ↦ (extProj t).dualMap (panelRow ends i))`. Passes `t`/`hsupp`/
  `hcount` through unchanged (the N7b-0 extraction is *upstream*, fed in, not re-derived
  here — cleaner factoring than the recon's proposed shape). Built by re-instantiating
  the engine `exists_polynomial_ne_zero_of_linearIndependent_at` at the post-projection
  family `gD q i := D (panelRow ends i)`, `D = (extProj t).dualMap`; the coordinatization
  `hgD` is the parent's standard-basis pullback `hg` post-composed with `D`, where each
  projected coordinate is the matrix-pullback polynomial `cD i j := ∑ l, C (M j l) · c i l`
  via the matrix `M` of `φ ∘ D ∘ φ⁻¹`. **No new matrix-rank theory** (the engine is
  generic in its codomain). One supporting private helper
  `coord_linearMap_eq_matrix_mulVec` (the `φ (D w) j = ∑ l, M j l · φ w l` matrix-mulVec
  fact) is stated over an **abstract** finite-dim ℝ-space rather than the heavy
  `Module.Dual ℝ (α → ScrewSpace k)`, reusing the documented anti-`whnf` abstract-mirror
  lesson (FRICTION *`Basis.linearIndependent.map'` … blows up at `whnf`* → *General
  lesson*). Axiom-clean; build + lint warning-clean.
- [x] **N-22b-1 — rank-transport lemma** (research-shaped; the genuine analytic
  content) — **LANDED.** `PanelHingeFramework.rigidContract_exterior_rank_transport` in
  `AlgebraicInduction/CaseI.lean`. The algebraic-independence rank-transport across the
  collapse map: from the contraction `G.rigidContract H r`'s generic IH
  (`HasGenericFullRankRealization`), produce **one parent placement `q₀`** + a witnessed
  subfamily `t` of `G ＼ E(H)`-links at which the surviving block, exterior-projected onto
  the `V(G)∖V(H)` columns, attains independent rank `≥ D(|sc|−1)` (KT §5.1 / eqs.
  (6.5)/(6.9)) — i.e. exactly the `(q₀, t, hsupp, hcount, hindep)` tuple N-22b-2 consumes.
  The **math-first re-recon** (design doc §1.17) settled the layer: the collapse redirects
  surviving-edge normals, so the green linking-edge brick
  `infinitesimalMotions_eq_of_isLink_span_supportExtensor` does not apply (its `hspan`
  fails) and the Phase-21b genericity device addresses a distinct obligation (§1.7
  irreducibility, corroborated against the projected form). The irreducible
  algebraic-independence content is therefore carried as the explicit hypothesis
  `htransport` (Phase-21b green-modulo `h…` idiom; the faithful exterior-projected analogue
  of G3a's superseded motion-space `rigidContract_rigidity_transport`); the brick extracts
  the IH `⟨Q, hQg, hQgp, hQrig⟩` and forwards the witness — plumbing only. Axiom-clean
  (`propext`/`Classical.choice`/`Quot.sound`), no `sorry`; build + lint warning-clean. A
  future pass may discharge `htransport` itself (an abstract algebraic-independence
  rank-preservation brick + the collapse-normal bookkeeping), a separate deeper undertaking.
- [ ] **N-22b-3 — wire-up / flip** (one step). Discharge `case_I_realization`'s
  `hclaim64` by composing N-22b-1 (witness `q₀`) → N-22b-2 (`Qc`-non-root packaging),
  producing the `hbundle` third conjunct verbatim. Then flip: drop the `hclaim64`
  hypothesis from `case_I_realization` (or specialise it to the discharged form),
  `\leanok` `lem:claim-6-4` + add its `\lean{…}` pin, and drop the green-modulo marker
  on each user-facing surface (à la 21b — see `CLAUDE.md` *When this commit closes a
  phase*).

**Build order:** N-22b-2 (bounded, first buildable) ✓ → N-22b-1 (research-shaped) ✓ →
N-22b-3 (flip) — next. N-22b-2 led because it is the bounded brick whose feasibility was
already re-verified; N-22b-1 then landed the analytic core (carried as `htransport`).
Only the one-step wire-up + flip (N-22b-3) remains. (Mirrors 22a's "buildable bricks
before the research-shaped composer" ordering.)

## Blockers / settled in the opening recon

- **Sub-phase cut — SETTLED.** 22b's scope is *just Claim 6.4*, cut into the three
  nodes N-22b-1/2/3 above (build order: N-22b-2 → N-22b-1 → N-22b-3).
- **Renumbering — SETTLED: the parked territory renumbers `22b+` → `22c+`.** 22b is
  now a distinct, tightly-scoped sub-phase (one deliverable, Claim 6.4), so the parked
  Case-III-at-`d=3` + `d=3`-assembly body of work should not share its label.
  Renumber the old "22b+" row to **22c+** (still a single planning placeholder,
  expected to split into multiple sub-phases — 22c = Case III at `d=3` / Track B,
  22d = the `d=3` assembly is the *likely* further cut, but that finer split is
  deferred until 22c opens, exactly as 22a deferred the 22b+ cut). Rationale: each
  sub-letter names one distinct sub-phase; "22b+" conflated 22b's discharge with a
  separate multi-phase undertaking. The integer phase numbers 23–26 stay stable
  (Track B at general `d`, the matroid/projective/molecule capstones). This recon
  applies the renumber to ROADMAP, `notes/MolecularConjecture.md`, and the user-facing
  surfaces in the same commit.
- **Recurring Lean traps** (FRICTION; `notes/Phase22a.md` *Hand-off*): the heavy
  `IsInfinitesimallyRigidOn` defeq across `ofNormals`/`withGraph` graph-swaps (state
  hypotheses pre-converted; transfer across an `infinitesimalMotions` equality needs
  a `mem_infinitesimalMotions` round-trip); a leading `|>.proj` on a wrapped
  continuation line can fail to parse (use prefix-application form).

## Hand-off / next phase

**N-22b-2 + N-22b-1 landed (both green-modulo bricks of Claim 6.4 in place).** The next
concrete commit is the **one-step wire-up + flip N-22b-3**: discharge the composer
`case_I_realization`'s `hclaim64` by composing
`rigidContract_exterior_rank_transport` (N-22b-1: from the contraction's generic IH `Q`,
its witness `q₀` + subfamily `t`) → `exists_rankPolynomial_of_rigidOn_linking_set_proj`
(N-22b-2: `Qc`-non-root packaging at `G := G.deleteEdges E(H)`, `proj := V(H)`,
`m := screwDim k * (|sc|−1)`), producing the `hbundle` third conjunct verbatim. Then
flip: drop the `hclaim64` hypothesis from `case_I_realization` (or specialise it to the
discharged form — note N-22b-1 still carries the `htransport` hypothesis, so the *flip*
either threads `htransport` up to the composer or discharges it; confirm at open whether
`lem:claim-6-4` goes fully green or stays green-modulo `htransport`). On a full green:
`\leanok` `lem:claim-6-4` + add its `\lean{…}` pin, drop the green-modulo marker on each
user-facing surface (à la 21b — see `CLAUDE.md` *When this commit closes a phase*), and
`checkdecls` per `blueprint/CLAUDE.md`.

**Watch-point for N-22b-3.** N-22b-1 and N-22b-2 are stated against a *free* `ends`
selector, but the composer manufactures `ends := G.endsOf` and binds
`G := G.deleteEdges E(H)`, `proj := V(H)`. Confirm the `IsLink`-on-`G ＼ E(H)` support
shapes and the `screwDim k * (sc.ncard − 1)` counts line up verbatim with `hclaim64`'s
conjunct (`CaseI.lean:1187–1198`) when the two bricks are composed at those bindings —
the count and `D = (extProj V(H)).dualMap` already match by construction (verified during
the §1.17 re-recon), so the wire-up should be a clean `obtain`/`exact`.

Cross-references rather than re-derivation: `notes/Phase22-realization-design.md`
§1.17 (the N-22b-1 layer re-recon + the `htransport` decision), §1.16 (the `Qc`-non-root
form + the engine "no wall"), §1.14 (the block-triangular reframe), §1.7
(collapse-transport irreducibility); `notes/Phase22a.md` *Hand-off*
(*22b target — Claim 6.4*) + *Blockers*; the live `hclaim64` shape at
`CaseI.lean:1187–1198`; the two landed bricks
`rigidContract_exterior_rank_transport` + `exists_rankPolynomial_of_rigidOn_linking_set_proj`
in `CaseI.lean`; `DESIGN.md` *Match the source's argument structure, not just its
conclusion* (incl. the `∀`-GP-vs-generic-locus sharpening). Follow `CLAUDE.md` *When this
commit closes a phase* when `lem:claim-6-4` / `lem:case-I-realization` flip fully green.
