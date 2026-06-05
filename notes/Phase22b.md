# Phase 22b — KT Claim 6.4 (Case-I green-modulo discharge) (work log)

**Status:** in progress — **discharging `htransport` (the U1→U4 cut); U1 + U2 landed (sound), the
U3b pin-count walling node now LANDED, the `Z ⊔ W = ⊤` assembly remains** (opened 2026-06-05 as the
coordinator's Close-C of Phase 22a; opening recon + the reduction N-22b-1/2/3 landed 2026-06-05; the
T2b math-first re-recon landed 2026-06-05; U2 opened + reconciliation core landed 2026-06-05; **U1 +
the U2 per-edge tail landed 2026-06-05** as `9098129`; the U3b build-recon corrected 2026-06-05
(design doc §1.22); **the U3b pin-count sub-lemma (the §1.22 walling node) landed 2026-06-05, this
commit**). The phase does *not* close until `htransport` is discharged: `lem:claim-6-4` stays red
green-modulo it (KT eq. (6.9)'s algebraic-independence content). **This commit lands the §1.22 U3b
walling node** `finrank_pinnedMotionsOn_of_isInfinitesimallyRigidOn_vertexSet_inter_eq_singleton`
(+ two supporting `s ⊇ V(G)` pin bricks) in `Pinning.lean`; axiom-clean, build + lint warning-clean.

**Course-correction (2026-06-05; design doc §1.20).** The U2-opening session **forked under
backgrounding**: its (lost) pre-reset analysis found that §1.19's "walling node retired at U2 / U3
is plumbing" is **wrong** — the research-shaped crux did not vanish, it *moved from U2 to U3*. The
post-reset (context-wiped) instance committed the sound U1 + U2 Lean (`9098129`) but wrote an
over-optimistic hand-off; that commit keeps the Lean and corrects the notes. U2 (the collapse-relabel
*row reconciliation* `panelRow_collapseTo_comp_extProj_dualMap` + `hingeRow_collapseTo_comp_extProj_eq`
+ U1 `degeneratePlacement`, KT's `p2`) **is** genuinely done. But the actual content of **KT Claim
6.4** — that the exterior-column projection `(extProj V(H)).dualMap` (which drops exactly the
`r`-column) *preserves* independent rank `D(|sc|−1)` — is a **pin-a-body** fact that needs a new,
**missing** linear-algebra brick, and it sits in **U3** (split into U3a alignment + U3b the crux).
See §1.20 for the full O1/O2 analysis and the corrected cut.

**Second course-correction (2026-06-05; design doc §1.22, this commit).** The U3b build-recon
(traced against the live finrank machinery + the mathlib dual API) found §1.21's "U3b is a bounded
one-line Lemma 5.1 corollary" was itself **wrong**: §1.21 assumed `Qcf'` rigid ⟹ `finrank(Z) = D`,
but `Qcf'` is rigid on its *vertex set* `sc ⊊ α`, so `finrank(Z) = D(|scᶜ|+1)` and
`finrank(pinnedMotions r) = D·|scᶜ| ≠ 0`. The clean `D(|sc|−1)` projected rank survives via an
**exact free-isolated-body cancellation**, not a zero-rank-loss pin. §1.22 re-derives the
verified-closing layer: the brick reduces to `Z ⊔ range(extProj V(H)) = ⊤` (via the mathlib dual
API), whose one real-content fact is the rigid-block pin-count
`finrank(F.pinnedMotionsOn V(H)) = D(|scᶜ| − |V(H)| + 1)`. This is a docs-only re-recon (no Lean this
commit): it corrects the build target before building, exactly the §1.20 pattern, so the U3b build
opens on the right walling node (the pin-count sub-lemma) rather than a mis-stated one.

The U3b math-first recon is **done and corrected** (design doc §1.21 → **§1.22**, this commit):
§1.21's "bounded one-line Lemma 5.1 corollary" was **wrong** — it assumed `finrank(Z) = D`, but
`Qcf'` is rigid on its *vertex set* `sc` (a proper subset of `α`), so `finrank(Z) = D(|scᶜ|+1)` and
`finrank(pinnedMotions r) = D·|scᶜ| ≠ 0`. The clean `D(|sc|−1)` projected rank survives via an
**exact free-isolated-body cancellation**. The corrected layer (§1.22, verified-closing against the
live finrank machinery + the mathlib dual API): the brick reduces to `Φ ⊓ ker D = ⊥` ⟺
`Z ⊔ range(extProj V(H)) = ⊤`, whose **one real-content fact** is the rigid-block pin-count
`finrank(F.pinnedMotionsOn V(H)) = D(|scᶜ| − |V(H)| + 1)` (a small product-space iso peeling the
free isolated columns). All mathlib + green project facts are confirmed present. The next concrete
commit is the **U3b build, opening on that pin-count sub-lemma** (the walling node); then the
`Z ⊔ W = ⊤` assembly + the projected-subfamily extraction, then U3a (alignment) → U4 (assemble +
flip). The *Discharge plan* checklist (U3b item) + design doc §1.20/§1.21/§1.22 carry the design.

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

22b discharges **KT Claim 6.4** (`lem:claim-6-4`) down to its single irreducible
analytic core. **All three planned nodes N-22b-1/2/3 are landed.** N-22b-2 (bounded
packaging, `exists_rankPolynomial_of_rigidOn_linking_set_proj`) and N-22b-1 (the
research-shaped rank-transport `rigidContract_exterior_rank_transport`, carrying the
irreducible algebraic-independence content as the explicit hypothesis `htransport`)
landed first; **N-22b-3 (the wire-up) is now landed** — the composer
`PanelHingeFramework.case_I_realization`'s third `hbundle` conjunct was reshaped from the
fully-packaged `hclaim64` (`∃ Qc …`) to the narrower `htransport` single-placement witness
(matching N-22b-1), and the `Qc`-non-root packaging the block-triangular coupling consumes
is now **reconstructed in-proof** by composing N-22b-1 (`rigidContract_exterior_rank_transport`,
witness `q₀`/`t`) → N-22b-2 (`exists_rankPolynomial_of_rigidOn_linking_set_proj`, packaging).
The graph-arg mismatch (`ofNormals G` in the coupling vs. `ofNormals (G.deleteEdges E(H))`
in N-22b-2) closes by defeq — `panelRow` for `ofNormals` consults only `normal`/`ends`/
`supportExtensor`, all graph-independent — so the final `exact` unifies them with no glue.
Axiom-clean (`propext`/`Classical.choice`/`Quot.sound`), build + lint warning-clean.

**State of 22b: reduction landed (green-modulo `htransport`); paused at the reduction
checkpoint, NOT closed.** The honesty gate (`blueprint/CLAUDE.md` *Every hypothesis of a
`\leanok` node is discharged*) forbids `\leanok` on `lem:claim-6-4` while `htransport` is an
undischarged load-bearing hypothesis. So `lem:claim-6-4` gets its `\lean{}` pins (the two
bricks) but **stays red**; `lem:case-I-realization` stays legitimately green via the case-(b)
green-modulo pattern (its load-bearing hypothesis IS the conclusion of the `\uses`'d
`lem:claim-6-4`). The remaining work — discharging `htransport` itself — is **not** an
indefinite "separate, deeper undertaking": a 2026-06-05 validation pass (design doc §1.18)
re-derived §1.17 skeptically against KT §5.1/§6.2 + the live code and found `htransport`
decomposes into a concrete, tractable node cut; the follow-up **T2b math-first re-recon**
(design doc §1.19, this commit) refined it to a **4-node cut U1→U2→U3→U4** (~240–400 LoC, 3/4
plumbing/green-reuse, one research-shaped crux **U2** = the collapse-relabel projected-row
reproduction) after finding §1.18's planned crux T2b (lower-semicontinuity) is *already green
inside N-22b-2*. Per the coordinator decision it **stays Phase 22b** (the *Hand-off* below
carries the cut). Nothing is mid-stream.

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
  (`propext`/`Classical.choice`/`Quot.sound`), no `sorry`; build + lint warning-clean.
  Discharging `htransport` itself is the *Discharge plan* (T1–T4) below — tractable, stays 22b
  (design doc §1.18 corrects §1.17's "separate, deeper undertaking" overstatement).
- [x] **N-22b-3 — wire-up / flip** (one step) — **LANDED.** Reshaped
  `case_I_realization`'s third `hbundle` conjunct from the packaged `hclaim64` (`∃ Qc …`)
  to the narrower `htransport` single-placement witness (matching N-22b-1's `htransport`
  parameter), and reconstructed the `Qc`-non-root packaging in-proof by composing N-22b-1
  (`rigidContract_exterior_rank_transport`, witness `q₀`/`t`) → N-22b-2
  (`exists_rankPolynomial_of_rigidOn_linking_set_proj`, the bounded packaging) at the
  bindings `G := G.deleteEdges E(H)`, `proj := V(H)`, `ends := G.endsOf`. The graph-arg
  mismatch closes by defeq (`panelRow` is graph-independent for `ofNormals`), so the final
  `exact` to the block-triangular coupling unifies with no glue. Blueprint: `lem:claim-6-4`
  gets its `\lean{…}` pins (both bricks) but **stays red** (the honesty gate forbids
  `\leanok` while `htransport` is undischarged with no node); `lem:case-I-realization` stays
  legitimately green via the case-(b) green-modulo pattern. Axiom-clean, build + lint
  warning-clean, `checkdecls` green.

**Build order (reduction):** N-22b-2 (bounded, first buildable) ✓ → N-22b-1 (research-shaped) ✓ →
N-22b-3 (wire-up) ✓. N-22b-2 led because it is the bounded brick whose feasibility was
already re-verified; N-22b-1 then landed the analytic core (carried as `htransport`); the
wire-up composed them. This **reduces** Claim 6.4 to the single hypothesis `htransport`,
green-modulo which `lem:claim-6-4` stays red. (Mirrors 22a's "buildable bricks before the
research-shaped composer" ordering.)

### Discharge plan — the remaining 22b work (design doc §1.19, the T2b re-recon; supersedes §1.18's 5-node cut)

The 2026-06-05 T2b math-first re-recon (design doc §1.19, traced against the live brick/engine
signatures) **retired the §1.18 lower-semicontinuity worry** and shrank the cut **5→4 nodes**.
Finding: `htransport`'s conclusion is *single-placement* (`∃ q₀, …`), and the "generic ≥
degenerate" lift it gated on is **already green inside N-22b-2**
(`exists_rankPolynomial_of_rigidOn_linking_set_proj` builds the rank polynomial from one witness
placement). So the degenerate member `q₀^deg` (KT's `p2`) is itself a valid witness — no generic
placement needed — and the one walling node re-localizes from T2b to the **collapse-relabel
projected-row reproduction (U2)**. `Gc := G.deleteEdges E(H)`, `f := collapseTo r V(H)`,
`sc := (V(G)∖V(H)) ∪ {r}`, `D = screwDim k`. The discharge **opens on U2**
(the one research-shaped node) per `DESIGN.md` *Constructibility recon … → design the LAYER*.

- [x] **U1 — degenerate placement bridge `q₀^deg`** (KT's `p2`, eq. 6.7, H-side collapsed) —
  **LANDED.** `degeneratePlacement r t nrm : α × Fin (k+2) → ℝ := fun p ↦ nrm (collapseTo r t p.1) p.2`
  (`CaseI.lean`), the plain pullback of a normal field through the collapse map: bodies of `V(H)`
  all take the representative normal `nrm r`, surviving bodies keep `nrm a`. The reproduction
  `degeneratePlacement_ofNormals_normal` records `(ofNormals … (degeneratePlacement …)).normal a =
  nrm (collapseTo r t a)` (`rw [ofNormals_normal]; rfl`). *No* genericity/moment-curve — the witness
  is the degenerate member (design doc §1.19, Finding 2). `degeneratePlacement_ofNormals_normal` is
  *not* `@[simp]` (its LHS reduces by the existing `ofNormals_normal`; `simpNF` flagged the eager
  `@[simp]`, dropped per the Lean-CLAUDE.md gate). Axiom-clean, build + lint warning-clean.
- [x] **U2 — collapse-relabel projected-row reproduction** *(the crux; the live part of §1.18's
  T2a+T2b)* — **LANDED.** Column core landed in the U2 opening (`hingeRow_collapseTo_comp_extProj_eq`
  + `extProj_apply_collapseTo` / `extProj_apply_not_mem`); **this commit lands the per-edge tail**
  `panelRow_collapseTo_comp_extProj_dualMap` (`CaseI.lean`): for any index `i`, the projected
  uncollapsed surviving-edge `panelRow` of `ofNormals Gc ends q₀^deg` equals the projected collapsed
  `panelRow` of `ofNormals (Gc.map f) endsᶠ q₀^deg'` over the contracted graph. Both framings read the
  *same* support extensor (the degenerate placement's normal is `nrm ∘ f` either way) hence the *same*
  annihilator functional; the only difference is the `hingeRow` endpoints — uncollapsed `(ends e)` vs.
  relabelled `(f (ends e))` — which the column core reconciles under `(extProj V(H)).dualMap`. Proof:
  a `rw` chain through `panelRow`/`toBodyHinge_supportExtensor`/`ofNormals_{ends,normal}`/
  `dualMap_apply'`, then `dsimp only [degeneratePlacement]`, then the column core. This IS §1.7's
  irreducible collapse-normal *row* reconciliation as a single per-edge row equality — sound and done.
  **Caveat (corrected 2026-06-05, §1.20): this retires the collapse-relabel *row* crux, NOT the whole
  Claim-6.4 content.** The *projected-rank-preservation* crux (KT Claim 6.4 proper) is separate and
  moved to **U3b**. Axiom-clean, build + lint warning-clean.
- [ ] **U3a — alignment transport (O1; bricked, medium).** Move the IH `Qcf`'s rigidity on
  `sc = V(Gc.map f)` to the constructed `endsᵐ`-selector framework `Qcf' := ofNormals (Gc.map f)
  endsᵐ (Qcf.normal-pullback)`, `endsᵐ e := (f (ends e).1, f (ends e).2)`, via the `ends`-swap brick
  `infinitesimalMotions_ofNormals_eq_of_ends_swap` (both selectors record links of `e` in `Gc.map f`,
  agree up to swap; swap cancels). The `hasGenericRealization_transport_ends` pattern. *Not* pure
  green-reuse, but not a wall.
- [ ] **U3b — pin-the-`r`-column projected-rank brick (O2; the genuine KT Claim 6.4 crux).** From
  `Qcf'` rigid on `sc`, show the exterior-column projection `(extProj V(H)).dualMap` — which drops
  *exactly the `r`-column* (`r` = the only `Qcf'` vertex in `V(H)`) — preserves independent rank
  `≥ D(|sc|−1)`. **Build-recon done + CORRECTED (design doc §1.22, this commit): §1.21's "one-line
  Lemma 5.1 corollary" was WRONG.** §1.21 read `Qcf'` rigid on `sc` as `finrank(Z) = D` ⟹
  `finrank(pinnedMotions r) = 0` ⟹ zero rank loss. But `Qcf'` is rigid on its **vertex set** `sc`,
  generally a *proper* subset of `α`, so `finrank(Z) = D(|scᶜ|+1)` (green
  `finrank_infinitesimalMotions_of_isInfinitesimallyRigidOn_vertexSet`), **not** `D` —
  `finrank(pinnedMotions r) = D·|scᶜ| ≠ 0`, and `(extProj V(H)).dualMap` does NOT drop the free
  isolated columns. The clean `D(|sc|−1)` survives only via an **exact free-isolated-body
  cancellation**, which must be proven. **Corrected, verified-closing layer (§1.22):** the brick
  reduces to `Φ ⊓ ker D = ⊥` (`D` injective on `Φ = span(linking rows)`, `finrank Φ = D(|sc|−1)` by
  green `span_panelRow_linking_eq_rigidityRows`), and by the mathlib dual API
  (`ker_dualMap_eq_dualAnnihilator_range` + `dualAnnihilator_sup_eq` + double-annihilator) that is
  `Z ⊔ range(extProj V(H)) = ⊤`. The **one real-content fact** is the rigid-block pin-count
  `finrank(F.pinnedMotionsOn V(H)) = D(|scᶜ| − |V(H)| + 1)` (`V(H)∩sc={r}`; pinning the `|V(H)|−1`
  isolated bodies of `V(H)∖{r} ⊆ scᶜ` removes `D(|V(H)|−1)` from `pinnedMotions r`'s `D·|scᶜ|`). All
  mathlib + green project facts confirmed present; the genuine kernel is a small product-space iso
  peeling the free isolated columns + an `extProj_range = ⨅ i ∈ V(H), ker(proj i)` identity. **Build
  opens on the pin-count sub-lemma** (the walling node, §1.22). The un-projected U3 tool does **not**
  suffice (projection can lower rank — the whole point of Claim 6.4).
  **U3b — pin-count walling node LANDED (this commit).** The §1.22 walling node is green
  (`Pinning.lean`): `finrank_pinnedMotionsOn_of_isInfinitesimallyRigidOn_vertexSet_inter_eq_singleton`
  — for `F` rigid on its vertex set and a block `t` with `V(F) ∩ t = {r}`,
  `finrank(F.pinnedMotionsOn t) = D·(|V(F)ᶜ| + 1 − |t|)` (the §1.22 pin-count, with the ℕ count
  stated subtraction-last per TACTICS-GOLF § 13 — the `|Vᶜ| − |t| + 1` real-arithmetic form
  truncates wrong at the boundary `t = {r} ∪ Vᶜ`). Built off two new supporting bricks
  (`pinnedMotionsOn_eq_iInf_ker_proj_of_vertexSet_subset` + `finrank_pinnedMotionsOn_of_vertexSet_subset`,
  the `s ⊇ V(G)` generalization of the green `pinnedMotionsOn_vertexSet_eq_iInf_ker_proj` /
  `finrank_pinnedMotionsOn_vertexSet`): pinning `t` ⇒ (rigidity propagates `S r = 0` over `V(F)`) ⇒
  `pinnedMotionsOn t = pinnedMotionsOn (V(F) ∪ t)`, whose dimension is the exact free-isolated count
  `D·|(V(F) ∪ t)ᶜ|`, then incl.–excl. on `|V(F) ∩ t| = 1`. All three axiom-clean
  (`propext`/`Classical.choice`/`Quot.sound`), build + lint warning-clean. **Remaining U3b:** the
  `Z ⊔ range(extProj V(H)) = ⊤` dual-annihilator assembly (using this pin-count + `finrank_iInf_ker_proj_eq`
  via the `extProj_range = ⨅ i∈V(H), ker(proj i)` identity + `finrank_sup_add_finrank_inf_eq`), then
  the projected-subfamily extraction (the U3-tool skeleton). The un-projected U3 tool does **not**
  suffice (projection can lower rank — the whole point of Claim 6.4). **Build target (remaining):
  the `Z ⊔ W = ⊤` assembly.**
- [ ] **U4 — assemble + flip.** U3b gives projected-*collapsed* independence; U2 (landed) carries it
  to projected-*uncollapsed* rows at `q₀^deg`; assemble `(q₀^deg, t, hsupp, hcount, hindep)` into
  `htransport`, translating subfamily indices from `Gc.map f`-links (at `endsᵐ`) to `Gc`-links (at
  parent `ends`) via a `Gc`-link `hends`; delete `htransport` from `case_I_realization`; `\leanok`
  `lem:claim-6-4`; then the phase-close ceremony (`CLAUDE.md` *When this commit closes a phase*).
  Plumbing; low risk.

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

**22b is discharging `htransport` (the U1→U4 cut); U1 + U2 landed (sound), one research-shaped crux
(U3b) remains.** The reduction N-22b-1/2/3 landed (KT Claim 6.4 formalized down to the single
hypothesis `htransport`); `lem:claim-6-4` carries its `\lean{…}` pins but stays red,
`lem:case-I-realization` stays legitimately green-modulo via the case-(b) pattern, ROADMAP row stays
◷. U1 (`degeneratePlacement` + `degeneratePlacement_ofNormals_normal`, KT's `p2`) and U2 (the
collapse-relabel *row* reconciliation: `panelRow_collapseTo_comp_extProj_dualMap` + the U2-opening
column core `hingeRow_collapseTo_comp_extProj_eq`) are landed and **sound** (`9098129`).

**Course-correction (design doc §1.20).** The U2-opening session **forked under backgrounding**; its
post-reset hand-off claimed "walling retired, U3+U4 plumbing" — **wrong**. The collapse-relabel
*row* crux (U2) is genuinely retired, but **KT Claim 6.4 proper — that the exterior-column
projection `(extProj V(H)).dualMap` (dropping the `r`-column) preserves rank `D(|sc|−1)` — is a
pin-a-body fact needing a MISSING brick, and it sits in U3b.** The crux did not vanish; it moved from
U2 to U3. §1.20 carries the recovered O1 (alignment, solved-in-principle) / O2 (projected rank, the
crux) analysis + the corrected cut.

The U3b **build-recon is done and corrected** (design doc §1.21 → **§1.22**): §1.21's "bounded
one-line Lemma 5.1 corollary" was wrong (it assumed `finrank(Z)=D`; `Qcf'` is rigid on its vertex
set `sc ⊊ α`, so `finrank(Z)=D(|scᶜ|+1)` and `finrank(pinnedMotions r)=D·|scᶜ|≠0`). §1.22 gives the
verified-closing layer: the brick reduces to `Z ⊔ range(extProj V(H)) = ⊤` (mathlib dual API), one
real-content fact = the rigid-block pin-count `finrank(F.pinnedMotionsOn V(H)) = D(|scᶜ|−|V(H)|+1)`.
**§1.22 was independently coordinator-verified** via a from-scratch motion-space decomposition (see
§1.22 *Coordinator verification*) — the layer is sound; do **not** re-recon it, build it.

**The U3b pin-count walling node is LANDED (this commit).** The §1.22 walling node is green in
`Pinning.lean`: `finrank_pinnedMotionsOn_of_isInfinitesimallyRigidOn_vertexSet_inter_eq_singleton`
— for `F` rigid on its vertex set and a block `t` with `V(F) ∩ t = {r}`,
`finrank(F.pinnedMotionsOn t) = D·(|V(F)ᶜ| + 1 − |t|)` (the ℕ count subtraction-last, TACTICS-GOLF
§ 13). Built off two new supporting bricks (`pinnedMotionsOn_eq_iInf_ker_proj_of_vertexSet_subset`
+ `finrank_pinnedMotionsOn_of_vertexSet_subset`, the `s ⊇ V(G)` generalization of the green
vertex-set pin lemmas). All three axiom-clean, build + lint warning-clean.

**The next concrete commit is the remaining U3b — the `Z ⊔ range(extProj V(H)) = ⊤` assembly**
(then the projected-subfamily extraction, the U3-tool skeleton), then U3a (alignment) and U4
(assemble + flip) (full statements/reuse/risk in the *Discharge plan* checklist above +
§1.20/§1.21/§1.22):
- **U3a** (O1; bricked, medium): move the IH `Qcf`'s rigidity on `sc = V(Gc.map f)` to the
  `endsᵐ`-selector framework `Qcf'` via the `ends`-swap brick
  `infinitesimalMotions_ofNormals_eq_of_ends_swap` (the `hasGenericRealization_transport_ends`
  pattern).
- **U3b** (O2; the genuine Claim-6.4 crux — recon-verified *bounded*, §1.22 + coordinator check):
  from `Qcf'` rigid on `sc`, the exterior-column projection preserves independent rank `≥ D(|sc|−1)`.
  **The pin-count sub-lemma is LANDED** (`finrank_pinnedMotionsOn_of_isInfinitesimallyRigidOn_vertexSet_inter_eq_singleton`,
  `Pinning.lean`, the walling node). **Remaining U3b build target = the `Z ⊔ range(extProj V(H)) = ⊤`
  dual-annihilator assembly** (pin-count + `finrank_iInf_ker_proj_eq` via a small
  `extProj_range = ⨅ i∈V(H), ker(proj i)` identity + `finrank_sup_add_finrank_inf_eq`) + the
  projected-subfamily extraction (the U3-tool skeleton). The un-projected U3 tool
  `exists_independent_panelRow_subfamily_of_rigidOn_linking_set` does **not** suffice (projection can
  lower rank — the point of Claim 6.4).
- **U4** (plumbing): U2 (landed) carries U3b's projected-*collapsed* independence to projected-*uncollapsed*
  rows at `q₀^deg`; assemble `(q₀^deg, t, hsupp, hcount, hindep)` into `htransport` (translating
  subfamily indices `Gc.map f`-link@`endsᵐ` → `Gc`-link@`ends`); delete `htransport` from
  `case_I_realization`'s `hbundle`; `\leanok` `lem:claim-6-4`; then the **full phase-close ceremony**
  — `CLAUDE.md` *When this commit closes a phase*: flip ROADMAP row to ✓ + compress its section, sync
  user-facing surfaces (`README.md`, `home_page/index.md`, `blueprint/src/chapter/intro.tex`), sync
  `notes/MolecularConjecture.md`, broadened blueprint re-read + `BlueprintExposition` ledger.

The surrounding territory (22c+: Case III at `d=3` + the `d=3` assembly) can proceed in parallel — it
depends on the green infra (N7b row sub-nodes, N7a, the device), not on `htransport`.

Cross-references rather than re-derivation: `notes/Phase22-realization-design.md`
**§1.20** (the course-correction: O1 alignment solved-in-principle / O2 projected-rank = the
genuine Claim-6.4 crux in U3b; corrects §1.19 — the crux moved U2→U3, not retired), §1.19 (the T2b
re-recon: lower-semicontinuity already green, the 4-node cut — but its "walling retired at U2 / U3
plumbing" is superseded by §1.20), §1.18 (the validation pass + the original 5-node cut + the phase-fit decision;
sharpens §1.17's irreducibility overstatement), §1.17 (the N-22b-1 layer re-recon + the
`htransport` decision), §1.16 (the `Qc`-non-root form + the engine "no wall"), §1.14 (the
block-triangular reframe), §1.7 (collapse-transport irreducibility); `notes/Phase22a.md`
*Hand-off* (*22b target
— Claim 6.4*) + *Blockers*; the wired composer `PanelHingeFramework.case_I_realization` + the
two bricks `rigidContract_exterior_rank_transport` +
`exists_rankPolynomial_of_rigidOn_linking_set_proj`, plus the discharge reuse targets
`exists_independent_panelRow_subfamily_of_rigidOn_linking_set`
(`GenericityDevice.lean`) and the moment-curve seed infra — all in `Molecular/`; `DESIGN.md`
*Match the source's argument structure, not just its conclusion* (incl. the
`∀`-GP-vs-generic-locus sharpening); `blueprint/CLAUDE.md` *Every hypothesis of a `\leanok`
node is discharged (the honesty gate)* — the rule that keeps `lem:claim-6-4` red while
`htransport` is undischarged.
