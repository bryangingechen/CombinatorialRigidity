# Phase 22e — candidate-completion + Claim 6.12 (KT §6.4.1, eqs. (6.24)–(6.45)) (work log)

**Status:** in progress (opened 2026-06-06 design-pass-first; opening recon +
eq.-(6.28) blueprint node + `w` constructibility recon + `w` node-cut landed).
Successor to 22d, the next chunk of Case III at `d=3` (KT §6.4.1,
Lemma 6.10). Lifts 22c's stratum-1 `D(|V|−1)−1` brick (`case_II_placement_eq612`,
green) to full `D(|V|−1)` by converting 22d's green redundant `ab`-row
(`exists_redundant_panelRow_ab_of_finrank_eq` = KT eq. (6.23)) into the missing
`+1` full-rank row, then resolving the `D`-candidate disjunction (Claim 6.12).
**Forward-mode / structural-edit:** no new blueprint chapter — the target nodes
(`lem:case-II-realization`, `lem:case-III`) are already stubbed red in
`algebraic-induction/case-ii.tex` / `case-iii.tex`; Lean lands in
`Molecular/AlgebraicInduction/` (+ `RigidityMatrix.lean` for LA leaves). KT math is
worked out in `notes/Phase22d.md` *Hand-off* + KT §6.4.1; 22e **formalizes** it.

## Current state

**Next concrete commit: build the seam identity for `w`** —
`R(G,p₁;E∖{vb},V∖{v}) = R(G_v^{ab},q)` (KT eq. (6.26)), the only research-shaped
piece left in the `w` construction (`lem:case-III-candidate-row`). The
constructibility recon (below) confirmed KT's eqs. (6.24)→(6.28) arithmetic closes
against this seam, so the node is cut and scheduled; the seam Lean statement is the
build.

**Landed this commit (docs-only, no Lean):**
- The green eq. (6.28) column-support leaf
  `BodyHingeFramework.dualMap_eq_comp_single_proj_of_vanish_off` (`RigidityMatrix.lean`,
  e8e7753, axiom-clean) now has its blueprint node `lem:case-III-vanish-off-column`
  (green, `\lean{}`+`\leanok`) under a new candidate-completion subsection in
  `case-iii.tex`. A row vanishing off `v`'s column factors as `(f ∘ₗ single v) ∘ₗ proj v`.
- The row-op `w` node `lem:case-III-candidate-row` is cut **red** (no `\lean{}` yet):
  KT eqs. (6.24)→(6.28) — transport the green redundant-`ab`-row combination
  (`exists_redundant_panelRow_ab_of_finrank_eq`) up to `R(G,p₁)` across the seam,
  giving `w ∈ span(R(G,p₁)-rows)` vanishing off `v`, which the eq.-(6.28) leaf turns
  into the pure `v`-column row `(Σⱼ λ_{(ab)j} rⱼ(q(ab)), 0)` of eq. (6.29).
- `lem:case-III` rewired to `\uses` both new nodes; its deferred-remainder prose now
  names the open piece precisely (the seam identity + the Claim-6.12 disjunction).

## Constructibility recon — `w`'s row operation (KT eqs. (6.24)→(6.28))

Read KT §6.4.1 pp. 684–686 (eqs. (6.22)–(6.30)) end-to-end against the green Lean.
**Verdict: the arithmetic closes; the only open Lean is the seam identity.**

- Claim 6.11 / eq. (6.23) gives the redundant `ab`-row; the green
  `exists_redundant_panelRow_ab_of_finrank_eq` delivers exactly KT's eq. (6.24)/(6.25):
  a redundant row `r i ∈ span(R(Gv,q)-rows) ⊔ span(r '' {j≠i})`, i.e. a vanishing
  combination of the `Gv`-rows + other `ab`-rows with `λ_{(ab)i*}=1`.
- **The seam (KT eq. (6.26), the build):** `R(G,p₁;E∖{vb},V∖{v}) = R(G_v^{ab},q)`.
  The `(ab)j`-row of `R(G_v^{ab},q)` ↔ the `(vb)j`-row of `R(G,p₁)` (KT (6.16)); the
  `ej`-rows (`e∈Ev`) correspond directly. Transporting the combination gives the new
  `(vb)i*`-row `w` (eq. (6.27)) in `span(R(G,p₁)-rows)`.
- **`V∖{v}` part of `w` vanishes:** those columns reproduce the `R(G_v^{ab},q)`-rows,
  which eq. (6.24) sums to 0.
- **`v`-column part:** `R(G,p₁;Ev,v)=0` (the `Ev`-edges avoid `v`, KT (6.16)), so only
  the `(vb)j`-rows contribute, `= Σⱼ λ_{(ab)j} rⱼ(p₁(vb)) = Σⱼ λ_{(ab)j} rⱼ(q(ab))`
  (using `p₁(vb)=q(ab)`, the eq.-(6.12) degenerate placement).
- The eq.-(6.28) leaf (green) then certifies `w` as a pure `v`-column row.

KT typo noted (not blocking): p. 684 says the seam restricts to `E∖{vb}`, p. 685 says
`E∖{va}`; the substance (the `V∖{v}` columns reproduce `R(G_v^{ab},q)`) is the same.
No new BlueprintExposition ledger entry: this is a *planned* node-cut matching KT's
stated argument, not a reroute surfacing a new insight (ledger inclusion = KT-math
reroute, not planned scoping).

## Red-node consistency gate — recon verdict (2026-06-06, this commit)

Read the three target red nodes end-to-end (statement + proof); ran the
supersession gate (`blueprint/CLAUDE.md` *Static checks → the supersession gate*)
over `algebraic-induction/*.tex`. **All consistent; gate clean.**

- **`lem:case-II-realization`** (case-ii.tex, KT's Case III producer) — statement +
  proof both route through `lem:case-II-realization-placement` (eq. (6.12) degenerate
  placement) → the N7a glue `lem:realization-of-independent-rows`. The two earlier
  dead-ends (row-side N7b-4, motion-side M1–M3) are named only as audit-trail
  `\cref{}` pointers, explicitly "off this route". Statement+proof `\uses` reach no
  superseded node.
- **`lem:case-II-realization-placement`** (genericity-and-count.tex) — routes through
  the green N7b-0/1/2/3 (`-new-rows`, `-old-rows`, `-old-rows-extract`,
  `-block-independent`) + the eq. (6.12) degeneracy (`p₁(vb)=q(ab)`, the `vb`-row
  reproduces the `e₀`-row). Superseded N7b-4 / M1–M3 referenced via audit-trail
  `\cref{}` only, never `\uses`.
- **`lem:case-III`** (case-iii.tex, the deferred Case-III target) — statement `\uses`
  the full green Claim-6.11 chain + `lem:case-II-realization-placement` (stratum-1
  brick) + `lem:extensor-independence` (green Lemma 2.1); proof "Deferred to
  Phases 22–23". The candidate-completion + Claim 6.12 are correctly its named
  deferred remainder. No superseded `\uses`.
- **Supersession gate:** superseded labels = {`-disjoint-line-meet`, `-e0-recovery`,
  `-motion-side-assembly`, `-pin-vertex`}; live-node-reaching-superseded set = ∅.
  All four carry the `superseded` marker in their environment title and `\uses` only
  each other or nothing.

**Verdict: the build is safe to scope.** The statements route through the same
argument they claim; the green N7b infra + the 22d redundant-`ab`-row are real
inputs; the candidate-completion is the genuine remaining content (no smuggled
hypothesis, no dead-end on the live route).

## Architectural choices made up front

- **Boundary preservation (confirmed against the existing plan).** The downstream
  `d=3` assembly (`prop:rigidity-matrix-prop11` `hub` partition brick — Track-%
  independent, Phase-19-partition — + the `thm:theorem-55` flip + wiring the
  fully-green `case_I_realization`) and **general-`d`** (Lemma 6.13) **stay separate**,
  as planned (ROADMAP §22 / `notes/MolecularConjecture.md`): the `d=3` assembly is the
  next deferred-unlettered cut after 22e, general-`d` is **Phase 23**. The recon found
  no reason to fold either in. 22e's scope is exactly the candidate-completion
  (eqs. (6.24)–(6.29)) + the Claim-6.12 disjunction (eqs. (6.30)–(6.45)) at `d=3`,
  stratum 1 — the content that takes `lem:case-II-realization` / `lem:case-III` from
  red to (the `d=3` half of) green.
- **Design-pass-first** (`DESIGN.md` *Scale-up: design the LAYER, not just the node*).
  Like 22c/22d, this is research-shaped and interlocking (the row-op `w` construction
  + the `D`-candidate disjunction + the eq. (6.44) "same `r`" reduction onto Lemma 2.1).
  Opened on this recon, not a build.

## Lemma checklist

- [x] `BodyHingeFramework.dualMap_eq_comp_single_proj_of_vanish_off` — eq. (6.28)
  column-support core (green, e8e7753). **Blueprint node `lem:case-III-vanish-off-column`
  added this commit (green).**
- [x] Constructibility recon on `w`'s row operation (KT eqs. (6.24)→(6.28)) — done
  this commit; arithmetic closes (verdict above). Node `lem:case-III-candidate-row`
  cut red.
- [ ] **The seam identity** `R(G,p₁;E∖{vb},V∖{v}) = R(G_v^{ab},q)` (KT eq. (6.26)) —
  the next build, the only research-shaped Lean left in `w`'s construction. The
  `(vb)j`↔`(ab)j` + `ej`↔`ej` row correspondence on the `V∖{v}` columns. Once green,
  transport the redundant combination + apply the eq.-(6.28) leaf to land
  `lem:case-III-candidate-row`. Its eq. (6.18)/(6.22) finrank hypotheses are wired
  from the green seed-rank-bridge / rank-attainment via rank-nullity
  `dim Z + dim span(rigidityRows) = D|α|`.
- [ ] **The conditional `D`-row block** — `w` (now a pure `v`-column row by eq. (6.28))
  extends the `va`-block to a `D`-row new block (`linearIndependent_sum_pinned_block`),
  giving a `D(|V|−1)`-family **conditional** on the top-left `D×D` block being full
  rank (eq. (6.29)).
- [ ] **Claim 6.12** — the `D`-candidate extensor-span disjunction (de-risked: bottoms
  on the green Phase-17 Lemma 2.1 `omitTwoExtensor_linearIndependent`; the degree-2
  eq. (6.44) forces all candidates to test the same `r ∈ ℝ⁶`, which ⟂ all `d+1`
  generic-panel extensors must vanish — contradiction, picking the full-rank candidate).
- [ ] **Flip** `lem:case-II-realization` (+ the `d=3` half of `lem:case-III`) green
  once the assembly lands. Candidate-completion subsection nodes
  (`lem:case-III-vanish-off-column` green, `lem:case-III-candidate-row` red) are in
  `case-iii.tex` as of this commit; the Claim-6.12 disjunction node is still to add.

## Blockers / open questions

- The constructibility recon (above) is done; the row-op arithmetic closes and the one
  research-shaped Lean piece is now isolated: the **seam identity**
  `R(G,p₁;E∖{vb},V∖{v}) = R(G_v^{ab},q)` (KT eq. (6.26)). Everything else (eq. (6.28)
  leaf — green; the pin-a-body block; the Lemma-2.1 disjunction) is bounded.
- **Recurring Lean trap (carry from 22a–d, FRICTION):** heavy
  `IsInfinitesimallyRigidOn` defeq across `ofNormals`/`withGraph` graph-swaps can
  `isDefEq`-timeout — make the two frameworks *syntactically* equal before `convert`;
  transfer rigidity via a `mem_infinitesimalMotions` round-trip. Bites in the
  candidate-completion assembly.

## Hand-off / next phase

**Next concrete commit: the seam-identity build.** State + prove in Lean (in
`RigidityMatrix.lean`, next to the `panelRow`/`rigidityRows` API)
`R(G,p₁;E∖{vb},V∖{v}) = R(G_v^{ab},q)` (KT eq. (6.26)): the `(vb)j`-row of `R(G,p₁)`
restricted to the `V∖{v}` columns equals the `(ab)j`-row of `R(G_v^{ab},q)`, and the
`ej`-rows (`e∈Ev`) correspond directly. This is the only research-shaped piece left in
the `w` construction (recon verdict above). It feeds `lem:case-III-candidate-row` (red,
cut this commit): once the seam is green, transport the green redundant-`ab`-row
combination across it and apply the green eq.-(6.28) leaf to produce `w`, the pure
`v`-column row. Watch the recurring `ofNormals`/`withGraph` defeq-timeout trap
(Blockers, FRICTION) — `R(G,p₁)` vs `R(G_v^{ab},q)` is exactly that graph-swap shape.

Downstream (still deferred, unlettered): the `d=3` assembly
(`prop:rigidity-matrix-prop11` `hub` brick + `thm:theorem-55` flip + Case-I wiring);
then general-`d` is **Phase 23**. KT math: `notes/Phase22d.md` *Hand-off*, KT §6.4.1
(eqs. (6.24)–(6.45)); `notes/AlgebraicIndependence.md` (the alg-independence tracker,
risk #8 — add a row if 22e introduces a new alg-independence use).

## Decisions made during this phase

### Phase-local choices and proof techniques
- **Open recon (2026-06-06).** Read the target red nodes end-to-end; ran the
  supersession gate clean; confirmed the existing planned boundaries (the `d=3`
  assembly + general-`d` Phase 23 stay separate). The eq. (6.28) leaf (e8e7753) folds
  in as the first green leaf; it needs a blueprint node, which 22e adds with the rest.
- **Candidate-completion node-cut (2026-06-06).** Added the candidate-completion
  subsection to `case-iii.tex`: `lem:case-III-vanish-off-column` (green, the eq.-(6.28)
  leaf) + `lem:case-III-candidate-row` (red, the eqs.-(6.24)→(6.28) row op). The
  constructibility recon (KT pp. 684–686) confirmed the arithmetic closes; the lone
  open Lean is the seam identity (KT eq. (6.26)). `lem:case-III` rewired to `\uses` both
  + its deferred-remainder prose sharpened to the seam + Claim 6.12. No new
  BlueprintExposition entry — planned scoping, not a KT-math reroute.
