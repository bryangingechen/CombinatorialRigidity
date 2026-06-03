# Phase 21 — Algebraic induction: Theorem 5.5 base + Cases I & II (work log)

**Status:** in progress (opened 2026-06-03). The mid-phase
panel-coplanarity re-scope (the panel-hinge = hinge-coplanar body-hinge
gap) is **resolved**: the gating foundations sub-phase **Phase 21a**
(Grassmann–Cayley meet) is complete (`notes/Phase21a.md`,
`Molecular/Meet.lean`), and the form-(B) panel plan is fixed in DESIGN.md
*Panel-hinge = hinge-coplanar body-hinge*. Phase 21 has **resumed** with
the panel layer; the earlier plan-first gate is cleared.

Stratum 5 of the molecular-conjecture program (the *algebraic* half of
Katoh–Tanigawa's proof, KT §5, §6.1–6.3). Where Phase 20 reduced every
minimal `0`-dof-graph to the two-vertex double edge combinatorially
(Theorem 4.9, `Graph.minimal_kdof_reduction`), this phase realizes that
reduction at the rigidity-matrix rank: KT **Theorem 5.5** (every minimal
`k`-dof-graph `G` with `|V| ≥ 2` has a panel-hinge realization with
`rank R(G,p) = D(|V|−1) − k`), its base case, **Case I** (proper rigid
subgraph), and **Case II** (`k>0` splitting). The crux **Case III**
(`k=0`, no proper rigid subgraph) is deferred to Phases 22–23.

Program-level plan, reuse map, citations, and risk register:
`notes/MolecularConjecture.md` *Phase 21*. Forward-mode dep-graph /
lemma index: `blueprint/src/chapter/algebraic-induction.tex`
(`sec:molecular-algebraic-induction`). Lean lands in a new file
`CombinatorialRigidity/Molecular/AlgebraicInduction.lean`.

## Current state

**Case II `hnew` reduction to per-edge span-membership landed (2026-06-03).** The brick that turns
the abstract `hnew` hypothesis of `pinnedMotions_withGraph_eq` into the concrete two-edge condition
the genericity device must discharge is green: `BodyHingeFramework.hnew_of_isLink_incident` and its
panel wrapper `PanelHingeFramework.toBodyHinge_hnew_of_isLink_incident`. In Case II's 1-extension
the only links of `F.graph` outside the splitting-off `G'` are `v`'s two new hinge edges (all
incident to `v`); for a base-`v`-pinned motion `S` (`S v = 0`) the hinge constraint `S v − S w ∈
span C(e)` of such an edge collapses to the single span-membership `S w ∈ span C(e)` at the non-`v`
endpoint (the pinned body contributes zero). So `hnew` follows from (a) every out-of-`G'` link is
`v`-incident (`hinc`) and (b) the non-`v` endpoint of each lands in the new edge's hinge span
(`hspan`). Proof: `rcases hinc` on the two orientations, `hingeConstraint_comm` to put `v` left in
the `w = v` case, then `hSv` + `zero_sub` + `Submodule.neg_mem_iff` reduce to `hspan`; the panel
wrapper is a defeq one-liner through `toBodyHinge_graph`. Axiom-clean
(propext/Classical.choice/Quot.sound). No friction. Blueprint folds both into the green
`lem:case-II-rank-lift` node (the per-edge collapse sentence + the two `\lean{...}` pins).
**Remaining red on Case II:** discharging `hspan` for the chosen general-position panel extensors
(the genuine Claim 6.9 content — *not* free for an arbitrary base motion; it holds via the rank/
dimension count, the genericity device) and wiring the vertex-level splitting-off op `G_v^{ab}`
(green in Phase 20, but differs from `G` by an edge substitution `e₀ ↔ {e_a,e_b}`, so it is not
directly `≤ G` — a graph-substitution bridge is needed) into `withGraph`.

**Case II genericity-gated tightness landed (2026-06-03).** The reverse `≥` half making the Case II
inclusion an *equality* is green: `BodyHingeFramework.pinnedMotions_withGraph_eq` (+ rank form
`finrank_pinnedMotions_withGraph_eq`) and its panel layer
`PanelHingeFramework.toBodyHinge_pinnedMotions_withGraph_eq` (+ rank form
`finrank_toBodyHinge_pinnedMotions_withGraph_eq`). For `G' ≤ F.graph`, `F.pinnedMotions v =
(F.withGraph G').pinnedMotions v` **provided** every base-`v`-pinned motion of `F.withGraph G'`
already satisfies the hinge constraint of each *re-added* edge (`hnew : ∀ S ∈ (F.withGraph
G').pinnedMotions v, ∀ e u w, F.graph.IsLink e u w → ¬G'.IsLink e u w → F.hingeConstraint S e u w`).
The `≤` is the green `pinnedMotions_le_withGraph`; the `≥` is exactly `hnew` (a base motion has
`S v = 0`, so the new `v`-incident constraints reduce to `S a ∈ span C(e_a)`, `S b ∈ span C(e_b)`).
`hnew` is the honest, genericity-free content of Claim 6.9: edges of `G'` are met automatically
(`withGraph` leaves their support extensors fixed), only the two new `v`-edges need clearing, the
job of `exists_independent_panelSupportExtensor` placing them in general position. Six declarations
(four lemmas + two rank forms); the panel wrappers route through `toBodyHinge_withGraph` and need
`omit [DecidableEq α]`. Proof is `le_antisymm` of the green `≤` with a `by_cases G'.IsLink` split
(in-`G'` edges close via `hS.1`, out-of-`G'` via `hnew`). Axiom-clean
(propext/Classical.choice/Quot.sound). No friction (mirror of `pinnedMotions_le_withGraph` +
`toBodyHinge_withGraph`). Blueprint folds all six into the green `lem:case-II-rank-lift` node (tight
inclusion sentence + the `lem:exists-independent-panel-extensor` `\uses` edge added). Composing with
the rank-lift `rankHypothesis_withNormal_iff_finrank_pinnedMotions` closes `lem:case-II`'s rank step.
**Remaining red on Case II:** wiring the vertex-level splitting-off op `G_v^{ab}` (green in Phase 20
combinatorially) into the panel rank-lift, and discharging `hnew` from the green general-position
existence (the two new supporting extensors independent) — the last two pieces of `lem:case-II`.

**Case II graph-half inclusion landed (2026-06-03).** The unconditional graph step of Case II's
1-extension is green: re-adding `v`'s two new hinge edges can only *shrink* the body-`v`-pinned
motions. Four one-liners. Body-hinge layer:
`BodyHingeFramework.pinnedMotions_le_withGraph` (`G' ≤ F.graph ⇒ F.pinnedMotions v ≤
(F.withGraph G').pinnedMotions v`, the single-body specialization of
`pinnedMotionsOn_le_withGraph_of_le` at `s = {v}` via the two `pinnedMotionsOn_singleton` rewrites)
and its rank form `finrank_pinnedMotions_le_withGraph`. Panel layer:
`PanelHingeFramework.toBodyHinge_pinnedMotions_le_withGraph` (the same inclusion through `toBodyHinge`,
routed by the green commute identity `toBodyHinge_withGraph` so coplanarity is preserved) and its rank
form `finrank_toBodyHinge_pinnedMotions_le_withGraph`. Read with `F`/`P` on the parent graph `G` and
`F.withGraph G'`/`P.withGraph G'` on the splitting-off `G_v^{ab} = G'`: the inductive realization of
`G_v^{ab}` bounds the extended framework's body-`v`-pinned dimension from above. The two panel lemmas
sit in the `[DecidableEq α]` `withNormal` block but don't need the binder (`omit [DecidableEq α] in`).
Axiom-clean (propext/Classical.choice/Quot.sound). No friction (mirror of `pinnedMotionsOn_le_with
Graph_of_le` + `toBodyHinge_withGraph`). Blueprint folds all four into the green `lem:case-II-rank-lift`
node (graph-step sentence added to its prose). **Remaining red on Case II:** the *equality* relating the
extended framework's `v`-pinned motions to the base's — the genericity-gated half (Claim 6.9, the two
new supporting extensors in general position so the inclusion is tight at the inductive dimension) —
plus wiring the vertex-level splitting-off op `G_v^{ab}` (green in Phase 20 combinatorially) into the
panel rank-lift.

**Case II rank-lift assembly landed (2026-06-03).** The panel-layer assembly that wires the
`withNormal` carrier into the `+D` rank-lift is green:
`PanelHingeFramework.rankHypothesis_withNormal_iff_finrank_pinnedMotions` — building the
1-extension by choosing a panel normal `n` for the re-inserted body `v`, the extended framework
`(P.withNormal v n).toBodyHinge` realizes the target rank at `k'` (`RankHypothesis k'`) iff the
*original* `P.toBodyHinge`'s body-`v`-pinned motions have dimension `k'`. Staged through two new
invariance lemmas under the no-incident-hinge hypothesis on `v` (`hv : ∀ e u w, P.graph.IsLink e u w
→ (P.ends e).1 ≠ v ∧ (P.ends e).2 ≠ v`): `toBodyHinge_withNormal_infinitesimalMotions_eq` (choosing
`v`'s panel leaves `Z(G,p)` unchanged when `v` is unhinged) and
`toBodyHinge_withNormal_pinnedMotions_eq` (hence every `pinnedMotions w` unchanged). Both rest on a
new general `BodyHingeFramework.infinitesimalMotions_eq_of_isLink_supportExtensor` (the motion space
depends only on the supporting extensors of the *linking* edges — two `infinitesimalMotions_mono_of_
graph_le`-style inclusions). The hypothesis `hv` is the honest, genericity-free content: it captures
"`v` carries no incident hinge yet" (true of `G_v^{ab}` before its two new edges are added), so the
panel normal at `v` is a free choice that the genericity step (Claim 6.9) later pins. Axiom-clean
(propext/Classical.choice/Quot.sound). No friction (mirror of `infinitesimalMotions_mono_of_graph_le`
+ submodule `ext`). Blueprint folds the two invariance lemmas into `def:framework-with-graph` and the
assembly into `lem:case-II-rank-lift` (both already green). **Remaining red on Case II:** *adding*
`v`'s two new hinge edges to the graph (via `withGraph`) and Claim 6.9 genericity ensuring the two
new supporting extensors are in general position — plus the vertex-level splitting-off op `G_v^{ab}`
(green in Phase 20 combinatorially).

**Case II panel-normal-extension carrier landed (2026-06-03).** The per-body panel-data primitive
Case II's 1-extension is assembled from is green: `PanelHingeFramework.withNormal v n` (override the
panel normal at the single body `v` by `n` via `Function.update`, keeping the multigraph, the
endpoint selector, and every other body's normal) with its simp lemmas (`withNormal_{graph,ends,
normal,normal_self}`, plus the non-simp `withNormal_normal_of_ne`) and the load-bearing invariance
`toBodyHinge_withNormal_supportExtensor_of_ne` (for an edge `e` whose endpoints `ends e` both avoid
`v`, the panel support extensor is unchanged). This is the per-body analogue of `withGraph` (which
swaps the whole graph): Case II re-inserts a reducible degree-2 body `v` into the splitting-off
`G_v^{ab}` by *choosing a panel normal for `v`*, and `withNormal` is the framework-side carrier of
that move; the invariance lemma is what carries the inductive realization of `G_v^{ab}` through the
1-extension untouched away from `v` (the `+D` lift coming entirely from `v`'s two new edges, accounted
by `rankHypothesis_iff_finrank_pinnedMotions`). Needs `[DecidableEq α]` (for `Function.update`),
carried on its own namespace block so the binder does not leak onto the earlier `[DecidableEq]`-free
panel lemmas. Axiom-clean (propext/Classical.choice/Quot.sound). No friction beyond the documented
`public section` `def`-opacity quirk (the `rfl` projection lemma `withNormal_normal` is rewritten
in before `Function.update_self`/`update_of_ne`, the standard pattern already used in this file).
Blueprint folds `withNormal` + the invariance into the existing green `def:framework-with-graph` node
(beside the panel `withGraph`). **Remaining red on Case II:** the actual rank-lift assembly — build the
extended `PanelHingeFramework` on `G` (via `withGraph` to add `v`'s two edges + `withNormal` to set
`v`'s panel), then show its body-`v`-pinned motions are the inductive motions of `G_v^{ab}` and apply
the `+D` accounting — plus the vertex-level splitting-off op `G_v^{ab}` and Claim 6.9 genericity.

**Panel `withGraph` carrier landed (2026-06-03).** The shared graph-swap primitive both
inductive cases need *on the panel layer* is green: `PanelHingeFramework.withGraph G'`
(swap the multigraph, keep `normal` + `ends`, hence every panel support extensor) with its
four `rfl` simp lemmas (`withGraph_{graph,normal,ends,graph_self}`) and the load-bearing
bridge `toBodyHinge_withGraph` (`(P.withGraph G').toBodyHinge = P.toBodyHinge.withGraph G'`,
`rfl`). This is the panel analogue of `BodyHingeFramework.withGraph`; the commute identity is
what lets the green body-hinge graph-monotonicity (`infinitesimalMotions_le_withGraph_of_le`)
and block-pin rank machinery (`pinnedMotionsOn_le_withGraph_of_le`,
`screwDim_add_finrank_pinnedMotionsOn_le`) apply verbatim to a panel realization placed on the
smaller inductive graph (`G/E(H)`, `G_v^{ab}`) and re-glued onto `G`, with coplanarity
preserved (the normals are untouched). Axiom-clean (propext/Classical.choice/Quot.sound). No
friction (mirror of an existing green def + trivial `rfl` lemmas). Blueprint folds the panel
`withGraph` + commute identity into the existing `def:framework-with-graph` node (still green;
now `\uses` `def:panel-hinge-framework`). **Remaining red on Cases I/II:** the vertex-level
graph ops on the panel layer (place panel data on `rigidContract`/`edgeSplit`, supply the
generic normals) and the block-triangular rank addition / Claim 6.4/6.9 genericity — the
combinatorial ops themselves (`rigidContract`, `splitOff`, `edgeSplit`) are green in Phase 20.

**Case I block-pin graph-monotonicity landed (2026-06-03).** The block-pin analogue of
`lem:motions-mono-of-graph-le` is green: `BodyHingeFramework.pinnedMotionsOn_le_withGraph_of_le`
(`G' ≤ G ⇒ pinnedMotionsOn s ≤ (withGraph G').pinnedMotionsOn s`) and its rank form
`…finrank_pinnedMotionsOn_le_of_graph_le` (`finrank` mono). The block pin is `infinitesimalMotions`
cut by the *graph-independent* vanishing conditions `∀ v ∈ s, S v = 0`, so the inclusion is the
already-green `infinitesimalMotions_le_withGraph_of_le` on the first conjunct, the vanishing
conditions carried unchanged; the rank form is `Submodule.finrank_mono` of it. This is the
direction Case I's block-triangular gluing travels: place the contraction realization on the
smaller `G/E(H)` and re-add `E(H)` — the block-pinned rank only grows, the slack in
`screwDim_add_finrank_pinnedMotionsOn_le` filled by the contraction's inductive rank. Axiom-clean
(propext/Classical.choice/Quot.sound). Blueprint adds a green `lem:pinned-motions-on-mono` node
(Case I section) that the still-red `lem:case-I` `\uses`. No friction (two one-liners mirroring
existing green lemmas). **Remaining red on Case I:** still the vertex-level contraction op `G/E(H)`
and the cited Claim 6.4 genericity / block-triangular gluing.

**Case I block-pin rank lower bound landed (2026-06-03).** The first rank-accounting
brick of Case I is green: `BodyHingeFramework.trivialMotions_inf_pinnedMotionsOn_eq_bot`
(for nonempty `s`, trivial ⊓ block-pin = ⊥ — the block analogue of Phase-18's
`trivialMotions_inf_pinnedMotions_eq_bot`, via `pinnedMotionsOn_le_pinnedMotions` into the
green singleton case) and `…screwDim_add_finrank_pinnedMotionsOn_le`
(`screwDim k + finrank (pinnedMotionsOn s) ≤ finrank Z(G,p)` — disjoint trivial + block-pin
submodules of `Z(G,p)`, via `finrank_sup_add_finrank_inf_eq` + `finrank_mono hle`). This is
the **inequality** form of the single-body pin-a-body **equality**
`finrank_pinnedMotions_add_screwDim`: a block pin of a rigid `H` collapses `V(H)` to one
effective body, the residual `D(|V(H)|−1)` constraints making it `≤` not `=`; the
contraction's inductive rank fills the slack. Axiom-clean (propext/Classical.choice/Quot.sound).
Blueprint adds a green `lem:pinned-motions-on-rank-bound` node (in the Case I section) that the
still-red `lem:case-I` `\uses`. **Remaining red on Case I:** the vertex-level contraction op
`G/E(H)` and the block-triangular gluing of the contraction realization with the pinned rigid
block (the genericity-device step, Claim 6.4).

**`m`-body cycle rigidity landed (2026-06-03).** The last remaining brick of
`lem:cycle-realization` (KT Lemma 5.4) — the general `m`-body cycle, `theorem_55_base`
analogue — is green: `BodyHingeFramework.rankHypothesis_zero_of_cycle` (cycle bodies `Fin m`,
`NeZero m`, edge `i` linking `i`→`i+1` cyclically, `m` independent supporting extensors ⇒
`RankHypothesis 0`) and its panel wrapper
`PanelHingeFramework.toBodyHinge_rankHypothesis_zero_cycle` (lifted verbatim through
`toBodyHinge`). The proof propagates `S i = S (i+1)` around the cycle: each hinge puts
`S i − S (i+1)` in `span C(p(eᵢ))`, the `m` differences telescope to `∑ = 0` (the shift
`i ↦ i+1` is `Equiv.addRight (1 : Fin m)`, a bijection), and the green core
`eq_zero_of_mem_span_singleton_of_sum_eq_zero` forces each to vanish; `S` is then constant on
the connected cycle (an `ℕ`-induction over `Fin.ofNat m j`, closed by `Fin.ofNat_val_eq_self`).
Staged through `eq_succ_of_isInfinitesimalMotion_cycle` (the step) and
`isTrivialMotion_of_isInfinitesimalMotion_cycle` (constancy). Axiom-clean
(propext/Classical.choice/Quot.sound). Blueprint adds a green `lem:cycle-realization-rigid`
node; `lem:cycle-realization` now `\uses` it and its three other pieces are all green, so only
the cited projective assembly (genericity device, Claim 6.4/6.9) is left non-Lean.

**Independent grade-2-join / panel-extensor existence landed (2026-06-03).** The existence
half of the genericity device is green: `exists_independent_normalsJoin` (for any
`m ≤ screwDim k = D`, there are `m` pairs of panel normals whose grade-2 joins are
independent in `⋀² ℝ^(k+2)`) and its screw-space corollary
`exists_independent_panelSupportExtensor` (via `panelSupportExtensor_linearIndependent_iff`).
The witness is a *basis choice*, not a perturbation: pick `m` distinct 2-subsets of
`Fin (k+2)` (possible since `Fintype.card (Set.powersetCard (Fin (k+2)) 2) = (k+2).choose 2 =
D ≥ m`) and take the corresponding pairs of `Pi.basisFun` standard basis vectors; each join is
then a member of the basis-indexed exterior-power family
(`exteriorPower.ιMulti_family_linearIndependent_ofBasis`), and the chosen subfamily inherits
independence via the index injection (`.comp g g.injective`). The member-identity bridge
`normalsJoin_basisFun_orderEmbOfFin` (`normalsJoin (b·)(b·) = ιMulti_family ℝ 2 b s` for a
2-subset `s`) is the `Fin 2`-eta plumbing. Axiom-clean
(`propext/Classical.choice/Quot.sound`). Blueprint adds a green
`lem:exists-independent-panel-extensor` node that the still-red `lem:cycle-realization`
`\uses`. **Remaining red on 5.4:** the `m`-body cycle `theorem_55_base` analogue
(propagating `S u = S v` around the cycle — needs a `Graph`-cycle/walk primitive; the
linear-algebra core `eq_zero_of_mem_span_singleton_of_sum_eq_zero` is already green).

**Genericity-device reduction landed (2026-06-03).** The substantive
reduction at the heart of Claim 6.4/6.9 is green:
`panelSupportExtensor_linearIndependent_iff` (AlgebraicInduction.lean,
beside the panel leaf) — a family of `m` panel support extensors is
linearly independent in `ScrewSpace k` iff the family of grade-2 joins
`normalsJoin (n₁ i) (n₂ i)` is independent in `⋀² ℝ^(k+2)`, because
`panelSupportExtensor = complementIso ∘ normalsJoin` and `complementIso`
(Phase 21a) is a `LinearEquiv` (preserves+reflects independence). Staged
through `panelSupportExtensor_eq_complementIso_comp_normalsJoin`
(definitional). This converts the still-open *analytic* generic-panel
independence question (the `lem:cycle-realization` blocker) into a
*concrete exterior-power-basis* question on the grade-2 joins — a basis
choice on `⋀²` (bottoming on Lemma 2.1) discharges it; `m ≤ D = dim ⋀²`
is the dimension cap already green
(`card_le_screwDim_of_supportExtensor_linearIndependent`). Axiom-clean
(propext/Classical.choice/Quot.sound). Blueprint adds a green
`lem:panel-support-extensor-independence` node that the still-red
`lem:cycle-realization` `\uses`. **Remaining red on 5.4:** the
*existence* of an independent grade-2-join family for a given cycle
(`3 ≤ m ≤ D`) — now a basis-selection construction
(`exteriorPower.ιMulti_family_linearIndependent_ofBasis` over
`Pi.basisFun`, picking `m` distinct 2-subsets of `Fin (k+2)`), plus the
`m`-body cycle `theorem_55_base` analogue (needs a `Graph`-cycle/walk
primitive to propagate `S u = S v` around the cycle).

**Panel framework landed (2026-06-03, resumed).** The panel layer now has
its framework structure in `Molecular/AlgebraicInduction.lean`:
`PanelHingeFramework` (graph + `normal : α → (Fin (k+2) → ℝ)` + endpoint
selector `ends : β → α × α`), its body-hinge interpretation `toBodyHinge`
(setting `supportExtensor e := panelSupportExtensor (normal u) (normal v)`
at `(u,v) = ends e`), and the coplanarity spec
`BodyHingeFramework.IsHingeCoplanar F := ∃ P, P.toBodyHinge = F` with
`isHingeCoplanar_toBodyHinge` (automatic for panel constructions). All
green, axiom-clean. **Design resolved (the open hand-off question):** went
option (a) — `BodyHingeFramework` now carries `supportExtensor : β →
ScrewSpace k` as a *field* (was `hinge : β → Fin k → Fin (k+1) → ℝ`); the
affine free-hinge model is preserved as the smart constructor
`BodyHingeFramework.ofHinge` (sets the field via `affineSubspaceExtensor`).
This decouples the Phase-18 rank theory from how the extensor arose, so
the affine hinge (`ofHinge`) and the panel hinge (`toBodyHinge`) feed the
same constraint family. `.hinge` was used *only* to define
`supportExtensor`, so the refactor is local: `supportExtensor_coe` became
`ofHinge_supportExtensor_coe`; `withGraph` copies the new field; all of
Phase 18 + the green Phase-21 nodes build unchanged. The earlier leaf
`def:panel-support-extensor` (`panelSupportExtensor`, `normalsJoin`, the
two nonvanishing iffs) is green and feeds `toBodyHinge` via
`toBodyHinge_supportExtensor_ne_zero_iff`.

Earlier leaf recap: `panelSupportExtensor n₁ n₂ := complementIso
(normalsJoin n₁ n₂)` is the meet of the two panels (the grade-2 join
`normalsJoin` in `⋀^2`, carried by Phase-21a `complementIso` to
`⋀^(k+2−2) = ⋀^k = ScrewSpace k`); `panelSupportExtensor_ne_zero_iff`
reduces transversality to independence of the two normals.

**Cycle-realization dimension bound landed (2026-06-03).** The
`|V| ≤ D` upper half of KT Lemma 5.4's hypothesis `3 ≤ |V| ≤ D` is
green: `card_le_screwDim_of_linearIndependent` (RigidityMatrix.lean,
beside `screwSpace_finrank`) — any linearly independent family of `m`
screw-space elements has `m ≤ screwDim k` — and its panel-cycle
specialization `PanelHingeFramework.card_le_screwDim_of_support
Extensor_linearIndependent` (AlgebraicInduction.lean). One-line
compositions of `LinearIndependent.fintype_card_le_finrank` with
`screwSpace_finrank`; axiom-clean (`#print axioms`:
`propext/Classical.choice/Quot.sound`). Blueprint adds a green
`lem:cycle-realization-dim-bound` node that the still-red
`lem:cycle-realization` `\uses`. **Remaining red on 5.4:** the
*existence* of an independent extensor family for a given cycle
(`3 ≤ m ≤ D`) — the generic-panel independence argument (Claim 6.4/6.9,
bottoming on Lemma 2.1), the open analytic blocker. The two bricks now
green (base + dim-bound) bound the cycle hypothesis from both ends; the
genericity device is the whole remaining content.

**Cycle-realization short-cycle base landed (2026-06-03).** The first
brick of `lem:cycle-realization` (KT Lemma 5.4) is green:
`PanelHingeFramework.toBodyHinge_rankHypothesis_zero` — the panel
analogue of `theorem_55_base`, lifted through `toBodyHinge`. A panel
framework on a two-body cover with two edges joining `u ≠ v` whose
panel support extensors are independent has an infinitesimally rigid
body-hinge interpretation (`RankHypothesis 0`, full rank `D`).
One-line composition with `theorem_55_base` on `P.toBodyHinge`
(defeq carries `graph`/`supportExtensor`); axiom-clean. Blueprint adds
a `lem:cycle-realization-base` node (green) that the still-red
`lem:cycle-realization` `\uses`.

The pre-21a induction-skeleton leaf nodes remain green (all
regime-agnostic, retained verbatim under the panel layer):
`def:rank-hypothesis`, `lem:theorem-55-base`, the Case
II rank-lift accounting `lem:case-II-rank-lift`
(`rankHypothesis_iff_finrank_pinnedMotions`, the basis-free `+D` core of
the panel-hinge 1-extension), and the framework-construction op
`def:framework-with-graph` / `lem:motions-mono-of-graph-le`. This commit
lands the **Case I block-pinning op** (`def:pinned-motions-on`, green):
`BodyHingeFramework.pinnedMotionsOn s` — the infinitesimal motions
vanishing on every body of a set `s ⊆ α`, the set-level analogue of
Phase 18's `pinnedMotions v` and the framework-side carrier of
contracting a rigid subgraph `H` (pin all of `V(H)` → one body). Ships
the membership simp lemma, `pinnedMotionsOn_singleton` (recovers
`pinnedMotions v` at `s = {v}`), `pinnedMotionsOn_eq_iInf` (block pin =
`⨅ v ∈ s, pinnedMotions v` for nonempty `s`), and the two monotonicity
facts (`pinnedMotionsOn_mono`, `pinnedMotionsOn_le_pinnedMotions`). The
`s.Nonempty` hypothesis on the iInf identity is essential: the empty
infimum is `⊤` and would drop the shared `IsInfinitesimalMotion`
condition. This is hand-off #1's incremental first piece (the
`pinnedMotions`-relationship lemma, landed before the genericity
device). The cycle input `lem:cycle-realization` (KT Lemma 5.4) is a
**verified cite** — not Lean: its proposition numbers ([4] Crapo–Whiteley
1982 Prop 3.4, [34] Whiteley 1999 Kluwer Prop 3) were checked against the
local OCR'd primaries and pinned. Still red: `prop:rigidity-matrix-prop11`,
`thm:theorem-55`, `lem:case-I`, `lem:case-II` (now gating on the *vertex-
level* graph ops — contraction `G/E(H)`, splitting-off `G_v^{ab}` — and
the genericity device, see *Hand-off*), and `lem:case-III` (deferred to
22–23).

**Basis-free rank convention (carried forward from Phase 18).** Phase 18
carries `rank R(G,p)` as the codimension `D|V| − dim Z(G,p)` of the null
space `Z(G,p) = F.infinitesimalMotions` (`finrank_screwAssignment`). The
realization hypothesis `rank R(G,p) = D(|V|−1) − k` is therefore stated
directly on the null-space dimension: `RankHypothesis F k' := (finrank
infinitesimalMotions : ℤ) = screwDim k + k'`. At `k'=0` this is exactly
infinitesimal rigidity (`rankHypothesis_zero_iff`, via
`finrank_trivialMotions` + `infinitesimalMotions_eq_trivialMotions_iff`).

## Architectural choices made up front

- **New file `Molecular/AlgebraicInduction.lean`, new chapter
  `algebraic-induction.tex`.** Per the one-`.lean` / one-`.tex` per
  molecular phase convention (post-Phase-18 cleanup split). Carrier:
  the Phase-18 panel-hinge rigidity matrix `R(G,p)` over `Graph α β`.
- **Driven by Theorem 4.9 (`thm:minimal-kdof-reduction`).** Theorem 5.5
  is induction on `|V|` over the *same* reduction dichotomy Phase 20's
  capstone exposes as a well-founded induction principle: base case
  `|V|=2`, then Case I (rigid-subgraph contraction) / Case II (splitting
  off) / Case III (deferred). Reuse the green `lem:reduction-step` +
  `lem:contraction-minimality` minimality-transport lemmas as the
  combinatorial inputs; this phase supplies only the rank realizations.
- **Rank arguments are block-triangular**, reusing Phase 18's pin-a-body
  Lemma 5.1 (`lem:rank-delete-vertex`) and parallel-hinges-full Lemma 5.3
  (`lem:rank-parallel-full`). Genericity (Claim 6.4 / 6.9: matrix entries
  are polynomials in algebraically independent panel coords ⇒ a generic
  point attains the max rank) lifts each single good realization to a
  generic one — the only genuinely new analytic device.
- **Cycle-realization Lemma 5.4** (`lem:cycle-realization`,
  Crapo–Whiteley [4] / Whiteley Kluwer 1999) enters as an input here;
  formalize-or-cite decision per-node (risk #4 in MolecularConjecture.md).
  Bib entry `crapoWhiteley1982` added this commit.

## Lemma checklist

Forward-mode: the authoritative node list is `algebraic-induction.tex`.
Tracked here for hand-off convenience; all red at phase open.

Panel layer (form (B), DESIGN.md; resumed 2026-06-03 post-21a):
- [x] `def:panel-support-extensor` — `panelSupportExtensor n₁ n₂ :=
  complementIso (normalsJoin n₁ n₂)`: the meet of two panel normals,
  landing in `ScrewSpace k`. Ships `normalsJoin` (grade-2 join, `⋀^2`),
  `normalsJoin_coe`, `normalsJoin_ne_zero_iff`,
  `panelSupportExtensor_ne_zero_iff` (transversal ⟺ normals independent).
  The panel-layer leaf; consumes Phase-21a `complementIso`. Axiom-clean.
  Green.
- [x] `def:panel-hinge-framework` — `PanelHingeFramework` (graph +
  per-vertex `normal` + endpoint selector `ends`), its body-hinge
  interpretation `toBodyHinge` (sets `supportExtensor` from
  `panelSupportExtensor` at each edge's endpoints), and the coplanarity
  spec `BodyHingeFramework.IsHingeCoplanar` (= "arises as a
  `toBodyHinge`") with `isHingeCoplanar_toBodyHinge` (automatic) and
  `toBodyHinge_supportExtensor_ne_zero_iff`. Resolved the structure-design
  question via option (a): `BodyHingeFramework` carries `supportExtensor`
  as a field, affine model retained as `ofHinge`. Axiom-clean. Green.

Generic-rank reconciliation (relocated forward from Phase 18/19):
- [ ] `prop:rigidity-matrix-prop11` — KT Prop 1.1, analytic half:
  `rank R(G,p) = D(|V|−1) − def(G̃)` for generic `(G,p)`. The matroidal
  half (`def = corank M(G̃)`, `thm:def-eq-corank`) is already green
  (Phase 19); this is the geometric side (JJ [15] Thm 6.1), depending on
  the Claim 6.4 generic-rank argument. Lands with / after Theorem 5.5.

Induction skeleton + base:
- [x] `def:rank-hypothesis` — the realization hypothesis (6.1):
  `RankHypothesis F k' := (finrank infinitesimalMotions : ℤ) = screwDim k + k'`
  (null-space form of `rank = D(|V|−1) − k`; see *Current state*). Green.
- [ ] `thm:theorem-55` — KT Theorem 5.5, the capstone of this phase.
  Induction on `|V|` over the Phase-20 reduction dichotomy.
- [x] `lem:theorem-55-base` — `|V|=2`, `k=0` base case (`theorem_55_base`
  + helper `rankHypothesis_zero_iff`); full rank `D` via
  `eq_of_hingeConstraint_two_parallel` (`lem:rank-parallel-full`, Phase 18
  green). Axiom-free.

Framework-construction op (shared infra for Cases I & II):
- [x] `def:framework-with-graph` — `BodyHingeFramework.withGraph`: swap
  the underlying multigraph, keep the hinge map (hence every supporting
  extensor / hinge-row block). The carrier for the inductive
  constructions. Now also carries the panel-layer analogue
  `PanelHingeFramework.withGraph` (swap multigraph, keep `normal`+`ends`)
  + the commute identity `toBodyHinge_withGraph`
  (`(P.withGraph G').toBodyHinge = P.toBodyHinge.withGraph G'`), routing
  the green body-hinge graph-monotonicity / block-pin rank facts onto
  panel realizations on a different graph, coplanarity preserved. Also carries the
  per-body `PanelHingeFramework.withNormal v n` (override `v`'s panel normal via
  `Function.update`, Case II's 1-extension primitive) + its simp lemmas and the
  support-extensor invariance `toBodyHinge_withNormal_supportExtensor_of_ne`
  (edges avoiding `v` unchanged). Green.
- [x] `lem:motions-mono-of-graph-le` — graph-monotonicity of the null
  space: `infinitesimalMotions_le_withGraph_of_le` (`G' ≤ G ⇒ Z(G,p) ≤
  Z(G',p)`) + its `finrank` form `finrank_infinitesimalMotions_le_of_
  graph_le` ("re-adding edges only grows the rank", the step
  `prop:rigidity-matrix-prop11` uses). Axiom-clean. Green.

Case I (proper rigid subgraph; KT §6.2):
- [x] `def:pinned-motions-on` — `BodyHingeFramework.pinnedMotionsOn s`:
  block-pin the bodies of a set `s` (motions vanishing on all of `s`).
  Set-level analogue of Phase 18's `pinnedMotions v`; the framework-side
  carrier of rigid-subgraph contraction (pin `V(H)`). Ships
  `pinnedMotionsOn_singleton`, `pinnedMotionsOn_eq_iInf` (nonempty `s`),
  `pinnedMotionsOn_mono`, `pinnedMotionsOn_le_pinnedMotions`. Axiom-clean.
  Green.
- [x] `lem:pinned-motions-on-mono` — block-pin graph monotonicity:
  `pinnedMotionsOn_le_withGraph_of_le` (`G' ≤ G ⇒ pinnedMotionsOn s ≤
  (withGraph G').pinnedMotionsOn s`) + rank form
  `finrank_pinnedMotionsOn_le_of_graph_le`. The block-pin analogue of
  `lem:motions-mono-of-graph-le`; the "re-adding `E(H)` only grows the block-pinned
  rank" direction Case I's gluing travels. Axiom-clean. Green.
- [~] `lem:cycle-realization` — KT Lemma 5.4. **Decision (2026-06-03):
  formalize as genuine *panel* content — its own sub-phase**, not cite,
  not the free-hinge telescoping reduction (which proved only the
  body-hinge cycle statement; superseded — see DESIGN.md). Statement is
  KT's form (a cycle with `3 ≤ |V| ≤ D` has an infinitesimally rigid
  full-rank `D(|V|−1)` *panel* realization). The **short-cycle base** is
  green (`lem:cycle-realization-base`,
  `PanelHingeFramework.toBodyHinge_rankHypothesis_zero`): the two-body
  panel analogue of `theorem_55_base` via `toBodyHinge`. The **`|V| ≤ D`
  dimension bound** is also green (`lem:cycle-realization-dim-bound`,
  `card_le_screwDim_of_linearIndependent` +
  `…card_le_screwDim_of_supportExtensor_linearIndependent`). The
  **genericity-device reduction** is now green too
  (`lem:panel-support-extensor-independence`,
  `panelSupportExtensor_linearIndependent_iff`): panel-extensor
  independence ⟺ grade-2-join independence via `complementIso` being a
  `LinearEquiv`, turning the analytic blocker into a `⋀²`-basis question.
  The *existence* of an independent grade-2-join / panel-extensor family
  for `m ≤ D` is now green too (`lem:exists-independent-panel-extensor`,
  `exists_independent_normalsJoin` + `exists_independent_panelSupportExtensor`,
  bridged by `normalsJoin_basisFun_orderEmbOfFin`): basis-selection on `⋀²`
  via `ιMulti_family_linearIndependent_ofBasis`, bottoming on Lemma 2.1.
  The **`m`-body cycle rigidity half** is now green too
  (`lem:cycle-realization-rigid`, `rankHypothesis_zero_of_cycle` +
  `…toBodyHinge_rankHypothesis_zero_cycle`, staged through
  `eq_succ_of_isInfinitesimalMotion_cycle` /
  `isTrivialMotion_of_isInfinitesimalMotion_cycle`): cycle bodies are `Fin m`
  (`NeZero m`), edge `i` links `i`→`i+1`, the per-edge `S i − S(i+1)` telescope
  to `∑ = 0` via `Equiv.addRight (1 : Fin m)` and `eq_zero_of_mem_span_singleton_
  of_sum_eq_zero` forces constancy — no `Graph`-walk primitive needed, the cyclic
  `Fin m` index *is* the cycle. All four Lean pieces of 5.4 now green; only the
  cited projective assembly (CW82 Prop 3.4 / Whiteley99 Prop 3) stays non-Lean.
- [x] `lem:pinned-motions-on-rank-bound` — block-pin rank lower bound:
  `trivialMotions_inf_pinnedMotionsOn_eq_bot` (nonempty `s`) +
  `screwDim_add_finrank_pinnedMotionsOn_le` (`D + finrank (pinnedMotionsOn s) ≤
  finrank Z(G,p)`). The inequality form of the single-body `lem:rank-delete-vertex`
  equality; the lower-bound brick of Case I's block-triangular gluing. Axiom-clean.
  Green.
- [ ] `lem:case-I` — KT Lemmas 6.2/6.3/6.5: contract a proper rigid
  subgraph `H` (smaller minimal `k`-dof by green `lem:contraction-minimality`),
  glue block-triangularly with a pinned rigid realization of `H`
  (`lem:rank-delete-vertex`, Phase 18 green; block-pin lower bound
  `lem:pinned-motions-on-rank-bound` green). Still needs the vertex-level
  contraction op `G/E(H)` + Claim 6.4 genericity.

Case II (`k>0` splitting; KT §6.3):
- [x] `lem:case-II-rank-lift` — the `+D` accounting core
  (`rankHypothesis_iff_finrank_pinnedMotions`): `RankHypothesis F k' ↔
  finrank (pinnedMotions v) = k'`, via the green
  `finrank_pinnedMotions_add_screwDim` (pin-a-body Lemma 5.1, Phase 18).
  Now also carries the **panel-layer assembly**
  `PanelHingeFramework.rankHypothesis_withNormal_iff_finrank_pinnedMotions`:
  the extended framework `(P.withNormal v n).toBodyHinge` realizes the rank
  at `k'` iff the original `P`'s `v`-pinned motions have dimension `k'`,
  staged through `toBodyHinge_withNormal_{infinitesimalMotions,pinnedMotions}_eq`
  (the panel choice at an unhinged `v` leaves `Z`/pins fixed) on the general
  `BodyHingeFramework.infinitesimalMotions_eq_of_isLink_supportExtensor`.
  Now also carries the **graph-half inclusion**
  `BodyHingeFramework.pinnedMotions_le_withGraph` (+ rank form) and its
  panel layer `PanelHingeFramework.toBodyHinge_pinnedMotions_le_withGraph`
  (+ rank form): re-adding `v`'s two edges only shrinks the `v`-pinned
  motions (single-body specialization of `pinnedMotionsOn_le_withGraph_of_le`,
  routed through `toBodyHinge_withGraph` on the panel layer). Axiom-clean.
  Green.
- [ ] `lem:case-II` — KT Lemmas 6.7/6.8: splitting off a reducible
  degree-2 vertex (smaller minimal `k`-dof by green `lem:reduction-step`),
  the panel-hinge analogue of Whiteley's bar-joint 1-extension; re-insert
  `v` to lift the rank by `D` (the accounting is `lem:case-II-rank-lift`,
  the panel assembly + graph-half inclusion now green). The *equality* of
  the extended `v`-pinned motions with the base's is now green too
  (`pinnedMotions_withGraph_eq` + panel `toBodyHinge_pinnedMotions_withGraph_eq`
  + rank forms): conditional on `hnew` (every base-`v`-pinned motion clears
  the re-added edges' constraints), the honest content of Claim 6.9. `hnew`
  now reduces to a per-edge single span-membership at the non-`v` endpoint
  (`hnew_of_isLink_incident` + panel `toBodyHinge_hnew_of_isLink_incident`,
  green): given all out-of-`G'` links are `v`-incident and `S v = 0`, the
  constraint `S v − S w` collapses to `S w ∈ span C(e)`. Still needs:
  discharging that span-membership (`hspan`) for the chosen general-position
  extensors (genuine Claim 6.9 — false pointwise, holds by the rank count),
  and wiring `G_v^{ab}` (Phase 20; needs an edge-substitution bridge,
  `splitOff` adds a fresh `e₀` so is not directly `≤ G`) into `withGraph`.

Case III (deferred to Phases 22–23):
- [ ] `lem:case-III` — KT Lemma 6.10/6.13: `k=0`, no proper rigid
  subgraph. Stated here only to close the Theorem-5.5 dichotomy; bottoms
  out on the extensor-independence Lemma 2.1 (`lem:extensor-independence`,
  Phase 17 green). **Deferred** — the crux, Phases 22–23.

## Carry-forwards inherited from Phase 20 (schedule as needed)

1. **Graph↔matroid contraction bridge.** `minimal_kdof_reduction`'s
   contraction branch is handed the IH rather than recursing internally
   (no `(G/E(H))̃ ↔ M(G̃)/E(H̃)` map built). Needed only if Case I's
   recursion wants a fully graph-level form; otherwise the IH-handed
   shape suffices. See `notes/Phase20.md` *Hand-off* #1.
2. **Forest surgery KT 4.2** (`lem:forest-surgery-unsplit`). Off the
   Theorem-4.9 critical path; sound, no balanced-packing gloss, not yet
   needed. See `notes/Phase20.md` *Hand-off* #2.

Also off the Thm-4.9 critical path, scheduled with this phase as Case 6.1
needs them: KT Lemma 3.2 (not 3-edge-connected), Lemma 3.6 (partition
decomposition).

## Decisions made during this phase

### Phase-local choices and proof techniques
- **`BodyHingeFramework` carries the support extensor as a field
  (option a).** The hand-off's open design question — generalize
  `BodyHingeFramework` to carry `supportExtensor`, or express the panel
  hinge as an `affineSubspaceExtensor` — resolved in favor of (a). The
  field `hinge : β → Fin k → Fin (k+1) → ℝ` became `supportExtensor : β →
  ScrewSpace k`; the affine free-hinge model is the smart constructor
  `ofHinge` (sets the field via `affineSubspaceExtensor`). Option (b) was
  blocked: mathlib's `Graph` keeps endpoints relational (no `e ↦ (u,v)`
  function) and `affineSubspaceExtensor` is not invertible, so there is no
  affine point-family realizing an arbitrary panel meet. (a) is local —
  `.hinge` fed only `supportExtensor`, so all of Phase 18 + the green
  Phase-21 nodes build unchanged. `PanelHingeFramework` carries its own
  `ends : β → α × α` endpoint selector to read the two panel normals.
- **Null-space form of the realization hypothesis.** `RankHypothesis`
  states `rank R(G,p) = D(|V|−1) − k` as the null-space dimension
  `dim Z(G,p) = D + k` rather than carrying an `ℤ`-valued rank and
  re-deriving the `D|V|` column count at each node — matches the
  basis-free convention Phase 18's rank lemmas
  (`finrank_pinnedMotions_add_screwDim`, `finrank_trivialMotions`) already
  speak. The two forms interchange by `finrank_screwAssignment`. See
  Phase21.md *Current state* and the file docstring.
- **Base case stated abstractly, not on a concrete 2-vertex graph.**
  `theorem_55_base` hypothesizes a 2-body framework (`Nonempty`/`Finite α`,
  `hcover : ∀ w, w = u ∨ w = v`) with two independent-extensor hinges
  linking `u v`, rather than constructing `Fin 2` + an explicit double
  edge. Keeps the base case reusable by the induction (which will supply
  the 2-body framework from its own data) and lets
  `eq_of_hingeConstraint_two_parallel` apply verbatim.
- **Framework-construction op landed at the `≤`/edge-set level only.**
  `withGraph` swaps `F.graph` keeping the hinge map; the one fact this
  phase needs is graph-monotonicity of `Z(G,p)` (`G' ≤ G ⇒ Z(G,p) ≤
  Z(G',p)`), proved through `Graph.IsLink.mono` (called explicitly, not
  via dot notation — FRICTION recurrence). The *vertex-level* ops
  (contraction `G/E(H)`, splitting-off `G_v^{ab}`) that actually change
  `|V|` are left for later commits — they are where Cases I/II diverge.
  Needed the `Mathlib.Combinatorics.Graph.Subgraph` import (`≤` on
  `Graph` lives there, not `.Basic`).
- **Case I block-pinning landed at the set-pin level (`pinnedMotionsOn`).**
  The first incremental piece of hand-off #1: rather than build a full
  vertex-quotient contraction op up front, the framework-side carrier of
  "contract rigid `H` to one body" is `pinnedMotionsOn (V(H))` — pin the
  whole block. Generalizes `pinnedMotions v` (= `pinnedMotionsOn {v}`)
  and equals `⨅ v ∈ s, pinnedMotions v` for nonempty `s`, the form Case
  I's block-triangular rank accounting will run against the per-body
  pin-a-body identity. No new mathlib needed; built directly mirroring
  the `pinnedMotions` submodule.
- **Cycle Lemma 5.4 citation work (Phase-local, stands).** Proposition
  numbers verified against the local OCR'd primaries: [4] Crapo–Whiteley
  1982 **Proposition 3.4** (`D=6` case) and [34] Whiteley 1999 Kluwer
  **Proposition 3**; KT attributes "[4, Prop 3.4] or [34, Prop 3]"
  itself. Discharged the *Citation accuracy caveat* in
  MolecularConjecture.md. Corrected a prior mis-statement (the blueprint
  glossed cycle realization as "rank one less" — backwards; short cycles
  are *rigid*, full rank). New bib entry `whiteley1999`.
- **Panel-coplanarity finding + Lemma 5.4 → formalize as panel content
  (2026-06-03).** Cross-cutting; full record promoted to DESIGN. Two
  superseded mid-Phase-21 calls are corrected there: (i) the cite-only
  call on 5.4, and (ii) the later "5.4 reduces to trivial telescoping in
  our free-hinge model" reduction — which proved only the *body-hinge*
  cycle statement (too weak), because `BodyHingeFramework` omits the
  hinge-coplanarity that *defines* panel-hinge. Net: add a **panel
  layer** (per-vertex hyperplanes, hinges as intersections — reuses all
  rank infra) and formalize 5.4 as genuine panel content, its own
  sub-phase. See *Promoted to … DESIGN* below.

### Promoted to TACTICS-GOLF / TACTICS-QUIRKS / FRICTION / DESIGN
- *Panel-hinge = hinge-coplanar body-hinge; the coplanarity layer (form
  (A) predicate vs (B) panel-data, (B) chosen); which nodes are reused
  vs gain the panel requirement; Lemma 5.4 formalized as a panel
  sub-phase* → DESIGN.md *Panel-hinge = hinge-coplanar body-hinge: the
  coplanarity layer*; risk #7 in MolecularConjecture.md.

## Blockers / open questions

- **Claim 6.4 / 6.9 genericity** is the new analytic device this phase
  introduces (matrix entries polynomial in alg.-indep. panel coords ⇒
  generic max rank). Reuse the Phase 6/8 genericity machinery
  (`Mathlib/LinearAlgebra/Matrix/Rank.lean` Gram-det LI mirrors,
  `exists_uniform_rowIndependent_placement`-style perturbation) where it
  transfers; assess on contact whether the panel-coordinate
  parametrization needs new infrastructure.
- **Panel-coplanarity re-scope (RESOLVED — panel layer now building).**
  The realization-existence nodes as first drafted proved the
  *body-hinge* rank theorem, not the molecular conjecture, because
  `BodyHingeFramework` omits hinge-coplanarity. The fix — a form-(B)
  panel layer (per-vertex normals, hinges as panel intersections via the
  meet; reuses all rank infra) — is decided (DESIGN.md; risk #7 in
  MolecularConjecture.md), its meet prerequisite Phase 21a is complete,
  and its first leaf `def:panel-support-extensor` is green. The
  panel-coplanarity gap is no longer a blocker.
- **Lemma 5.4 — formalize as genuine panel content** (user decision
  2026-06-03). The cycle's panel realization with independent hinge
  extensors is the Crapo–Whiteley projective fact: needs the panel layer
  (`panelSupportExtensor` + the forthcoming `PanelHingeFramework`) + a
  generic-panel independence argument bottoming on Lemma 2.1 (Phase 17).
  Citation work stands as the source pointer. Lands after the panel
  framework + `IsHingeCoplanar`.

## Hand-off / next phase

**Phase 21 has RESUMED; the panel layer is fully stood up (2026-06-03).**
Phase 21a (the meet) is complete, the form-(B) panel plan is fixed in
DESIGN.md, and both panel nodes are green in
`Molecular/AlgebraicInduction.lean`: `def:panel-support-extensor`
(`panelSupportExtensor` + `normalsJoin` + the two nonvanishing iffs) and
`def:panel-hinge-framework` (`PanelHingeFramework` + `toBodyHinge` +
`BodyHingeFramework.IsHingeCoplanar` + `isHingeCoplanar_toBodyHinge`).

Green so far: both panel nodes above, the regime-agnostic
rank/structure facts retained verbatim under the panel layer —
`def:rank-hypothesis`, `lem:theorem-55-base` (rank content; gains a
coplanarity conjunct when assembled into the full Theorem 5.5),
`lem:case-II-rank-lift`, `def:framework-with-graph` +
`lem:motions-mono-of-graph-le`, `def:pinned-motions-on` — and now the
**short-cycle base** of Lemma 5.4 (`lem:cycle-realization-base`,
`toBodyHinge_rankHypothesis_zero`) and its **`|V| ≤ D` dimension bound**
(`lem:cycle-realization-dim-bound`,
`card_le_screwDim_of_linearIndependent` +
`PanelHingeFramework.card_le_screwDim_of_supportExtensor_linearIndependent`) — and now the
**`m`-body cycle rigidity** (`lem:cycle-realization-rigid`,
`rankHypothesis_zero_of_cycle` + `toBodyHinge_rankHypothesis_zero_cycle`). All four Lean
pieces of `lem:cycle-realization` are green; the node itself stays red (its statement is the
cited projective *existence* assembly, not a single Lean theorem).
Remaining red: `lem:cycle-realization` (cited assembly only),
`prop:rigidity-matrix-prop11` (stays body-hinge), `thm:theorem-55`,
`lem:case-I`, `lem:case-II`, `lem:case-III` (III is 22–23).

**Genericity-device reduction is now green** — `panelSupportExtensor_
linearIndependent_iff` reduces the analytic blocker to a concrete
exterior-power-basis question (see *Current state*). The
**assess-on-contact** finding the prior hand-off requested: the Phase
6/8 Gram-det perturbation machinery (`Mathlib/LinearAlgebra/Matrix/Rank
.lean`) is **not** the right tool — genericity here is purely
exterior-algebraic, not a real-polynomial-perturbation argument. The
right device is `exteriorPower.ιMulti_family_linearIndependent_ofBasis`
(an independent basis-indexed family of `⋀² ℝ^(k+2)`), already in
mathlib; no new perturbation infrastructure needed.

**Independent-family existence is now green** (this commit):
`exists_independent_normalsJoin` + `exists_independent_panelSupportExtensor`,
bridged by `normalsJoin_basisFun_orderEmbOfFin`. The witness was a basis
choice exactly as planned — `m` distinct 2-subsets of `Fin (k+2)` (card cap
`Fintype.card (Set.powersetCard (Fin (k+2)) 2) = (k+2).choose 2 = D ≥ m`),
standard basis vectors, `ιMulti_family_linearIndependent_ofBasis` + `.comp`
of the index injection. No new mathlib needed.

**`m`-body cycle rigidity is now green** (this commit):
`BodyHingeFramework.rankHypothesis_zero_of_cycle` +
`PanelHingeFramework.toBodyHinge_rankHypothesis_zero_cycle`, staged through
`eq_succ_of_isInfinitesimalMotion_cycle` /
`isTrivialMotion_of_isInfinitesimalMotion_cycle`. **No `Graph`-cycle/walk primitive was
needed** (the prior hand-off's anticipated cost): the cycle is the cyclic index type `Fin m`
itself (`NeZero m`), edge `i` linking `i`→`i+1`, so the per-edge `S i − S(i+1)` telescope to
`∑ = 0` by `Equiv.addRight (1 : Fin m)` (a bijection of `Fin m`) and the green
`eq_zero_of_mem_span_singleton_of_sum_eq_zero` (RigidityMatrix.lean, commit `5d72764`) forces
constancy. The constant-propagation is an `ℕ`-induction over `Fin.ofNat m j`
(`Fin.ofNat_val_eq_self` closes the return); the small `Fin` fact
`Fin.ofNat m p + 1 = Fin.ofNat m (p+1)` is a one-line `Fin.ext` + `simp [Fin.add_def,
Nat.add_mod]`.

**Case I block-pin rank lower bound is now green** (this commit):
`BodyHingeFramework.trivialMotions_inf_pinnedMotionsOn_eq_bot` +
`…screwDim_add_finrank_pinnedMotionsOn_le` — `D + finrank (pinnedMotionsOn s) ≤ finrank Z(G,p)`
for nonempty `s`, the block analogue (in inequality form) of the single-body pin-a-body equality
`finrank_pinnedMotions_add_screwDim`. The disjointness routes through the green singleton case
via `pinnedMotionsOn_le_pinnedMotions`; the bound is `finrank_sup_add_finrank_inf_eq` +
`finrank_mono` of `trivial ⊔ blockpin ≤ Z(G,p)`. Blueprint node
`lem:pinned-motions-on-rank-bound` (green), in the Case I section, that the still-red
`lem:case-I` `\uses`.

**Case I block-pin graph-monotonicity is now green** (this commit):
`BodyHingeFramework.pinnedMotionsOn_le_withGraph_of_le` +
`…finrank_pinnedMotionsOn_le_of_graph_le` — the block-pin analogue of
`lem:motions-mono-of-graph-le`. Two one-liners: the inclusion is
`infinitesimalMotions_le_withGraph_of_le` on the first conjunct (the vanishing
conditions `∀ v ∈ s, S v = 0` are graph-independent), the rank form is
`Submodule.finrank_mono`. Blueprint node `lem:pinned-motions-on-mono` (green), in the
Case I section, that the still-red `lem:case-I` `\uses`. The block-pin infra for Case I's
block-triangular gluing is now fully stocked (`def:pinned-motions-on` + rank lower bound +
graph monotonicity); the remaining red on Case I is the *vertex-level* contraction op
`G/E(H)` and the cited Claim 6.4 genericity / block-triangular rank addition.

**Panel `withGraph` carrier is now green** (this commit): `PanelHingeFramework.withGraph` +
the commute identity `toBodyHinge_withGraph`, folded into `def:framework-with-graph`. The
graph-swap primitive both inductive cases need on the panel layer now exists, and the commute
identity routes the green body-hinge graph-monotonicity / block-pin rank machinery onto panel
realizations placed on a smaller graph and re-glued. The combinatorial vertex-level ops
themselves are already green in Phase 20 (`rigidContract`, `splitOff`, `edgeSplit`).

**Case II panel-normal-extension carrier is now green** (this commit):
`PanelHingeFramework.withNormal v n` (override `v`'s panel normal via `Function.update`) + its simp
lemmas (`withNormal_{graph,ends,normal,normal_self}`, `withNormal_normal_of_ne`) + the invariance
`toBodyHinge_withNormal_supportExtensor_of_ne` (the support extensor at an edge avoiding `v` is
unchanged). Folded into `def:framework-with-graph` (panel layer), beside the panel `withGraph`. Needs
`[DecidableEq α]` on its own namespace block. With `withGraph` (to add `v`'s two edges) this is the
full panel-data carrier for the 1-extension; what remains is wiring it into the rank-lift.

**Case II rank-lift assembly is now green** (this commit):
`PanelHingeFramework.rankHypothesis_withNormal_iff_finrank_pinnedMotions` — the extended framework
`(P.withNormal v n).toBodyHinge` realizes the rank at `k'` iff `P`'s `v`-pinned motions have
dimension `k'`, under the no-incident-hinge hypothesis `hv` on `v`. Staged through
`toBodyHinge_withNormal_{infinitesimalMotions,pinnedMotions}_eq` (panel choice at an unhinged `v`
leaves `Z`/pins fixed) on the new general `infinitesimalMotions_eq_of_isLink_supportExtensor`
(motions depend only on the *linking* edges' extensors). The `hv` hypothesis is the honest
genericity-free content — "`v` is unhinged in the base graph `G_v^{ab}`". See *Current state*.

**Case II graph-half inclusion is now green** (this commit):
`BodyHingeFramework.pinnedMotions_le_withGraph` (+ rank form
`finrank_pinnedMotions_le_withGraph`) and the panel layer
`PanelHingeFramework.toBodyHinge_pinnedMotions_le_withGraph` (+ rank form). The `withGraph` step that
enlarges `P.graph` to `G` by `v`'s two new edges and the unconditional inclusion
`pinnedMotions_G(v) ≤ pinnedMotions_{G_v^{ab}}(v)` the prior hand-off anticipated both landed here, as
predicted via the green `pinnedMotionsOn_le_withGraph_of_le` at the singleton (two
`pinnedMotionsOn_singleton` rewrites) + `toBodyHinge_withGraph` on the panel layer. Four one-liners,
axiom-clean, no friction.

**Case II genericity-gated tightness is now green** (this commit):
`BodyHingeFramework.pinnedMotions_withGraph_eq` (+ rank form `finrank_pinnedMotions_withGraph_eq`)
and the panel layer `PanelHingeFramework.toBodyHinge_pinnedMotions_withGraph_eq` (+ rank form). The
equality `F.pinnedMotions v = (F.withGraph G').pinnedMotions v` is conditional on `hnew` — every
base-`v`-pinned motion of `F.withGraph G'` already clears the re-added edges' hinge constraints
(`∀ S ∈ … , ∀ e u w, F.graph.IsLink e u w → ¬G'.IsLink e u w → F.hingeConstraint S e u w`). The
equality landed in one commit given the green `≤` (`pinnedMotions_le_withGraph`): the proof is
`le_antisymm` of it with a `by_cases G'.IsLink` split (in-`G'` edges close via `hS.1`, the two new
`v`-edges via `hnew`). The prior hand-off's "assess whether a bridge is needed" resolved to: `hnew`
*is* the honest genericity-free brick (mirror of the `hv` pattern in the rank-lift assembly), and
discharging it from `exists_independent_panelSupportExtensor` is the remaining genericity step (a
base motion has `S v = 0`, so the new constraints are `S a ∈ span C(e_a)`, `S b ∈ span C(e_b)`).

**Case II `hnew` reduction is now green** (this commit): `BodyHingeFramework.hnew_of_isLink_incident`
+ panel `toBodyHinge_hnew_of_isLink_incident` reduce the `hnew` hypothesis of
`pinnedMotions_withGraph_eq` to a per-edge single span-membership `S w ∈ span C(e)` at each new
edge's non-`v` endpoint (using `S v = 0` to collapse the relative-screw difference). Folded into the
green `lem:case-II-rank-lift` node.

**Correction to the prior hand-off's route (A).** The prior hand-off proposed "show a `v`-pinned base
motion satisfies `S a ∈ span C(e_a)`, `S b ∈ span C(e_b)`" as a small commit. This is **not a
theorem pointwise** — a base motion on `G_v^{ab}` (constrained only by `e₀`: `S a − S b ∈ span
C(e₀)`) does not generally land each of `S a, S b` in the new spans for independently-chosen
extensors. That is the genuine Claim 6.9 genericity content, which holds via a rank/dimension count,
not pointwise. The reduction landed this commit (`hnew_of_isLink_incident`) isolates exactly the
span-memberships (`hspan`) the genericity device must achieve, so the open piece is now sharply
stated.

**Smallest next concrete commit:** two genuinely-open pieces remain, both feeding `lem:case-II`.
(A′) Discharge `hspan` (`S w ∈ span C(e)` for the two new edges) via the rank/dimension count of the
genericity device — *not* a pointwise fact; reuses `exists_independent_panelSupportExtensor` for the
extensor placement but needs the rank-counting argument to conclude every base-pinned motion lands.
(B) Wire the vertex-level splitting-off op `G_v^{ab}` (`Graph.splitOff`, green in Phase 20) as `G'`
in `withGraph`; note `splitOff` adds a fresh edge `e₀` joining `a–b`, so it is **not** directly
`≤ G` — an edge-substitution bridge relating `G` (with `v`'s two edges) to `splitOff G v a b e₀`
(with `e₀`) is the missing graph-level brick. Either is a clean standalone next commit.
Alternatively continue Case I: place the contraction
realization (panel data on `rigidContract`) and re-add `E(H)` via `withGraph`; the slack in
`screwDim_add_finrank_pinnedMotionsOn_le` is the contraction's inductive rank (block-triangular
gluing). The vertex-level splitting-off / contraction ops (`splitOff`, `rigidContract`) are green
in Phase 20 combinatorially; the genericity device for both is the same
`panelSupportExtensor_linearIndependent_iff` + `exists_independent_panelSupportExtensor` pair already
green for the cycle. Cases carry the panel (coplanarity) requirement automatically (panel
constructions are `IsHingeCoplanar` by `isHingeCoplanar_toBodyHinge`); III is deferred to 22–23.
