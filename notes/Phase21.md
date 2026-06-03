# Phase 21 — Algebraic induction: Theorem 5.5 base + Cases I & II (work log)

**Status:** in progress (opened 2026-06-03). Two re-scopes landed
2026-06-03. (1) The panel-coplanarity re-scope (panel-hinge =
hinge-coplanar body-hinge) is **resolved**: the gating foundations
sub-phase **Phase 21a** (Grassmann–Cayley meet) is complete
(`notes/Phase21a.md`, `Molecular/Meet.lean`), the form-(B) panel plan is
fixed in DESIGN.md *Panel-hinge = hinge-coplanar body-hinge*, and the
panel layer is green. (2) **Genericity scope-out (user decision):** the
shared analytic crux Claim 6.4/6.9 (the rank/dimension-count argument) is
**scoped out of Phase 21 into its own focused sub-phase, Phase 21b** (the
analytic sibling of 21a). Phase 21 now **aims to close on the
genericity-free content**: each remaining red node is formalized in full
*modulo* the device, which enters as an explicit cited input / black-box
hypothesis. Decision: DESIGN.md *Genericity device (Claim 6.4/6.9) is its
own sub-phase (Phase 21b)*; risk #4/#7 + Phase-21b detail in
`notes/MolecularConjecture.md`. The node-by-node "needs from 21b vs.
genericity-free and still to formalize" split is the *Hand-off* section
below.

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

**Case II 1-extension assembly landed — `lem:case-II` GREEN-modulo-21b (2026-06-03).** The
genericity-free assembly of `lem:case-II` is green:
`PanelHingeFramework.rankHypothesis_withNormal_withGraph_iff_finrank_pinnedMotions`
(`Molecular/AlgebraicInduction.lean`, end of the `[DecidableEq α]` panel block). For a panel
framework `P` on the splitting-off `G_v^{ab} = P.graph` with `v` yet unhinged (`hv`) and
`P.graph ≤ G`, the extended framework `(P.withNormal v n).withGraph G` realizes `RankHypothesis k'`
iff `P` carries body-`v`-pinned dimension `k'` — the inductive realization lifts to `G` with the
two new hinge-row blocks accounting for the `+D`. The proof composes the three green reduction
bricks: `rankHypothesis_iff_finrank_pinnedMotions` (the `+D` core), `toBodyHinge_pinnedMotions_
withGraph_eq` (the genericity-gated `≥` tightness, fed `hnew`), and `toBodyHinge_withNormal_
pinnedMotions_eq` (the unhinged-`v` panel-normal invariance), with the key `withGraph`-composition
identity `(Q.withGraph P.graph) = P.withNormal v n` (definitional, `rfl`). The single Phase-21b
input is `hspan` (each base-`v`-pinned motion in the two new edges' panel-support spans — false
pointwise, holds by the rank/dimension count, supplied by `exists_independent_panelSupportExtensor`);
taking it as an explicit hypothesis closes the node modulo the device. The incidence side `hinc`
(every link of `G` lost on passing to `G_v^{ab}` is `v`-incident) is genericity-free graph data,
also an explicit hypothesis — instantiated by `isLink_incident_of_not_removeVertex` at the common
lower bound in the consumer. Axiom-clean (propext/Classical.choice/Quot.sound). No friction (a
three-rw composition of green bricks; the `withGraph`-composition `rfl` was the one thing checked via
`lean_multi_attempt`). Blueprint flips `lem:case-II` to green (`\lean` + `\leanok` on both
environment and proof; `\uses` `lem:exists-independent-panel-extensor` added). **Remaining red on
Phase 21:** `lem:case-I` (Case I contraction plumbing — the natural parallel follow-up),
`thm:theorem-55` (the capstone induction, assembled once Cases I/II are green-modulo-21b),
`prop:rigidity-matrix-prop11` (analytic half via the device). All four `\uses` the cited 21b node
transitively.

**Case II `hinc` incidence brick landed (2026-06-03).** The graph-side hypothesis of
`hnew_of_isLink_incident`, instantiated at the Case II common lower bound `G' = G − v`, is green:
`Graph.isLink_incident_of_not_removeVertex` (`Molecular/Induction.lean`, beside `removeVertex_le`):
a link `e u w` of `G` that does *not* survive `removeVertex v` has `u = v ∨ w = v` (else it avoids
`v`, and `removeVertex_isLink` would keep it). Four-line `by_contra` + `not_or` + `removeVertex_isLink.mpr`.
This discharges the *incidence* side (`hinc`) of `hnew` for the splitting-off 1-extension over the shared
`G − v` lower bound: the only links of `G` re-added over `G − v` are the `v`-incident ones, so each
re-added hinge constraint on a `v`-pinned motion (`S v = 0`) collapses to the single span membership
`S w ∈ span C(e)` at its non-`v` endpoint (`hnew_of_isLink_incident`). Axiom-clean
(propext/Classical.choice/Quot.sound). No friction. Blueprint folds the name into the green
`lem:splitoff-edge-substitution` node (the edge-substitution bridge; now `\lean`s three names) with a
one-sentence prose addition. **Remaining red on Case II:** only the genericity span membership (`hspan`,
A′ — `S w ∈ span C(e)` for the two new edges via the rank/dimension count of Claim 6.9, *not* pointwise);
the `hinc` side and the `G − v` plumbing are now fully stocked. Plus Case I.

**Case II edge-substitution graph bridge landed (2026-06-03).** The missing graph-level brick of
`lem:case-II` (hand-off option B) is green: `Graph.removeVertex_le` (`G − v ≤ G`, via
`deleteVerts_le`) and `Graph.removeVertex_le_splitOff` (`e₀ ∉ E(G) ⇒ G − v ≤ G.splitOff v a b e₀`),
both in `Molecular/Induction.lean` beside the `splitOff` def. The point: `splitOff G v a b e₀` is
**not** `≤ G` (it adds the fresh short-circuit edge `e₀ ∉ E(G)`), so the `withGraph` machinery —
which needs `G' ≤ F.graph` — cannot compare `G` and `G_v^{ab}` directly. They are instead an *edge
substitution*, sharing the common subgraph `G − v`; both these inclusions route through that shared
lower bound. Proofs are anonymous-constructor one-liners on the `Graph` `≤` structure (vertex-set +
`isLink_mono`): for the splitting-off inclusion, a link of `G − v` is a link of `G` avoiding `v`, so
its edge is in `E(G)`, hence `≠ e₀` (else `e₀ ∈ E(G)`), so it survives into `splitOff`'s `v`-avoiding
branch. Axiom-clean (propext/Classical.choice/Quot.sound). No friction. Blueprint adds a green
`lem:splitoff-edge-substitution` node that the still-red `lem:case-II` `\uses`. **Remaining red on
Case II:** discharging `hspan` (option A′ — `S w ∈ span C(e)` for the two new edges via the
genericity rank/dimension count, *not* pointwise) and wiring the inductive realization on `G_v^{ab}`
into the parent framework on `G` *through* this `G − v` common lower bound (the rank-lift assembly +
`pinnedMotions_withGraph_eq` now have the graph relationship they were missing).

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
- [x] `lem:case-II` — KT Lemmas 6.7/6.8: splitting off a reducible
  degree-2 vertex (smaller minimal `k`-dof by green `lem:reduction-step`),
  the panel-hinge analogue of Whiteley's bar-joint 1-extension; re-insert
  `v` to lift the rank by `D`. **GREEN-modulo-21b**
  (`rankHypothesis_withNormal_withGraph_iff_finrank_pinnedMotions`): the
  extended `(P.withNormal v n).withGraph G` realizes `RankHypothesis k'`
  iff `P` (on `G_v^{ab}`) carries `v`-pinned dimension `k'`, composing the
  green `+D` core (`rankHypothesis_iff_finrank_pinnedMotions`), the
  genericity-gated tightness (`toBodyHinge_pinnedMotions_withGraph_eq`), and
  the unhinged-`v` invariance (`toBodyHinge_withNormal_pinnedMotions_eq`),
  via the `withGraph`-composition `rfl` `(Q.withGraph P.graph) = withNormal`.
  Genericity-free hypotheses `hv` (v unhinged) + `hinc` (lost links
  v-incident, via `isLink_incident_of_not_removeVertex`); the **one** 21b
  input is `hspan` (base-pinned motions in the two new panel-support spans —
  false pointwise, supplied by `exists_independent_panelSupportExtensor`),
  taken as an explicit hypothesis. Axiom-clean.

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

- **Claim 6.4 / 6.9 genericity — SCOPED OUT to Phase 21b** (user
  decision 2026-06-03). The shared analytic device (matrix entries
  polynomial in alg.-indep. panel coords ⇒ generic max rank) is no
  longer a Phase 21 blocker: it is its own focused sub-phase, entering
  Phase 21's remaining nodes as a cited black-box (see *Hand-off*
  node-by-node split + DESIGN.md *Genericity device …*). The
  reuse-to-assess note (Phase 6/8 Gram-det machinery vs. fresh argument)
  moves with it to `notes/MolecularConjecture.md` *Phase 21b*.
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

**Re-scoped 2026-06-03 (user decision): close Phase 21 on the
genericity-free content; the genericity device is Phase 21b.** The
shared analytic crux Claim 6.4/6.9 (matrix entries polynomial in
alg.-indep. panel coords ⇒ generic max rank) is no longer Phase 21
work — it is sub-phase **21b** (DESIGN.md *Genericity device …*;
`notes/MolecularConjecture.md` *Phase 21b*). Phase 21's job on each
remaining red node is to land everything *except* the device, then
state/close the node with the device's conclusion as a cited
input / named hypothesis so the node is GREEN-modulo-21b. Do **not**
follow the prior hand-off's "tackle A′ / continue Case I" framing
verbatim — A′ (`hspan`) is exactly the genericity content now in 21b.

**Green so far (genericity-free, retained):** both panel nodes
(`def:panel-support-extensor`, `def:panel-hinge-framework`); the
regime-agnostic rank/structure nodes (`def:rank-hypothesis`,
`lem:theorem-55-base`, `lem:case-II-rank-lift`,
`def:framework-with-graph` + `withNormal`, `lem:motions-mono-of-graph-le`,
`def:pinned-motions-on`, `lem:pinned-motions-on-mono`,
`lem:pinned-motions-on-rank-bound`); all four Lean pieces of
`lem:cycle-realization` (`-base`, `-dim-bound`, `-rigid`,
`-panel-support-extensor-independence`, `-exists-independent-panel-extensor`);
and Case II's reduction stack (`pinnedMotions_le_withGraph`,
`pinnedMotions_withGraph_eq` conditional on `hnew`,
`hnew_of_isLink_incident`, `lem:splitoff-edge-substitution`); and the
Case II 1-extension assembly `lem:case-II` itself
(`rankHypothesis_withNormal_withGraph_iff_finrank_pinnedMotions`,
GREEN-modulo-21b with `hspan` an explicit hypothesis).

### Node-by-node path to close Phase 21

Three red nodes remain (Case III excepted — deferred to 22–23; Case II is
now GREEN-modulo-21b). For each: what it still needs **from the cited 21b
device** vs. what is **genericity-free and still to formalize in Phase 21**.

1. **`lem:case-I`** (KT 6.2/6.3/6.5 rigid-subgraph contraction). **The
   smallest next concrete commit** — the natural parallel of the now-green
   Case II assembly.
   - *Genericity-free, still to do in 21:* the vertex-level contraction
     op `G/E(H)` on the panel layer (place panel data on
     `rigidContract`, green in Phase 20) + the block-triangular rank
     *accounting*: re-add `E(H)` via `withGraph` (block-pin monotonicity
     `pinnedMotionsOn_le_withGraph_of_le` + lower bound
     `screwDim_add_finrank_pinnedMotionsOn_le` are green), reducing
     `lem:case-I` to "the two blocks' ranks add" with the contraction's
     inductive rank filling the slack.
   - *From 21b (cited):* the block-triangular *generic* gluing — that a
     generic choice makes the combined matrix attain the sum of the two
     block ranks (Claim 6.4). `lem:case-I` `\uses` the 21b node.

2. **`thm:theorem-55`** (the capstone induction).
   - *Genericity-free, still to do in 21:* the induction on `|V|`
     wiring `lem:theorem-55-base` (green) + `lem:case-I` + `lem:case-II`
     over the Phase-20 reduction dichotomy
     (`minimal_kdof_reduction`, green) + `lem:case-III` (deferred stub).
     Once Cases I/II are GREEN-modulo-21b, the induction itself is
     genericity-free assembly; it inherits the 21b citation transitively
     through the cases.
   - *From 21b (cited):* none directly — only through Cases I/II/III.

3. **`prop:rigidity-matrix-prop11`** (KT Prop 1.1 analytic half).
   - *Genericity-free, still to do in 21:* the upper-bound /
     codimension side (`lem:trivial-motions-rank-bound` + deficiency
     count) and the edge-strip-to-minimal-`k`-dof reduction (re-adding
     edges only grows rank, `lem:motions-mono-of-graph-le`, green); the
     matroidal half `def = corank` is green (Phase 19,
     `thm:def-eq-corank`).
   - *From 21b (cited):* the generic-max-rank lower bound —
     `rank R(G,p) = D(|V|−1) − def(G̃)` for generic `(G,p)`, which is
     Theorem 5.5 pushed through the device. `prop:rigidity-matrix-prop11`
     `\uses` `thm:theorem-55` (already) and the 21b node.

### What opening Phase 21b will involve

Per *When this commit opens a phase* (CLAUDE.md): create
`notes/Phase21b.md`, add its forward-mode blueprint section (likely in
`algebraic-induction.tex` beside the consumers — a single
`lem:genericity-device` / `claim:6.4` node the four consumers `\uses`,
or its own chapter if it grows), sync the user-facing surfaces, flip the
21b status row to *in progress*. Scope and reuse-to-assess are in
`notes/MolecularConjecture.md` *Phase 21b*. The device is **also
consumed by Phases 22–23** (Case III candidate genericity), so building
it standalone pays forward.

**Smallest next concrete commit (recommended):** state `lem:case-I` as a
Lean theorem taking the genericity block-triangular-gluing conclusion as
an explicit hypothesis (the parallel of the now-green Case II assembly
`rankHypothesis_withNormal_withGraph_iff_finrank_pinnedMotions`), and
discharge everything genericity-free: place panel data on the contraction
`G/E(H)` (combinatorially green in Phase 20), re-add `E(H)` via `withGraph`
(block-pin monotonicity `pinnedMotionsOn_le_withGraph_of_le` + lower bound
`screwDim_add_finrank_pinnedMotionsOn_le`, both green), reducing the node to
"the two blocks' ranks add" with the generic gluing (Claim 6.4) the one 21b
input. That takes `lem:case-I` to GREEN-modulo-21b; then `thm:theorem-55` is
genericity-free induction assembly. All can proceed before 21b lands.
