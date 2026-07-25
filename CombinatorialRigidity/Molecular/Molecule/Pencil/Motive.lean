/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Mathlib.Combinatorics.Graph.Delete
import CombinatorialRigidity.Molecular.Molecule.Pencil.Arms

/-!
# The pencil-nondegenerate motive (Phase 39 PENCIL, W5-L0)

Carved out of `Molecule/Pencil.lean` (the post-Phase-39 file-size split,
`notes/PERFORMANCE.md`) for file size / navigability: the `≤1500`-LoC soft cap. This leaf carries
the W5 design pass's final conditioned-pair motive (`PencilPair`, its `IsNondegPencilRealization` /
`PencilNondegFeasible` / `HasGenericPencilRealization` ingredients, `Graph.PencilHub` /
`Graph.closedHubNbhd` / `Graph.closedNbhd`), the forgetful map back to the W3 bare motive
(`hasPencilRealization_of_generic`), and the loop-arm guard
(`not_pencilNondegFeasible_of_isLoopAt`). Builds on `Molecule/Pencil/Statement.lean` (via
`Molecule/Pencil/Arms.lean`). `Graph.closedNbhd` moved here 2026-07-24 from
`Molecule/Pencil/Chart.lean` (its original home) — the W5-L4 restatement's new
`IsNondegPencilRealization` conjunct needs it, and `Chart.lean` is downstream of this file.
`PencilPair` **restated 2026-07-24** per the W5-L5 blocker recon's (b′) route, user-adjudicated
(`notes/Phase39.md` *Blockers*): its generic conjunct is now conditioned on `G.Simple` in addition
to `PencilNondegFeasible`, and this leaf gained the corresponding vacuity helper
`not_simple_of_parallel`. The W5-L5 cut-arm restriction infra (`IsNondegPencilRealization.mono`
and its monotonicity feeders, 2026-07-24) also lives here — the predicates it restricts are this
file's.

This split is rename-free — every declaration keeps its `CombinatorialRigidity.Molecular`
namespace, so the blueprint `\lean{...}` pins and `checkdecls` are unaffected.

See `notes/Phase39.md`, `notes/Phase39-design.md` (§"W5 design pass"), and
`blueprint/src/chapter/pencil.tex`.
-/

open scoped Matrix
open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K]
variable {α β : Type*}

/-! ## W5-L0: the pencil-nondegenerate motive (Phase 39 PENCIL, W5 design pass)

The W5 design pass (`notes/Phase39-design.md` §"W5 design pass") pinned the final induction
motive: a *conditioned pair*, mirroring KT Theorem 5.5's own `(G.Simple →
HasGenericFullRankRealization) ∧ HasPanelRealization` shape (`Theorem55.lean`). The design pass's
first cut conditioned the generic conjunct on the stratum's own nondegenerate-satisfiability
(`PencilNondegFeasible`) *instead of* `G.Simple` — a `Simple`-conditioned generic conjunct alone is
refuted at `K4` (every body's closed hub-neighbourhood has `4` members there, forcing every hub
normal into a common orthogonal complement, so no nondegenerate point exists), and a
bare-existential generic conjunct starves both downstream consumers (the product-route genericity
argument needs a *nondegenerate* stratum point to perturb from, not merely a full-rank one).
**Restated 2026-07-24** (W5-L5 blocker recon, the user's (b′) adjudication): a `≥ 2`-fold parallel
class turns out to be nondegeneracy-*feasible* on its own
(`exists_isNondegPencilRealization_parallel_pair`, `Pencil/Pair.lean`) yet caps the achievable rank
one short of the target, so `PencilNondegFeasible` alone is not enough either — the generic
conjunct now nests `PencilNondegFeasible` inside a `G.Simple` antecedent, exactly Theorem 5.5's own
shape, with `PencilNondegFeasible` doing the additional `K4`-style work `G.Simple` alone cannot.
This section lands the motive layer: the hub / closed-hub-neighbourhood combinatorics, the
nondegeneracy predicate, its feasibility conditioning, the generic pencil motive, the
conditioned-pair motive itself, the forgetful map back to the bare motive, the loop guard showing
feasibility already fails at a loop (so the loop arm's generic obligation is free, mirroring the
landed program's `loop ⟹ ¬Simple`), and the parallel-class vacuity guard `not_simple_of_parallel`
(a `≥ 2`-fold parallel class already fails `G.Simple`, the same landed-program precedent applied to
the pencil base arm). -/

/-- **A pencil hub** (`def:pencil-nondegenerate`; Phase 39 W5-L0): a body of `G` of degree at least
three, exactly where the pencil pin bites (a degree-`≤ 2` body is automatically a pencil, two
coplanar lines being automatically concurrent — `exists_concurrency_point_of_extensorInPanel_pair`).
-/
def _root_.Graph.PencilHub (G : Graph α β) (v : α) : Prop :=
  v ∈ V(G) ∧ 3 ≤ G.degree v

/-- **The closed hub-neighbourhood of `v`** (`def:pencil-nondegenerate`; Phase 39 W5-L0): the
pencil hubs among `v` itself and its neighbours. These are exactly the bodies whose star-plane
normal `v`'s concurrency point `point v` is forced orthogonal to — `v`'s own normal by the
panel-point incidence, and a neighbouring hub `w`'s normal by the cross-incidence W2's necessity
direction forces on the link's shared pencil line
(`dotProduct_eq_zero_of_extensorInPanel_of_extensorThroughPoint`). -/
def _root_.Graph.closedHubNbhd (G : Graph α β) (v : α) : Set α :=
  {w | G.PencilHub w ∧ (w = v ∨ ∃ e, G.IsLink e v w)}

/-- **`v`'s closed neighbourhood** (`def:pencil-nondegenerate`; Phase 39 W5-L0/W5-L4): `v` together
with every body linked to it by an edge, hub or not. Unlike `closedHubNbhd` (which filters to hubs),
this is the target set of the fourth `IsNondegPencilRealization` conjunct below — the pencil chart's
own non-hub normal construction (`pencilChartNormal`, `Molecule/Pencil/Chart.lean`) reads exactly
this set, so it is the target the chart's image needs to be characterized against — and, at a
non-hub `v` (degree `≤ 2`), it always has at most three members, matching the arity the D6
re-seeding sweep (`Molecule/Pencil/Engine.lean`) was built for. -/
def _root_.Graph.closedNbhd (G : Graph α β) (v : α) : Set α :=
  {w | w = v ∨ ∃ e, G.IsLink e v w}

/-- **Stratum nondegeneracy** (`def:pencil-nondegenerate`; Phase 39 W5-L0, **restated 2026-07-24 per
the W5-L4 blocker recon**, `notes/Phase39-design.md` §"W5 leaf decomposition" L4 "Blocker verdict"):
a pencil panel realization whose adjacent concurrency points are projectively distinct (every
link's two endpoint points span a genuine line, not a single point counted twice), whose per-body
closed-hub-neighbourhood normals are linearly independent — the pencil analogue of KT's "no two
hinges parallel" nondegenerate-hinge condition (`def:genuine-hinge-realization`) — and whose
per-body closed-neighbourhood points are linearly independent at every non-hub body. The fourth
conjunct is the piece a compiler-checked collinear counterexample on the path `P₃` showed the
first three do not already force: nothing in them forbids the two hinges at an ordinary
degree-`2` body from coinciding projectively, which is exactly the degenerate case this conjunct
rules out. It bites only at a `3`-member closed neighbourhood (a `≤ 2`-member one is already
forced independent by nonzero-ness / the link pair-LI conjunct above), is invariant under
independent per-body nonzero rescaling of `point`/`normal` (so it composes with the chart's
projective reproduction contract, W5-L4), and must not be imposed at hubs (a degree-`≥ 4` hub's
`≥ 5`-member `closedNbhd` is never LI in `K⁴`). -/
def IsNondegPencilRealization (G : Graph α β) (F : BodyHingeFramework K 2 α β)
    (normal point : α → Fin 4 → K) : Prop :=
  HasPencilPanelRealization G F normal point ∧
  (∀ e u v, G.IsLink e u v → LinearIndependent K ![point u, point v]) ∧
  (∀ v ∈ V(G), LinearIndepOn K normal (G.closedHubNbhd v)) ∧
  (∀ v ∈ V(G), ¬ G.PencilHub v → LinearIndepOn K point (G.closedNbhd v))

/-- **Nondegenerate-realization feasibility** (`def:pencil-nondegenerate`; Phase 39 W5-L0): the
second conditioning predicate for the pencil induction's generic conjunct, nested inside a
`G.Simple` antecedent (`PencilPair` below) — mirroring KT Theorem 5.5's own conditioned pair, with
this extra layer because `G.Simple` alone does not exclude every degeneration of the pencil
stratum: this predicate is refuted at `K4` (verdict 1, `notes/Phase39-design.md` §"W5 design pass"
— every body's closed hub-neighbourhood has all four vertices, over-determining the panel normals
against a nonzero point), a graph on which `G.Simple` alone says nothing. **Correction (2026-07-24,
W5-L5):** the original verdict also claimed this predicate is refuted at any graph with a `≥ 2`-fold
parallel class between two hubs — that claim is FALSE, refuted by a compiler-checked witness
(`exists_isNondegPencilRealization_parallel_pair`, `Pencil/Pair.lean`): a parallel class is
nondegeneracy-*feasible* (even without any hub, via two independent panels/points), even though the
achievable rank there is capped one short of the target (`notes/Phase39.md` *Blockers*). **Resolved
2026-07-24 by the user's (b′) adjudication:** this is exactly why `PencilPair`'s generic conjunct
keeps a `G.Simple` layer alongside this predicate rather than dropping it in favor of feasibility
alone — the witness above is the documented proof that feasibility cannot replace simplicity, and
`not_simple_of_parallel` below discharges the parallel case by non-simplicity instead. -/
def PencilNondegFeasible (K : Type*) [Field K] (G : Graph α β) : Prop :=
  ∃ (F : BodyHingeFramework K 2 α β) (normal point : α → Fin 4 → K),
    IsNondegPencilRealization G F normal point

/-- **The generic pencil motive** (`def:pencil-generic-motive`; Phase 39 W5-L0): a nondegenerate
pencil realization attaining the deficiency-rank target, the pencil analogue of
`HasGenericFullRankRealization`. -/
def HasGenericPencilRealization (K : Type*) [Field K] (n : ℕ) (G : Graph α β) : Prop :=
  ∃ (F : BodyHingeFramework K 2 α β) (normal point : α → Fin 4 → K),
    IsNondegPencilRealization G F normal point ∧
    (Module.finrank K (Submodule.span K F.rigidityRows) : ℤ)
      = screwDim 2 * ((V(G).ncard : ℤ) - 1) - G.deficiency n

/-- **The conditioned-pair motive** (`def:pencil-conditioned-pair`; Phase 39 W5-L0, **restated
2026-07-24 per the user's (b′) adjudication** to the W5-L5 blocker recon
(`notes/Phase39-design.md` §"W5 leaf decomposition" L5 "Blocker verdict"): the final `P` of the
pencil reduction (`Graph.pencil_reduction`) — a bare pencil realization together with, when `G` is
both simple and nondegeneracy-feasible, a genuinely generic one. Two-layer conditioning, each layer
earning its keep: `G.Simple` excludes the multigraph degenerations exactly as KT Theorem 5.5's own
conditioned pair does (`Theorem55.lean`) — a `≥ 2`-fold parallel class IS nondegeneracy-*feasible*
(`exists_isNondegPencilRealization_parallel_pair`, `Pencil/Pair.lean`) but caps the achievable rank
one short of the target, since two hinges through the same pair of bodies are forced onto a single
supporting line — while `PencilNondegFeasible` excludes the stratum collapses a simplicity-only
conditioning misses (`K4`, verdict 1, `notes/Phase39-design.md` §"W5 design pass"). This is now the
exact Theorem-5.5 shape `(G.Simple → HasGenericFullRankRealization K k n G) ∧
HasPanelRealization K k n G`, with `PencilNondegFeasible` nested inside the `G.Simple` antecedent
rather than replacing it. -/
def PencilPair (K : Type*) [Field K] (n : ℕ) (G : Graph α β) : Prop :=
  (G.Simple → PencilNondegFeasible K G → HasGenericPencilRealization K n G) ∧
    HasPencilRealization K n G

/-- **A parallel class is never simple** (Phase 39 W5-L5, the (b′) repair's vacuity helper): two
distinct edges linking the same pair of vertices already break `G.Simple`
(`Graph.Simple.eq_of_isLink`). This is the fact `PencilPair`'s new `G.Simple` antecedent uses to
route the base arm's parallel-class sub-case around `PencilNondegFeasible`'s own witness there
(`exists_isNondegPencilRealization_parallel_pair`), mirroring the landed program's own
`not_simple_of_isMinimalKDof_of_ncard_two` at the same graphs. -/
theorem not_simple_of_parallel {G : Graph α β} {e f : β} {x y : α}
    (hef : e ≠ f) (hl_e : G.IsLink e x y) (hl_f : G.IsLink f x y) : ¬ G.Simple :=
  fun hSimple => hef (hSimple.eq_of_isLink hl_e hl_f)

/-- **The forgetful map** (Phase 39 W5-L0, the pencil analogue of `hasPanelRealization_of_generic`):
a generic pencil realization is in particular a bare pencil realization at the same rank — drop the
nondegeneracy conjuncts. -/
theorem hasPencilRealization_of_generic {n : ℕ} {G : Graph α β}
    (h : HasGenericPencilRealization K n G) : HasPencilRealization K n G := by
  obtain ⟨F, normal, point, ⟨hreal, _, _, _⟩, hrank⟩ := h
  exact ⟨F, normal, point, hreal, hrank⟩

/-- **The loop guard** (Phase 39 W5-L0): a loop already breaks nondegeneracy feasibility, the
pencil analogue of `loop ⟹ ¬Simple`. A loop `e` at `v` is a link `G.IsLink e v v`, so
`IsNondegPencilRealization`'s adjacent-distinct-points conjunct would force
`LinearIndependent K ![point v, point v]` — impossible, since `1 • point v + (-1) • point v = 0`
exhibits a nontrivial dependency (`LinearIndependent.pair_iff`). Consequently the loop arm's
generic obligation (`PencilNondegFeasible K G → HasGenericPencilRealization K n G`) is vacuously
true at any loop, mirroring the landed program's non-simple flows. -/
theorem not_pencilNondegFeasible_of_isLoopAt {G : Graph α β} {e : β} {v : α}
    (hloop : G.IsLoopAt e v) : ¬ PencilNondegFeasible K G := by
  rintro ⟨F, normal, point, _, hLI, _, _⟩
  have h := (LinearIndependent.pair_iff).1 (hLI e v v hloop) 1 (-1)
    (by rw [one_smul, neg_one_smul, add_neg_cancel])
  exact one_ne_zero h.1

/-! ## W5-L5 cut-arm infra: nondegeneracy restricts to subgraphs, off demoted hubs (Phase 39)

The cut arm of the conditioned-pair reduction owes each side's induction hypothesis its own
`PencilNondegFeasible` input (`notes/Phase39-design.md` §"W5 leaf decomposition" L5, "Long-run
comparison" point 1). This section lands the route-neutral restriction core behind that: a
nondegenerate pencil realization of `G` restricts to any subgraph `H ≤ G` — same supporting
extensors, same panels and points — with every conjunct surviving by monotonicity **except** the
fourth (non-hub closed-neighbourhood point LI) at a **demoted hub**: a body that is a pencil hub
of `G` but not of `H`. There `G`'s witness genuinely carries nothing (the fourth conjunct is
exempt at `G`-hubs, and the other three do not force it — `G` may legitimately place the two
surviving `H`-hinges of a demoted hub on one common line), so `IsNondegPencilRealization.mono`
takes the residual as an explicit hypothesis, and the feasibility corollary
`PencilNondegFeasible.mono` discharges it whenever every demotion lands at `H`-degree `≤ 1`,
where the closed neighbourhood has at most two members and the adjacent-point conjunct already
carries it. Demotion to `H`-degree exactly `2` is the genuinely gapped case — see
`notes/Phase39.md` *Blockers* (the 2026-07-24 cut-arm finding). -/

/-- **A pencil hub of a subgraph is a pencil hub of the ambient graph** (Phase 39 W5-L5 cut-arm
infra): vertex membership and degree are both monotone along `H ≤ G` (`Graph.vertexSet_mono`,
`Graph.degree_mono`; the latter asks the ambient graph to be locally finite). -/
theorem _root_.Graph.PencilHub.of_le {G H : Graph α β} [G.LocallyFinite] {v : α}
    (h : H.PencilHub v) (hle : H ≤ G) : G.PencilHub v :=
  ⟨Graph.vertexSet_mono hle h.1, h.2.trans (Graph.degree_mono hle v)⟩

/-- **The closed hub-neighbourhood is monotone along `H ≤ G`** (Phase 39 W5-L5 cut-arm infra):
hubs promote to the ambient graph (`Graph.PencilHub.of_le`) and links persist
(`Graph.IsLink.of_le`). -/
theorem _root_.Graph.closedHubNbhd_mono {G H : Graph α β} [G.LocallyFinite]
    (hle : H ≤ G) (v : α) : H.closedHubNbhd v ⊆ G.closedHubNbhd v := by
  rintro w ⟨hhub, rfl | ⟨e, hlink⟩⟩
  · exact ⟨hhub.of_le hle, Or.inl rfl⟩
  · exact ⟨hhub.of_le hle, Or.inr ⟨e, hlink.of_le hle⟩⟩

/-- **The closed neighbourhood is monotone along `H ≤ G`** (Phase 39 W5-L5 cut-arm infra). -/
theorem _root_.Graph.closedNbhd_mono {G H : Graph α β}
    (hle : H ≤ G) (v : α) : H.closedNbhd v ⊆ G.closedNbhd v := by
  rintro w (rfl | ⟨e, hlink⟩)
  · exact Or.inl rfl
  · exact Or.inr ⟨e, hlink.of_le hle⟩

/-- **Restriction of a nondegenerate pencil realization to a subgraph** (Phase 39 W5-L5 cut-arm
infra). A nondegenerate pencil realization of `G` restricts to any `H ≤ G` — keep the supporting
extensors, panels, and points — with every conjunct surviving by monotonicity except the fourth
at a **demoted hub** (`G.PencilHub v` but `¬ H.PencilHub v`), where `G`'s witness genuinely
carries no closed-neighbourhood point LI; that residual is the explicit hypothesis `hdemote`.
At a demoted body of `H`-degree `≤ 1` the residual follows from the adjacent-point conjunct
(the closed neighbourhood has at most two members — `PencilNondegFeasible.mono` below packages
this); at `H`-degree exactly `2` it is genuinely unavailable, since `G` may place the body's two
surviving hinges on one common line (`notes/Phase39.md` *Blockers*, the cut-arm finding). -/
theorem IsNondegPencilRealization.mono {G H : Graph α β} [G.LocallyFinite]
    {F : BodyHingeFramework K 2 α β} {normal point : α → Fin 4 → K}
    (hnd : IsNondegPencilRealization G F normal point) (hle : H ≤ G)
    (hdemote : ∀ v ∈ V(H), G.PencilHub v → ¬ H.PencilHub v →
      LinearIndepOn K point (H.closedNbhd v)) :
    IsNondegPencilRealization H ⟨H, F.supportExtensor⟩ normal point := by
  obtain ⟨⟨⟨-, hnnz, hSnz, hpanel⟩, hpnz, hpinc, hthrough⟩, hadj, hhubLI, hnbhdLI⟩ := hnd
  have hV : V(H) ⊆ V(G) := Graph.vertexSet_mono hle
  refine ⟨⟨⟨rfl, fun v hv => hnnz v (hV hv), hSnz,
      fun e u v hl => hpanel e u v (hl.of_le hle)⟩,
    fun v hv => hpnz v (hV hv), fun v hv => hpinc v (hV hv),
    fun e u v hl => hthrough e u v (hl.of_le hle)⟩,
    fun e u v hl => hadj e u v (hl.of_le hle),
    fun v hv => (hhubLI v (hV hv)).mono (Graph.closedHubNbhd_mono hle v), ?_⟩
  intro v hv hvnothub
  by_cases hGhub : G.PencilHub v
  · exact hdemote v hv hGhub hvnothub
  · exact (hnbhdLI v (hV hv) hGhub).mono (Graph.closedNbhd_mono hle v)

/-- **Feasibility restricts to subgraphs whose demotions are all pendant-or-isolated**
(Phase 39 W5-L5 cut-arm infra). `PencilNondegFeasible` descends along `H ≤ G` whenever every
`G`-pencil-hub of `H` either stays an `H`-hub or drops to `H`-degree `≤ 1`: the witness restricts
by `IsNondegPencilRealization.mono`, and the residual fourth conjunct at a degree-`≤ 1` demotion
follows from the adjacent-point conjunct — the closed neighbourhood is `{v}` or `{v, w}` for the
unique pendant neighbour `w` (`Graph.Inc.isPendant_of_degree_le_one`). The `≤ 1` bound is sharp:
at a demotion to `H`-degree `2` the residual genuinely has no source in `G`'s witness
(`notes/Phase39.md` *Blockers*, the cut-arm finding). -/
theorem PencilNondegFeasible.mono {G H : Graph α β} [G.LocallyFinite]
    (hfeas : PencilNondegFeasible K G) (hle : H ≤ G)
    (hhub : ∀ v ∈ V(H), G.PencilHub v → H.PencilHub v ∨ H.degree v ≤ 1) :
    PencilNondegFeasible K H := by
  haveI : H.LocallyFinite := ‹G.LocallyFinite›.mono hle
  obtain ⟨F, normal, point, hnd⟩ := hfeas
  have hadj := hnd.2.1
  have hpnz := hnd.1.2.1
  refine ⟨⟨H, F.supportExtensor⟩, normal, point, hnd.mono hle ?_⟩
  intro v hv hGhub hvnothub
  rcases hhub v hv hGhub with hHhub | hdeg
  · exact absurd hHhub hvnothub
  by_cases hinc : ∃ e w, H.IsLink e v w
  · obtain ⟨e, w, hl⟩ := hinc
    have hpend : H.IsPendant e v := hl.inc_left.isPendant_of_degree_le_one hdeg
    have hvw : v ≠ w := by rintro rfl; exact hpend.not_isLoopAt e hl
    have hsub : H.closedNbhd v ⊆ {v, w} := by
      rintro u (rfl | ⟨e', hl'⟩)
      · exact Set.mem_insert _ _
      · obtain rfl := hpend.edge_unique hl'.inc_left
        obtain rfl := hl.right_unique hl'
        exact Set.mem_insert_of_mem _ rfl
    have hLI : LinearIndepOn K point {v, w} := by
      rw [LinearIndepOn.pair_iff point hvw]
      exact LinearIndependent.pair_iff.1 (hadj e v w (hl.of_le hle))
    exact hLI.mono hsub
  · have hsub : H.closedNbhd v ⊆ {v} := by
      rintro u (rfl | ⟨e', hl'⟩)
      · rfl
      · exact absurd ⟨e', u, hl'⟩ hinc
    exact (LinearIndepOn.singleton (i := v)
      (hpnz v (Graph.vertexSet_mono hle hv))).mono hsub

/-! ## W5-L5 cut-arm infra: nondegeneracy transports along a contragredient pair (Phase 39,
L5-cut-ii)

The cut arm's non-hub matching sub-case (`notes/Phase39-design.md` §"W5 leaf decomposition" L5
"Cut-arm route verdict" item 1b) repositions one side's realization by a linear automorphism `g`
of `K⁴` (with contragredient `h`) before gluing. The panel-realization half of that transport is
already landed (`hasPencilPanelRealization_mapSupport_screwEquivOfLinearEquiv`, W3-L4 infra,
`Molecule/Pencil/Arms.lean`); this section layers the three nondegeneracy conjuncts on top —
conjuncts 2–4 transport by injectivity of `g`/`h` alone (`LinearIndependent.map_injOn` /
`LinearIndepOn.map_injOn`), with no further geometric content, since `G` itself is unchanged so
`PencilHub`/`closedHubNbhd`/`closedNbhd` are unchanged too. -/

/-- **Nondegeneracy transports along a contragredient linear-equivalence pair**
(Phase 39 W5-L5 cut-arm infra, L5-cut-ii; the `IsNondegPencilRealization` companion of
`hasPencilPanelRealization_mapSupport_screwEquivOfLinearEquiv`). Transporting a nondegenerate
pencil realization `(F, normal, point)` along a linear automorphism `g` of `K⁴` (acting on the
concurrency points) with contragredient `h` (acting on the panel normals, `g x ⬝ᵥ h y = x ⬝ᵥ y`)
produces another nondegenerate realization on the same graph `G`. -/
theorem IsNondegPencilRealization.mapSupport_screwEquivOfLinearEquiv
    {G : Graph α β} {F : BodyHingeFramework K 2 α β} {normal point : α → Fin 4 → K}
    (g h : (Fin 4 → K) ≃ₗ[K] (Fin 4 → K)) (hgh : ∀ x y : Fin 4 → K, g x ⬝ᵥ h y = x ⬝ᵥ y)
    (hnd : IsNondegPencilRealization G F normal point) :
    IsNondegPencilRealization G (F.mapSupport (BodyHingeFramework.screwEquivOfLinearEquiv g))
      (fun v => h (normal v)) (fun v => g (point v)) := by
  obtain ⟨hreal, hadj, hhubLI, hnbhdLI⟩ := hnd
  refine ⟨hasPencilPanelRealization_mapSupport_screwEquivOfLinearEquiv g h hgh hreal,
    fun e u v hl => ?_, fun v hv => ?_, fun v hv hnothub => ?_⟩
  · have hli := (hadj e u v hl).map_injOn g.toLinearMap g.injective.injOn
    have heq : g.toLinearMap ∘ ![point u, point v] = ![g (point u), g (point v)] := by
      funext i; fin_cases i <;> rfl
    rwa [heq] at hli
  · have hli := (hhubLI v hv).map_injOn h.toLinearMap h.injective.injOn
    simpa [Function.comp_def] using hli
  · have hli := (hnbhdLI v hv hnothub).map_injOn g.toLinearMap g.injective.injOn
    simpa [Function.comp_def] using hli

/-! ## Motive-consequence incidence and cardinality lemmas (Phase 39 W5-L4, re-homed W5-L5)

The cross-incidence orthogonality facts and the closed-hub-neighbourhood cardinality bound an
*arbitrary* nondegenerate realization satisfies. Landed with W5-L4 in
`Molecule/Pencil/Engine.lean`; **moved here 2026-07-24** (the W5-L5 cut-arm import-cone re-home,
`notes/Phase39-design.md` §"W5 leaf decomposition" L5-cut-i): they are consequences of the motive
alone — their only nontrivial inputs are `Molecule/Pencil/Statement.lean`'s W2 necessity engine
(`dotProduct_eq_zero_of_extensorInPanel_of_extensorThroughPoint`) and perp-dimension count
(`finrank_toDualPerp_single_eq`), both already in this file's import cone — and the cut arm's
consumers (`Molecule/Pencil/Pair.lean`, which imports only this leaf) need them without pulling
in the chart stack (`Chart`/`Engine`/`Reseed`). -/

/-- **A nondegenerate realization's point is orthogonal to every selected closed-neighbour's
normal** (Phase 39 W5-L4, the general form feeding both the cardinality bound below and the piece-3
assembly): for `w ∈ closedNbhd v`, `point v ⬝ᵥ normal w = 0` — own-panel incidence when `w = v`; the
W2 necessity cross-incidence (`dotProduct_eq_zero_of_extensorInPanel_of_extensorThroughPoint`, via
the linking edge's own-panel membership of `normal w` and through-point membership of `point v`)
otherwise. The proof never uses a hub hypothesis on `w`, so this generalizes what used to be stated
only for `closedHubNbhd` (`dotProduct_point_eq_zero_of_mem_closedHubNbhd` below is now a one-line
corollary); this generalizes the chart's by-construction fact
(`dotProduct_pencilChartPoint_hubNormal_of_mem_closedHubNbhd`, `Molecule/Pencil/Chart.lean`) from
the chart's own constructed data to an *arbitrary* nondegenerate realization. -/
theorem dotProduct_point_eq_zero_of_mem_closedNbhd
    {G : Graph α β} {F : BodyHingeFramework K 2 α β}
    {normal point : α → Fin 4 → K} (h : IsNondegPencilRealization G F normal point)
    {v w : α} (hv : v ∈ V(G)) (hw : w ∈ G.closedNbhd v) :
    point v ⬝ᵥ normal w = 0 := by
  obtain ⟨hcop, _, hself, hthru⟩ := h.1
  obtain ⟨_, _, hCne, hpanel⟩ := hcop
  rcases hw with rfl | ⟨e, hlink⟩
  · exact hself w hv
  · exact dotProduct_eq_zero_of_extensorInPanel_of_extensorThroughPoint (hCne e)
      (hpanel e v w hlink).2 (hthru e v w hlink).1

/-- **The `closedHubNbhd` specialization** (Phase 39 W5-L4): immediate from the general
`closedNbhd` form above, forgetting the hub conjunct on `w` (`closedHubNbhd v ⊆ closedNbhd v`
pointwise, `hw.2`). -/
theorem dotProduct_point_eq_zero_of_mem_closedHubNbhd
    {G : Graph α β} {F : BodyHingeFramework K 2 α β}
    {normal point : α → Fin 4 → K} (h : IsNondegPencilRealization G F normal point)
    {v w : α} (hv : v ∈ V(G)) (hw : w ∈ G.closedHubNbhd v) :
    point v ⬝ᵥ normal w = 0 :=
  dotProduct_point_eq_zero_of_mem_closedNbhd h hv hw.2

/-- **The symmetric form: a nondegenerate realization's normal is orthogonal to every selected
closed-neighbour's point** (Phase 39 W5-L4, feeding the piece-3 assembly's non-hub chart-normal
reproduction): for `w ∈ closedNbhd v`, `point w ⬝ᵥ normal v = 0`. Applies the general fact above at
`(w, v)` in place of `(v, w)`: the `w = v` case reduces to itself; the linked case transports `w`'s
own graph membership via `hlink.right_mem` and rewrites `v ∈ closedNbhd w` from
`w ∈ closedNbhd v` by symmetrizing the link (`hlink.symm`). -/
theorem dotProduct_normal_eq_zero_of_mem_closedNbhd
    {G : Graph α β} {F : BodyHingeFramework K 2 α β}
    {normal point : α → Fin 4 → K} (h : IsNondegPencilRealization G F normal point)
    {v w : α} (hv : v ∈ V(G)) (hw : w ∈ G.closedNbhd v) :
    point w ⬝ᵥ normal v = 0 := by
  rcases hw with rfl | ⟨e, hlink⟩
  · exact dotProduct_point_eq_zero_of_mem_closedNbhd h hv (Or.inl rfl)
  · exact dotProduct_point_eq_zero_of_mem_closedNbhd h hlink.right_mem (Or.inr ⟨e, hlink.symm⟩)

/-- **A nondegenerate realization's closed hub-neighbourhoods have `≤ 3` members**
(Phase 39 W5-L4, the re-seeding assembly's cardinality bound — the same argument as the design
doc's K4 refutation, `notes/Phase39-design.md` §"W5 design pass" verdict 1). Any `4`-member
sub-family of an independent `normal` assignment on `closedHubNbhd v` would span all of `K⁴` (the
ambient rank), forcing `point v` — orthogonal to every member (the cross-incidence lemma above) —
to vanish, contradicting nondegeneracy. Concretely: the span of `normal '' closedHubNbhd v` sits
inside `point v`'s `3`-dimensional perp (`finrank_toDualPerp_single_eq`), so its rank is `≤ 3`; the
independence conjunct makes that rank exactly `(closedHubNbhd v).ncard` (`finrank_span_eq_card`,
`[Finite α]` supplying the `Fintype` instance the plain `Set` needs). -/
theorem ncard_closedHubNbhd_le_three_of_isNondegPencilRealization
    [Finite α] {G : Graph α β} {F : BodyHingeFramework K 2 α β} {normal point : α → Fin 4 → K}
    (h : IsNondegPencilRealization G F normal point) {v : α} (hv : v ∈ V(G)) :
    (G.closedHubNbhd v).ncard ≤ 3 := by
  classical
  have hpt_ne : point v ≠ 0 := h.1.2.1 v hv
  have hLI : LinearIndepOn K normal (G.closedHubNbhd v) := h.2.2.1 v hv
  set Vperp : Submodule K (Fin 4 → K) :=
    LinearMap.ker ((Pi.basisFun K (Fin 4)).toDual.flip (point v)) with hVperp
  have hVdim : Module.finrank K Vperp = 3 := finrank_toDualPerp_single_eq hpt_ne
  have hsub : Submodule.span K (normal '' G.closedHubNbhd v) ≤ Vperp := by
    rw [Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    simp only [SetLike.mem_coe, hVperp, LinearMap.mem_ker, LinearMap.flip_apply,
      piBasisFun_toDual_eq_dotProduct]
    rw [dotProduct_comm]
    exact dotProduct_point_eq_zero_of_mem_closedHubNbhd h hv hw
  have hspan_le : Module.finrank K (Submodule.span K (normal '' G.closedHubNbhd v)) ≤ 3 := by
    have hmono := Submodule.finrank_mono hsub
    rwa [hVdim] at hmono
  haveI : Fintype (G.closedHubNbhd v) := Fintype.ofFinite _
  have hspan_eq : Module.finrank K
      (Submodule.span K (Set.range (fun x : G.closedHubNbhd v => normal x)))
      = Fintype.card (G.closedHubNbhd v) := finrank_span_eq_card hLI
  have himg : Set.range (fun x : G.closedHubNbhd v => normal x) = normal '' G.closedHubNbhd v :=
    (Set.image_eq_range normal (G.closedHubNbhd v)).symm
  rw [himg] at hspan_eq
  have hcard : (G.closedHubNbhd v).ncard = Fintype.card (G.closedHubNbhd v) := by
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]
  rw [hcard, ← hspan_eq]
  exact hspan_le

/-- **A non-hub body's closed neighbourhood has `≤ 3` members** (Phase 39 W5-L4, the `closedNbhd`
companion of the cardinality bound above — purely combinatorial, no genericity; **re-homed
2026-07-25 from `Molecule/Pencil/Engine.lean`**, the same import-cone reason as the bound above —
the W5-L5 cut arm's sub-case-1 producer needs it without the chart stack in the import cone): a
non-hub `v` has degree `≤ 2` (`Graph.PencilHub`'s negation), and the distinct-neighbour set
`N(G, v)` embeds into the incident-edge set via "an edge's other endpoint"
(`Graph.encard_adj_le_encard_inc`, unconditional — no loopless/simple hypothesis needed), which has
cardinality `≤ eDegree v = degree v` (`[Finite β]` supplying `LocallyFinite`,
`Graph.natCast_degree_eq`); `closedNbhd v = insert v (N(G, v))` (`rfl`), so `Set.ncard_insert_le`
gives the `+ 1`. -/
theorem ncard_closedNbhd_le_three_of_not_pencilHub [Finite β] {G : Graph α β} {v : α}
    (hv : ¬ G.PencilHub v) :
    (G.closedNbhd v).ncard ≤ 3 := by
  classical
  have hdeg : G.degree v ≤ 2 := by
    by_contra hcon
    push Not at hcon
    by_cases hvV : v ∈ V(G)
    · exact hv ⟨hvV, by omega⟩
    · have h0 := Graph.degree_eq_zero_of_notMem (G := G) hvV
      omega
  have hNle : (N(G, v)).encard ≤ G.eDegree v :=
    (Graph.encard_adj_le_encard_inc).trans (Graph.encard_inc_le_eDegree)
  have heDeg : (G.degree v : ℕ∞) = G.eDegree v := Graph.natCast_degree_eq G v
  rw [← heDeg] at hNle
  have hcast : (G.degree v : ℕ∞) ≤ (2 : ℕ∞) := by exact_mod_cast hdeg
  have hNle2 : (N(G, v)).encard ≤ (2 : ℕ∞) := hNle.trans hcast
  obtain ⟨hNfin, hNcard⟩ := Set.encard_le_coe_iff_finite_ncard_le.mp hNle2
  have heq : G.closedNbhd v = insert v (N(G, v)) := rfl
  rw [heq]
  calc (insert v (N(G, v))).ncard ≤ (N(G, v)).ncard + 1 := Set.ncard_insert_le v (N(G, v))
    _ ≤ 2 + 1 := Nat.add_le_add_right hNcard 1
    _ = 3 := by norm_num

/-! ## W5-L5 cut-arm structure layer: the edge-closed side `Gᵢ⁺` (Phase 39)

The cut-arm route verdict (`notes/Phase39-design.md` §"W5 leaf decomposition" L5 "Cut-arm route
verdict") pinned the IH-consumption shape for the generic half: not the bare induced side
`G.induce Vᵢ` (whose demoted-hub restriction gap is the recorded cut-arm finding) but the
**edge-closed side** `Gᵢ⁺ = G.induce (Vᵢ ∪ {far})`, where `far` is the single crossing edge's
endpoint on the other side. With at most one crossing edge and a loopless `G`, this graph carries
exactly the side's edges plus the cut edge, so every `Vᵢ`-vertex keeps its full `G`-degree (no
demotion — the fourth conjunct restricts wholesale) and the far endpoint drops to degree `1`
(a demotion `PencilNondegFeasible.mono` already bridges). This section lands that structure
layer: the two degree lemmas, the feasibility corollary through `.mono`, and the deficiency
bookkeeping `def(Gᵢ⁺) = def(G.induce Vᵢ) + 1` (the split `deficiency_eq_of_cutEdges_ncard_le_one`
applied *inside* `Gᵢ⁺` at its singleton far side, whose induced side is edgeless; the re-induce
collapses by the mirrored `Graph.induce_induce_of_subset`). The rank-side companion — dropping
the cut edge's rows costs at most `screwDim k − 1` — is the new brick
`BodyHingeFramework.finrank_span_rigidityRows_le_add_of_links_subset`
(`RigidityMatrix/Bricks.lean` §CutEdgeBrick). -/

/-- **Under `≤ 1` crossing edge, every crossing link is the pinned cut edge** (Phase 39 W5-L5
cut-arm structure layer, the dispatch fact all three `Gᵢ⁺` lemmas below share): a link `e = xy`
with `x ∈ V₁` and `y ∉ V₁` is a member of `G.cutEdges V₁`, which contains the pinned `e₀` and has
at most one member. -/
theorem _root_.Graph.eq_cutEdge_of_isLink_crossing [Finite β] {G : Graph α β} {V₁ : Set α}
    {e₀ : β} {u₀ w₀ : α} (hl₀ : G.IsLink e₀ u₀ w₀) (hu₀ : u₀ ∈ V₁) (hw₀ : w₀ ∉ V₁)
    (hcut : (G.cutEdges V₁).ncard ≤ 1) {e : β} {x y : α}
    (hl : G.IsLink e x y) (hx : x ∈ V₁) (hy : y ∉ V₁) : e = e₀ := by
  have he : e ∈ G.cutEdges V₁ := ⟨hl.edge_mem, x, y, hl, hx, hy⟩
  have he₀ : e₀ ∈ G.cutEdges V₁ := ⟨hl₀.edge_mem, u₀, w₀, hl₀, hu₀, hw₀⟩
  exact (Set.ncard_le_one (Set.toFinite _)).mp hcut e he e₀ he₀

/-- **The edge-closed side preserves own-side degrees** (Phase 39 W5-L5 cut-arm structure layer,
degree lemma 1): with at most one crossing edge `e₀ = u₀w₀`, every `v ∈ V₁` has the same degree in
`Gᵢ⁺ = G.induce (V₁ ∪ {w₀})` as in `G` — an edge at `v` is either `V₁`-internal or the crossing
`e₀` itself, and both survive the induce (`w₀` is exactly the vertex the closure adds). Hence no
pencil hub of `G` on `V₁` is demoted in `Gᵢ⁺` — the gap the cut-arm finding exhibited for the bare
side `G.induce V₁` closes structurally. -/
theorem _root_.Graph.degree_induce_union_singleton_of_mem [Finite β] {G : Graph α β}
    {V₁ : Set α} {e₀ : β} {u₀ w₀ : α}
    (hl₀ : G.IsLink e₀ u₀ w₀) (hu₀ : u₀ ∈ V₁) (hw₀ : w₀ ∉ V₁)
    (hcut : (G.cutEdges V₁).ncard ≤ 1) {v : α} (hv : v ∈ V₁) :
    (G.induce (V₁ ∪ {w₀})).degree v = G.degree v := by
  have hloops : {e | (G.induce (V₁ ∪ {w₀})).IsLoopAt e v} = {e | G.IsLoopAt e v} := by
    ext e
    exact ⟨fun h => ((Graph.induce_isLink G (V₁ ∪ {w₀}) e v v).mp h).1,
      fun h => (Graph.induce_isLink G (V₁ ∪ {w₀}) e v v).mpr
        ⟨h, Set.mem_union_left _ hv, Set.mem_union_left _ hv⟩⟩
  have hnonloops : {e | (G.induce (V₁ ∪ {w₀})).IsNonloopAt e v}
      = {e | G.IsNonloopAt e v} := by
    ext e
    constructor
    · rintro ⟨y, hyv, hl⟩
      exact ⟨y, hyv, ((Graph.induce_isLink G (V₁ ∪ {w₀}) e v y).mp hl).1⟩
    · rintro ⟨y, hyv, hl⟩
      refine ⟨y, hyv, (Graph.induce_isLink G (V₁ ∪ {w₀}) e v y).mpr
        ⟨hl, Set.mem_union_left _ hv, ?_⟩⟩
      by_cases hy : y ∈ V₁
      · exact Set.mem_union_left _ hy
      · obtain rfl := Graph.eq_cutEdge_of_isLink_crossing hl₀ hu₀ hw₀ hcut hl hv hy
        rcases hl.eq_and_eq_or_eq_and_eq hl₀ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Set.mem_union_right _ rfl
        · exact absurd hv hw₀
  rw [Graph.degree_eq_ncard_add_ncard, Graph.degree_eq_ncard_add_ncard, hloops, hnonloops]

/-- **The edge-closed side's far endpoint has degree exactly `1`** (Phase 39 W5-L5 cut-arm
structure layer, degree lemma 2): in `Gᵢ⁺ = G.induce (V₁ ∪ {w₀})` the closure vertex `w₀` is
incident to the crossing edge `e₀` only — any other `Gᵢ⁺`-edge at `w₀` would have its far endpoint
in `V₁`, making it a second crossing edge of `G` (impossible under `≤ 1`), and a loop at `w₀` is
excluded by `[G.Loopless]`. In particular a `G`-pencil-hub `w₀` is demoted to `Gᵢ⁺`-degree `1`,
exactly the demotion `PencilNondegFeasible.mono`'s adjacent-point bridge covers. -/
theorem _root_.Graph.degree_induce_union_singleton_far [Finite β] {G : Graph α β} [G.Loopless]
    {V₁ : Set α} {e₀ : β} {u₀ w₀ : α}
    (hl₀ : G.IsLink e₀ u₀ w₀) (hu₀ : u₀ ∈ V₁) (hw₀ : w₀ ∉ V₁)
    (hcut : (G.cutEdges V₁).ncard ≤ 1) :
    (G.induce (V₁ ∪ {w₀})).degree w₀ = 1 := by
  have huw : u₀ ≠ w₀ := fun h => hw₀ (h ▸ hu₀)
  have hloops : {e | (G.induce (V₁ ∪ {w₀})).IsLoopAt e w₀} = ∅ := by
    ext e
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    exact fun h =>
      G.not_isLoopAt e w₀ ((Graph.induce_isLink G (V₁ ∪ {w₀}) e w₀ w₀).mp h).1
  have hnonloops : {e | (G.induce (V₁ ∪ {w₀})).IsNonloopAt e w₀} = {e₀} := by
    ext e
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨y, hyw, hl⟩
      obtain ⟨hlG, -, hy⟩ := (Graph.induce_isLink G (V₁ ∪ {w₀}) e w₀ y).mp hl
      have hy₁ : y ∈ V₁ := hy.resolve_right hyw
      exact Graph.eq_cutEdge_of_isLink_crossing hl₀ hu₀ hw₀ hcut hlG.symm hy₁ hw₀
    · rintro he
      rw [he]
      exact ⟨u₀, huw, (Graph.induce_isLink G (V₁ ∪ {w₀}) e₀ w₀ u₀).mpr
        ⟨hl₀.symm, Set.mem_union_right _ rfl, Set.mem_union_left _ hu₀⟩⟩
  rw [Graph.degree_eq_ncard_add_ncard, hloops, hnonloops, Set.ncard_empty, Set.ncard_singleton]

/-- **Every `Gᵢ⁺`-link is either `Vᵢ`-internal or the pinned cut edge** (Phase 39 W5-L5, L5-cut-iv
sub-case 1: the `hlinks` hypothesis the drop brick
`finrank_span_rigidityRows_le_add_of_links_subset` (`RigidityMatrix/Bricks.lean`) wants at
`G' := Gᵢ⁺`, `Gs := G.induce Vᵢ`). Dispatches on whether each endpoint is in `V₁` or is `w₀`: both
in `V₁` survive the induce directly; one endpoint `w₀` forces the edge to be `e₀`
(`Graph.eq_cutEdge_of_isLink_crossing`, in either orientation); both endpoints `w₀` is a loop,
excluded by `[G.Loopless]`. -/
theorem _root_.Graph.isLink_induce_union_singleton_of_isLink [Finite β] {G : Graph α β}
    [G.Loopless] {V₁ : Set α} {e₀ : β} {u₀ w₀ : α}
    (hl₀ : G.IsLink e₀ u₀ w₀) (hu₀ : u₀ ∈ V₁) (hw₀ : w₀ ∉ V₁)
    (hcut : (G.cutEdges V₁).ncard ≤ 1) {e : β} {u v : α}
    (hl : (G.induce (V₁ ∪ {w₀})).IsLink e u v) :
    (G.induce V₁).IsLink e u v ∨ e = e₀ := by
  obtain ⟨hlG, hu, hv⟩ := (Graph.induce_isLink G (V₁ ∪ {w₀}) e u v).mp hl
  by_cases hu₁ : u ∈ V₁
  · by_cases hv₁ : v ∈ V₁
    · exact Or.inl ((Graph.induce_isLink G V₁ e u v).mpr ⟨hlG, hu₁, hv₁⟩)
    · have hvw : v = w₀ := hv.resolve_left hv₁
      subst hvw
      exact Or.inr (Graph.eq_cutEdge_of_isLink_crossing hl₀ hu₀ hw₀ hcut hlG hu₁ hw₀)
  · have huw : u = w₀ := hu.resolve_left hu₁
    by_cases hv₁ : v ∈ V₁
    · exact Or.inr (Graph.eq_cutEdge_of_isLink_crossing hl₀ hu₀ hw₀ hcut hlG.symm hv₁ hu₁)
    · have hvw : v = w₀ := hv.resolve_left hv₁
      have huv : u = v := huw.trans hvw.symm
      exact absurd (huv ▸ hlG) (G.not_isLoopAt e v)

/-- **Feasibility descends to the edge-closed side** (Phase 39 W5-L5 cut-arm structure layer, the
IH-input corollary; the composition the cut-arm route verdict spiked): `PencilNondegFeasible K G`
restricts to `Gᵢ⁺ = G.induce (V₁ ∪ {w₀})` through `PencilNondegFeasible.mono` — every `G`-hub on
`V₁` keeps its full degree (degree lemma 1, no demotion), and the far endpoint `w₀` drops to
degree `1` (degree lemma 2), the pendant demotion the `.mono` bridge already carries. This is the
input half of the sub-case-1/2 IH consumption; the output half (transport of the glued conjuncts)
is L5-cut-ii/iii. -/
theorem PencilNondegFeasible.induce_union_singleton [Finite β] {G : Graph α β} [G.Loopless]
    {V₁ : Set α} {e₀ : β} {u₀ w₀ : α}
    (hfeas : PencilNondegFeasible K G)
    (hl₀ : G.IsLink e₀ u₀ w₀) (hu₀ : u₀ ∈ V₁) (hw₀ : w₀ ∉ V₁)
    (hV₁ : V₁ ⊆ V(G)) (hcut : (G.cutEdges V₁).ncard ≤ 1) :
    PencilNondegFeasible K (G.induce (V₁ ∪ {w₀})) := by
  have hle : G.induce (V₁ ∪ {w₀}) ≤ G := Graph.induce_le (by
    rintro x (hx | rfl)
    · exact hV₁ hx
    · exact hl₀.right_mem)
  refine hfeas.mono hle ?_
  rintro v (hv₁ | rfl) hGhub
  · exact Or.inl ⟨Set.mem_union_left _ hv₁, by
      rw [Graph.degree_induce_union_singleton_of_mem hl₀ hu₀ hw₀ hcut hv₁]
      exact hGhub.2⟩
  · exact Or.inr (Graph.degree_induce_union_singleton_far hl₀ hu₀ hw₀ hcut).le

/-- **The edge-closed side's deficiency bookkeeping** (Phase 39 W5-L5 cut-arm structure layer;
`def(Gᵢ⁺) = def(G.induce V₁) + 1`): apply the cut split (KT Lemma 3.6,
`deficiency_eq_of_cutEdges_ncard_le_one`) *inside* `Gᵢ⁺` at its singleton far side `{w₀}` — the
unique crossing edge there is `e₀`, the singleton side is edgeless (`[G.Loopless]`) with
deficiency `0` (`deficiency_of_edgeSet_empty`), the complementary side re-induces to
`G.induce V₁` (`Graph.induce_induce_of_subset`), and the cut term contributes
`D − (D − 1)·1 = 1` for every `D`. This is the bookkeeping that converts the IH rank at `Gᵢ⁺`
(target `screwDim k · (|V₁| + 1 − 1) − def(Gᵢ⁺)`) into the bare-side form the landed cut assembly
`finrank_span_rigidityRows_cutEdge_eq` consumes, once the drop brick removes the cut edge's rows. -/
theorem _root_.Graph.deficiency_induce_union_singleton [Finite α] [Finite β] {G : Graph α β}
    [G.Loopless] {n : ℕ} (hD : 1 ≤ Graph.bodyBarDim n) {V₁ : Set α} {e₀ : β} {u₀ w₀ : α}
    (hl₀ : G.IsLink e₀ u₀ w₀) (hu₀ : u₀ ∈ V₁) (hw₀ : w₀ ∉ V₁)
    (hcut : (G.cutEdges V₁).ncard ≤ 1) :
    (G.induce (V₁ ∪ {w₀})).deficiency n = (G.induce V₁).deficiency n + 1 := by
  classical
  set Gp := G.induce (V₁ ∪ {w₀}) with hGpdef
  have hne : ({w₀} : Set α).Nonempty := ⟨w₀, rfl⟩
  have hssub : ({w₀} : Set α) ⊂ V(Gp) :=
    (Set.ssubset_iff_of_subset (fun x hx => Set.mem_union_right _ hx)).mpr
      ⟨u₀, Set.mem_union_left _ hu₀, fun h => hw₀ (h ▸ hu₀)⟩
  have hcut' : Gp.cutEdges {w₀} = {e₀} := by
    ext e
    simp only [Graph.cutEdges, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨-, x, y, hl, hx, hy⟩
      obtain ⟨hlG, -, hyV⟩ := (Graph.induce_isLink G (V₁ ∪ {w₀}) e x y).mp hl
      rw [hx] at hlG
      have hy₁ : y ∈ V₁ := hyV.resolve_right hy
      exact Graph.eq_cutEdge_of_isLink_crossing hl₀ hu₀ hw₀ hcut hlG.symm hy₁ hw₀
    · rintro he
      rw [he]
      have hl' : Gp.IsLink e₀ w₀ u₀ := (Graph.induce_isLink G (V₁ ∪ {w₀}) e₀ w₀ u₀).mpr
        ⟨hl₀.symm, Set.mem_union_right _ rfl, Set.mem_union_left _ hu₀⟩
      exact ⟨hl'.edge_mem, w₀, u₀, hl', rfl, fun h => hw₀ (h ▸ hu₀)⟩
  have hsplit := Graph.deficiency_eq_of_cutEdges_ncard_le_one (G := Gp) hD hne hssub
    (by rw [hcut', Set.ncard_singleton])
  have hdiff : V(Gp) \ {w₀} = V₁ := by
    ext x
    simp only [Set.mem_diff, Set.mem_singleton_iff]
    exact ⟨fun ⟨hx, hxw⟩ => (hx.resolve_right hxw : x ∈ V₁),
      fun hx => ⟨Set.mem_union_left _ hx, fun h => hw₀ (h ▸ hx)⟩⟩
  have hE : E(Gp.induce {w₀}) = ∅ := by
    ext e
    simp only [Graph.edgeSet_induce, Set.mem_setOf_eq, Set.mem_singleton_iff,
      Set.mem_empty_iff_false, iff_false]
    rintro ⟨x, y, hl, hx, hy⟩
    rw [hx, hy] at hl
    exact G.not_isLoopAt e w₀ ((Graph.induce_isLink G (V₁ ∪ {w₀}) e w₀ w₀).mp hl).1
  have hdef₀ : (Gp.induce {w₀}).deficiency n = 0 := by
    rw [Graph.deficiency_of_edgeSet_empty hE]
    simp [Set.ncard_singleton]
  have hind : Gp.induce V₁ = G.induce V₁ :=
    Graph.induce_induce_of_subset G Set.subset_union_left
  rw [hcut', Set.ncard_singleton, hdiff, hind, hdef₀] at hsplit
  rw [hsplit]
  push_cast
  ring

/-! ## W5-L5 cut-arm structure layer: boundary identities on `Vᵢ` (Phase 39, L5-cut-ii)

The matching transport (`notes/Phase39-design.md` §"W5 leaf decomposition" L5 "Cut-arm route
verdict" item 1b) reads `Gᵢ⁺.closedHubNbhd`/`closedNbhd` at the crossing endpoint `u₀` and its
neighbours, all inside `V₁`. This section identifies both against `G`'s own: `closedNbhd` agrees
on the nose (no exception — every `G`-neighbour of a `V₁`-vertex already lies in `V₁ ∪ {w₀}`, the
full vertex set of `Gᵢ⁺`, since any other crossing neighbour would be a second cut edge); the
`closedHubNbhd` differs from `G`'s own only by dropping `w₀` (the single `u₀` exception the design
doc records — `w₀` is never a `Gᵢ⁺`-hub, degree lemma 2), a difference that is a no-op away from
`u₀` since no other `V₁`-vertex is `G`-adjacent to `w₀`. -/

/-- **`G`'s closed neighbourhood of a `V₁`-vertex stays inside `Gᵢ⁺`'s vertex set**
(Phase 39 W5-L5 cut-arm structure layer): with at most one crossing edge, the only possible
`V₁`-external `G`-neighbour of any `v ∈ V₁` is `w₀` itself (a second crossing destination would be
a second cut edge, ruled out by `Graph.eq_cutEdge_of_isLink_crossing` forcing `v = u₀`, contradicted
since `w₀ ∉ V₁`). -/
theorem _root_.Graph.closedNbhd_subset_of_mem [Finite β] {G : Graph α β}
    {V₁ : Set α} {e₀ : β} {u₀ w₀ : α}
    (hl₀ : G.IsLink e₀ u₀ w₀) (hu₀ : u₀ ∈ V₁) (hw₀ : w₀ ∉ V₁)
    (hcut : (G.cutEdges V₁).ncard ≤ 1) {v : α} (hv : v ∈ V₁) :
    G.closedNbhd v ⊆ V₁ ∪ {w₀} := by
  rintro w (rfl | ⟨e, hl⟩)
  · exact Set.mem_union_left _ hv
  · by_cases hw : w ∈ V₁
    · exact Set.mem_union_left _ hw
    · obtain rfl := Graph.eq_cutEdge_of_isLink_crossing hl₀ hu₀ hw₀ hcut hl hv hw
      rcases hl.eq_and_eq_or_eq_and_eq hl₀ with ⟨-, rfl⟩ | ⟨rfl, -⟩
      · exact Set.mem_union_right _ rfl
      · exact absurd hv hw₀

/-- **`Gᵢ⁺`'s closed neighbourhood of a `V₁`-vertex equals `G`'s own, on the nose**
(Phase 39 W5-L5 cut-arm structure layer). No exception at `u₀`: `closedNbhd` carries no
hub/degree filter, so every `G`-link at `v ∈ V₁` survives the induce verbatim
(`Graph.closedNbhd_subset_of_mem` places the far endpoint inside `Gᵢ⁺`'s vertex set whenever it
isn't already in `V₁`). -/
theorem _root_.Graph.closedNbhd_induce_union_singleton [Finite β] {G : Graph α β}
    {V₁ : Set α} {e₀ : β} {u₀ w₀ : α}
    (hl₀ : G.IsLink e₀ u₀ w₀) (hu₀ : u₀ ∈ V₁) (hw₀ : w₀ ∉ V₁)
    (hcut : (G.cutEdges V₁).ncard ≤ 1) {v : α} (hv : v ∈ V₁) :
    (G.induce (V₁ ∪ {w₀})).closedNbhd v = G.closedNbhd v := by
  apply Set.Subset.antisymm
  · rintro w (rfl | ⟨e, hl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨e, ((Graph.induce_isLink G (V₁ ∪ {w₀}) e v w).mp hl).1⟩
  · rintro w hw
    have hwmem : w ∈ V₁ ∪ ({w₀} : Set α) :=
      Graph.closedNbhd_subset_of_mem hl₀ hu₀ hw₀ hcut hv hw
    rcases hw with rfl | ⟨e, hl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨e, (Graph.induce_isLink G (V₁ ∪ {w₀}) e v w).mpr
        ⟨hl, Set.mem_union_left _ hv, hwmem⟩⟩

/-- **`Gᵢ⁺`'s closed hub-neighbourhood of a `V₁`-vertex is `G`'s own, minus `w₀`**
(Phase 39 W5-L5 cut-arm structure layer; the design doc's "single `u₀` exception"). Hub status
agrees on all of `V₁` (degree lemma 1, `Graph.degree_induce_union_singleton_of_mem`), and `w₀` is
never a `Gᵢ⁺`-hub (degree lemma 2, `Graph.degree_induce_union_singleton_far` — degree `1 < 3`); the
`\ {w₀}` correction is a no-op away from `u₀`, since no other `V₁`-vertex is `G`-adjacent to `w₀`
(`Graph.closedNbhd_subset_of_mem`). -/
theorem _root_.Graph.closedHubNbhd_induce_union_singleton [Finite β] {G : Graph α β} [G.Loopless]
    {V₁ : Set α} {e₀ : β} {u₀ w₀ : α} (hV₁ : V₁ ⊆ V(G))
    (hl₀ : G.IsLink e₀ u₀ w₀) (hu₀ : u₀ ∈ V₁) (hw₀ : w₀ ∉ V₁)
    (hcut : (G.cutEdges V₁).ncard ≤ 1) {v : α} (hv : v ∈ V₁) :
    (G.induce (V₁ ∪ {w₀})).closedHubNbhd v = G.closedHubNbhd v \ {w₀} := by
  have hNeq := Graph.closedNbhd_induce_union_singleton hl₀ hu₀ hw₀ hcut hv
  ext w
  constructor
  · intro hmem
    have hhub := hmem.1
    have hcase : w ∈ (G.induce (V₁ ∪ {w₀})).closedNbhd v := hmem.2
    have hwmem : w ∈ V₁ ∪ ({w₀} : Set α) := hhub.1
    have hwG : w ∈ G.closedNbhd v := hNeq ▸ hcase
    rcases hwmem with hw₁ | hweq
    · have hdeg3 : 3 ≤ (G.induce (V₁ ∪ {w₀})).degree w := hhub.2
      rw [Graph.degree_induce_union_singleton_of_mem hl₀ hu₀ hw₀ hcut hw₁] at hdeg3
      exact ⟨⟨⟨hV₁ hw₁, hdeg3⟩, hwG⟩, fun h => hw₀ (h ▸ hw₁)⟩
    · exfalso
      have hweq' : w = w₀ := hweq
      have hdeg3 : 3 ≤ (G.induce (V₁ ∪ {w₀})).degree w := hhub.2
      rw [hweq', Graph.degree_induce_union_singleton_far hl₀ hu₀ hw₀ hcut] at hdeg3
      omega
  · intro hmem
    have hmemG : w ∈ G.closedHubNbhd v := hmem.1
    have hwne : w ∉ ({w₀} : Set α) := hmem.2
    have hwG : G.PencilHub w := hmemG.1
    have hwcase : w ∈ G.closedNbhd v := hmemG.2
    have hwmem : w ∈ V₁ ∪ ({w₀} : Set α) :=
      Graph.closedNbhd_subset_of_mem hl₀ hu₀ hw₀ hcut hv hwcase
    have hw₁ : w ∈ V₁ := hwmem.resolve_right hwne
    have hcase' : w ∈ (G.induce (V₁ ∪ {w₀})).closedNbhd v := hNeq.symm ▸ hwcase
    refine ⟨⟨Or.inl hw₁, ?_⟩, hcase'⟩
    rw [Graph.degree_induce_union_singleton_of_mem hl₀ hu₀ hw₀ hcut hw₁]
    exact hwG.2

/-! ## W5-L5 cut-arm structure layer: the disjoint-sides case (Phase 39, L5-cut-iv sub-case 2)

The `|C| = 0` sub-case of the cut-arm route verdict (`notes/Phase39-design.md` §"W5 leaf
decomposition" L5 "Cut-arm route verdict", item 2) needs no `Gᵢ⁺` closure at all: with no crossing
edge, every `G`-neighbour of a `V₁`-vertex already lies in `V₁` (and symmetrically for `V₂`), so
degree, hub status, `closedHubNbhd`, and `closedNbhd` all transfer *on the nose* between `G` and
each side — no exception, no demotion. This section lands the three general-purpose lemmas behind
that, parametrized by an arbitrary "closed under `G`-adjacency" set `S` (reused for both `V₁` and
`V₂` by the sub-case's producer, `Pencil/Pair.lean`), rather than duplicating the `Gᵢ⁺`-style
per-side pair. -/

/-- **A `G`-adjacency-closed set's induced degree agrees with `G`'s own** (Phase 39 W5-L5
disjoint-sides structure layer): if every `G`-neighbour of a member of `S` stays in `S`, the
induced subgraph `G.induce S` preserves the degree of every `v ∈ S` — every edge at `v` (loop or
not) survives the induce, since its other endpoint is already in `S` (`hS`). -/
theorem _root_.Graph.degree_induce_of_forall_isLink_mem [Finite β] {G : Graph α β} {S : Set α}
    (hS : ∀ e x y, G.IsLink e x y → x ∈ S → y ∈ S) {v : α} (hv : v ∈ S) :
    (G.induce S).degree v = G.degree v := by
  have hloops : {e | (G.induce S).IsLoopAt e v} = {e | G.IsLoopAt e v} := by
    ext e
    exact ⟨fun h => ((Graph.induce_isLink G S e v v).mp h).1,
      fun h => (Graph.induce_isLink G S e v v).mpr ⟨h, hv, hv⟩⟩
  have hnonloops : {e | (G.induce S).IsNonloopAt e v} = {e | G.IsNonloopAt e v} := by
    ext e
    constructor
    · rintro ⟨y, hyv, hl⟩
      exact ⟨y, hyv, ((Graph.induce_isLink G S e v y).mp hl).1⟩
    · rintro ⟨y, hyv, hl⟩
      exact ⟨y, hyv, (Graph.induce_isLink G S e v y).mpr ⟨hl, hv, hS e v y hl hv⟩⟩
  rw [Graph.degree_eq_ncard_add_ncard, Graph.degree_eq_ncard_add_ncard, hloops, hnonloops]

/-- **A `G`-adjacency-closed set's induced closed hub-neighbourhood agrees with `G`'s own**
(Phase 39 W5-L5 disjoint-sides structure layer): every member `w` of the closed hub-neighbourhood
on either side is itself in `S` (either `w = v` or linked to `v ∈ S`, `hS`), so degree agreement
(`Graph.degree_induce_of_forall_isLink_mem`) transports hub status both ways; `hSVG` supplies the
ambient vertex membership `Graph.PencilHub` needs on the `G`-side. -/
theorem _root_.Graph.closedHubNbhd_induce_of_forall_isLink_mem [Finite β] {G : Graph α β}
    {S : Set α} (hSVG : S ⊆ V(G)) (hS : ∀ e x y, G.IsLink e x y → x ∈ S → y ∈ S) {v : α}
    (hv : v ∈ S) :
    (G.induce S).closedHubNbhd v = G.closedHubNbhd v := by
  ext w
  constructor
  · rintro ⟨⟨hwS, hdeg⟩, hw⟩
    rw [Graph.degree_induce_of_forall_isLink_mem hS hwS] at hdeg
    refine ⟨⟨hSVG hwS, hdeg⟩, ?_⟩
    rcases hw with rfl | ⟨e, hl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨e, ((Graph.induce_isLink G S e v w).mp hl).1⟩
  · rintro ⟨⟨hwG, hdeg⟩, hw⟩
    have hwS : w ∈ S := by
      rcases hw with rfl | ⟨e, hl⟩
      · exact hv
      · exact hS e v w hl hv
    refine ⟨⟨hwS, ?_⟩, ?_⟩
    · rwa [Graph.degree_induce_of_forall_isLink_mem hS hwS]
    · rcases hw with rfl | ⟨e, hl⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨e, (Graph.induce_isLink G S e v w).mpr ⟨hl, hv, hwS⟩⟩

/-- **A `G`-adjacency-closed set's induced closed neighbourhood agrees with `G`'s own**
(Phase 39 W5-L5 disjoint-sides structure layer): the `closedHubNbhd` lemma above without the hub
filter, hence no ambient-membership hypothesis needed. -/
theorem _root_.Graph.closedNbhd_induce_of_forall_isLink_mem [Finite β] {G : Graph α β}
    {S : Set α} (hS : ∀ e x y, G.IsLink e x y → x ∈ S → y ∈ S) {v : α} (hv : v ∈ S) :
    (G.induce S).closedNbhd v = G.closedNbhd v := by
  ext w
  constructor
  · rintro (rfl | ⟨e, hl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨e, ((Graph.induce_isLink G S e v w).mp hl).1⟩
  · rintro (rfl | ⟨e, hl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨e, (Graph.induce_isLink G S e v w).mpr ⟨hl, hv, hS e v w hl hv⟩⟩

/-! ## W5-L5 cut-arm structure layer: the pendant side (Phase 39, L5-cut-iv sub-case 3)

The `|V₃₋ᵢ| = 1` sub-case of the cut-arm route verdict (`notes/Phase39-design.md` §"W5 leaf
decomposition" L5 "Cut-arm route verdict", item 3): the far side is a single pendant vertex, so
`Gᵢ⁺ = G` and the edge-closed-side trick (L5-cut-i) is inapplicable — the induction hypothesis
fires directly at the *bare* induced side `H := G.induce V₁`, one vertex smaller than `G`. Unlike
the `Gᵢ⁺` structure layer, the two lemmas below need no far-vertex membership hypothesis on `G` at
all: they are the same "at most one crossing edge" fact, read for the bare induced side rather than
its edge-closure, so they hold regardless of how large the complementary side is (the pendant
configuration only enters once the far vertex's own degree/hub-status needs pinning, which the
sub-case-3 producer, `Pencil/Pair.lean`, does locally). The crossing endpoint `u₀`'s hub status is
the one place degree actually differs between `H` and `G` (by exactly one, the dropped crossing
edge); `Graph.pencilHub_iff_induce_of_degree_ne` shows it does not change at all when `G.degree u₀`
avoids exactly `3` — the sharp value where a single dropped edge can flip pencil-hub status. -/

/-- **The bare induced side keeps the ambient degree away from the crossing endpoint**
(Phase 39 W5-L5 cut-arm structure layer, L5-cut-iv sub-case 3; dual to
`Graph.degree_induce_union_singleton_of_mem`, read for the bare induced side instead of its
edge-closure). With at most one crossing edge `e₀ = u₀w₀`, every `v ∈ V₁` other than `u₀` keeps the
same degree in `G.induce V₁` as in `G`: any `G`-edge at `v` crossing out of `V₁` would, by
uniqueness of the crossing edge, have to be `e₀` itself, forcing `v = u₀` — contradicting
`v ≠ u₀`. -/
theorem _root_.Graph.degree_induce_eq_of_ne [Finite β] {G : Graph α β} {V₁ : Set α}
    {e₀ : β} {u₀ w₀ : α} (hl₀ : G.IsLink e₀ u₀ w₀) (hu₀ : u₀ ∈ V₁) (hw₀ : w₀ ∉ V₁)
    (hcut : (G.cutEdges V₁).ncard ≤ 1) {v : α} (hv : v ∈ V₁) (hvne : v ≠ u₀) :
    (G.induce V₁).degree v = G.degree v := by
  have hloops : {e | (G.induce V₁).IsLoopAt e v} = {e | G.IsLoopAt e v} := by
    ext e
    exact ⟨fun h => ((Graph.induce_isLink G V₁ e v v).mp h).1,
      fun h => (Graph.induce_isLink G V₁ e v v).mpr ⟨h, hv, hv⟩⟩
  have hnonloops : {e | (G.induce V₁).IsNonloopAt e v} = {e | G.IsNonloopAt e v} := by
    ext e
    constructor
    · rintro ⟨y, hyv, hl⟩
      exact ⟨y, hyv, ((Graph.induce_isLink G V₁ e v y).mp hl).1⟩
    · rintro ⟨y, hyv, hl⟩
      refine ⟨y, hyv, (Graph.induce_isLink G V₁ e v y).mpr ⟨hl, hv, ?_⟩⟩
      by_cases hy₁ : y ∈ V₁
      · exact hy₁
      · exfalso
        obtain rfl := Graph.eq_cutEdge_of_isLink_crossing hl₀ hu₀ hw₀ hcut hl hv hy₁
        rcases hl.eq_and_eq_or_eq_and_eq hl₀ with ⟨hveq, -⟩ | ⟨hveq, -⟩
        · exact hvne hveq
        · rw [hveq] at hv; exact hw₀ hv
  rw [Graph.degree_eq_ncard_add_ncard, Graph.degree_eq_ncard_add_ncard, hloops, hnonloops]

/-- **The crossing endpoint loses exactly the crossing edge's degree on the bare induced side**
(Phase 39 W5-L5 cut-arm structure layer, L5-cut-iv sub-case 3): `G.degree u₀ = (G.induce
V₁).degree u₀ + 1` — the nonloop edges at `u₀` are exactly the bare induced side's, plus `e₀`
itself (any other crossing edge at `u₀` would duplicate `e₀` by crossing-edge uniqueness, and no
`H`-internal edge is `e₀`, whose far endpoint `w₀` sits outside `V₁`). -/
theorem _root_.Graph.degree_eq_degree_induce_succ [Finite β] {G : Graph α β} [G.Loopless]
    {V₁ : Set α} {e₀ : β} {u₀ w₀ : α} (hl₀ : G.IsLink e₀ u₀ w₀) (hu₀ : u₀ ∈ V₁) (hw₀ : w₀ ∉ V₁)
    (hcut : (G.cutEdges V₁).ncard ≤ 1) :
    G.degree u₀ = (G.induce V₁).degree u₀ + 1 := by
  have hloopG : {e | G.IsLoopAt e u₀} = ∅ := by
    ext e
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    exact G.not_isLoopAt e u₀
  have hloopH : {e | (G.induce V₁).IsLoopAt e u₀} = ∅ := by
    ext e
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro h
    exact G.not_isLoopAt e u₀ ((Graph.induce_isLink G V₁ e u₀ u₀).mp h).1
  have hwu : w₀ ≠ u₀ := fun h => hw₀ (h ▸ hu₀)
  have hec_notmem : e₀ ∉ {e | (G.induce V₁).IsNonloopAt e u₀} := by
    rintro ⟨y, -, hl⟩
    obtain ⟨hlG, -, hyV₁⟩ := (Graph.induce_isLink G V₁ e₀ u₀ y).mp hl
    obtain rfl := hlG.right_unique hl₀
    exact hw₀ hyV₁
  have hnonloop_eq :
      {e | G.IsNonloopAt e u₀} = insert e₀ {e | (G.induce V₁).IsNonloopAt e u₀} := by
    ext e
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff]
    constructor
    · rintro ⟨y, hyu, hl⟩
      by_cases hy₁ : y ∈ V₁
      · exact Or.inr ⟨y, hyu, (Graph.induce_isLink G V₁ e u₀ y).mpr ⟨hl, hu₀, hy₁⟩⟩
      · have he := Graph.eq_cutEdge_of_isLink_crossing hl₀ hu₀ hw₀ hcut hl hu₀ hy₁
        exact Or.inl he
    · rintro (rfl | ⟨y, hyu, hl⟩)
      · exact ⟨w₀, hwu, hl₀⟩
      · exact ⟨y, hyu, ((Graph.induce_isLink G V₁ e u₀ y).mp hl).1⟩
  rw [Graph.degree_eq_ncard_add_ncard, Graph.degree_eq_ncard_add_ncard, hloopG, hloopH,
    hnonloop_eq, Set.ncard_insert_of_notMem hec_notmem (Set.toFinite _)]
  omega

/-- **The crossing endpoint's pencil-hub status is unchanged whenever its `G`-degree avoids `3`**
(Phase 39 W5-L5 cut-arm structure layer, L5-cut-iv sub-case 3): combining the degree-succ fact
above with `G.degree u₀ ≠ 3`, either `G.degree u₀ ≥ 4` (so both sides are hubs, the dropped edge
still leaving `≥ 3`) or `G.degree u₀ ≤ 2` (so neither side is, `G.PencilHub u₀` already failing).
This is the sub-case-3 producer's key structural fact: at `deg = 3` exactly, the dropped edge can
flip hub status (`H`-degree `2 < 3`) while `G`-degree stays `≥ 3` — the arm's residual sub-case
(L5-cut-v). -/
theorem _root_.Graph.pencilHub_iff_induce_of_degree_ne [Finite β] {G : Graph α β} [G.Loopless]
    {V₁ : Set α} {e₀ : β} {u₀ w₀ : α} (hl₀ : G.IsLink e₀ u₀ w₀) (hu₀ : u₀ ∈ V₁) (hw₀ : w₀ ∉ V₁)
    (hcut : (G.cutEdges V₁).ncard ≤ 1) (hdeg3 : G.degree u₀ ≠ 3) :
    G.PencilHub u₀ ↔ (G.induce V₁).PencilHub u₀ := by
  have hsucc := Graph.degree_eq_degree_induce_succ hl₀ hu₀ hw₀ hcut
  constructor
  · intro h
    exact ⟨hu₀, by have := h.2; omega⟩
  · intro h
    exact ⟨hl₀.left_mem, by have := h.2; omega⟩

end CombinatorialRigidity.Molecular
