/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
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

end CombinatorialRigidity.Molecular
