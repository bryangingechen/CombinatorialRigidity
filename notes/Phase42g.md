# Phase 42g — PD-STEPS: cycles and long open ears in every dimension (work log)

**Status:** in progress, opened 2026-10-30 at the PI's word ("-long first (Recommended)", design
doc §1), a sub-phase of Phase 42 and the second of PD-STEPS. Forward mode, the Lean under
`/coordinate-phase`: the seven red nodes of `blueprint/src/chapter/pencil-d.tex` in
`sec:pencil-d-long` (Phase 40's cycle and long-ear steps in `Pᵈ`, on CERT's closed polygons with
independent joins), on the `Pencil/Grade/` carrier. The pre-build recon pinned all seven Lean
statements and spiked each complete, with no `sorry`, for two new files (*Lemma checklist*); no
statement changes. **Both builds have landed: `Pencil/Grade/Polygon.lean` (the five polygon nodes) and
`Pencil/Grade/Chain.lean` (the cycle and the long ear), so all seven nodes are green.** At the PI's
word the chapter's star and insertion proofs follow their Lean, and a cleanup after Phase 42 tracks
the other route differences (`notes/Cleanup42.md`, R-3 to R-6). Next (*Hand-off*): the 42g close, an
intermediate sub-phase close (`PHASE-BOUNDARIES.md`).

## Current state

**Landed: `Pencil/Grade/Polygon.lean`** (the five polygon nodes, with the five `Fin` index lemmas
in the mirror `Mathlib/Data/Fin/Basic.lean`) **and `Pencil/Grade/Chain.lean`** (`thm:pencil-d-cycle`
as `Graph.X0AttainsGrade.of_cycle` and `thm:pencil-d-open-ear-long` as
`Graph.X0AttainsGrade.of_openEar`, each pinned with `\lean` and `\leanok` on statement and proof;
the certificate lemmas `…of_cycle_of_certificate` and `…of_openEar_of_cert` and the helpers
`card_le_finrank_of_linearIndependent_normalsJoin`, `three_le_screwDim_succ` and
`pencilConfigPointGrade_ofPoints` live there too), transcribed from the recon's spike with full
docstrings and no proof change. Both modules are in the root `CombinatorialRigidity.lean` and
build warning-clean. PD-STATE's hinge-form deferral is discharged (design doc §3). The ledger
(`notes/Cleanup42.md`): R-5 rechecked against the landed cycle (it matches the spike), and R-6
added (the cycle's heights are restricted to `V(G)`). The long ear's landed proof follows the
chapter's. **Next: the 42g close** (*Hand-off*). The chapter is the lemma index (forward mode);
`-short` (12 nodes) stays mapped by section in design doc §3, with no letter minted.

## Architectural choices made up front

- **Scope** (the PI's, verbatim in design doc §1): the seven nodes above.
- **Encoding** as 42b–42f: `m = d − 2` heights at grade `k = m + 1`, `D = screwDim (m + 1)`
  (`= Graph.bodyBarDim (m + 2)`), `def_d` is `G.deficiency (m + 2)`. Attaining is
  `Graph.X0AttainsGrade K m`, its witness lemma `Graph.x0AttainsGrade_of_exists`. The point
  `pencilConfigPointGrade q z w` is `(x_w, y_w, z_w, 1)`, so a vector with last coordinate `1` is a
  configuration point (`gradeMk_eta`), and the chapter's `P_0`, `P_1`, `P_2` are the points with
  pictures `(0, 0)`, `(1, 0)`, `(0, 1)` and zero heights. As in 42e and 42f, the Lean may hold at
  every `m` while the nodes keep `d ≥ 3`.

## Lemma checklist

Shorthand, exact by substitution. Every declaration is in
`namespace CombinatorialRigidity.Molecular`, with
`variable {K : Type*} [Field K] {α β : Type*} {k m : ℕ}`, under `@[expose] public section`;
`Graph.` names are `_root_.Graph.…`. A closed `n`-gon is `Y : Fin n → Fin (k + 2) → K` with
`[NeZero n]`, indices cyclic in `Fin n`; `J(Y)` is `fun j => normalsJoin (Y j) (Y (j + 1))` and
`W(Y)` is `Submodule.span K (Set.range J(Y))`. `V` is `Fin (m + 1 + 2) → K`, `last` is
`Fin.last (m + 2)`, `P₀`, `P₁`, `P₂` are `gradeMk 0 0 0 1`, `gradeMk 1 0 0 1`, `gradeMk 0 1 0 1`,
and `D` is `screwDim (m + 1)`. `hpath`, `hsep`, `honly` are as in `MainComponent/Chain.lean`.

- [x] **Pre-build recon** (this commit): the signatures below, every spike complete.
- [x] `lem:pencil-d-polygon-normal`, in the new `Pencil/Grade/Polygon.lean` (imports
  `Grade.Embedding`, `Grade.Carrier`). Pin `linearIndependent_polygon_vertices` (part (1):
  `(hn : 3 ≤ n) {Y : Fin n → Fin (k + 2) → K} (hY : LinearIndependent K J(Y)) (i : Fin n) :
  LinearIndependent K ![Y (i - 1), Y i, Y (i + 1)]`) and `exists_linearEquiv_polygon_normal`
  (part (2): `(hn : 3 ≤ n) {Y : Fin n → V} (hY1 : ∀ j, Y j last = 1) (hY) (i) : ∃ g : V ≃ₗ[K] V,
  (∀ v, g v last = v last) ∧ g (Y (i - 1)) = P₁ ∧ g (Y i) = P₀ ∧ g (Y (i + 1)) = P₂ ∧
  LinearIndependent K (fun j => normalsJoin (g (Y j)) (g (Y (j + 1)))) ∧ ∀ j, g (Y j) last = 1`).
  Route: (1) as the chapter, with `normalsJoin_ne_zero_iff` and `LinearIndependent.pair_iff`;
  (2) `Submodule.exists_linearEquiv_restrict_eq` on the span of the three vertices
  (`Module.Basis.span` of (1) and of `P₁, P₀, P₂`), then the transvection `v ↦ v + φ v • P₀`,
  `φ = f ∘ g₁⁻¹ − f` for `f` the last coordinate, and `exteriorPower_map_normalsJoin`.
- [x] `lem:pencil-d-polygon-star`, in `Grade/Polygon.lean`. Pin
  `exists_normalsJoin_notMem_span_polygon` (`{Y : Fin n → Fin (k + 2) → K} (hY) (hnD : n <
  screwDim k) : ∃ i u, normalsJoin (Y i) u ∉ W(Y)`). Route: the chapter's split. If the vertices
  span, every join lies in `W(Y)` by linearity in the first point (`Submodule.span_induction`)
  and the joins span `⋀²` (`exteriorPower.ιMulti_span`), against `dim W(Y) = n < D`; else the
  2 × 2-minor functional `ψ₁(a)ψ₂(b) − ψ₂(a)ψ₁(b)` (`exists_linearMap_normalsJoin_eq`), `ψ₂`
  vanishing on the span (`Submodule.exists_dual_map_eq_bot_of_notMem`), kills `W(Y)` but not
  `Y 0 ∨ u`.
- [x] `lem:pencil-d-polygon-insert`, in `Grade/Polygon.lean`. Pin
  `exists_insertNth_linearIndependent_join` (`(hK : 4 ≤ ENat.card K) {Y : Fin n → Fin (k + 2) → K}
  (hY1 : ∀ j, Y j (Fin.last (k + 1)) = 1) (hY) {i u} (hu : normalsJoin (Y i) u ∉ W(Y)) : ∃ y,
  y (Fin.last (k + 1)) = 1 ∧ LinearIndependent K J(Z)`, `Z` the `(n + 1)`-gon
  `(Fin.insertNth i.succ y Y : Fin (n + 1) → Fin (k + 2) → K)`). Route: the chapter's `y(t)` and
  three exclusions (`Finset.exists_notMem_of_card_lt_enatCard`); "at most one root" as
  `eq_of_add_smul_mem_of_add_smul_mem` (`J_i + t w` meets `A = span(J_j, j ≠ i; Y_i ∨ u)` for at
  most one `t`), and independence by `linearIndependent_iff_card_le_finrank_span`.
- [x] `lem:pencil-d-polygons`, in `Grade/Polygon.lean`. Pin `exists_polygon_linearIndependent_join`
  (`(hK : 4 ≤ ENat.card K) (hn : 3 ≤ n) (hnD : n ≤ D) : ∃ Y : Fin n → V, (∀ j, Y j last = 1) ∧
  LinearIndependent K J(Y) ∧ Y (-1) = P₁ ∧ Y 0 = P₀ ∧ Y 1 = P₂`). Route: induction on `Fin (n + 3)`
  (`exists_polygon_linearIndependent_join_aux`), base `![P₀, P₁, P₂]` by three minor functionals
  (`linearIndependent_join_triangle`), step the star and the insertion; then part (2) at `i = 0`.
- [x] `lem:pencil-d-polygon-collapse`, in `Grade/Polygon.lean`, index-level (no `Y`). Pin the defs
  `polygonCollapse N M : Fin M → Fin N` (`π_M`: `j ↦ N − 1` if `j + 1 = M`, else `min j (N − 2)`)
  and `polygonCollapseEdge N M : Fin N → Fin M` (`l ↦ l` if `l + 2 < N`, else `l + (M − N)`), and
  `polygonCollapseEdge_injective (hNM : N ≤ M)` and `polygonCollapse_polygonCollapseEdge (hN : 2 ≤
  N) (hNM : N ≤ M) l : π (ι l) = l ∧ π (ι l + 1) = l + 1` (part (1): distinct edges carrying
  `J_0, …, J_{N−1}`), with `polygonCollapse_zero`, `polygonCollapse_one`,
  `polygonCollapse_neg_one` (part (2)'s positions at `M = k + 1`; `b` at `π 0` is the consumer's).
- [x] `thm:pencil-d-cycle`, in `Pencil/Grade/Chain.lean`: `Graph.X0AttainsGrade.of_cycle`, on a
  closed `N`-gon, `N = min (k + 2) D`, through `…of_cycle_of_certificate` (R-5, R-6).
- [x] `thm:pencil-d-open-ear-long`, in `Grade/Chain.lean`: `Graph.X0AttainsGrade.of_openEar`, on the
  normalized `D`-gon, through `…of_openEar_of_cert`.
- [ ] **Close** 42g, an intermediate sub-phase close (`PHASE-BOUNDARIES.md`).

Helpers (no node): in `Grade/Polygon.lean`, `normalsJoin_add_right`, `normalsJoin_smul_right`,
`normalsJoin_zero_left`, `exists_linearMap_normalsJoin_eq`, `finrank_exteriorPower_two_eq_screwDim`,
`linearIndependent_gradeMk_P` (name it at the build), `eq_of_add_smul_mem_of_add_smul_mem`,
`val_polygonCollapse`, `val_polygonCollapseEdge`, `val_neg_one_fin`, and five `Fin` index lemmas
(`Fin.val_add_one'`, `Fin.val_succ_succAbove`, `Fin.succ_succAbove_add_one`,
`Fin.succ_add_one_eq_succAbove`, `Fin.succ_succAbove_self`), upstream-eligible, so a new mirror
`CombinatorialRigidity/Mathlib/Data/Fin/Basic.lean`; in `Grade/Chain.lean`, the hinge form
`card_le_finrank_of_linearIndependent_normalsJoin` (every `k`), `three_le_screwDim_succ` and
`pencilConfigPointGrade_ofPoints`.

## Blockers / open questions

- None blocking. The open's questions, resolved by the recon:
  1. **The polygon carrier**: `Fin n → Fin (k + 2) → K` with `[NeZero n]` and `j + 1` in `Fin n`;
     joins as `normalsJoin`, "independent joins" as `LinearIndependent`; the inserted polygon is
     `Fin.insertNth i.succ y Y`. No definition. **No basis of `⋀²`** is needed: the star and the
     base case use `exteriorPower.ιMulti_span` and 2 × 2-minor functionals
     (`exteriorPower.alternatingMapLinearEquiv`), the count `exteriorPower.finrank_eq`.
  2. **No statement changes; the proof routes are ledger rows**: `notes/Cleanup42.md` §2, R-1 to
     R-5 (the star and the insertion aligned; part (2) of `-normal`, the base triangle and the
     cycle's placement open). The Chain build adds a row, or updates R-5, wherever its Lean departs
     from the chapter's proof (design doc §3, the standing rule).
  3. **The insertion keeps `|K| ≥ 4`**, as `4 ≤ ENat.card K` (the node's hypothesis exactly); the
     cycle and the ear derive it from `[Infinite K]` (`ENat.card_eq_top_of_infinite`).
     `-short`'s twin `lem:pencil-d-insertion` (a dimension gain at `[Infinite K]`) is a different
     statement: it shares `eq_of_add_smul_mem_of_add_smul_mem` and the `normalsJoin` algebra, not
     a lemma, so a `d`-general `exists_insertion_gain` serves `-short` only.
  4. **The hinge form** is `card_le_finrank_of_linearIndependent_normalsJoin`, every `k`, in the
     new `Grade/Chain.lean` (`span_supportExtensor_ofNormals_eq`, `complementIso` injective): no
     `P³` file edited or importing `Grade/`, so PD-STATE's hinge-form deferral (design doc §3) is
     discharged by the second build, not triggered.
  5. **The placement** is any `pt : α → V` with last coordinate `1`
     (`pencilConfigPointGrade_ofPoints`): the cycle restricts its heights to `V(G)` inside the
     certificate lemma; the ear puts every body off `range x` at `P₀`, so its heights vanish off
     `V(G)` as `Graph.liftingSpace` asks.
  6. **No deferral is triggered**: both builds are new files (plus the root import list and the
     `Fin` mirror). The `normalsJoin` lemmas stay out of `PanelLayer.lean` (42c's deferral) and
     `pencilConfigPointGrade_ofPoints` out of `Grade/Carrier.lean` (42e's fold), each a FRICTION
     home-debt line at the build; 42f's fold names `MainComponent/ContractAdditive.lean`, untouched.

## Hand-off / next phase

The next concrete commit is the **42g close**, an intermediate sub-phase close
(`PHASE-BOUNDARIES.md` *When this commit closes a phase*): flip and re-thin the ROADMAP row,
compress the planning section and this note to its archive form, sync the user-facing status
surfaces, re-read the chapter's `sec:pencil-d-long` end to end, and write the exposition-ledger
entry. Carry into it the FRICTION home-debt line for `pencilConfigPointGrade_ofPoints` (out of
`Grade/Carrier.lean`, 42e's fold; not yet filed) and the open ledger rows R-3 to R-6 of
`notes/Cleanup42.md`, which belong to the post-Phase-42 cleanup. The next sub-phase, `-short`, opens
at the PI's word.

## Decisions made during this phase

- **The open** (the PI, 2026-10-30; verbatim in design doc §1): 42g opens as PD-STEPS's `-long`,
  seven nodes; `-short` stays mapped by section, no letter minted.
- **The open's consistency read:** all seven proofs route through the argument their statements
  claim, on the `Grade/` carrier; the sections share no node, the coordinator's hypothesis now
  checked; no chapter edit.
- **The star and the insertion follow the Lean** (the PI, 2026-10-30; verbatim in design doc §1 and
  `notes/Cleanup42.md` §1): their chapter proofs were rewritten to the Lean's routes, statements
  unchanged; the star's proof `\uses` `def:extensor`, not `lem:pencil-d-polygon-normal`. The other
  three route differences stay as written for the post-Phase-42 cleanup, in that note's ledger,
  which every later recon or build extends (design doc §3).
- **The builds** (`Grade/Polygon.lean`, `Grade/Chain.lean`): the spikes transcribed, no proof
  changed, no statement changed. The five `Fin` lemmas are in the mirror `Mathlib/Data/Fin/Basic.lean`;
  the `normalsJoin` lemmas stay in `Polygon.lean` (42c's deferral; FRICTION). The cycle's and ear's
  certificate lemmas are pinned beside their nodes. The cycle's placement is R-5 and its restricted
  heights R-6 in `notes/Cleanup42.md`.
- **The pre-build recon** (spikes in `scratch/42g/`): two new files, no landed file edited, no
  deferral triggered; no polygon definition and no basis of `⋀²`; `|K| ≥ 4` kept as
  `4 ≤ ENat.card K`; the collapse index-level.
