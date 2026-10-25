# Phase 41 — RECONCILE-FORMAL: design (cross-phase plan and recon)

**Status:** opened 2026-10-24 with the PI. Sub-phase **41a** (CARRIER) is open, work log
`notes/Phase41a.md`; RESTATE, MULTIGRAPH and UNSTATED are tracked by code (§3) and get letters when
they open. The build-time detour the PI scheduled before 41a's spike is done (items P1–P5), and so
are the spike and the switch (item 5a). Next concrete task: 41a's item 5b, the footprint's
docstrings (`notes/Phase41a.md`).

The phase is the last part of the RECONCILE program (`notes/Reconcile.md`, with its standing rules
in §2 and the plan of this phase in §3 *The phase*). Its input is PROSE's findings report
`notes/Prose-report.md`, and every finding's home stays the ledger `notes/Prose-findings.md`. This
file is the single entry point for the phase: the PI's decisions at the open (§1), the open's recon
(§2), the sub-phases (§3) and the open questions (§4).

## 0. Target

- **S2** (`F-122`, `F-125`, `F-128`): `PanelHingeFramework` records for each edge label a pair of
  bodies, `ends`, which nothing ties to the edge's ends. So KT Theorem 5.6's main result
  (`rankHypothesis_of_theorem_55_gen`) is met at deficiency zero by the framework whose normals are
  all zero. The fix is a field of the structure.
- **S1** (`F-207`; the pins of `F-206`, `F-216`, `F-221`): the generic panel and body-hinge
  theorems of `GenericLift/` take `hends` (every label is an edge of `G`) and `hfresh` (every
  minimal `k'`-dof-graph misses a label), which contradict each other at every minimal
  `k`-dof-graph. So the theorems are vacuous there.
- Within the same sub-phases: S13, S18, G6 (the generic panel theorem's own row),
  `cor:theorem-55-d3-spanning`, the footprint's docstrings that round 3 moved here, and `F-323` and
  `F-324`. Then M1 (the multigraph generic body-hinge theorem, JJ 2010 Theorem 6.1) and the claims
  no declaration states (S22–S25, S31, S3, S16, S19, G5, `F-061`'s forest lemma).

## 1. The PI's decisions at the open (2026-10-24)

The PI read the recon's verdict (§2) and its six questions. The PI's answer, verbatim:

> 1. Agreed. A it is
> 2. Sounds good
> 3. What KT states is a minimum here; if we can get something stronger, we should consider it too
> 4. Agreed
> 5. Agreed
> 6. OK.

What each answer settles:

1. **Design A.** The field `isLink_ends` goes on the one carrier `PanelHingeFramework`, so a
   framework whose selector misses an edge's ends cannot be built. Rejected: design C, a field-free
   carrier for the internal machinery with the condition only on predicates and statements.
2. **`molecular_conjecture`'s `2 ≤ |V(G)|` relaxes to `V(G).Nonempty`**, since with nondegeneracy
   asked only on `E(G)` the bound is no longer forced (its docstring). The multigraph rows
   (`molecular_conjecture_multigraph`, `theorem_55_6_multigraph_gen`) also ask nondegeneracy only
   on `E(G)`.
3. **KT's conclusion is the floor, and stronger forms are considered.** Checked against KT 2011
   (`.refs/`): a hinge is by definition a `(d − 2)`-dimensional affine subspace (KT §1), so every
   hinge of a KT panel-hinge framework is nondegenerate; Theorem 5.5 gives a realization that is
   *nonparallel* when `G` is simple, i.e. the panels of any two distinct bodies are not parallel
   (KT §5.1), which is `IsGeneralPosition`; Theorem 5.6 states only the rank. So the floor is
   nondegenerate hinges on `E(G)` in Theorem 5.6's restated conclusion, and general position for
   simple `G` in Theorem 5.5's (which `theorem_55_minimalKDof_gen` already gives, through
   `HasGenericFullRankRealization`). The stronger candidates, for RESTATE's open to settle: general
   position in Theorem 5.6's conclusion for every `G`, and the generic form, every generic
   realization attaining the rank (G6's row).
4. **`IsHingeCoplanar` constrains only the hinges on `E(G)`**, not those at unused labels.
5. **`F-323` and `F-324` are in**: the three main results' unused `[DecidableEq β]` and
   `theorem_55_minimalKDof_gen`'s derivable `hD` are dropped with RESTATE's restatements, with the
   binders round 3 kept for them.
6. **Four sub-phases** (§3), the plan's (a) split into CARRIER and RESTATE. Letters are minted as
   each opens; only 41a now.

## 2. The open's recon (2026-10-24; Claude Opus 5.5, read-only, at `95e2f418`)

**Evidence**, committed in `notes/reconcile-formal/`:
- `S2Witness.lean`, a Lean witness outside the library (`lake env lean
  notes/reconcile-formal/S2Witness.lean`; no errors, three standard axioms). It models the field
  on a mirror structure `LinkedPHF`.
- `carrier_inventory.py`, the reference count from the built `.ilean` files (`python3
  notes/reconcile-formal/carrier_inventory.py`): **32 modules, 167 declarations, 648 references**
  (`ofNormals` 601, `withNormal` 14, `reaimSubLink` 9, `reaim` 6, `withGraph` 5, `reaimSub` 5,
  `ofParam` 4, `withMomentNormals` 4). Only 9 direct structure literals exist: five constructor
  bodies in `PanelHinge.lean`, the three `reaim*` and the single-body framework at
  `Theorem55.lean:2566`.

**Corrections to the plan's premises.** Round 1's "~70 sites in 21 files" and round 3's "257
declarations in 33 files" are not reproducible; the count above replaces them.
`BodyHingeFramework.withGraph` cannot break link-recording, since that structure has no selector.
`rankHypothesis_of_theorem_55_gen` already takes `hcard` (`Theorem55.lean:2542`); S1's change
from `hfresh` to `hcard` is the `GenericLift/` theorems'.

**The field.** `isLink_ends : ∀ e ∈ E(graph), graph.IsLink e (ends e).1 (ends e).2`. It is
equivalent, by one line each way, to the edge-restricted `hends` and to the "up to swap" conjunct
of `HasGenericFullRankRealization` (`PanelHinge.lean:680`). Rejected: the total form `∀ e, …`
(it forces `E(G)` to be the whole label type, S1's vacuity in the carrier), and deriving `ends`
from `G.endsOf` (every computation that fixes an orientation would need sign bookkeeping:
`panelRow`, `normalRow`, the genericity device's `annihRowPoly`, Case III's relabelled selectors).

**The field alone does not close S2** (`zeroPHF_rankHypothesis_zero`): the zero-normal framework
with `ends := G.endsOf` meets the field and is rigid on any preconnected spanning graph, hence
meets `RankHypothesis 0`. Adding `∀ e ∈ E(G), Q.toBodyHinge.supportExtensor e ≠ 0` to the
conclusion excludes it (`zeroPHF_not_nondegenerate`). `molecular_conjecture` already asks for
nondegenerate hinges, so for it the field alone closes S2.

**Proposed restatements** (RESTATE settles them, with §1.3's stronger forms):
- `rankHypothesis_of_theorem_55_gen`, without `[DecidableEq β]`: `∃ Q, Q.graph = G ∧ (∀ e ∈ E(G),
  Q.toBodyHinge.supportExtensor e ≠ 0) ∧ Q.toBodyHinge.RankHypothesis (G.deficiency n)`. The
  single-body branch holds trivially (no edges).
- `molecular_conjecture`: the same iff with `∀ e ∈ E(G), … ≠ 0` on both sides; the
  `(⇒)` direction already uses nondegeneracy only at links
  (`screwDim_add_deficiency_le_finrank_infinitesimalMotions`, `PanelLayer.lean:1580`).
- The panel generic theorem (G6's row): `(∀ Q, Q.graph = G → Q.IsGenericNormals →
  Q.toBodyHinge.IsInfinitesimallyRigidOn V(G)) ↔ G.deficiency n = 0` under `hd`, `hcard`, `hV`,
  `hspan`, `hSimple`; no `ends`, no `hends`. The rank formula likewise.
- The body-hinge theorem (`HingeGeneric.lean:1005`): `hcard` for `hfresh`; no `ends`, `hends` or
  `hD`; genericity `IsGenericHingePoints G q` over rows indexed by `E(G)`.

**Construction sites by class** (measured by a regex scan plus a hand review of R and X; the
classifier was not retained; CARRIER's spike superseded it, `notes/Phase41a.md` item 4): **T**
trivial, 29 declarations (`G.endsOf`, the framework's own `Q.ends`,
`withNormal`/`withMomentNormals`); **P** provable from a
hypothesis in scope, 75; **H** needs a new hypothesis, at most 56 (graph-generic lemmas, e.g.
`ofNormals_supportExtensor_eq_panel_of_ends`, `exists_generalPosition_polynomial`, five in
`Duality.lean`; an upper bound, since the scan misses some shapes); **R** internal statement too
weak, 4 (`CaseIII/Realization.lean` :823, :1330, :1430 pinned to
`lem:case-III-chain-discriminator`, :1943: the link conjunct names `G − v` while the framework is
on the splitting-off, whose links `Q.ends` already records, :900–911; :1751, first counted here, is
not one, as its selector hypothesis `hrecGab` is already on the splitting-off, a correction made at
41a's item 3); **X** broken by
design, 2 (`reaimSub` and its motion lemma). By area: `PanelHinge` 40 references; the genericity
device, coupling, Case I and II 145; `CaseIII/` 225; `Theorem55` 78; `GenericLift/PanelGeneric` 15
(`HingeGeneric` builds none); `Molecule/` top level 22; `Pencil/MainComponent/` 123.

**Friction, witnessed.** With the link proof as a last argument of `ofNormals` filled in by a small
tactic (`link_tac` in the witness), the common sites need no edit: `G.endsOf`, an edge-restricted
`hends`, `Q.ends`, a subgraph (through `recordsLinks_mono`) and structure eta. `rw [hG]` on the
graph argument fails ("motive is not type correct"); `subst` and `simp only` work, and about 71
`rw [h…]` lines on graph arguments sit in the footprint. `ofNormals_ends` and
`toBodyHinge_supportExtensor` stay `rfl`. Four scattered link lemmas can become one predicate with
its graph-operation lemmas: `Graph.isLink_update_splitOff` (`Short.lean:341`),
`Graph.isLink_ends_induce` (`Cut.lean:172`), `recordsLinks_map_of_records` (`CaseI.lean:52`) and
`recordsLinks_swap_endsOf` (`Coupling.lean:66`).

**`reaimSub`, `reaim`, `withGraph`.** `reaimSub` (`Theorem55.lean:846`) gives the edges of
`E(G) ∖ E(G')` the pair `(x₀, y₀)`; its only callers are its motion lemma (:860) and
`rankHypothesis_genuine_of_theorem_55_gen` (:2179), whose hypotheses are those of the
link-recording form (:2272, through `reaimSubLink`). So the first form follows from the second and
`reaimSub` goes. `reaim` (:816) meets the field; it exists only because `rigidityMatrix_prop11`'s
`hC` (`PanelHinge.lean:768`) is asked at every label while its proof needs links, so it goes when
`hC` moves to links. `PanelHingeFramework.withGraph` (:385) has no caller outside its own lemmas;
it becomes `P.withGraph G' (hle : G' ≤ P.graph)`, which keeps the field (`isLink_ends_of_le`).

**S1 after S2.** The field is `hends` restricted to `E(G)`, so the panel theorems need neither
`ends` nor `hends`, and S1 reduces to `hfresh` → `hcard`, genericity over rows indexed by `E(G)`, and
`IsGenericHingePoints` oriented by the links. The families stay indexed by the label type, with
conditions only on `E(G)` (the body-bar precedent, `BodyBar/GenericLift.lean:190–213`); a subtype
index would need transport for `ofHinge`, `MvPolynomial (β × …)`, `induce` and `mulTilde`. The
extraction lemma (`GenericityDevice.lean:491–498`) already returns linking indices with
nondegeneracy only at links. Folded in: S13 (genericity reads only the `E(G)` coordinates), S18
(`prop:rigidity-matrix-prop11` restated conditionally, `hC` on links) and
`cor:theorem-55-d3-spanning` (derived from `theorem_55_d3` under `hcard`, with general position
and nondegenerate hinges on `E(G)`, `_hSimple` dropped, `F-126`).

**`BodyHingeFramework`** needs no structural change: it has no selector and its rows read `IsLink`
(`RigidityMatrix/Basic.lean:243`). M1 can reuse `theorem_55_6_multigraph` (`Theorem55.lean:2903`),
whose nonzero hinges are each spanned by points in the panels, so the witness transplant of
`HingeGeneric.lean:751` carries over.

**`F-323` and `F-324`.** `F-323` costs no commit for the two S2 main results (drop the binder, add
`classical`; precedent `rankHypothesis_of_theorem_55_d3`, :2619), and one small commit for the two
multigraph rows unless they are restated anyway (§1.2 restates them). `F-324` is about one commit:
`theorem_55_minimalKDof_gen` (:2107), the `hD` chain below it (`F-293`, `F-297`, `F-298`, about
ten signatures) and seven call sites; the spanning-trees theorem's `hD` goes with S1.

## 3. Sub-phases, by code

| Code | Letter | Contents | Commits |
|---|---|---|---|
| **CARRIER** | 41a (open) | retire `reaimSub`; the link predicate, its lemmas and the fill-in tactic; the four R statements; a throwaway spike to list what the switch breaks; the switch (the field, the constructors, the H binders, the graph rewrites, the footprint's docstrings file by file, `def:panel-hinge-framework` restated); `withGraph` restricted; `reaim` deleted with `hC` on links; the two genuine forms merged | 9 besides the build-time detour: the switch is one commit and a docstring commit (the spike) |
| **RESTATE** | — | S2's main results and nodes (with `F-323`, §1.2–1.4); `cor:theorem-55-d3-spanning`; S1's panel and body-hinge theorems (with S13 and `F-324`); G6's row; round 1's scope sentences removed (`formalization.yaml`, README, home page, `intro.tex`, ROADMAP); non-vacuity witnesses at minimal graphs for these rows; S18; the remaining footprint docstrings | 9–13 |
| **MULTIGRAPH** | — | M1: the multigraph generic body-hinge theorem (JJ 2010 Theorem 6.1) | 3–5 |
| **UNSTATED** | — | the claims no declaration states, the report's estimates: S22 1–2, S23 1, S24 2–3, S25 1, S31 2–3, S3 0–2, S16 1, S19 0–3, G5 3–5, `F-061` 1–2; after CARRIER, since S3 and S19 touch carrier code (`case_II_placement_eq612`) | 13–23 |

**Why the switch is one commit**: under the lint gate a field cannot be staged file by file without
a temporary twin structure (an unused proof argument fails `unusedArguments`). This is Phase 22l's
lesson: the API first, the switch last (`notes/Phase22l.md` *Architectural choices*). The spike
confirmed it: 65 declarations take a record binder, unused without the field, and the whole Lean
side is one patch, build-green and lint-clean.

The program closes with the phase: ROADMAP's RECONCILE bullet compressed, and the ledger's last
`reported` entries given dispositions (`notes/Reconcile.md` §3).

## 4. Open questions

- **The switch's size**, resolved by CARRIER's spike (2026-10-24): 123 declarations in 27 of the 32
  carrier files, +418/−139 lines, with H at 65 (the scan's bound of 56 was low;
  `Graph.exists_earBase_splitOff` needs no edit once `link_tac` tries `update_splitOff`). One commit
  for the Lean side and one for the docstrings (`notes/Phase41a.md` items 4 and 5).
- **M1 and loops**: assume `G.Loopless`, or relax the upper bound's `hC` to non-loop links (a loop's
  constraint is vacuous, and a loop never crosses a partition). MULTIGRAPH's open decides. JJ 2010
  Theorem 6.1 (EJC 31, p. 582) is a maximum-rank statement for 2-edge-coloured multigraphs; the
  row's "every generic realization" is the project's strengthening.
- **The stronger forms of §1.3**: general position in Theorem 5.6's conclusion for every `G`, and
  the generic form; RESTATE's open decides, each with a witness that it holds.
