# Phase 39 — PENCIL: the hinge-pencil molecular conjecture (work log)

**Status:** in progress — W0–W2 complete, the W3–W5 route recon accepted, W3-L0 +
W3-L1 + W3-L2 + W3-L2a + W3-L3 + **W3-L4 (cut arm complete)** + W3-L5 (base arm
complete) + W3-L6a landed (all 2026-07-24); phase stays open, only W3-L7 (the
provisional wrapper) remains to close W3's shell (opened 2026-07-23, recon-first).

## Current state

**The phase stays OPEN — do NOT run the close checklist.** Two 2026-07-24 user
adjudications (verbatim, later supersedes earlier) revised the same-day "wrap up"
one: *"Let's leave the phase open and continue the work on the conjecture in this
phase. Unless there's a good reason to split here."* (coordinator assessed: no
reason to split — the phase's charter is the conjecture itself), then *"Let's end
the loop after this dispatch returns and you've confirmed its results; we'll begin
the research on the conjecture in a fresh session."* So: **W0, W1, and W2 are all
complete** (W2 = existence + necessity + the design-doc iff), no phase-close.

**The W3–W5 route recon landed 2026-07-24** (`notes/Phase39-design.md`
§W3–W5 route recon — the canonical record). Verdicts: **attack order W3 → W5 →
W4**; W3's candidate route (a) (pencil-compatible strip) **refuted** (no such
strip exists on K4, and the cross-incidence repair provably caps the stripped
4-cycle at rank 17 < 18 — re-added edges must contribute rank, so no
strip-extend route is sound); route **(b′) adopted** — the induction restated on
ALL spanning multigraphs, dispatch made total without minimality by a new
min-degree-3 ⟹ proper-rigid-subgraph lemma (via the landed
`circuit_induces_isRigidSubgraph`); W3 decomposed into leaves L0–L7 with
typechecked signatures (in the design doc; skeleton `Graph.pencil_reduction`,
motive `HasPencilRealization`, arms as hypotheses). New numerics: **N2** confirms
W5's genericity route (on the exact Case-III habitat the obstruction vector `r`
misses the 1-dim escape line in 5/5 exact samples — all three KT candidates work
individually; target = single-candidate `r ⬝ Λ²Π̂(a) ≠ 0` pencil-generically);
**N3** confirms W4's constrained-family (Claim-6.4 specialization) route's
G′-block witness (constrained C4 at 18/18), while the keep-hinges
coincidence-cluster route is refuted deterministically. **The coordinator accepted
these verdicts 2026-07-24** (same-session adjudication) — builds on the W3 core
are sanctioned; W3-L1 landed the same session (below).

**Earlier W3 leaves landed 2026-07-24** (settled; gates green; detail in git + design doc):
- **W3-L0** `HasPencilRealization` (`Molecule/Pencil.lean`, node `def:pencil-rank-hypothesis`): the
  `V(G)`-relative motive — grade-2 `HasPencilPanelRealization` whose rigidity-row span attains
  `screwDim 2·(|V|−1) − def(G̃)`. This is the `P` the cut arm produces (assembly's target shape).
- **W3-L3** `hasPencilRealization_of_isLoopAt` (node `lem:pencil-loop-case`) + loop-deletion
  deficiency `deficiency_deleteEdges_singleton_eq_of_isLoopAt` (`Deficiency.lean`): the loop arm,
  via the elementary rigidityRows-span route (a loop's row is `0` by `hingeRow_self`).
- **W3-L6a** `Graph.rigidContract_deficiency_eq` (`Induction/Contraction.lean`, node
  `lem:pencil-contraction-deficiency`): minimality-free contraction-deficiency bookkeeping (contract
  arm dep). [`set_option linter.unusedDecidableInType false` — `[DecidableEq β]` empirically needed.]

**W3-L4 CUT ARM COMPLETE 2026-07-24** (`Molecular/Molecule/Pencil.lean`, node
`lem:pencil-cut-case` green): the assembly `hasPencilRealization_of_not_twoEdgeConnected` — from
pencil realizations of the two induced sides of a cut (`≤ 1` crossing edge), produce
`HasPencilRealization K n G`, minimality-free. Mirrors Theorem55's `case_cut_edge_realization_gen`
but **unfolds `¬TwoEdgeConnected` directly** (that wrapper's opener needs `IsMinimalKDof`) and splits
the deficiency by `deficiency_eq_of_cutEdges_ncard_le_one`. `|C|=0` is a disjoint union (no
transport); `|C|=1` transports the `V₂` side by the repositioning automorphism so the crossing
edge's cross-incidences hold, then takes its hinge from `exists_extensor_two_pencils` (in both
panels, through both points). Its four supporting pieces (all landed the same session):
- *transport* `hasPencilPanelRealization_mapSupport_screwEquivOfLinearEquiv` (node
  `lem:pencil-projective-transport`): a pencil realization transports along `g : K⁴ ≃ₗ K⁴` (points
  by `g`, normals by contragredient `h`, hinges by `screwEquivOfLinearEquiv g`/`mapSupport`); rank
  preserved by `finrank_span_rigidityRows_mapSupport`.
- *nondegeneracy* `exists_reposition_cross_incidences` (node `lem:pencil-cut-nondegeneracy`): the
  `(g, h)` meeting the two cross-incidences exists over any field (explicit frame construction, **no
  `[Infinite K]`**), via `exists_contragredient_linearEquiv` + `exists_perp_linearIndependent`.
- *rank assembly* `finrank_span_rigidityRows_cutEdge_eq` + *side-span* `span_rigidityRows_eq_of_supportExtensor_agree`
  (no blueprint node — technical rank arithmetic): the minimality-free public re-derivations of
  Theorem55's `private` `cutEdge_finrank_assemble` / `span_rigidityRows_side_eq`. Intentional
  duplication (a future cleanup could extract a shared core to `Bricks.lean`).

Two derivation-guard corrections settled during the leaves (design doc §W3, canonical): the landed
`thm:projective-invariance` is ℝ-only/`supportExtensor`-only (so the `K`-level `(normal,point)`
transport was built fresh on `HingeGeneric.lean`); `exists_cut_decomposition_of_not_twoEdgeConnected`
is **not** minimality-free. Gates green (`lake build` warning-clean 2862 jobs; `lake lint`;
`blueprint/verify.sh` + `lint.sh`; `#print axioms` = propext/Classical.choice/Quot.sound on
`hasPencilRealization_of_not_twoEdgeConnected`).

**W3-L5 BASE ARM COMPLETE 2026-07-24** (`Molecular/Molecule/Pencil.lean`, `hasPencilRealization_of_ncard_le_two`,
node `lem:pencil-base-case` green): the last non-wrapper W3 leaf — every loopless multigraph on `≤ 2`
bodies has a pencil realization at the deficiency rank, dispatched on `E(G)` into three shapes (all
sharing one pencil pair `(q₀, Ce, Cf)` from `exists_linearIndependent_extensor_pair_through_point`):
edgeless (`|V|=1` or `|V|=2` with no edges: rank `0` against `def = D(|V|-1)`, the all-`Ce` framework
with no per-link obligation); single edge (rank `D−1 = 5` against `def = 1`, sandwiched between the
landed `D−1`-independent-rows brick `exists_independent_rigidityRows_of_edge` (lower bound) and the B2
deficiency cap `finrank_span_rigidityRows_add_deficiency_le` (upper bound) — no need to redo
Theorem55's `panelRow`/powerset machinery); parallel class of `m ≥ 2` edges, unbounded since no
minimality (rank `D = 6` against `def = 0`, via `theorem_55_base` — which needs only two genuine
parallel hinges `e ≠ f`, not `E(G) = {e,f}` exactly — extended to any further edges by reusing the
second hinge `Cf` for free, mirroring the loop arm's extension pattern). The `def = 0` fact is the
restriction argument `isKDof_zero_of_parallel_pair` on `H := G ↾ {e,f}` transported to `G` by
`deficiency_le_deficiency_of_le_vertexSet_eq`, mirroring the landed
`edgeSet_ncard_le_two_of_isMinimalKDof_of_ncard_two`. Gates green (`lake build` warning-clean 2862
jobs; `lake lint`; `blueprint/verify.sh` + `lint.sh`; `#print axioms` =
propext/Classical.choice/Quot.sound).

**W3-L2a landed 2026-07-24** (`Molecular/Induction/ReducibleVertex.lean`,
`Graph.simple_of_loopless_of_noRigid`, node `lem:pencil-simple-of-noRigid`): the
minimality-free sibling of `simple_of_isMinimalKDof_of_noRigid`, homed right after it
(same file, same ingredients: `isKDof_zero_of_parallel_pair` + the induce/restrict
two-vertex subgraph construction) — a parallel pair on `{x,y} ⊊ V(G)` is a `0`-dof
proper rigid subgraph once `3 ≤ |V(G)|`, so no-proper-rigid-subgraph + looplessness
forces `G.Simple`. Proof is a verbatim mirror of the sibling's `eq_of_isLink` argument
with looplessness supplied directly (`hloop : G.Loopless`) instead of derived from
`IsMinimalKDof` — dropped `[DecidableEq β]` from the signature (genuinely unused here,
unlike the sibling where it's needed to state `IsMinimalKDof`; caught by
`unusedDecidableInType`). Gates green (`lake build` warning-clean, full-project;
`lake lint`; `blueprint/verify.sh` + `lint.sh`).

**W3-L2 landed 2026-07-24** (`Molecular/Induction/ForestSurgery/Reduction.lean`,
`Graph.pencil_reduction`, node `thm:pencil-reduction`): the reduction skeleton itself —
strong induction on the lexicographic measure `(|V(G)|, |E(G)|)`, homed alongside its
sibling skeletons `minimal_kdof_reduction`/`minimal_kdof_reduction_all_k` (same file,
transitively imports `Operations.lean`'s W3-L1). Five arms as hypotheses
(loop/base/cut/contract/split); the split arm's degree-2 witness is the
`exists_isProperRigidSubgraph_of_three_le_degree` contrapositive (no proper rigid
subgraph ⟹ some vertex has degree `< 3`) sharpened to exactly `2` by
`two_le_degree_of_twoEdgeConnected`. Proof shape: nested `Nat.strong_induction_on`
(outer on `|V|`, inner on `|E|` within each fixed `|V|`, since only the loop arm can
hold `|V|` fixed) — implemented via a `suffices` restating the goal over both measure
components, rather than the `induction hN : … generalizing G` idiom the single-measure
sibling skeletons use (that idiom's `generalizing` clause fights the second, dependent
induction). Gates green (`lake build` warning-clean, incl. the same
`unusedDecidableInType` false positive as W3-L1 — `classical` shadows the pinned
`[DecidableEq β]` — and TACTICS-QUIRKS § 51's `set_option … in` before-the-docstring
ordering; `lake lint`; `blueprint/verify.sh` + `lint.sh`).

**W2 COMPLETE** (`Molecular/Molecule/Pencil.lean` + `Meet.lean`): the design-doc
biconditional `exists_extensor_two_pencils_iff` (node `lem:two-pencil-extension-iff`).
Three parts:
- **Existence** (`←`, node `lem:two-pencil-extension`): `exists_extensor_two_pencils`
  — under the own-panel incidences + `pt_u ≠ 0` + the two cross-incidences
  (`pt_u ⬝ᵥ n_v = 0`, `pt_v ⬝ᵥ n_u = 0`), a nonzero `C : ScrewSpace K 2` in both
  panels through both points. Both points in the common perp `n_u^⊥ ∩ n_v^⊥`
  (dim ≥ 2, **no transversality**); hinge = their span (distinct pts) or `span{pt_u, w}`
  (coincident pts). Coincident-panel / zero-`pt_v` degeneracies handled from the bodies.
- **Span-uniqueness** (`Meet.lean`, node-less like its sibling): `span_range_eq_of_extensor_eq`
  — two pairs with equal nonzero `2`-extensor span the same plane (Plücker injectivity,
  the converse of `exists_smul_extensor_eq_of_mem_span_range`), via the grade-3 join
  factorization `extensor ![x,a,b] = extensor ![x] * extensor ![a,b]` + the wedge-kernel
  helper `extensor_triple_eq_zero_iff`.
- **Necessity** (`→`): `dotProduct_eq_zero_of_extensorInPanel_of_extensorThroughPoint`
  — a nonzero `C` in `n`'s panel through `q` forces `q ⬝ᵥ n = 0` (span-uniqueness + the
  landed `dotProduct_eq_zero_of_mem_span`).

Gates green (`lake build` warning-clean + `lake lint`; `blueprint/verify.sh` + `lint.sh`);
`#print axioms` = propext/Classical.choice/Quot.sound on both new headline decls.

**W0 + W1 complete** (detail in *Decisions made*): W0 = statement layer
(`ExtensorThroughPoint`, `HasPencilPanelRealization`) + polarity bridge
(`screwComplementIso_mk_extensor`) + two forward transport implications + stratum
self-duality; five green nodes in the phase-open `blueprint/src/chapter/pencil.tex`.
W1 = coincident-panel pencil pair + two-body parallel-pair realization + degree-2
concurrency-is-automatic + nonvacuity witness + cycle coplanar/pencil wraps (six
nodes, `3 ≤ cy.m ≤ 4`).

The opening recon ran 2026-07-23 (full record + grounding:
`notes/Phase39-design.md`). Verdicts: **R1** — statement pinned
(containment model + per-body homogeneous concurrency point;
typechecked candidate shapes in the design doc), stratum satisfiable,
projectively self-dual on-stratum modulo one new transport lemma.
**R2** — no refutation: exact-rational rank experiments attain the
full target on every graph tested (incl. four deg-3 bodies at the
tight minimal-0-dof count and five deg-4 bodies); negative data is
confined to the deep all-coplanar locus of *sparse* graphs. **R3** —
KT's route does **not** survive verbatim: Lemma 6.2 / Case II survive,
but the outer Theorem-5.6 strip-extend layer, the Case-I connecting
glue, and Claim 6.12's span (6 → 5, a quantified 1-dim shortfall) all
consume freedom the pencil pin removes — three open cores, so the
phase is **not** the queued "warmup".

## The question

KT's theorem (formalized: `molecular_conjecture`, Phases 17–26; the
multigraph/coplanar-model strengthening, Phase 35) says the generic
body-hinge rank in `ℝ³` is already achieved on the *panel* stratum —
each body's hinges coplanar — and, by projective duality (Phase 25),
on the *molecular* stratum — each body's hinges concurrent. PENCIL
asks about the **intersection stratum**: each body's hinges both
concurrent *and* coplanar, i.e. a **pencil** of lines through a point
in a plane. Does a pencil realization generic in that stratum still
achieve the generic body-hinge rank (Tay's tree-packing count;
`5G` ⊇ 6 edge-disjoint spanning trees at `d = 3` via KT Cor. 5.7)?

In the `G²` molecular reading (Phase 25/26 modelling), the hinges at
the body of atom `v` are the bond lines through `p(v)` — concurrency
is automatic — so the pencil condition says **`v`'s bond-star is
coplanar** (its neighbors lie in a plane through `p(v)`). Chemically:
sp²/planar-bonded atoms. So PENCIL reads: *does the molecular count
stay valid for molecules with planar-bonded atoms?* The condition
only bites at bodies of degree ≥ 3 (two coplanar lines are
automatically projectively concurrent).

Trivial direction: pencil ⇒ panel per body, so pencil rank ≤ generic
(KT). The content is the lower bound. The all-bodies statement is the
strongest form: any mixed version (pencil on a subset of bodies,
generic elsewhere) follows by rank lower-semicontinuity, since the
all-pencil stratum sits inside every mixed stratum.

The queue entry hoped for a warmup (no new carrier material); the
opening recon **refuted the warmup premise** — the carrier material is
indeed all in-tree, but three KT proof steps consume panel-only
freedom the pencil pin removes (see *Opening recon verdicts*). As of
2026-07-23 no literature result on this stratum was found (searched;
Jordán 2016 and the KT paper are silent) — **this is new mathematics**.

## Opening recon verdicts (R1–R3, landed 2026-07-23)

Full record, grounding, and the W0–W5 decomposition:
**`notes/Phase39-design.md`**. One-line verdicts:

- **R1** — panel-side statement pinned in the Phase-35 containment
  model + per-body homogeneous concurrency point (`ExtensorThroughPoint`
  dual of `ExtensorInPanel`; typechecked shapes in the design doc);
  satisfiable for every graph; self-dual on-stratum via the landed
  `screwComplementIso` modulo one new transport lemma. Surprise: for
  dense graphs (K4, K3,3, theta(2,2,2)) the stratum *collapses* to the
  all-coplanar locus.
- **R2** — conjecture survives all exact-rational rank tests
  (pencil-generic = full target rank everywhere tested, incl. the
  collapsed dense strata); the deep all-coplanar locus is deficient
  exactly when `2|E| < 3|V| − 3` (deficit = the spline count) — the
  queued "all-coplanar is rank-deficient" claim is a *bar-joint-side*
  fact, false for body-hinge on dense graphs.
- **R3** — KT Lemma 6.2 / Case II survive with pinned choices; the
  outer Thm-5.6 strip-extend, the Case-I glue (Claim 6.4), and Case
  III's Claim 6.12 span (6 → 5, exactly 1-dim short when both chain
  ends have deg ≥ 3) break — three open cores.

## Blockers / open questions

- **Nothing blocks the next build.** W0–W2 built and gated; the W3–W5 route
  recon's verdicts (`notes/Phase39-design.md` §W3–W5 route recon) are accepted
  and W3-L1 has landed. Open research questions now live inside the pinned
  routes: the in-stratum genericity device's design (first W5 deliverable,
  sets the final induction hypothesis), W4's witness generality, and the k = 0
  split case's non-minimal residue (design doc, W5 sub-obligations).
- The full biconditional transport `ExtensorThroughPoint C q ↔
  ExtensorInPanel (screwComplementIso C) q` (design doc's W0 pin) is
  landed only as its **two forward implications** (which is all the
  self-duality consumes). The reverse arms need a `complementIso`
  involution lemma (`screwComplementIso` applied twice = a scalar),
  not in tree — a separate result, deferred; not on the W0–W2 critical
  path. Land it only if a later node needs the `↔`.

## Hand-off / next phase

**W0 + W1 + W2 all COMPLETE; W3-L0/L1/L2/L2a/L3/L4/L5/L6a LANDED 2026-07-24** — the W3-L5 base arm
is now COMPLETE (`hasPencilRealization_of_ncard_le_two`, node `lem:pencil-base-case` green; see
*Current state*; canonical record `notes/Phase39-design.md` §W3–W5 route recon). The phase stays
OPEN (the two superseding 2026-07-24 adjudications — no phase-close). **Next concrete buildable
commit** — the only remaining non-provisional W3 leaf:

1. **W3-L7** (provisional bare-motive wrapper `pencil_conjecture_of_arms`) — assembles the arms via
   `Graph.pencil_reduction`. The base arm plugs in directly (`hasPencilRealization_of_ncard_le_two`,
   signature already matches `hbase`'s shape verbatim). The cut arm plugs in as
   `hasPencilRealization_of_not_twoEdgeConnected` (drop the arm's `hloop`/`3 ≤ |V|`, which it does
   not use; supply `hD`/`hn` from context).

After W3's shell closes (only W3-L7's provisional bare-motive wrapper remains — **GP caveat**: its
interfaces are provisional, the final IH is expected to be a conditioned pair with a pencil-generic
conjunct, pinned as the first W5 deliverable): W5 (in-stratum genericity device + single-candidate
Claim-6.12 replacement, seeds = N2 sampler), then W4 (constrained-family Claim-6.4 analogue).

Gates for any continuation: `lake build` (warning-clean) + `lake lint` when
`.lean` is touched; `blueprint/verify.sh` + `blueprint/lint.sh` (vocabulary gate
bans "stratum"/"strata") when `.tex` is touched.

## Adjacent directions (orientation only, not this phase)

ORIGAMI (`notes/Origami.md`, next queued) is the bar-joint-side
analog; the wider unqueued survey — incl. IDENT-PANEL, the nearest
neighbor — is `notes/IdeaBacklog.md`.

## Decisions made during this phase

- **W3-L4 CUT ARM COMPLETE** (2026-07-24, four commits, `Molecular/Molecule/Pencil.lean`, node
  `lem:pencil-cut-case` green): the assembly `hasPencilRealization_of_not_twoEdgeConnected` + its four
  supporting pieces (transport `lem:pencil-projective-transport`, nondegeneracy
  `lem:pencil-cut-nondegeneracy`, node-less rank infra `finrank_span_rigidityRows_cutEdge_eq` /
  `span_rigidityRows_eq_of_supportExtensor_agree`); see *Current state* for the shape + the two
  derivation-guard corrections. Design notes: nondegeneracy needs **no `[Infinite K]`** (explicit
  frame construction over any field, not the doc's genericity plan); the assembly **drops the `hcut`
  arm's `hloop`/`3 ≤ |V|`** (unused — mirrors the panel sibling's `_hV3`) and unfolds
  `¬TwoEdgeConnected` directly (its cut-decomposition wrapper needs `IsMinimalKDof`); the induce-link
  endpoint helpers `mem_of_induce_isLink_left`/`_right` were re-derived (private in Theorem55 —
  FRICTION `[mirror-candidate]`); rank/side-span infra is the intentional minimality-free
  re-derivation of Theorem55's `private` `cutEdge_finrank_assemble`/`span_rigidityRows_side_eq`
  (cleanup: shared core → `Bricks.lean`, low priority). **Promoted:** span-transport-along-`LinearEquiv`
  → TACTICS-GOLF § 22; frame-map composition idiom → § 23.
- **W3–W5 route recon landed** (2026-07-24, docs-only; canonical record
  `notes/Phase39-design.md` §W3–W5 route recon): attack order W3 → W5 → W4;
  W3 route (a) refuted (K4: no pencil-compatible strip exists, and the
  cross-incidence repair caps the stripped 4-cycle at 17 < 18 — N1), route (b′)
  adopted (induction on all spanning multigraphs, min-degree-3 dispatch lemma,
  leaves L0–L7 with typechecked signatures); W5 genericity route confirmed by
  the new escape-line numerics (N2, 5/5 samples, all three candidates work);
  W4 keep-hinges route refuted, constrained-family Claim-6.4 route supported (N3).
- **W3-L1 landed** (2026-07-24, `Molecular/Induction/Operations.lean`,
  `exists_isProperRigidSubgraph_of_three_le_degree`): a loopless multigraph on
  `≥ 3` bodies with every degree `≥ 3` has a proper rigid subgraph, no
  minimality hypothesis. **Homed in `Operations.lean`, not `Deficiency.lean`**
  as the hand-off named: `Deficiency.lean` is imported *by* `Operations.lean`,
  so a circuit-based constructor (needing `circuit_induces_isRigidSubgraph`)
  cannot sit upstream of its own ingredient — the sibling circuit-based
  lemma `indep_edgeSet_mulTilde_of_noRigid_of_pos` is already routed the same
  way, further downstream still. Proof: pick a min-degree vertex `v`
  (`Set.exists_min_image`); handshake (`MinDegreeGE.le_ncard_edgeSet`) with
  `δ ≥ 3` gives the edges avoiding `v` a `(D−1)`-fold fiber exceeding the
  `(D,D)`-sparsity cap on any vertex set omitting `v`; `matroidMG_indep_iff`
  + `Matroid.Dep.exists_isCircuit_subset` + `circuit_induces_isRigidSubgraph`
  extract the proper rigid span. Blueprint chapter's new §"Reduction on all
  spanning multigraphs" opened the same commit (`pencil.tex`): this node
  green, the L0/L2–L7 decomposition red (`def:pencil-rank-hypothesis`,
  `thm:pencil-reduction`, `lem:pencil-simple-of-noRigid`,
  `lem:pencil-loop-case`, `lem:pencil-cut-case`, `lem:pencil-base-case`,
  `lem:pencil-contraction-deficiency`, `thm:pencil-conditional-realization`).
  Gates green (`lake build` warning-clean, incl. a
  `set_option linter.unusedDecidableInType false` — `classical` shadows the
  pinned `[DecidableEq β]`; `lake lint`; `blueprint/verify.sh` + `lint.sh`).
- **W3-L2 landed** (2026-07-24, `Molecular/Induction/ForestSurgery/Reduction.lean`,
  `Graph.pencil_reduction`, node `thm:pencil-reduction`) — see *Current state* for
  the proof-shape summary. **New idiom**: nesting `Nat.strong_induction_on` for a
  lexicographic two-component measure via a `suffices` over both components (the
  single-measure `induction hN : … generalizing G` idiom doesn't nest cleanly);
  promoted to TACTICS-GOLF § 11. Hit (and resolved via) the already-documented
  TACTICS-QUIRKS § 51 `set_option … in`-before-docstring ordering.
- **W2 COMPLETE — span-uniqueness + necessity + iff landed** (2026-07-24, `Meet.lean`
  + `Molecular/Molecule/Pencil.lean`): the design-doc iff `exists_extensor_two_pencils_iff`
  (node `lem:two-pencil-extension-iff`) = existence (`←`, prior commit) ⊕ necessity (`→`).
  Necessity rests on Plücker injectivity `span_range_eq_of_extensor_eq` (Meet.lean, node-less
  like its sibling `exists_smul_extensor_eq_of_mem_span_range`): equal nonzero grade-2 extensors
  span the same plane, via join factorization `extensor ![x,a,b] = extensor ![x] * extensor ![a,b]`
  + wedge-kernel helper `extensor_triple_eq_zero_iff` (both general `d`, with the `extensor`
  machinery). Two `[idiom]` friction notes lifted (join_extensor rewrite direction;
  `linearIndependent_finCons` deprecation). Gates green; axioms clean.
- **W1 COMPLETE — cycle pencil wrap landed** (2026-07-24, `Molecular/Molecule/Pencil.lean`,
  node `lem:cycle-pencil-realization`): `exists_pencilPanelRealization_cycle` — a
  `Graph.CycleData` cycle (`cy.m ≤ 4`) carries a full `HasPencilPanelRealization` rigid
  on `V(G)`. Second decompose slice, on the coplanar wrap's custom framework: body `i`'s
  point is the concurrency of `C₁ = panelSupportExtensor (nrm (i-1)) (nrm i)` /
  `C₂ = panelSupportExtensor (nrm i) (nrm (i+1))` via the landed concurrency lemma,
  `choose`n + `Function.extend`ed off `cy.vtx`; cyclic `Fin` identities `(i-1)+1 = i`,
  `(j+1)-1 = j` by `abel` (needs `[NeZero cy.m]`), endpoint match by
  `IsLink.eq_and_eq_or_eq_and_eq`. **De-dup:** made `exists_coplanarPanelRealization_cycle`
  a 2-line corollary (pencil ⇒ coplanar via `.1`), so the fragile framework construction
  exists once — blueprint keeps both nodes, `lem:cycle-pencil-realization` `\uses` the
  coplanar node + concurrency (math order), opposite the Lean derivation (harmless).
- **W1 cycle coplanar wrap landed** (2026-07-24, `Molecular/Molecule/Pencil.lean`,
  node `lem:cycle-coplanar-realization`): a `Graph.CycleData` cycle with `cy.m ≤ 4`
  carries a `HasCoplanarPanelRealization` rigid on `V(G)`. First decompose slice.
  **Chose a custom `Function.extend` framework over `cycle_realization`/`ofNormals`** —
  cleaner, drops all `Infinite K`/finiteness hyps (needs only `exists_cycle_normals`,
  `extensorInPanel_panelSupportExtensor`, `theorem_55_cycle`). **Honest `m`-range**
  `3 ≤ cy.m ≤ 4` (CycleData floor + `exists_cycle_normals`' `m ≤ k+2 = 4`), *not*
  the hand-off's "only triangle" — the ceiling is the seed lemma's, not `cy.m ≤ n`.
  (Follow-up commit demoted this to the corollary above.)
- **W1 nonvacuity witness landed** (2026-07-24, `Molecular/Molecule/Pencil.lean`,
  `exists_hasPencilPanelRealization_witness`): `HasPencilPanelRealization`
  inhabited at a concrete two-vertex double edge
  `(Graph.singleEdge 0 1 0).addEdge 1 0 1`, rigid on its bodies — immediate from
  the two-body producer. No blueprint node (Lean-only certificate, per
  `molecular_conjecture_witness` precedent; re-flagged). Landed as the sanctioned
  "smaller honest slice": the cycle-realization wrap (coordinator's primary next
  item) is a large fragile meet-framework assembly (see *Hand-off* for the
  assessed route + decompose plan), so the bounded witness went first.
- **W1 pencil-cycles geometric core landed** (2026-07-23,
  `Molecular/Molecule/Pencil.lean`, node `lem:coplanar-hinges-concurrent`):
  `exists_concurrency_point_of_extensorInPanel_pair` — two coplanar hinges
  automatically share a concurrency point (degree-2 pencil pin free), via a
  two-2-planes-in-a-3-space modular-law argument (`finrank_sup_add_finrank_inf_eq`
  + the new single-vector panel-dim helper `finrank_toDualPerp_single_eq`
  mirroring `Meet.lean`'s pair version). Scoped to the geometric *check*, not
  the framework *wrap* of `cycle_realization` — the per-body edge-incidence
  extraction from `CycleData` is the fiddly remainder, handed off. Low ScrewSpace
  fragility (pure `Fin 4 → K` subspace linear algebra).
- **W1 base case landed** (2026-07-23, `Molecular/Molecule/Pencil.lean`, two
  green nodes): (1) `exists_linearIndependent_extensor_pair_through_point`
  (`lem:extensor-pair-through-point`) — the coincident-panel pencil pair (KT
  Lemma 5.3 core), reusing `linearIndependent_pair_extensor_of_li3` (its two
  shared-vector wedges give the pencil point free), LI transported to
  `ScrewSpace K 2` via `LinearMap.linearIndependent_iff`. (2)
  `exists_pencilPanelRealization_parallel_pair` (`lem:pencil-base-parallel-pair`)
  — the two-body realization: parallel-pair graph carries a
  `HasPencilPanelRealization` rigid on `V(G)` via `theorem_55_base`. Scoped the
  rank to `IsInfinitesimallyRigidOn V(G)` (the `def=0`, `V(G)`-relative rank-`D`
  form), *not* the global `RankHypothesis`/prop11 chain — that needs a spanning
  graph and is a W3 concern; B1 bridges the two if a later node needs it.
- **W0 Lean core landed** (2026-07-23, `Molecular/Molecule/Pencil.lean`):
  statement layer + polarity bridge + two forward transport implications
  + self-duality (`#print axioms` clean: propext/Classical.choice/Quot.sound).
  The transport is delivered as the two forward arms, not the pinned `↔`:
  the self-duality (W0's operational core) consumes only the forward arms,
  and the reverse arms need a `complementIso` involution not in tree (see
  *Blockers*). Self-duality's meet→through arm rides a dimension-count
  helper (`mem_span_of_dotProduct_perp_pair`, via `finrank_toDualPerp_pair_eq`);
  the through→meet arm is pure linearity. Blueprint chapter deferred to a
  follow-up commit (kept the fragile ScrewSpace Lean commit off the
  blueprint toolchain surface) — landed the same day, next entry.
- **W0 blueprint chapter opened** (2026-07-23, `blueprint/src/chapter/pencil.tex`):
  five green nodes per *Current state* above. `screwComplementIso_mk_extensor`
  reused the existing `lem:panel-hinge-dual-molecular` label (its own
  doc-comment already pinned it as the arbitrary-point generalization of
  `screwComplementIso_lineExtensor`) rather than minting a new one — the
  additive-successor discipline (`CLAUDE.md` *Working*): extended that
  node's `\lean{...}` list + one generalizing sentence in
  `molecule-modelling.tex`, same commit. No W1/W2 red nodes: neither has a
  typechecked statement spike yet, unlike W0's.
- **Opening recon landed** (2026-07-23): R1–R3 verdicts as above;
  canonical record `notes/Phase39-design.md`. Method: KT primary
  source (page pointers re-verified), landed definition bodies, a
  typechecked `lake env lean` statement spike (scratch, not
  committed), exact-rational rank experiments (configurations +
  results tabulated in the design doc).
- **Negative-data correction** (2026-07-23, recon): the queued
  "all-atoms-coplanar is rank-deficient" is a bar-joint/`G²` fact
  (via the general-position-gated dictionary); in the body-hinge
  model the coplanar locus attains full target rank whenever
  `2|E| ≥ 3|V| − 3` (numerics), and is deficient by exactly the
  spline count otherwise. PENCIL carries no `G²` corollary without
  new dictionary work at degenerate placements.
- **Recon-first; no pinned statement at open** (2026-07-23, per the
  queue entry + `notes/Pencil.md`): R1's statement/satisfiability
  questions are genuinely open, so the open commit pins no Lean
  signature and no blueprint node.
- **Blueprint chapter deferred to the R1 verdict** (2026-07-23):
  `notes/Pencil.md` planned the forward-mode chapter opening with the
  phase, but with R1 unsettled a chapter-open red node risks the
  known plausible-"corrected"-statement failure mode (dispatch-log
  2026-07-11); the Phase-32/34/35 precedent — chapter opens on the
  recon verdicts — applies instead. Re-flagged here rather than
  silently dropped.
- **Higher-`d` flag discharged** (2026-07-23, recon): the stratum is
  self-dual and the chain analysis carries over at every `d` (only
  chain *ends* get pinned); nothing about `d > 3` looks easier — see
  `notes/Phase39-design.md` *Higher-`d` note*. The between-strata
  hierarchy stays in `notes/IdeaBacklog.md` Tier A.

## Citations (transcribed, project-canonical sources)

- Katoh–Tanigawa, *A proof of the molecular conjecture*, Discrete
  Comput. Geom. **45** (2011) — the KT pointers in this note
  (Cor. 5.7, Thm 4.9, Thm 5.5, Lemma 6.13, the Case I/II/III split)
  are transcribed from `notes/Pencil.md`'s 2026-07-23 survey against
  the project-canonical source (ROADMAP *References*); KT pointer
  verification history: `notes/Phase35.md` *Citations*,
  `notes/Phase23-cleanup.md`.
- Jordán 2016 (MSJ Memoirs 34) — checked silent on the pencil stratum
  in the 2026-07-23 survey (the no-literature-result finding).
