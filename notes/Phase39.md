# Phase 39 — PENCIL: the hinge-pencil molecular conjecture (work log)

**Status:** in progress — **W0–W3 all COMPLETE**; **W5 design settled** (2026-07-24 design
pass: motive + device pinned, design doc §"W5 design pass"); **W5-L0 (the motive layer),
W5-L1 (`cross₃`), and the chart-construction core of W5-L2 landed** 2026-07-24; phase stays
open (two user adjudications, below); next: finish W5-L2 (framework + full nondeg-stratum
derivation) or proceed to L3; W4 after W5 (phase opened 2026-07-23, recon-first).

## Current state

**The phase stays OPEN — do NOT run the close checklist.** Two 2026-07-24 user
adjudications (verbatim, later supersedes earlier) revised the same-day "wrap up"
one: *"Let's leave the phase open and continue the work on the conjecture in this
phase. Unless there's a good reason to split here."* (coordinator assessed: no
reason to split — the phase's charter is the conjecture itself), then *"Let's end
the loop after this dispatch returns and you've confirmed its results; we'll begin
the research on the conjecture in a fresh session."* So: **W0, W1, W2, and now W3
are all complete**, no phase-close.

**The W3–W5 route recon** (`notes/Phase39-design.md` §W3–W5 route recon — the canonical
record) set the attack order **W3 → W5 → W4**: W3's candidate route (a) (pencil-compatible
strip) was **refuted** (no such strip exists on K4; the cross-incidence repair provably caps
the stripped 4-cycle at rank 17 < 18); route **(b′)** was adopted — the induction restated on
ALL spanning multigraphs, dispatch made total without minimality by a new min-degree-3 ⟹
proper-rigid-subgraph lemma, decomposed into leaves **L0–L7**. New numerics: **N2** confirms
W5's genericity route (the obstruction vector `r` misses the 1-dim escape line in 5/5 exact
samples on the Case-III habitat); **N3** confirms W4's constrained-family (Claim-6.4
specialization) route (G′-block witness at 18/18), refuting the keep-hinges
coincidence-cluster alternative.

**All eight W3 leaves are now landed** (2026-07-24, one session; `Molecular/Molecule/Pencil.lean`
unless noted — full per-leaf detail in *Decisions made* below and the design doc §W3 leaf
decomposition):
- **L0** `HasPencilRealization` (`def:pencil-rank-hypothesis`) — the `V(G)`-relative bare motive.
- **L1** `exists_isProperRigidSubgraph_of_three_le_degree` (`Induction/Operations.lean`) — the
  min-degree-3 ⟹ proper-rigid-subgraph dispatch lemma, minimality-free.
- **L2** `Graph.pencil_reduction` (`Induction/ForestSurgery/Reduction.lean`, `thm:pencil-reduction`)
  — the reduction skeleton, nested strong induction on the lex measure `(|V|, |E|)`.
- **L2a** `Graph.simple_of_loopless_of_noRigid` (`Induction/ReducibleVertex.lean`,
  `lem:pencil-simple-of-noRigid`) — minimality-free sibling of `simple_of_isMinimalKDof_of_noRigid`.
- **L3** `hasPencilRealization_of_isLoopAt` (`lem:pencil-loop-case`) — the loop arm.
- **L4** `hasPencilRealization_of_not_twoEdgeConnected` (`lem:pencil-cut-case`) — the cut arm, via
  four supporting pieces (transport `lem:pencil-projective-transport`, nondegeneracy
  `lem:pencil-cut-nondegeneracy`, node-less rank/side-span infra).
- **L5** `hasPencilRealization_of_ncard_le_two` (`lem:pencil-base-case`) — the `≤ 2`-body base arm
  (edgeless / single-edge / parallel-class, sandwiched between landed rank bounds).
- **L6a** `Graph.rigidContract_deficiency_eq` (`Induction/Contraction.lean`,
  `lem:pencil-contraction-deficiency`) — minimality-free contraction-deficiency bookkeeping.
- **L7** `pencil_conjecture_of_arms` (`thm:pencil-conditional-realization`) — the provisional
  bare-motive wrapper (below).

Two derivation-guard corrections settled during the leaves (design doc §W3, canonical): the landed
`thm:projective-invariance` is ℝ-only/`supportExtensor`-only (so the `K`-level `(normal,point)`
transport was built fresh on `HingeGeneric.lean`); `exists_cut_decomposition_of_not_twoEdgeConnected`
is **not** minimality-free.

**W5 design pass landed 2026-07-24** (docs-only; canonical record `notes/Phase39-design.md`
§"W5 design pass"): the final conditioned-pair motive is **pinned** (typechecked) —
`PencilPair K n G := (PencilNondegFeasible K G → HasGenericPencilRealization K n G) ∧
HasPencilRealization K n G`, generic half = *stratum-nondegenerate* realization (adjacent
points projectively distinct + closed-hub-neighbourhood normals LI) at the deficiency rank;
`Simple`-conditioning refuted (K4 derivation), bare-existential generic half refuted
(consumer-starving). Device = the grade-0 molecular-side chart (N2 sampler made uniform,
cross-product constructed points, hinges = point-joins) + the **landed** engine
(`exists_polynomial_ne_zero_of_linearIndependent_at_reindex`); no transfer-form conjunct
(RELAX precedent); the D6 re-seeding lemma keeps the motive chart-independent. New numerics
N4–N6: every forced nondegenerate stratum branch tested attains full target (theta collinear
24/24, K3,3 two-line 30/30, spider-K4 coincidence 54/54). Leaves W5-L0…L8 pinned in
dependency order; the research core is L7 (the single-candidate escape certificate).

**W5-L0 landed 2026-07-24** (`Molecular/Molecule/Pencil.lean`, new §"W5-L0: the pencil-nondegenerate
motive"): the six pinned decls transcribed verbatim from the design doc (`Graph.PencilHub`,
`Graph.closedHubNbhd`, `IsNondegPencilRealization`, `PencilNondegFeasible`,
`HasGenericPencilRealization`, `PencilPair`), the forgetful map `hasPencilRealization_of_generic`
(two-line drop-the-conjuncts proof), and the loop guard `not_pencilNondegFeasible_of_isLoopAt`
(`LinearIndependent.pair_iff` at `s = 1, t = -1` on the repeated vector `point v`). **One fixup
against the design-doc spike:** `Graph.PencilHub`/`Graph.closedHubNbhd` need the `_root_.Graph.`
prefix (not bare `Graph.`) to land as top-level `Graph.foo` — the spike typechecked outside this
file's `namespace CombinatorialRigidity.Molecular`, where a bare `Graph.foo` prefix instead nests
under the open namespace (established project idiom, e.g. `Graph.ChainData.d_eq_kAdd` in
`CaseIII/Realization.lean`). Blueprint: new subsection "Nondegenerate realizations and the
conditioned pair" in `pencil.tex` — three green nodes (`def:pencil-nondegenerate`,
`def:pencil-generic-motive`, `def:pencil-conditioned-pair`) plus the W3-L7 successor restated red
(`thm:pencil-conditional-realization-pair`, no `\lean{}` yet — the successor itself is W5-L5); the
landed `thm:pencil-conditional-realization` node and its `fmlnote:pencil-conditional-bare` are
untouched, per the scope pin. Gates green (`lake build` warning-clean 2862 jobs; `lake lint`;
`blueprint/verify.sh` + `lint.sh`).

**W5-L1 landed 2026-07-24** (`Molecular/Molecule/Pencil.lean`, new §"W5-L1: the `K⁴` generalized
cross product"): `cross₃ x y z` — the unique vector representing, via the standard dot product, the
linear functional `w ↦ det[x, y, z, w]` (`dotProduct_cross₃`, the defining property) — plus
orthogonality (`cross₃_dotProduct_fst/snd/thd`), multilinearity (`cross₃_add_*`/`cross₃_smul_*`,
six lemmas, the "polynomial-in-entries" property L2/L3 need), vanishing-iff-dependent
(`cross₃_ne_zero_iff_linearIndependent`), and the perp-sweep lemma feeding D6
(`range_cross₃L_eq_perp`, via the bundled third-slot linear map `cross₃L`). **Route: the direct
cofactor def, not the grade-3 `complementIso` specialization** — the `complementIso` route needs a
fresh grade-`1`-toDual-to-dot-product bridge lemma with no precedent in the tree, while the cofactor
route stays entirely inside mature `Matrix.det` API (`Matrix.det_updateRow_add/_smul`,
`Matrix.det_zero_of_row_eq`, `Matrix.linearIndependent_rows_iff_isUnit`) plus the standard
`linearIndependent_finSnoc` extension fact, so it proved shorter (the design doc's own
tie-breaker). No blueprint node: the design doc's L1 bullet names no `def:`/`lem:` tag (unlike L0),
matching the W3-L4 rank-helpers precedent for unnamed technical infra — no `.tex` change this
commit. Gates green (`lake build` warning-clean 2862 jobs; `lake lint`; axioms clean on the three
headline decls). **Friction:** `dotProduct_eq_iff`/`dotProduct_eq_zero_iff`/`add_dotProduct`/
`smul_dotProduct` live unnamespaced in `Mathlib.LinearAlgebra.Matrix.DotProduct` (not under
`Matrix.`) — cost a guessed-wrong-name round; logged in `FRICTION.md`, alongside an open
mirror-candidate for the "`LinearIndependent` of `n` rows in `Kⁿ` iff `det ≠ 0`" 3-lemma chain
(`Matrix.linearIndependent_rows_iff_isUnit` + `Matrix.isUnit_iff_isUnit_det` +
`isUnit_iff_ne_zero`) used twice in this commit.

**W5-L2 chart-construction core landed 2026-07-24** (`Molecular/Molecule/Pencil.lean`, new §"W5-L2:
the grade-0 pencil chart"): `PencilSeed` (per-body free hub-normal + three fill vectors);
`Graph.closedNbhd` (all neighbours, unfiltered — feeds non-hub normals, unlike hub-filtered
`closedHubNbhd`); the selector idiom `IsFin3SelectorOf` (a `Fin 3 → Option α` correct exactly when
bijective between its "some"-slots and a target set — the pencil analogue of the panel framework's
`ends`/`hends`, since a body's closed-hub-/closed-neighbourhood is a `Set`, not a function, and
`cross₃` needs three explicit inputs); `hubSlotNormal`/`pencilChartPoint` and
`nbrSlotPoint`/`pencilChartNormal` (hub branch = the seed's own hub-normal, non-hub branch = `cross₃`
of closed-neighbourhood points, via `open Classical in` on the `PencilHub` case split); chart
well-formedness `PencilChartWF` (selector correctness + 3-slot LI at every body + adjacent-point
distinctness). **By construction:** the point/normal orthogonality core validating the chart's
shape — `dotProduct_pencilChartPoint_hubNormal_of_mem_closedHubNbhd` (the point is automatically
orthogonal to every selected hub's normal — own-panel incidence at `w=v`, cross-incidence at a
hub-neighbour) and its non-hub sibling `dotProduct_pencilChartPoint_pencilChartNormal_of_mem_closedNbhd`,
both via the general helper `cross₃_dotProduct_apply_self` — plus the two nonzero corollaries
(`pencilChartPoint_ne_zero`, `pencilChartNormal_ne_zero_of_not_pencilHub`). **Scoped smaller slice**
(pre-authorized): `pencilChartFramework` (bundling into a `BodyHingeFramework`) and the full
`IsNondegPencilRealization` derivation are deferred — the latter additionally needs identifying the
framework's *specific* supporting extensor `panelSupportExtensor (normal u) (normal v)` with the
point-join `extensor ![point u, point v]` up to the Plücker-proportionality scalar (W2's
`exists_extensor_two_pencils` only shows *some* such extensor exists, not that this one is it), and
the closed-hub-neighbourhood normal-LI conjunct's derivation from `PencilChartWF`'s 3-slot condition
via the selector's injectivity (a sub-independent-family argument, not yet built). No blueprint node:
the design doc's L2 bullet names no `def:`/`lem:` tag, matching the W3-L4/W5-L1 unnamed-technical-
infra precedent. Gates green (`lake build` warning-clean 2862 jobs; `lake lint`; axioms clean on the
two by-construction theorems). **Friction:** hit two already-documented gotchas, no new entries —
a literal `-/` inside the prose "hub-/closed-neighbourhood" terminated a `/-!` block early
(TACTICS-QUIRKS § 57, fixed by rewording); `fin_cases i` on an `obtain`-destructured witness produces
a `(fun i ↦ i) ⟨n, ⋯⟩`-wrapped term that doesn't `simp`-match a numeral-indexed goal (FRICTION
*"`fin_cases i` leaves `⟨n, ⋯⟩`"*/TACTICS-QUIRKS § 46 family) — sidestepped by proving
`cross₃_dotProduct_apply_self` generically over a **fresh** `∀ i`, then applying it at the specific
witness index without a second case-split.

**W3-L7 landed 2026-07-24** (`pencil_conjecture_of_arms`, node `thm:pencil-conditional-realization`
green): instantiates `Graph.pencil_reduction` at `n = 3`, discharging the loop/base/cut arms
internally from L3/L5/L4 and taking `hcontract`/`hsplit` as hypotheses, then bridges the
`V(G) = univ` conclusion to `RankHypothesis` via the rank-nullity complement identity
`finrank_span_rigidityRows_add_finrank_infinitesimalMotions` (linear algebra: `finrank(span rows) =
D(|V|−1) − def` and `finrank(span rows) + finrank(motions) = D|V|` give `finrank(motions) = D +
def`). Dropped `[Infinite K]` from the design-doc spike's instance list (genuinely unused). **This
wrapper is PROVISIONAL** (the recorded GP caveat, kept in both the docstring and the blueprint
node): its `hcontract`/`hsplit` hypotheses are the bare-motive arms, and the final induction
hypothesis is expected to grow a pencil-generic conjunct once W5 lands — do not treat its
interfaces as final. Gates green (`lake build` warning-clean 2862 jobs; `lake lint`;
`blueprint/verify.sh` + `lint.sh`; `#print axioms` = propext/Classical.choice/Quot.sound).

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

- **Nothing blocks the next build.** W0–W3 built and gated; the W5 design pass
  (2026-07-24, design doc §"W5 design pass") pinned the final motive and the
  device, so the induction hypothesis W3-L7 was provisional on is now settled
  on paper. Open research questions inside the pinned route: **W5-L7** (the
  uniform escape certificate `r ⬝ Λ²Π̂(a) ≢ 0` on the chart — the genuinely new
  mathematics, N2 witnesses one instance), **W5-L6** (habitat feasibility
  lemma), **W5-L8** (the k = 0 residue — emptiness route recommended; KT's
  Claim-6.11 proof consumes minimality twice, p. 684 re-verified), and W4's
  witness generality (unchanged, after W5).
- The full biconditional transport `ExtensorThroughPoint C q ↔
  ExtensorInPanel (screwComplementIso C) q` (design doc's W0 pin) is
  landed only as its **two forward implications** (which is all the
  self-duality consumes). The reverse arms need a `complementIso`
  involution lemma (`screwComplementIso` applied twice = a scalar),
  not in tree — a separate result, deferred; not on the W0–W2 critical
  path. Land it only if a later node needs the `↔`.

## Hand-off / next phase

**W0–W3 COMPLETE; W5 design settled 2026-07-24; W5-L0, W5-L1, and W5-L2's chart-construction core
landed 2026-07-24.** The phase stays OPEN (the two superseding 2026-07-24 adjudications — no
phase-close). **W5-L2 landed:** `PencilSeed`, the `hubSel`/`nbrSel` selector idiom
(`IsFin3SelectorOf`), `pencilChartPoint`/`pencilChartNormal`, chart well-formedness
(`PencilChartWF`), and the by-construction own-panel/cross-incidence orthogonality theorems
(`dotProduct_pencilChartPoint_hubNormal_of_mem_closedHubNbhd` and its non-hub sibling) — validating
the chart's shape against the motive's conjuncts. **Not yet landed** (retargeted, scope-to-fit):
`pencilChartFramework` (bundling the chart into a `BodyHingeFramework`) and the full
`IsNondegPencilRealization` derivation — the latter needs (a) the Plücker-proportionality bridge
identifying `panelSupportExtensor (normal u) (normal v)` with the point-join extensor up to scalar
(W2's `exists_extensor_two_pencils` only shows *some* extensor works, not this one), and (b) the
closed-hub-neighbourhood normal-LI conjunct via the selector's injectivity (a
sub-independent-family/reindexing argument, not yet built). **Next concrete buildable commit:**
either finish W5-L2 (the framework + the two deferred derivations above), or fold that work into L3
(rows-polynomial + engine hookup) if it turns out cleaner to derive there — assess at pickup. Then
L4/D6 (re-seeding, now able to cite the landed perp-sweep lemma `range_cross₃L_eq_perp`) — the
device spine — then L5 (the W3-L7 successor `pencil_conjecture_of_arms_pair` + arm re-derivations,
red node `thm:pencil-conditional-realization-pair` already restated in `pencil.tex`); L6/L8 parallel
after L0; L7 (the research core) last. Then W4 (constrained-family Claim-6.4 analogue, G′-block
witness confirmed by N3).

Gates for any continuation: `lake build` (warning-clean) + `lake lint` when
`.lean` is touched; `blueprint/verify.sh` + `blueprint/lint.sh` (vocabulary gate
bans "stratum"/"strata") when `.tex` is touched.

## Adjacent directions (orientation only, not this phase)

ORIGAMI (`notes/Origami.md`, next queued) is the bar-joint-side
analog; the wider unqueued survey — incl. IDENT-PANEL, the nearest
neighbor — is `notes/IdeaBacklog.md`.

## Decisions made during this phase

- **W5 design pass landed** (2026-07-24, docs-only; canonical record
  `notes/Phase39-design.md` §"W5 design pass"): final motive = the conditioned pair
  `PencilPair` over the *feasibility-conditioned* nondegenerate generic half —
  `Simple`-conditioning refuted at K4, bare-existential half refuted as
  consumer-starving; device = grade-0 molecular chart + the landed engine, no
  transfer-form conjunct (RELAX precedent), D6 re-seeding keeps the motive
  chart-independent; N4–N6 numerics all positive; leaves W5-L0…L8 pinned with
  typechecked shapes (forgetful map already proved in-spike); KT p. 684
  re-verified (Claim 6.11 consumes minimality twice — sharpens L8).
- **W3-L7 landed — W3's shell fully closed** (2026-07-24, `Molecular/Molecule/Pencil.lean`,
  `pencil_conjecture_of_arms`, node `thm:pencil-conditional-realization` green): instantiates
  `Graph.pencil_reduction` at `n = 3` with `hloop`/`hbase`/`hcut` discharged internally from
  L3/L5/L4 and `hcontract`/`hsplit` as hypotheses; bridges the resulting `HasPencilRealization`'s
  span-rank equation to `RankHypothesis` via
  `finrank_span_rigidityRows_add_finrank_infinitesimalMotions` (the same rank-nullity pattern as
  `Theorem56.lean`'s `hrank0`/`hcompl` derivation — reused verbatim). Dropped `[Infinite K]` from
  the design-doc spike (nothing in the proof needs it). One `lake lint` fixup: `show` → `change`
  (the `linter.style.show` false-`show` check fires when `show` actually changes the goal, as ours
  does unfolding `RankHypothesis`). **PROVISIONAL** per the recorded GP caveat — kept verbatim in
  both the docstring and the blueprint `fmlnote:pencil-conditional-bare` (not removed): `hcontract`/
  `hsplit` are the bare-motive arms, expected to need a pencil-generic conjunct once W5 lands.
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
