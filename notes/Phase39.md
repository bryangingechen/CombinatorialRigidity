# Phase 39 — PENCIL: the hinge-pencil molecular conjecture (work log)

**Status:** in progress — **W0–W3 all COMPLETE**; **W5 design settled** (2026-07-24 design
pass: motive + device pinned, design doc §"W5 design pass"); **W5-L0 through W5-L3 all
COMPLETE** 2026-07-24; **W5-L4 in progress** (2026-07-24: per-arity sweep helpers, cardinality
bound + selector construction, and the **route-2 motive restatement** — the fourth
`IsNondegPencilRealization` conjunct + `PencilChartWF`'s matching relativization + the
`linearIndepOn_pencilChartPoint_closedNbhd` transfer mirror — all landed); phase stays open (two
user adjudications, below); next: piece 3, the `exists_pencilSeed_of_nondeg` assembly
(*Hand-off*); W4 after W5 (phase opened 2026-07-23, recon-first).
**`Molecule/Pencil.lean` split into `Molecule/Pencil/{Statement,Arms,Motive,Chart,Engine}.lean`
2026-07-24** (housekeeping; see *Decisions made* for the file map).

## Current state

**The phase stays OPEN — do NOT run the close checklist.** Two 2026-07-24 user
adjudications (verbatim, later supersedes earlier) revised the same-day "wrap up"
one: *"Let's leave the phase open and continue the work on the conjecture in this
phase. Unless there's a good reason to split here."* (coordinator assessed: no
reason to split — the phase's charter is the conjecture itself), then *"Let's end
the loop after this dispatch returns and you've confirmed its results; we'll begin
the research on the conjecture in a fresh session."*

**W0–W3 are all COMPLETE; W5 design is settled; W5-L0 through W5-L3 are COMPLETE; W5-L4 is
in progress** with its motive-restatement prerequisite now landed (below). The per-milestone
detail for every completed piece — decls, proof shape, gate status, friction — lives in
*Decisions made* below (reverse-chronological, one entry per landing) and in
`notes/Phase39-design.md`; this section stays a pointer, not a second copy.

**The W3–W5 route recon** (`notes/Phase39-design.md` §W3–W5 route recon) set the attack
order **W3 → W5 → W4**: W3 route (a) (pencil-compatible strip) refuted at K4; route
**(b′)** adopted — induction on ALL spanning multigraphs, dispatch made total by a
min-degree-3 ⟹ proper-rigid-subgraph lemma, decomposed into leaves **L0–L7** (all landed).
W5's genericity route and W4's constrained-family route both confirmed by numerics (N2, N3).

**W5's device** (design pass, `notes/Phase39-design.md` §"W5 design pass"): final motive =
the conditioned pair `PencilPair` over the feasibility-conditioned nondegenerate generic half;
device = the grade-0 molecular chart (`Molecule/Pencil/Chart.lean`) + the rows-polynomial
engine (`Molecule/Pencil/Engine.lean`), decomposed into leaves **L0–L8** (L0–L3 complete, L4
in progress per *Hand-off*, L5–L8 not started).

**W5-L4, this session's focus:** the per-arity re-seeding sweep helpers, the cardinality
bound + selector construction, and (this commit) the motive restatement that resolves the
piece-3 blocker are all landed in `Molecule/Pencil/{Motive,Chart,Engine}.lean`. The
`exists_pencilSeed_of_nondeg` global assembly itself (piece 3's actual construction) is the
next concrete commit — see *Hand-off*.

The opening recon ran 2026-07-23; full verdicts (R1–R3) are below in *Opening recon verdicts*.

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

- ~~W5-L4 blocked~~ **resolved** (2026-07-24 blocker recon; design doc L4 bullet
  "Blocker verdict"): the triple can genuinely fail — route 2 (motive
  restatement) pinned with typechecked shapes, **and landed** (same day, the
  restatement slice below): `IsNondegPencilRealization`'s fourth conjunct,
  `PencilChartWF`'s matching relativization, and the transfer mirror
  `linearIndepOn_pencilChartPoint_closedNbhd`. No open question remains here;
  piece 3 (`exists_pencilSeed_of_nondeg`'s global assembly) is the next build
  commit (*Hand-off*).
- Open research questions inside the pinned W5 route, downstream of L4: **W5-L7**
  (the uniform escape certificate `r ⬝ Λ²Π̂(a) ≢ 0` on the chart — the genuinely
  new mathematics, N2 witnesses one instance), **W5-L6** (habitat feasibility
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

**W0–W3 COMPLETE; W5 design settled 2026-07-24; W5-L0 through W5-L3 all COMPLETE 2026-07-24;
W5-L4 in progress (sweep helpers + cardinality bound + selector construction + the route-2 motive
restatement all landed 2026-07-24).** The phase stays OPEN (the two superseding 2026-07-24
adjudications — no phase-close).

**The W5-L4 restatement slice landed** (route 2, design doc L4 bullet "Blocker verdict"):
`IsNondegPencilRealization` gained its fourth conjunct
`∀ v ∈ V(G), ¬ G.PencilHub v → LinearIndepOn K point (G.closedNbhd v)` (`Pencil/Motive.lean`, which
also now hosts `Graph.closedNbhd`, moved from `Pencil/Chart.lean` to resolve the import-order
dependency); the four destructuring consumers were fixed
(`hasPencilRealization_of_generic`/`not_pencilNondegFeasible_of_isLoopAt` arity bumps,
`ncard_closedHubNbhd_le_three_of_isNondegPencilRealization`'s `h.2.2` → `h.2.2.1`;
`dotProduct_point_eq_zero_of_mem_closedHubNbhd` needed no change, only `h.1`); `PencilChartWF`'s
fourth conjunct is relativized to `¬ G.PencilHub v` (`Pencil/Chart.lean`) with its sole consumer
fixed (`hNbrLI v hv`); the transfer mirror `linearIndepOn_pencilChartPoint_closedNbhd` landed and
feeds the extended headline theorem `isNondegPencilRealization_pencilChartFramework_of_pencilChartWF`.
Blueprint `def:pencil-nondegenerate` restated (new `Graph.closedNbhd` `\lean{...}` pin, a third
conjunct clause, and a companion `fmlnote` on why it's non-hub-only); the Engine §"W5-L4 continued"
gap paragraph rewritten as resolved.

**Next concrete commit: piece 3, the `exists_pencilSeed_of_nondeg` global assembly** — now
buildable. The per-case plan from the design doc's verdict: at a non-hub `3`-member `closedNbhd`
the new conjunct feeds the relativized WF conjunct directly (via the just-landed transfer mirror,
in reverse — this direction needs the *chart* to reproduce a *given* realization's point, the
re-seeding direction, not the by-construction direction the mirror proves); the `≤ 2`-member cases
pad by fill (a vector outside a `≤ 2`-dim span exists); hub points reproduce via the closed-hub-
neighbourhood normal-LI conjunct + the landed per-arity sweeps (`exists_cross₃_eq_of_ne_zero`/
`_of_ne_zero_of_dotProduct_eq_zero`/`exists_smul_cross₃_eq_of_linearIndependent`, projective at
full arity); and the non-hub chart normal reproduces automatically (orthogonal to the LI point-
triple whose common perp is `1`-dimensional, `finrank_toDualPerp_triple_eq`, hence proportional to
`cross₃` of it). Assemble `exists_pencilSeed_of_nondeg` in `Pencil/Engine.lean` (or a new
`Pencil/Reseed.lean` leaf if the file nears the `≤1500`-LoC cap again) and restate/green the
`lem:pencil-reseeding`-style blueprint node once named.

**Once W5-L4 closes:** L5 (the W3-L7 successor `pencil_conjecture_of_arms_pair` + arm
re-derivations, red node `thm:pencil-conditional-realization-pair` already restated in
`pencil.tex`); L6/L8 parallel after L0; L7 (the research core, likely the first leaf needing the
`normalRow_eq_panelRow`-style graph bridge deferred from L3) last. Then W4 (constrained-family
Claim-6.4 analogue, G′-block witness confirmed by N3).

**Infrastructure landed across W5-L4, all feeding the piece-3 assembly above:** the per-arity sweep
helpers (`range_cross₃L_eq_perp`, `exists_cross₃_eq_of_ne_zero_of_dotProduct_eq_zero`,
`exists_smul_cross₃_eq_of_linearIndependent`, `exists_cross₃_eq_of_ne_zero`), the cardinality bounds
(`ncard_closedHubNbhd_le_three_of_isNondegPencilRealization`,
`ncard_closedNbhd_le_three_of_not_pencilHub`), the selector builder
(`exists_isFin3SelectorOf_of_ncard_le_three`), the corrected/relativized `PencilChartWF`, and the
restated `IsNondegPencilRealization` + its transfer mirror `linearIndepOn_pencilChartPoint_closedNbhd`.

Gates for any continuation: `lake build` (warning-clean) + `lake lint` when
`.lean` is touched; `blueprint/verify.sh` + `blueprint/lint.sh` (vocabulary gate
bans "stratum"/"strata") when `.tex` is touched.

## Adjacent directions (orientation only, not this phase)

ORIGAMI (`notes/Origami.md`, next queued) is the bar-joint-side
analog; the wider unqueued survey — incl. IDENT-PANEL, the nearest
neighbor — is `notes/IdeaBacklog.md`.

## Decisions made during this phase

- **W5-L4 restatement slice landed** (2026-07-24, route 2 per the blocker recon below):
  `IsNondegPencilRealization` gained its fourth conjunct (non-hub `closedNbhd`-point-LI,
  `Pencil/Motive.lean`), which forced `Graph.closedNbhd` to move from `Pencil/Chart.lean` (its
  W5-L2 birthplace) up into `Motive.lean` — the new conjunct needs it, and `Motive.lean` sits
  upstream of `Chart.lean` in the split's linear import chain, so the definition had to move rather
  than be duplicated. `PencilChartWF`'s fourth conjunct (`nbrSlotPoint` triple LI) is relativized
  to `¬ PencilHub v` to match, its sole consumer fixed one call-site (`hNbrLI v hv`), and the
  transfer mirror `linearIndepOn_pencilChartPoint_closedNbhd` lands one step shorter than its
  hub-normal sibling (no `if`-branch to unfold, since `nbrSlotPoint`'s "some" case reads
  `pencilChartPoint` directly). Of the four flagged destructuring consumers, three needed the
  mechanical arity/index fix; `dotProduct_point_eq_zero_of_mem_closedHubNbhd` turned out to need
  none (it only ever destructures `h.1`, not the conjunct that moved). Gates green (`lake build`
  warning-clean; `lake lint`; `blueprint/verify.sh`/`lint.sh`).
- **W5-L4 blocker recon landed** (2026-07-24, docs-only; canonical record: the design doc L4
  bullet's "Blocker verdict"): route 1 (derive the non-hub point-triple LI) **refuted** by a
  compiler-checked collinear `IsNondegPencilRealization` on the path `P₃` (scratch spike, not
  committed — nothing in the motive forbids coincident hinges at a degree-2 body); route 2
  **pinned**: strengthen the motive by the non-hub `closedNbhd`-point-LI conjunct (the exact
  condition making it the projective characterization of the grade-0 chart's image), relativize
  `PencilChartWF`'s fourth conjunct (sole consumer is non-hub), extend the headline theorem via
  a mirrored transfer lemma. All carried obligations checked — chart satisfiability, L3 engine,
  L5–L7 consumers, feasibility findings (K4 a fortiori, parallel-pair and N4-theta survive).
- **`Molecule/Pencil.lean` split into a `Pencil/` subdirectory** (2026-07-24 housekeeping,
  `notes/PERFORMANCE.md` split pattern; the file had grown to ~3455 lines, 2.3×+ the ~1500-LoC
  soft cap): five files, each keeping the shape of the original `/-! ## … -/` sections and every
  declaration's fully-qualified name (pure move; `checkdecls` unaffected, zero `.tex` edits) —
  `Statement.lean` (W0–W2: statement layer, transport, duality, two-pencil machinery, 837 lines),
  `Arms.lean` (W3 induction arms + the provisional bare-motive wrapper, 1033 lines),
  `Motive.lean` (W5-L0 nondegenerate motive, 94 lines), `Chart.lean` (W5-L1 `cross₃` device +
  W5-L2 grade-0 chart, 817 lines), `Engine.lean` (W5-L3 rows-polynomial engine + W5-L4 sweep
  helpers, 673 lines). Linear import chain (each imports its predecessor); the top-level
  aggregator's `import …Pencil` became `import …Pencil.Engine`. One stale in-body cross-reference
  fixed (`Chart.lean`'s W5-L1 docstring pointed at "`Molecular/Molecule/Pencil.lean` W5-L2 onward",
  now self-referential — reworded to "this file, W5-L2 below"). Gates green (`lake build`
  warning-clean 2866 jobs; `lake lint`; `blueprint/verify.sh` + `lint.sh`).
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
  `span_rigidityRows_eq_of_supportExtensor_agree`); shape + the derivation-guard corrections
  (the landed `thm:projective-invariance` is ℝ-only/`supportExtensor`-only, so the `K`-level
  transport was built fresh; `exists_cut_decomposition_of_not_twoEdgeConnected` is not
  minimality-free) in `notes/Phase39-design.md` §W3 leaf decomposition. Design notes: nondegeneracy
  needs **no `[Infinite K]`** (explicit
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
  `Graph.pencil_reduction`, node `thm:pencil-reduction`) — the reduction skeleton (dispatch on
  `hloop`/`hbase`/`hcut`/`hcontract`/`hsplit`, measure lex `(|V|, |E|)`), signature in
  `notes/Phase39-design.md` §W3 leaf decomposition. **New idiom**: nesting `Nat.strong_induction_on` for a
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
- **W1 COMPLETE — cycle pencil + coplanar wraps landed** (2026-07-24,
  `Molecular/Molecule/Pencil.lean`, nodes `lem:cycle-pencil-realization` +
  `lem:cycle-coplanar-realization`): `exists_pencilPanelRealization_cycle` — a
  `Graph.CycleData` cycle (`cy.m ≤ 4`) carries a full `HasPencilPanelRealization` rigid on
  `V(G)`, on a custom `Function.extend` framework (body `i`'s point is the concurrency of
  `C₁ = panelSupportExtensor (nrm (i-1)) (nrm i)` / `C₂ = panelSupportExtensor (nrm i) (nrm
  (i+1))`, `choose`n off `cy.vtx`; cyclic `Fin` identities by `abel`, `[NeZero cy.m]`) — chosen
  over `cycle_realization`/`ofNormals` since it drops all `Infinite K`/finiteness hypotheses.
  Honest `m`-range `3 ≤ cy.m ≤ 4` (`CycleData` floor + `exists_cycle_normals`' `m ≤ k+2 = 4`),
  not the hand-off's "only triangle". **De-dup:** `exists_coplanarPanelRealization_cycle`
  is a 2-line corollary (pencil ⇒ coplanar via `.1`), so the fragile framework exists once —
  blueprint keeps both nodes, `lem:cycle-pencil-realization` `\uses` the coplanar node +
  concurrency (math order), opposite the Lean derivation (harmless).
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
  five green nodes (the W0 statement layer, polarity bridge, and self-duality above).
  `screwComplementIso_mk_extensor`
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
