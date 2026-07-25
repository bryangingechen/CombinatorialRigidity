# Phase 39 — PENCIL: the hinge-pencil molecular conjecture (work log)

**Status:** in progress — **W0–W3 all COMPLETE**; **W5 design settled**; **W5-L0 through W5-L4 all
COMPLETE**; **W5-L5 COMPLETE modulo the carried family** (loop/base/cut arms all landed against
the (b′) `PencilPair`, wired by the successor `pencil_conjecture_of_arms_pair`
(`Pair2.lean`, node `thm:pencil-conditional-realization-pair` green);
`hcontract`/`hsplit`/`hcutPendant3` remain open hypotheses — *Decisions made* carries the full
per-leaf landing history, L5-cut-i through the dispatch shell). **L5-cut-v** (the `hcutPendant3`
discharge route): assessed GO, route PINNED (2026-07-25 recon); **v-a landed**
(`not_pencilNondegFeasible_of_triangle_two_hubs`, the triangle-`≥2`-hub infeasibility lemma);
**v-b construction recipe derived** (docs-only, 2026-07-25), its bridging/computational infra
**landed** (`Graph.neighbor_eq_of_degree_eq_three`, `Graph.not_adj_of_ne_of_mem_of_cutEdges_le_one`
in `Motive.lean`; `linearIndependent_pi_single_triple`, `exists_smul_cross₃_pi_single`,
`exists_fin3_rank_injOn` in `Engine.lean`) — the last of these fixes a genuine padding-collision
gap the recipe's first slice missed; next: the `fin_cases`-per-vertex assembly (*Hand-off*). L6/L8
are parallel
combinatorial tracks buildable now; L7 (the research core) is
last; W4 after W5 (phase opened 2026-07-23, recon-first). `Molecule/Pencil.lean` split into
`Molecule/Pencil/{Statement,Arms,Motive,Chart,Engine,Reseed,Pair,Pair2}.lean` (2026-07-24/25
housekeeping).

## Current state

**The phase stays OPEN — do NOT run the close checklist.** Two 2026-07-24 user
adjudications (verbatim, later supersedes earlier) revised the same-day "wrap up"
one: *"Let's leave the phase open and continue the work on the conjecture in this
phase. Unless there's a good reason to split here."* (coordinator assessed: no
reason to split — the phase's charter is the conjecture itself), then *"Let's end
the loop after this dispatch returns and you've confirmed its results; we'll begin
the research on the conjecture in a fresh session."*

**W0–W3 all COMPLETE; W5 design settled; W5-L0–L4 all COMPLETE; W5-L5 closed modulo the carried
family** (loop, base, and cut arms all landed against `PencilPair`, and the successor assembly
`pencil_conjecture_of_arms_pair` wires them through `Graph.pencil_reduction`; three explicit
hypotheses remain open — `hsplit` (awaits W5-L6/L7/L8), `hcontract` (a W4 obligation), and
`hcutPendant3` (L5-cut-v), *Blockers*/*Hand-off*). Per-milestone detail for every completed piece
lives in *Decisions made* below (reverse-chronological, one entry per landing) and in
`notes/Phase39-design.md`; this section stays a pointer, not a second copy.

**The W3–W5 route recon** (`notes/Phase39-design.md` §W3–W5 route recon) set the attack
order **W3 → W5 → W4**: W3 route (a) refuted at K4; route **(b′)** adopted — induction on ALL
spanning multigraphs, dispatch made total by a min-degree-3 ⟹ proper-rigid-subgraph lemma,
leaves L0–L7 (all landed). **W5's device** (design pass, `notes/Phase39-design.md` §"W5 design
pass"): final motive = the conditioned pair `PencilPair` (further `Simple`-conditioned 2026-07-24,
route (b′)); device = the grade-0 molecular chart (`Molecule/Pencil/Chart.lean`) + the
rows-polynomial engine (`Molecule/Pencil/Engine.lean`) + the D6 re-seeding lemma
(`Molecule/Pencil/Reseed.lean`), leaves **L0–L8** (L0–L4 complete; L5 closed modulo the carried
family, L5-cut-v in progress; L6/L8 parallel combinatorial tracks; L7, the research core, last).

The opening recon ran 2026-07-23; verdicts (R1–R3) below in *Opening recon verdicts*.

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
  dual of `ExtensorInPanel`); satisfiable for every graph; self-dual
  on-stratum via the landed `screwComplementIso`. Surprise: for dense
  graphs (K4, K3,3, theta(2,2,2)) the stratum *collapses* to the
  all-coplanar locus.
- **R2** — conjecture survives all exact-rational rank tests; the deep
  all-coplanar locus is deficient exactly when `2|E| < 3|V| − 3` — the
  queued "all-coplanar is rank-deficient" claim is a *bar-joint-side*
  fact, false for body-hinge on dense graphs.
- **R3** — KT Lemma 6.2 / Case II survive with pinned choices; the
  outer Thm-5.6 strip-extend, the Case-I glue (Claim 6.4), and Case
  III's Claim 6.12 span break — three open cores.

## Blockers / open questions

- **W5-L5 cut arm: L5-cut-iv COMPLETE; L5-cut-v route PINNED, v-a LANDED** (canonical record:
  `notes/Phase39-design.md` §"W5 leaf decomposition" L5 "Cut-arm route verdict" for the `Gᵢ⁺`
  repair + sub-case split, L5 "Feasibility propagation" for the triangle-`≥2`-hub infeasibility
  finding — full per-leaf landing history in *Decisions made* below). L5-cut-iv's dispatch shell
  `pencilPair_of_not_twoEdgeConnected` carries the residual sub-case (`deg_G u_c = 3`) as the
  explicit hypothesis `hcutPendant3`. L5-cut-v's chart-steering route (engine on both `G`'s and
  `H`'s charts) is ASSESSED GO (numerics + a composition spike, 2026-07-25); its gating lemma
  `not_pencilNondegFeasible_of_triangle_two_hubs` (`Motive.lean`, any field) is now **landed** —
  full leaf list v-a…v-g and composition findings: design doc L5 "Cut-arm route verdict"
  **L5-cut-v bullet**. **v-b's construction recipe (docs-only) plus its bridging + computational
  infra is landed**, including a same-session correction (a real padding-collision gap the
  recipe's first slice missed, now fixed by `exists_fin3_rank_injOn`) — design doc's "v-b
  construction recipe" sub-bullet; **next: the `fin_cases`-per-vertex assembly** (*Hand-off*).
  Feasibility propagation *as a proposition* stays open but bounded: the triangle-hub mechanism
  refutes any purely combinatorial (`≤ 3`-closedHubNbhd) feasibility criterion, while leaving L6's
  habitat claim untouched (no triangles in the no-proper-rigid habitat at `|V| ≥ 4`).
- ~~W5-L5 base-arm parallel-class blocker~~ **resolved** (2026-07-24; canonical record
  `notes/Phase39-design.md` §"W5 leaf decomposition" L5 "Blocker verdict" + "Long-run comparison").
  Rank cap real (`PencilPair` as first landed was FALSE at parallel pairs); **user adjudication
  (2026-07-24, verbatim)**: asked "With the long-run recon in: which repair route for the
  `PencilPair` motive?", the user selected "(b′) Simple-condition the pair (Recommended)".
  Landed same day: `PencilPair` restated, loop arm fixed, `not_simple_of_parallel` +
  blueprint nodes restated; base arm closed on top (*Decisions made*). New bounded L6
  sub-obligation: `G′ = G^{ab}_v` simple (design doc L6 bullet).
- ~~W5-L4 WF-conjunct blocker~~ / ~~W5-L4 shared-`fill` blocker~~ — both **resolved**
  (2026-07-24, design doc L4 bullet): the motive gained its fourth conjunct
  (route 2, landed), and `PencilSeed`'s single `fill` split into `fillHub`/`fillNbr`.
  No open question remains at either; W5-L4 closed (*Decisions made*).
- Open research questions inside the pinned W5 route, downstream of L4: **W5-L7**
  (the uniform escape certificate `r ⬝ Λ²Π̂(a) ≢ 0` on the chart — the genuinely
  new mathematics, N2 witnesses one instance), **W5-L6** (habitat feasibility
  lemma + the new `G′.Simple` sub-obligation), **W5-L8** (the k = 0 residue —
  emptiness route recommended), and W4's witness generality (unchanged, after W5).
- The full biconditional transport `ExtensorThroughPoint C q ↔
  ExtensorInPanel (screwComplementIso C) q` (design doc's W0 pin) is
  landed only as its **two forward implications** (all the self-duality
  consumes). The reverse arms need a `complementIso` involution lemma,
  not in tree — deferred; not on any critical path.

## Hand-off / next phase

**The phase stays OPEN** (the two superseding 2026-07-24 adjudications — no phase-close).

**W5-L5 is closed modulo the carried family** (loop/base/cut arms + the successor
`pencil_conjecture_of_arms_pair`, `Pencil/Pair2.lean`, node
`thm:pencil-conditional-realization-pair` green; `hcontract`/`hsplit`/`hcutPendant3` remain open
hypotheses — full detail in *Decisions made*, below).

**Next: the L5-cut-v-b main assembly, `fin_cases`-per-vertex shaped.** L5-cut-v-a is landed; v-b's
construction recipe (design doc L5-cut-v "v-b construction recipe" sub-bullet) has its bridging +
computational infra landed (2026-07-25, `Motive.lean`/`Engine.lean`, *Decisions made*): the
`Graph.degree`/`Simple` neighbour-exhaustiveness and non-adjacency facts, the `cross₃`-of-
standard-basis-vectors computation, and (this session) `exists_fin3_rank_injOn`, fixing a real
gap the first-slice recipe missed — a *single fixed* padding value collides whenever a body needs
two `none` slots at once (as few as one real member is common at `u_c`/`w1`/`w2`), and no fixed
function of the slot index alone can dodge every possible placement of the real member (a
pigeonhole fact, checked by exhaustion). **What remains** (design doc's revised "What remains"
under the same sub-bullet): for each of `u_c, w1, w2`, `obtain` the slot index of the
always-present real member (itself for `u_c`, `u_c` for `w1`/`w2`) via `(hHubSel _).2.1`, then
`fin_cases` it (3 branches pinning the literal slot layout); the hub-status case split (7
non-impossible combinations, using the landed neighbour-exhaustiveness + cardinality-exclusion +
v-a adjacency facts) determines which indices are already "real" per branch, hence the two safe
fill values `exists_fin3_rank_injOn` assigns collision-free to the (≤ 2) `none` slots; close via
`exists_smul_cross₃_pi_single` (arity 3) or a direct orthogonality argument on the concrete
positional triple (arity 1/2 — no separate permutation-invariance lemma needed, since
`exists_smul_cross₃_eq_of_linearIndependent` already takes its 3 arguments in whatever order the
branch pins down). Then **v-c**…**v-g** per the design doc's L5-cut-v leaf list (the last leaf
rewires the
shell/successor — deleting `hcutPendant3`, adding `[Infinite K]` — and restates the blueprint
node). **L6/L8 are parallel combinatorial tracks** buildable now (L6: habitat feasibility, the
`≤ 3` closed-hub-neighbourhood lemma + witness-seed construction + the `G′.Simple` sub-obligation,
design-doc L6 bullet; L8: the `k = 0` residue, emptiness route recommended). **L7 (the research
core) is last** — the uniform escape certificate `r ⬝ Λ²Π̂(a) ≢ 0`; N2 witnesses one instance. Full
leaf detail: `notes/Phase39-design.md` §"W5 leaf decomposition". Then W4 (constrained-family
Claim-6.4 analogue, G′-block witness confirmed by N3) after W5.

Gates for any continuation: `lake build` (warning-clean) + `lake lint` when `.lean` is touched;
`blueprint/verify.sh` + `blueprint/lint.sh` (vocabulary gate bans "stratum"/"strata") when `.tex`
is touched.

## Adjacent directions (orientation only, not this phase)

ORIGAMI (`notes/Origami.md`, next queued) is the bar-joint-side
analog; the wider unqueued survey — incl. IDENT-PANEL, the nearest
neighbor — is `notes/IdeaBacklog.md`.

## Decisions made during this phase

- **L5-cut-v-b bridging/computational infra landed, incl. a same-session padding-collision fix**
  (2026-07-25, `Motive.lean` + `Engine.lean`; canonical record design doc L5-cut-v "v-b
  construction recipe" sub-bullet, both the original text and the "correction found assembling
  the main witness" update): `Graph.neighbor_eq_of_degree_eq_three` / `Graph.not_adj_of_ne_of_
  mem_of_cutEdges_le_one` (`Motive.lean`, the `Graph.degree`/`Simple` bridging facts) and
  `linearIndependent_pi_single_triple` / `exists_smul_cross₃_pi_single` / `exists_fin3_rank_injOn`
  (`Engine.lean`, the `cross₃`-of-standard-basis-vectors computation plus a fix for a real gap:
  a single fixed padding value collides whenever a body needs two simultaneous `none` slots, and
  no fixed function of the slot index alone can dodge every placement of the real member — design
  doc has the full pigeonhole argument). Remaining assembly is now `fin_cases`-per-vertex shaped,
  not the flat `index`-formula first assumed — *Hand-off*. All sorry-free; gates green (build
  warning-clean + lint); axioms clean (`propext`/`Classical.choice`/`Quot.sound` only).
- **L5-cut-v-b construction recipe derived** (2026-07-25, docs-only; canonical record design doc
  L5 "Cut-arm route verdict" L5-cut-v "v-b construction recipe" sub-bullet): re-deriving witness
  (i) against the current `Chart.lean`/`Motive.lean` (F9) found the design doc's "arity sweeps"
  phrasing fragile to chain (the sweep lemmas' abstract outputs can't be certified to avoid a
  later sweep's target); the route that works is an explicit standard-basis-vector assignment via
  `cross₃_apply`'s cofactor identity. Two facts, newly derived, make it watertight: a non-hub
  `w1`/`w2` has at most one extra hub-neighbour beyond `u_c` (`PencilHub`'s own `degree ≤ 2`,
  sharper than the blanket `ncard ≤ 3` bound — resolves a genuine near-miss the naive bound would
  have missed), and v-a's exclusion is load-bearing at the specific collision "`w1`~`w2` both
  hubs". No blueprint node (infrastructure-planning, not a stated theorem).
- **L5-cut-v-a landed** (2026-07-25, `not_pencilNondegFeasible_of_triangle_two_hubs`,
  `Motive.lean`, any field): the triangle-`≥2`-hub infeasibility finding as a lemma — `y, z`
  adjacent hubs (edge `e₂`), `x` the triangle's third vertex, conclusion
  `¬ PencilNondegFeasible K G`. Conjunct 3 at `y` forces `normal y, normal z` LI, putting all three
  triangle points in their `2`-dim common perp (`finrank_toDualPerp_pair_eq`); if `x` is not a hub,
  conjunct 4 forces the three points LI (`3 > 2`, contradiction); if `x` is also a hub, conjunct 3
  at `x` forces `normal x, normal y, normal z` LI, squeezing `point x, point y` into the `1`-dim
  triple perp (`finrank_toDualPerp_triple_eq`) — yet conjunct 2 forces them LI (`2 > 1`). Two
  supporting lemmas moved `Engine.lean → Motive.lean` alongside it (same import-cone reason as
  L5-cut-i): `linearIndependent_triple_of_linearIndepOn`, `finrank_toDualPerp_triple_eq` — both
  fully general, no chart-stack dependency. No new FRICTION (clean first-try build). No blueprint
  node (unnamed technical infra, as the sibling L5-cut leaves). Gates green (build warning-clean +
  lint); axioms clean (`propext`/`Classical.choice`/`Quot.sound` only, `#print axioms`-checked).
- **L5-cut-v assessment recon — GO, route PINNED** (2026-07-25, docs-only; canonical record
  design doc L5 "Cut-arm route verdict" L5-cut-v bullet): exact-rational numerics (`K₃+pendant`,
  `C₄+pendant`, a double-star tree with a genuine 2-member promoted family; + one adversarial
  triangle-2-hub instance) and a typechecked composition spike confirm the chart-steering route
  end-to-end — both somewhere-witnesses generic (first random seed each), glued rank exact, and
  the promoted-family obstruction identically dependent exactly at the configurations
  `PencilNondegFeasible K G` excludes. Findings: discharge = shell rewire (the producer needs
  `hIH`; `hcutPendant3` deleted, not proved); `[Infinite K]` propagates to arm/successor/blueprint
  node; `ofCoord`'s `fillNbr`-coupling harmless. Leaves v-a…v-g pinned; v-a next (*Hand-off*).
- **W5-L5 successor `pencil_conjecture_of_arms_pair` landed — W5-L5 closed modulo the carried
  family** (2026-07-25, `Pencil/Pair2.lean`, node `thm:pencil-conditional-realization-pair` green):
  mirrors W3-L7's `pencil_conjecture_of_arms`, instantiating `Graph.pencil_reduction` at
  `P := PencilPair K 3` — `hloop_arm`/`hbase_arm`/`hcut_arm` wrap the three landed leaves
  (`pencilPair_of_isLoopAt`/`pencilPair_of_ncard_le_two`/`pencilPair_of_not_twoEdgeConnected`)
  exactly as W3-L7's wrap the bare-motive leaves, and `hcut_arm` re-exposes `hcutPendant3` as a
  `∀ (G : Graph α β) {V₁ e_c u_c v_c}, …` hypothesis (the cut arm's own version is scoped to a
  single ambient `G`). Concludes `PencilPair K 3 G` directly, not W3-L7's `RankHypothesis`-bridged
  form — the blueprint's `def:pencil-conditioned-pair` node already **is** `PencilPair`, so no
  extra rank-nullity bridging step earns its keep here. Blueprint restated in the same commit: the
  theorem's antecedent gained a second clause (the pendant-attachment-degree-3 configuration) the
  prior red-node prose predated (it was written before the cut-arm findings surfaced the residual).
  No new FRICTION (pure re-derivation of the W3-L7 pattern, first-try clean build). Gates green
  (build + lint + `blueprint/verify.sh`/`lint.sh`); axioms clean
  (`propext`/`Classical.choice`/`Quot.sound` only, `#print axioms`-checked).
- **W5-L5 L5-cut-iv COMPLETE — the dispatch shell landed** (2026-07-25, `Pencil/Pair2.lean`):
  `pencilPair_of_not_twoEdgeConnected` wires the three completed sub-case producers together. Bare
  half reuses `hasPencilRealization_of_not_twoEdgeConnected` unchanged (fed `hIH`'s own bare
  halves); generic half re-derives the cut decomposition and dispatches on `(G.cutEdges V₁).ncard`
  then, at the single crossing edge, on which side (if either) is a pendant singleton — **both
  orientations route through the same pendant producer** with `u_c`/`v_c`/`V₁`/`V₂` swapped, since
  the cut-vertex-set unfold is unoriented (a case the design doc's own sub-case list didn't need to
  distinguish but the shell does, since it doesn't get to choose which side is which). The residual
  sub-case 4 (`deg_G u_c = 3`) is carried as the explicit hypothesis `hcutPendant3` — the standing
  no-`sorry` idiom — shaped as the pendant producer's own premises (degree inequality flipped to an
  equality, IH-witness/rank arguments dropped) **plus `G.Simple`/`PencilNondegFeasible K G`
  antecedents**, threaded from the ambient `hSimple`/`hfeas`. **Verification catch, corrected same
  day:** the first landing dropped those two antecedents ("scoped to `G` already, costs nothing to
  omit") — backwards: omitting them makes the obligation *unsatisfiable*, not cleaner. The "net"
  graph (triangle + one pendant per vertex) meets every configuration premise at each of its three
  cuts yet is infeasible (triangle-`≥2`-hub finding), so the unconditioned conclusion is actually
  false there. Conditioning restores satisfiability (vacuous at exactly such graphs) and matches
  what the L5-cut-v chart-steering discharger needs anyway (it re-seeds `G`'s own feasibility
  witness). No new FRICTION (all infra reused verbatim); no blueprint node (unnamed technical
  infra, as the sibling sub-cases). Gates green (build warning-clean + lint); axioms clean
  (`propext`/`Classical.choice`/`Quot.sound` only, `#print axioms`-checked).
- **W5-L5 L5-cut-iv sub-case 3 landed (pendant, `deg_G u_c ≠ 3`)** (2026-07-25, new file
  `Pencil/Pair2.lean` — `Pair.lean` was at the ~1500-LoC cap, `notes/PERFORMANCE.md` — plus three
  structure-layer lemmas in `Motive.lean`): the producer
  `hasGenericPencilRealization_of_isNondegPencilRealization_induce_pendant` takes `H := G.induce V₁`'s
  IH-supplied witness (nondegeneracy + target rank) directly — no `Gᵢ⁺`, since the pendant IS the
  far side, so the closure trick is degenerate (`Gᵢ⁺ = G`). The key structural fact, landed as
  `Graph.pencilHub_iff_induce_of_degree_ne` (`Motive.lean`, with the supporting degree lemmas
  `Graph.degree_induce_eq_of_ne` / `Graph.degree_eq_degree_induce_succ`, all *general*, no
  pendant-configuration hypothesis needed): `u_c`'s pencil-hub status agrees between `H` and `G`
  whenever `G.degree u_c ≠ 3` (the sharp value where the one dropped edge can flip it) — so no
  hub-status case split anywhere in the construction, unlike sub-case 1. The one new construction
  is choosing fresh pendant data `normal v_c`/`point v_c`: `point_vc` inside `normal₁ u_c`'s
  `3`-dimensional perp, avoiding a `≤ 2`-generator cover of `H.closedNbhd u_c`'s point images
  (dimension count, `SetLike.not_le_iff_exists`, mirroring `exists_perp_linearIndependent`'s
  technique generalized from a single vector to a small span); `normal_vc` inside the joint
  `2`-dimensional perp of `point₁ u_c` and `point_vc` (`le_finrank_toDualPerp_inf`). Rank closes by
  `finrank_span_rigidityRows_cutEdge_eq` verbatim, `hlb₂ = 0` (pendant side edgeless). One new
  FRICTION `[idiom]`: `Module.finrank K (A ⊓ B)` needs an explicit `Submodule K M` ascription on
  the `⊓`-expression or elaboration fails with a baffling `Min (Type u_1)` instance error. No
  blueprint node (unnamed technical infra, as the sibling sub-cases). Gates green; axioms clean
  (`propext`/`Classical.choice`/`Quot.sound` only).
- **W5-L5 L5-cut-iv sub-case 1's repositioning/gluing half landed** (2026-07-25,
  `Pencil/Pair.lean`): `hasGenericPencilRealization_of_isNondegPencilRealization_induce_union_singleton`
  — the standalone glue taking both `Gᵢ⁺` side witnesses + `G`'s feasibility witness (IH
  consumption deferred to the dispatch shell, *Hand-off*). The 2×2 hub-status split lives in four
  slot-choice `obtain`s up front (conditional covers via `exists_subset_pair_of_ncard_le_two` +
  the `≤ 3`-minus-crossing-endpoint cardinality bounds), so the repositioning lemma is called
  ONCE; each glued conjunct then does a local insert-vs-`congr` split at the crossing endpoint
  (`LinearIndepOn.insert` off the covered `≤ 2`-generator span, one avoidance conclusion each),
  and the cut pair-LI derives in every branch from `point₁ u_c ∈ span {q₁, q₂}` (the hub branch
  pads the q-slot with `point₁ u_c` itself, per the recorded no-forced-match insight). Compiled
  warning-clean on the first build (all-mirrored patterns); no new FRICTION; no blueprint node
  (unnamed technical infra, as the sibling pieces). Gates green; axioms clean.
- **W5-L5 L5-cut-iv sub-case 1's rank half landed** (2026-07-25, `Pencil/Pair.lean` +
  `Pencil/Motive.lean` + `Molecular/Deficiency.lean`): re-deriving the full sub-case-1 assembly
  against current statements (F9) confirmed it is much larger than sub-case 2 (a 2×2 hub-status
  case split driving `exists_reposition_cross_incidences_avoiding`'s eight args, plus two `Gᵢ⁺` IH
  consumptions), so this dispatch shrank further to the **rank half** alone, mirroring how
  L5-cut-i/ii/iii each landed one infrastructure piece before any assembly. Landed:
  `hlb_induce_of_isNondegPencilRealization_induce_union_singleton` (generic in `V₁`/`e₀`/`u₀`/`w₀`,
  so the eventual assembly instantiates it once per crossing endpoint) packages the drop brick
  (`BodyHingeFramework.finrank_span_rigidityRows_le_add_of_links_subset`) + the deficiency
  bookkeeping (`Graph.deficiency_induce_union_singleton`) into exactly the `hlbᵢ` shape
  `finrank_span_rigidityRows_cutEdge_eq` wants; its own `hlinks` case-dispatch is the new
  `Graph.isLink_induce_union_singleton_of_isLink` (`Motive.lean`); side 2's own
  `(G.cutEdges V₂).ncard ≤ 1` (needed for the `Gᵢ⁺` construction on that side) derives from side
  1's via the new general `Graph.cutEdges_diff_subset` (`Deficiency.lean` — an edge crossing
  `V(G) ∖ V'` also crosses `V'`, by an endpoint-swap). Also landed the generic cover helper
  `exists_subset_pair_of_ncard_le_two` (any `ncard ≤ 2` set embeds in a two-element set, padding
  with an arbitrary element when smaller) and re-homed `ncard_closedNbhd_le_three_of_not_pencilHub`
  `Engine.lean → Motive.lean` (same import-cone precedent as its `closedHubNbhd` sibling, L5-cut-i)
  — both needed by the repositioning half, still open. One recurrence of the already-documented
  TACTICS-QUIRKS § 4 (`subst` between two free variables can pick the "wrong" one to eliminate,
  breaking a later bare-identifier reference) — no new entry, already covered. No blueprint node
  (unnamed technical infra). Gates green; axioms clean (`propext`/`Classical.choice`/`Quot.sound`
  only).
- **W5-L5 L5-cut-iv sub-case 2 landed (disjoint union)** (2026-07-25, `Pencil/Pair.lean` +
  `Pencil/Motive.lean`): the full arm assembly `pencilPair_of_not_twoEdgeConnected` (four sub-cases
  + the carried sub-case-4 hypothesis) proved too large for one sitting, so this dispatch shrank
  the deliverable to a standalone, complete producer for the easiest sub-case:
  `hasGenericPencilRealization_of_cutEdges_eq_empty` glues the two sides' IH-supplied generic
  realizations exactly like the bare arm's own `|C| = 0` branch (no `Gᵢ⁺`, no repositioning, no
  `[Infinite K]`), with the three new nondegeneracy conjuncts (adjacent-point LI, closed-hub/-
  neighbourhood LI) transferred wholesale via three new adjacency-closed-set structure lemmas
  (`Graph.degree_induce_of_forall_isLink_mem` / `Graph.closedHubNbhd_induce_of_forall_isLink_mem` /
  `Graph.closedNbhd_induce_of_forall_isLink_mem`, `Motive.lean` — no `Gᵢ⁺`-style exception, since
  there is no far vertex) composed with the sides' own conjuncts through `LinearIndepOn.congr`.
  Promoted `mem_of_induce_isLink_left`/`_right` (`Arms.lean`) from `private` to shared (now needed
  from `Pair.lean` too). One FRICTION-adjacent lift: `Graph.PencilHub` joins the
  `refine ⟨?_,?_⟩`-for-`def`s family (TACTICS-GOLF § 4) — `rw` doesn't see through it in a
  *hypothesis* either; destructure first (`obtain ⟨-, hdeg⟩ := hcon`). Sub-cases 1 and 3 plus the
  final dispatch remain — concrete guidance in *Hand-off* and design doc L5-cut-iv bullet. No
  blueprint node (unnamed technical infra, as L5-cut-i/ii/iii). Gates green; axioms clean
  (`propext`/`Classical.choice`/`Quot.sound` only).
- **W5-L5 L5-cut-iii landed — the risk leaf closed, match-free** (2026-07-25,
  `exists_reposition_cross_incidences_avoiding`, `Molecule/Pencil/Arms.lean` + a new mirror):
  the spike (run first, per the recon's own recommendation) showed the route verdict's projective
  *point matches* at non-hub endpoints are unnecessary — the conjunct-4 transfers they were routed
  through are equally served by span-avoidance inserts — so ONE uniform lemma covers all four
  hub-status combinations: the landed cross-incidence pair plus **four `∉ span` conclusions**
  (transported normal/point off fixed-side 2-generator spans; fixed normal/point off transported
  spans), each against arbitrary pair-generator slots padded with `0` when idle, over **any**
  field (no `[Infinite K]`, no polynomial method) with only four nonzero-ness hypotheses.
  Construction: all conclusions pull back through the contragredient identity to prescribed
  values of `g` on a 4-vector frame (`Basis.equiv` along the involution `0 ↔ 2, 1 ↔ 3`); each
  frame vector is an "inside a perp, off ≤ 2 spans" pick — dimension counts
  (`le_finrank_toDualPerp_single`/`_inf`, `finrank_span_pair_le`/`_triple_le`/`_insert_le`, all
  new plumbing in `Arms.lean`) + the newly mirrored any-field two-subspace exchange
  `Submodule.exists_mem_notMem_notMem` (`Mathlib/Algebra/Module/Submodule/Union.lean`, FRICTION
  `[mirrored]`). The `≤ 3` closed-hub-neighbourhood bound feeds the *consumer* (it presents each
  avoided family as a 2-generator span) — cardinality logic deferred to L5-cut-iv by design. One
  new FRICTION `[idiom]` (`linearIndependent_fin2`'s unreduced matrix-literal atoms + smul-side
  orientation). No blueprint node (unnamed technical infra, as L5-cut-i/ii). Gates green; axioms
  clean (`propext`/`Classical.choice`/`Quot.sound` only).
- **W5-L5 L5-cut-ii landed** (2026-07-25, transport + transfer bookkeeping, `Statement.lean` +
  `Motive.lean` + a mirror lemma): `IsNondegPencilRealization.mapSupport_screwEquivOfLinearEquiv`
  layers nondegeneracy conjuncts 2–4 over the landed conjunct-1 panel transport by injectivity of
  `g`/`h` alone (`LinearIndependent.map_injOn`/`LinearIndepOn.map_injOn` — no geometric content,
  since `G` itself is unchanged); the forced-hinge lemma
  `exists_smul_eq_extensor_of_extensorThroughPoint_pair` (`C ≠ 0` through an LI pair `p,q` ⟹
  `∃c≠0, c•C.val = extensor ![p,q]`) is the Meet.lean composition
  (`span_range_eq_of_extensor_eq` + `exists_smul_extensor_eq_of_mem_span_range`); four
  scale-invariance iffs for `ExtensorInPanel`/`ExtensorThroughPoint` (both the extensor slot and
  the normal/point slot), stated at the concrete grade `k = 2` (a generic `{k:ℕ}` hits `OfNat (Fin
  k) 0` indexing the witness family — caught by the build, not a new FRICTION entry); the mirror
  `LinearIndepOn.units_smul` (`Mathlib/LinearAlgebra/LinearIndependent/Basic.lean`); and the
  boundary identities `Graph.closedNbhd_induce_union_singleton` (`Gᵢ⁺.closedNbhd v = G.closedNbhd
  v` on `V₁`, no exception) / `Graph.closedHubNbhd_induce_union_singleton` (`= G.closedHubNbhd v \
  {w₀}`, the design doc's "single `u₀` exception"), via the shared subset helper
  `Graph.closedNbhd_subset_of_mem`. Two build-time frictions, both already-documented idioms (no
  new FRICTION entries): the `OfNat` trap above, and a self-referential `rw` over-rewrite
  (TACTICS-QUIRKS § 41 family) fixed by rewriting a fresh named hypothesis forward instead of
  substituting a derived equation into the goal. No blueprint node (unnamed technical infra, as
  L5-cut-i). Gates green; axioms clean (`propext`/`Classical.choice`/`Quot.sound` only).
- **W5-L5 L5-cut-i landed** (2026-07-25, the `Gᵢ⁺` structure layer, `Motive.lean` + `Bricks.lean`):
  degree lemmas `Graph.degree_induce_union_singleton_{of_mem,far}` (`≤ 1` crossing +
  `[G.Loopless]`); feasibility corollary `PencilNondegFeasible.induce_union_singleton` (the
  recon-spiked `.mono` composition); bookkeeping `Graph.deficiency_induce_union_singleton`
  (`def(Gᵢ⁺) = def(G[V₁]) + 1`, KT Lemma 3.6 applied inside `Gᵢ⁺` at its singleton far side;
  induce-idempotence minted as mirror `Mathlib/Combinatorics/Graph/Delete.lean`); the spike's drop
  brick `finrank_span_rigidityRows_le_add_of_links_subset` (`Bricks.lean` §CutEdgeBrick). Import-cone
  decision: MOVED `ncard_closedHubNbhd_le_three_…` + `dotProduct_{point,normal}_eq_zero_of_mem_
  closedNbhd` Engine → Motive (their `finrank_toDualPerp_single_eq` dependency sits upstream in
  `Statement.lean`, so `Pair.lean` keeps a chart-free cone). No blueprint node (technical infra).
- **W5-L5 cut-arm route recon** (2026-07-24, docs-only; canonical record design doc L5 "Cut-arm
  route verdict"): `Gᵢ⁺ = G.induce (Vᵢ ∪ {far})` CONFIRMED as the IH-consumption shape; the
  shared-edge rank fear dissolved by regrouping (one new drop brick, proved sorry-free in the
  scratch spike, + the landed cut assembly verbatim); transport decomposed per endpoint hub
  status; leaves L5-cut-i…v pinned. Residual: pendant-deg-3 sub-case open (no IH consumption can
  close its output gap; option (c) refuted as a full repair; chart-steering candidate recorded).
  New finding: triangle-`≥2`-hub infeasibility (refutes any `≤3`-closedHubNbhd feasibility
  criterion; L6's habitat claim untouched). Successor demand confirmed: `hcut` needed at full
  conditioned strength.
- **W5-L5 cut-arm finding + restriction infra landed** (2026-07-24, this session;
  `Molecule/Pencil/Motive.lean`, canonical finding record design doc L5 "Cut-arm finding"):
  the cut arm's generic half is gapped both ways at a `G`-degree-3 cut endpoint (input: witness
  restriction fails the fourth conjunct at a demoted hub, explicit `K_{1,3}` scenario; output:
  the glue owes the third conjunct at the promoted endpoint with no side-witness source). Landed
  the route-neutral restriction core: `Graph.PencilHub.of_le` / `Graph.closedHubNbhd_mono` /
  `Graph.closedNbhd_mono` / `IsNondegPencilRealization.mono` (explicit `hdemote` residual) /
  `PencilNondegFeasible.mono` (demotions at `H`-degree `≤ 1` bridge via the adjacent-point
  conjunct + `Graph.Inc.isPendant_of_degree_le_one`). Candidate `Gᵢ⁺` repair recorded, unverified
  (*Blockers*). No blueprint node (unnamed technical infra). Gates green; axioms clean.
- **W5-L5 base arm CLOSED** (2026-07-24, `pencilPair_of_ncard_le_two`, `Molecule/Pencil/Pair.lean`):
  mirrors the bare arm's three-way `E(G)` dispatch — bare half reused verbatim; edgeless case
  nondegenerate for free (`closedHubNbhd`/`closedNbhd` collapse to `⊆ {v}`); single-edge case a
  genuine distinct-panel/distinct-point producer (the `exists_isNondegPencilRealization_parallel_pair`
  technique, one edge) + the bare arm's `exists_independent_rigidityRows_of_edge` rank sandwich;
  parallel class vacuous via `not_simple_of_parallel`. Friction: `LinearIndepOn.singleton` needs
  an explicit `(i := v)` (FRICTION `[idiom]`).
- **W5-L5 `PencilPair` route-(b′) restatement landed** (2026-07-24, user-adjudicated — verbatim in
  *Blockers*): `PencilPair` restated to `(G.Simple → PencilNondegFeasible K G →
  HasGenericPencilRealization K n G) ∧ HasPencilRealization K n G` (`Motive.lean`, the exact
  `Theorem55.lean` pair shape); loop arm one-line fixed; `not_simple_of_parallel` landed;
  blueprint `def:pencil-conditioned-pair` + `thm:pencil-conditional-realization-pair` restated
  (`pencil.tex`, statement-change gate). All gates green.
- **W5-L5 blocker recon** (2026-07-24, docs-only; canonical record design doc L5 "Blocker
  verdict"): rank cap confirmed against definition bodies; option (c) refuted, (b) unworkable
  standalone; charter safe (the collapse is KT Thm 5.5's own non-simple phenomenon); repairs
  (a)/(b′) spike-typechecked, (b′) recommended → adjudicated + landed (entry above).
- **W5-L5 base-arm parallel-class blocker found** (2026-07-24, `Pencil/Pair.lean`): re-deriving
  the "parallel classes are infeasible" plan against the current 4-conjunct motive refuted it —
  `exists_isNondegPencilRealization_parallel_pair` is a compiler-checked feasibility witness,
  while the rank at any `≥ 2`-fold parallel class caps at `5 < 6` (full derivation design doc L5).
- **W5-L5 opened** (2026-07-24, new leaf `Molecule/Pencil/Pair.lean`, imports `Pencil.Motive`
  only): loop arm `pencilPair_of_isLoopAt` — free, the bare half + `absurd`/
  `not_pencilNondegFeasible_of_isLoopAt` for the vacuous generic half. No blueprint node.
- **W5-L4 COMPLETE** (2026-07-24; full landing history design doc §"W5 leaf decomposition" L4):
  the re-seeding lemma `exists_pencilSeed_of_nondeg` (`Pencil/Reseed.lean`) — every nondegenerate
  pencil realization is, up to per-body projective scalars, a `PencilChartWF` chart seed. Along
  the way: the WF-conjunct blocker (resolved by the motive's fourth conjunct — non-hub
  `closedNbhd`-point LI, a collinear-`P₃` counterexample refuting the derivation route), the
  shared-`fill` blocker (resolved by the `fillHub`/`fillNbr` split), both piece-3 global
  assemblies, the per-arity sweep helpers, and the fifth WF conjunct as a `units_smul` transport.
  Two promotions: TACTICS-QUIRKS §99/100; one FRICTION `[open]` (no mathlib `n ≥ 3` sibling of
  `LinearIndepOn.pair_iff`). Axioms clean throughout.
- **`Molecule/Pencil.lean` split into `Pencil/`** (2026-07-24 housekeeping, ~3455 lines → 5 files
  along the `/-! ## -/` sections, rename-free, zero `.tex` edits; `Pair.lean`/`Reseed.lean` were
  added later the same day). Linear import chain; aggregator import updated. Gates green.
- **W5 design pass landed** (2026-07-24, docs-only; canonical record design doc §"W5 design
  pass"): final motive = the conditioned pair over the feasibility-conditioned generic half;
  device = grade-0 chart + engine, D6 re-seeding keeps the motive chart-independent; N4–N6
  numerics positive; leaves W5-L0…L8 pinned with typechecked shapes.
- **W3-L7 landed — W3's shell fully closed** (2026-07-24, `pencil_conjecture_of_arms`, node
  `thm:pencil-conditional-realization` green): `Graph.pencil_reduction` at `n = 3`,
  loop/base/cut discharged internally, `hcontract`/`hsplit` as hypotheses; **PROVISIONAL** per
  the recorded GP caveat (docstring + `fmlnote:pencil-conditional-bare`) — the bare-motive arms
  are expected to need the pencil-generic conjunct once W5 lands.
- **W3-L4 CUT ARM COMPLETE** (2026-07-24, four commits, node `lem:pencil-cut-case` green): the
  bare-motive assembly `hasPencilRealization_of_not_twoEdgeConnected` + transport
  (`lem:pencil-projective-transport`), nondegeneracy (`lem:pencil-cut-nondegeneracy` — explicit
  frames, no `[Infinite K]`), and the minimality-free rank infra
  (`finrank_span_rigidityRows_cutEdge_eq` / `span_rigidityRows_eq_of_supportExtensor_agree`).
  Promoted: TACTICS-GOLF §22 (span transport along `LinearEquiv`), §23 (frame-map composition).
  Shape + derivation-guard corrections: design doc §W3 leaf decomposition.
- **W3–W5 route recon landed** (2026-07-24, docs-only; canonical record design doc §W3–W5 route
  recon): attack order W3 → W5 → W4; W3 route (a) refuted at K4 (N1), (b′) adopted; W5 genericity
  confirmed (N2); W4 keep-hinges refuted, constrained-family supported (N3).
- **W3-L1 landed** (2026-07-24, `exists_isProperRigidSubgraph_of_three_le_degree`, homed in
  `Operations.lean` for import-order reasons; blueprint §"Reduction on all spanning multigraphs"
  opened same commit, L0/L2–L7 red nodes minted).
- **W3-L2 landed** (2026-07-24, `Graph.pencil_reduction`, node `thm:pencil-reduction`): the
  dispatch skeleton on measure lex `(|V|, |E|)`. New idiom promoted: TACTICS-GOLF §11 (nesting
  `Nat.strong_induction_on` for a lex measure).
- **W2 COMPLETE** (2026-07-24, `exists_extensor_two_pencils_iff`, node
  `lem:two-pencil-extension-iff`; necessity via Plücker injectivity, `Meet.lean`). Two `[idiom]`
  friction notes lifted.
- **W1 COMPLETE** (2026-07-23/24, four landings; core
  `exists_concurrency_point_of_extensorInPanel_pair`, `lem:coplanar-hinges-concurrent`, plus the
  base pair / nonvacuity witness / cycle wraps — details in the blueprint chapter + git).
- **W0 COMPLETE** (2026-07-23, two commits: statement layer + polarity bridge + forward
  transports + self-duality; blueprint chapter opened on the R1 verdict, five green nodes).
- **Opening recon + phase-open choices** (2026-07-23): R1–R3 verdicts (canonical record
  `notes/Phase39-design.md`); the queued "all-coplanar is rank-deficient" claim corrected to a
  bar-joint-side fact; recon-first (no pinned statement or blueprint node at open, Phase-32/34/35
  precedent); higher-`d` flag discharged (self-dual stratum, chain analysis carries over —
  design doc *Higher-`d` note*).

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
