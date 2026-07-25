# Phase 39 — PENCIL: the hinge-pencil molecular conjecture (work log)

**Status:** in progress — **W0–W3 all COMPLETE**; **W5 design settled**; **W5-L0 through W5-L4 all
COMPLETE** (2026-07-24); **W5-L5 in progress**: loop arm and base arm landed against the (b′)
`PencilPair` (the parallel-class blocker found, user-adjudicated to route (b′), and repaired, all
2026-07-24 — *Decisions made*); **the cut arm's generic-half route is PINNED** (the 2026-07-24
recon verdict on the `Gᵢ⁺` repair: three of four sub-cases buildable as leaves L5-cut-i…iv, the
pendant-deg-3 residual open — *Blockers*); **L5-cut-i, L5-cut-ii, and L5-cut-iii all landed**
(2026-07-25: the `Gᵢ⁺` structure layer, the transport/transfer-bookkeeping infra, and the
strengthened repositioning lemma — the risk leaf closed match-free over any field, *Decisions
made*); **L5-cut-iv in progress** (2026-07-25: sub-case 2, the disjoint-union generic producer,
landed standalone — the full four-sub-case assembly did not fit one sitting, *Decisions made*).
Next: build L5-cut-iv's sub-case 1 (`|C| = 1`, generic — the hard part) or sub-case 3 (pendant,
`deg_G u_c ≠ 3`) (*Hand-off*); W4 after W5 (phase
opened 2026-07-23, recon-first). `Molecule/Pencil.lean` split into
`Molecule/Pencil/{Statement,Arms,Motive,Chart,Engine,Reseed,Pair}.lean` (2026-07-24 housekeeping).

## Current state

**The phase stays OPEN — do NOT run the close checklist.** Two 2026-07-24 user
adjudications (verbatim, later supersedes earlier) revised the same-day "wrap up"
one: *"Let's leave the phase open and continue the work on the conjecture in this
phase. Unless there's a good reason to split here."* (coordinator assessed: no
reason to split — the phase's charter is the conjecture itself), then *"Let's end
the loop after this dispatch returns and you've confirmed its results; we'll begin
the research on the conjecture in a fresh session."*

**W0–W3 all COMPLETE; W5 design settled; W5-L0–L4 all COMPLETE; W5-L5 mid-stream** (loop + base
arms landed; cut arm blocked at design level, *Blockers*). Per-milestone detail for every completed
piece lives in *Decisions made* below (reverse-chronological, one entry per landing) and in
`notes/Phase39-design.md`; this section stays a pointer, not a second copy.

**The W3–W5 route recon** (`notes/Phase39-design.md` §W3–W5 route recon) set the attack
order **W3 → W5 → W4**: W3 route (a) refuted at K4; route **(b′)** adopted — induction on ALL
spanning multigraphs, dispatch made total by a min-degree-3 ⟹ proper-rigid-subgraph lemma,
leaves L0–L7 (all landed). **W5's device** (design pass, `notes/Phase39-design.md` §"W5 design
pass"): final motive = the conditioned pair `PencilPair` (further `Simple`-conditioned 2026-07-24,
route (b′)); device = the grade-0 molecular chart (`Molecule/Pencil/Chart.lean`) + the
rows-polynomial engine (`Molecule/Pencil/Engine.lean`) + the D6 re-seeding lemma
(`Molecule/Pencil/Reseed.lean`), leaves **L0–L8** (L0–L4 complete; L5 mid-stream; L6/L8 parallel
combinatorial tracks; L7, the research core, last).

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

- **W5-L5 cut arm (generic half): route PINNED, one residual sub-case OPEN** (2026-07-24 recon
  verdict; canonical record — sub-case split, spike-proved drop brick, leaf list L5-cut-i…v,
  the two refuted dodges, and the new triangle-hub infeasibility finding:
  `notes/Phase39-design.md` §"W5 leaf decomposition" L5 "Cut-arm route verdict"). The `Gᵢ⁺ =
  G.induce (Vᵢ ∪ {far endpoint})` repair is CONFIRMED wherever it applies: the feared
  shared-edge rank assembly dissolves by regrouping (consume the IH rank at `Gᵢ⁺`, drop the cut
  edge's rows — a new small brick, proved sorry-free in the recon's spike — and the landed
  `finrank_span_rigidityRows_cutEdge_eq` closes verbatim), and the matching transport decomposes
  per crossing-endpoint hub status. **The risk-carrying leaf is CLOSED** (L5-cut-iii, 2026-07-25):
  the strengthened repositioning lemma landed in a *match-free avoidance form* — the recon's
  point-match mechanism proved unnecessary, and the uniform statement holds over **any** field
  (no `[Infinite K]`; *Decisions made*). Sub-cases `|C| = 0`, two-sided `|C| = 1`, and pendant
  with `deg_G u_c ≠ 3` are buildable now — **sub-case `|C| = 0` landed** (L5-cut-iv, 2026-07-25, a
  standalone producer; *Decisions made*); sub-cases 1 (two-sided `|C| = 1`) and 3 (pendant,
  `deg_G u_c ≠ 3`) plus the final dispatch remain (*Hand-off*). **OPEN residual: the pendant sub-case at `deg_G u_c = 3`** (`G = H + pendant`
  at a degree-3 hub — exactly the `K_{1,3}` configuration; not vacuous, `K₃ + pendant` is simple
  + feasible): no IH consumption can close its output gap (sharpened this recon), motive option
  (c) is REFUTED as a full repair (input half only), and the candidate is a chart-steering route
  (engine on both `G`'s and `H`'s charts) whose two somewhere-witness constructions need a
  numerics-first assessment before building. Feasibility propagation *as a proposition* stays
  open but bounded: the new **triangle-`≥2`-hub infeasibility** mechanism refutes any purely
  combinatorial (`≤ 3`-closedHubNbhd) criterion, while leaving L6's habitat claim untouched (no
  triangles in the no-proper-rigid habitat at `|V| ≥ 4`).
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

**Next: continue L5-cut-iv** — the arm assembly `pencilPair_of_not_twoEdgeConnected` did NOT fit
one sitting (four sub-cases + the carried hypothesis is a very large single theorem), so this
session shrank the deliverable per the standing scope-to-fit discipline: **sub-case 2 (`|C| = 0`,
disjoint union) landed as a standalone, complete producer**
`hasGenericPencilRealization_of_cutEdges_eq_empty` (`Pair.lean`), plus the three general
disjoint-sides structure lemmas it needs (`Graph.degree_induce_of_forall_isLink_mem` /
`Graph.closedHubNbhd_induce_of_forall_isLink_mem` / `Graph.closedNbhd_induce_of_forall_isLink_mem`,
`Motive.lean` — *Decisions made*). **Two pieces remain before the dispatch shell can close:**

- **Sub-case 1** (`|C| = 1`, both sides `≥ 2` — the hard part, not yet attempted): consume the
  IH's generic half at `Gᵢ⁺` (not `G.induce Vᵢ`) on both sides (mirrors L5-cut-i's structure
  layer); get `hlbᵢ` via the drop brick `finrank_span_rigidityRows_le_add_of_links_subset`;
  case-split `by_cases hu_hub : G.PencilHub u_c` / `by_cases hv_hub : G.PencilHub v_c` (2×2, the
  "complementary, never simultaneous" verdict) to pick
  `exists_reposition_cross_incidences_avoiding`'s (`Arms.lean`) args per branch — its four
  avoidance conclusions map to the glued conjuncts as its docstring records (steering 1 → third
  conjunct at `u_c` when `v_c` is a hub, steering 2 → third conjunct at `v_c` when `u_c` is a hub,
  avoidance 3 → fourth conjunct at `u_c` + the cut hinge's pair-LI via `q₁ := point₁⁺ u_c` ALWAYS
  (never junk — via `LinearIndependent.pair_iff'`, regardless of hub status), avoidance 4 → fourth
  conjunct at `v_c`); pad idle slots with `0`; present each avoided family as a two-generator span
  — closed-hub-neighbourhood targets via `ncard_closedHubNbhd_le_three_of_isNondegPencilRealization`
  on `G`'s own feasibility witness minus the crossing endpoint (needs a new small "cover an
  `ncard ≤ 2` set by two vectors" helper, not yet built), closed-neighbourhood targets via
  `ncard_closedNbhd_le_three_of_not_pencilHub` (currently in `Engine.lean` — re-home to
  `Motive.lean` first, the L5-cut-i import-cone precedent); transport by
  `IsNondegPencilRealization.mapSupport_screwEquivOfLinearEquiv`; take the fresh cut hinge from
  `exists_extensor_two_pencils`; rank per the route verdict's 1a regrouping. Full derivation:
  `notes/Phase39-design.md` §"W5 leaf decomposition" L5-cut-iv bullet.
- **Sub-case 3** (pendant, `deg_G u_c ≠ 3`): no `Gᵢ⁺` (the pendant IS the far side); feasibility
  restricts by blanket `.mono` (no demotion — verdict item 3); the one new construction is
  choosing fresh pendant data (`point v_c`/`normal v_c`) off the bad span, dimension-counting as
  `exists_perp_linearIndependent` already does; rank is the landed
  `finrank_span_rigidityRows_cutEdge_eq` verbatim (pendant side edgeless, `hlb₂ = 0`).

Then the dispatch shell: case-split on `(G.cutEdges V₁).ncard = 0` vs. the single crossing edge,
then on `|V₂| = 1` (sub-case 3) vs. `≥ 2` (sub-case 1) vs. `deg_G u_c = 3` (sub-case 4, carried as
an explicit hypothesis — the standing no-`sorry` idiom; phrase its shape to match the chart-steering
route's two somewhere-witness conclusions, design doc sub-case 4). **Do not build L5-cut-v** (the
pendant-deg-3 residual) until its two chart-steering somewhere-witnesses get a numerics-first
assessment (a separate small recon/numerics dispatch — design doc, sub-case 4).

**After the cut arm**: the successor assembly `pencil_conjecture_of_arms_pair` (mirrors
`pencil_conjecture_of_arms`, W3-L7, wiring `pencilPair_of_isLoopAt` + `pencilPair_of_ncard_le_two`
+ the cut arm + `hcontract`/`hsplit` through `Graph.pencil_reduction`) — red node
`thm:pencil-conditional-realization-pair` already restated in `pencil.tex`. **L6/L8 are parallel
combinatorial tracks** buildable now (L6: habitat feasibility, the `≤ 3` closed-hub-neighbourhood
lemma + witness-seed construction + the `G′.Simple` sub-obligation, design-doc L6 bullet; L8: the
`k = 0` residue, emptiness route recommended). **L7 (the research core) is last** — the uniform
escape certificate `r ⬝ Λ²Π̂(a) ≢ 0`; N2 witnesses one instance. Full leaf detail:
`notes/Phase39-design.md` §"W5 leaf decomposition". Then W4 (constrained-family Claim-6.4
analogue, G′-block witness confirmed by N3) after W5.

Gates for any continuation: `lake build` (warning-clean) + `lake lint` when `.lean` is touched;
`blueprint/verify.sh` + `blueprint/lint.sh` (vocabulary gate bans "stratum"/"strata") when `.tex`
is touched.

## Adjacent directions (orientation only, not this phase)

ORIGAMI (`notes/Origami.md`, next queued) is the bar-joint-side
analog; the wider unqueued survey — incl. IDENT-PANEL, the nearest
neighbor — is `notes/IdeaBacklog.md`.

## Decisions made during this phase

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
  `lem:two-pencil-extension-iff`): existence ⊕ necessity; necessity via Plücker injectivity
  `span_range_eq_of_extensor_eq` (`Meet.lean`). Two `[idiom]` friction notes lifted.
- **W1 COMPLETE** (2026-07-23/24, four landings): the geometric core
  `exists_concurrency_point_of_extensorInPanel_pair` (`lem:coplanar-hinges-concurrent`, two
  coplanar hinges automatically share a concurrency point); the base pair
  `exists_linearIndependent_extensor_pair_through_point` + two-body realization
  `exists_pencilPanelRealization_parallel_pair`; the nonvacuity witness
  `exists_hasPencilPanelRealization_witness` (no blueprint node, Lean-only certificate); the
  cycle wraps `exists_pencilPanelRealization_cycle` (+ 2-line coplanar corollary), honest range
  `3 ≤ cy.m ≤ 4`, `Function.extend` framework dropping all `Infinite K` hypotheses.
- **W0 COMPLETE** (2026-07-23, two commits): statement layer + polarity bridge + two forward
  transport implications + self-duality (`#print axioms` clean); blueprint chapter opened on the
  R1 verdict (five green nodes; `screwComplementIso_mk_extensor` reused
  `lem:panel-hinge-dual-molecular` per the additive-successor discipline).
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
