# Phase 39 — PENCIL: the hinge-pencil molecular conjecture (work log)

**Status:** in progress — **W0–W3 all COMPLETE**; **W5 design settled**; **W5-L0 through W5-L4 all
COMPLETE**; **W5-L5 COMPLETE modulo the carried family** (loop/base/cut arms all landed against
the (b′) `PencilPair`, wired by the successor `pencil_conjecture_of_arms_pair`
(`Pair2.lean`, node `thm:pencil-conditional-realization-pair` green);
`hcontract`/`hsplit`/`hcutPendant3` remain open hypotheses — *Decisions made* carries the full
per-leaf landing history, L5-cut-i through the dispatch shell). **L5-cut-v** (the `hcutPendant3`
discharge route): assessed GO, route PINNED (2026-07-25 recon); **v-a landed**
(`not_pencilNondegFeasible_of_triangle_two_hubs`); **v-b LANDED** (2026-07-25,
`exists_coord_linearIndependent_pencilChartPoint_of_pendant_deg3` — the somewhere-witness on
`G`'s chart, new file `Molecule/Pencil/Witness.lean`, closed via the abstract padding lemma
`exists_injective_extension_of_isFin3SelectorOf`); **v-c LANDED** (2026-07-25,
`exists_coord_linearIndependent_pencilChartNormal_of_pendant_deg3`, same file — witness (ii) on
`H := G.induce V₁`'s chart, reusing v-b's toolkit + combinatorics); **v-d extraction gadget +
WF-flattening witnesses LANDED** (2026-07-25 gadget, `Engine.lean`; 2026-07-29 flattening bridge,
new file `Molecule/Pencil/Steer.lean`); next: **rest of v-d** (`fillNbr` re-choice + the
`exists_fin3_rank_injOn` retirement call — *Hand-off*).
L6/L8 are parallel
combinatorial tracks buildable now; L7 (the research core) is
last; W4 after W5 (phase opened 2026-07-23, recon-first). `Molecule/Pencil.lean` split into
`Molecule/Pencil/{Statement,Arms,Motive,Chart,Engine,Reseed,Pair,Pair2}.lean` (2026-07-24/25
housekeeping; `Witness.lean` added 2026-07-25).

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
family, L5-cut-v-a/-b/-c landed, v-d next; L6/L8 parallel combinatorial tracks; L7, the research
core, last).

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
  **L5-cut-v bullet**. **v-a/-b/-c all LANDED** (`Molecule/Pencil/Witness.lean`); the witness (ii)
  lemma (v-c) reuses v-b's toolkit + combinatorics, adding the pendant config `hVG` so `v_c` is a
  degree-`1` non-hub (never in a family — matching the design's "promoted families are
  `fillNbr`-free" analysis). **v-d's extraction gadget LANDED** (2026-07-25, `Engine.lean`:
  `exists_polynomial_ne_zero_of_linearIndependent_pencilChart{Point,Normal}` + the
  `pencilChartNormalPoly`/`nbrSlotPointPoly` mirror). **v-d WF-flattening witnesses LANDED**
  (2026-07-29, new file `Molecule/Pencil/Steer.lean`: `PencilSeed.toCoord` + `pencilChartPoint`/
  `hubSlotNormal` coincidence + `pencilChartWF_standing_ofCoord_toCoord`, the four `fillNbr`-free
  conjuncts at the flattening). `exists_fin3_rank_injOn` (`Engine.lean`) still unconsumed (neither
  gadget nor flattening bridge used it); retirement call still deferred (the `fillNbr` re-choice may
  want it — decide then, with the deletion-hygiene sweep). **Next: rest of v-d** (`fillNbr`
  re-choice, *Hand-off*).
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

**Next: rest of L5-cut-v-d.** The **extraction gadget LANDED** (2026-07-25, `Engine.lean`): the two
chart-family steering gadgets `exists_polynomial_ne_zero_of_linearIndependent_pencilChart{Point,
Normal}` (thin `[Field K]`-only specializations of the maximal-minor engine
`exists_polynomial_ne_zero_of_linearIndependent_at_reindex` — no `[Infinite K]`; that enters only in
the product-route workhorse downstream) + the "`cross₃Poly` cases" mirror `pencilChartNormalPoly`
(with `nbrSlotPointPoly`) and its eval identity. The **WF-flattening witnesses LANDED** (2026-07-29,
new file `Molecule/Pencil/Steer.lean`, imports `Pencil.Engine`): `PencilSeed.toCoord` (the
`fillNbr`-free flattening onto the engine's `α × Fin 4 × Fin 4` space), the point-side coincidence
lemmas (`pencilChartPoint_ofCoord_toCoord`, `hubSlotNormal_ofCoord_toCoord`), and
`pencilChartWF_standing_ofCoord_toCoord` (the four `fillNbr`-free `PencilChartWF` conjuncts at the
flattening — the sole `fillNbr`-reading fourth conjunct is deliberately excluded, supplied by (1)
below). **Still owed for v-d** (the smallest next commit is the first): (1) the **post-steering
`fillNbr` re-choice lemma** — at deg-`≤1` non-hub bodies re-choose `fillNbr` (the `nbrSel`-unassigned
slots) so `PencilChartWF`'s fourth conjunct holds, without disturbing the point-side / steered
conditions (`pencilChartPoint`/`hubSlotNormal` never read `fillNbr`); (2) the
**`exists_fin3_rank_injOn` retirement call** (`Engine.lean`, still unconsumed — neither the gadget
nor the flattening bridge used it; retire with the tree-wide deletion-hygiene sweep IF (1) does not
want it, else keep). `Steer.lean` is the home for the remaining steering pieces; v-e/v-f will add the
`Pencil.Witness` import there when they consume the somewhere-witnesses. Then **v-e**…**v-g** per the
design doc's L5-cut-v leaf list (the last leaf rewires the
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

- **L5-cut-v-d WF-flattening witnesses LANDED — standing WF conditions at the `fillNbr`-free
  flattening** (2026-07-29, new file `Molecule/Pencil/Steer.lean`, imports `Pencil.Engine`;
  composition finding (3)): `PencilSeed.toCoord` flattens a re-seeded seed onto the engine's
  `α × Fin 4 × Fin 4` space, dropping the independent `fillNbr` (`PencilSeed.ofCoord` re-derives it
  as `fillHub`). As `pencilChartPoint`/`hubSlotNormal` never read `fillNbr`, points coincide
  (`pencilChartPoint_ofCoord_toCoord`) and the four `fillNbr`-free `PencilChartWF` conjuncts transfer
  (`pencilChartWF_standing_ofCoord_toCoord`); the fourth (non-hub `nbrSlotPoint` LI, sole
  `fillNbr`-reader) is left to the `fillNbr` re-choice — NOT carried here (unsatisfiable at deg-`≤1`
  non-hubs). `Fin.cons` constant-motive ascription → TACTICS-QUIRKS § 96 (broadened from `Fin.snoc`).
  No blueprint node (unnamed infra). Gates green; axioms clean.
- **L5-cut-v-d extraction gadget LANDED — the chart-family steering gadgets** (2026-07-25,
  `Engine.lean`): `exists_polynomial_ne_zero_of_linearIndependent_pencilChart{Point,Normal}` turn a
  chart point/normal subfamily LI at one seed into a seed-polynomial nonzero there whose non-roots
  keep it LI (the "nonvanishing somewhere" input the product-route workhorse consumes). Both are
  thin `[Field K]`-only instances of the maximal-minor engine
  `exists_polynomial_ne_zero_of_linearIndependent_at_reindex` (`φ := refl`,
  `e := finCongr (Module.finrank_fin_fun K)`; `[Infinite K]` enters only downstream). New
  "`cross₃Poly` cases" mirror `pencilChartNormalPoly` (+ `nbrSlotPointPoly`) + eval identity.
  No new FRICTION (reused existing eval-mirror + engine-hookup patterns). `exists_fin3_rank_injOn`
  still unconsumed. Gates green; axioms clean.
- **L5-cut-v-c LANDED — the somewhere-witness on `H := G.induce V₁`'s chart** (2026-07-25,
  `exists_coord_linearIndependent_pencilChartNormal_of_pendant_deg3`, `Molecule/Pencil/Witness.lean`):
  the pinned witness (ii). Reuses v-b's toolkit (`exists_injective_extension_of_isFin3SelectorOf`
  for the three chart points → `±e₃/e₂/e₁`) and v-b's exact combinatorics (`idx`, the `≤ 3`
  cardinality bound, the v-a triangle exclusion, `huniq_*`), plus two small
  `LinearIndepOn`/`LinearIndependent`-of-scaled-distinct-basis engines. Two additions over v-b:
  the demoted `u_c`'s forced normal `= cross₃` of the three points is steered to `±e_0`
  (`exists_smul_cross₃_eq_of_linearIndependent`, `nbrSel u_c` fully assigned since
  `H.closedNbhd u_c = {u_c, w₁, w₂}`), and the family sets are `G.closedHubNbhd v` (stronger than
  `H`'s; the consumer restricts by `LinearIndepOn.mono`). **Statement refinement, flagged:** carries
  the pendant config `hVG : V(G) = V₁ ∪ {v_c}` (matching sub-case-3's producer, in scope at the
  v-g discharge), making `v_c` a degree-`1` non-hub so it never enters a family — this is exactly
  the design's composition-finding assumption ("every promoted family is `fillNbr`-free"), which
  fails if `v_c` is a hub. `exists_fin3_rank_injOn` still unconsumed (retirement deferred to v-d).
  No new FRICTION (all patterns reused / `LinearIndepOn.congr` + `Pi.basisFun` composition). No
  blueprint node (unnamed technical infra, as the sibling L5-cut leaves). Gates green (build
  warning-clean + lint); axioms clean (`propext`/`Classical.choice`/`Quot.sound`).
- **L5-cut-v-b LANDED — the somewhere-witness on `G`'s chart** (2026-07-25,
  `exists_coord_linearIndependent_pencilChartPoint_of_pendant_deg3`, new file
  `Molecule/Pencil/Witness.lean` + aggregator import; canonical construction record design doc
  L5-cut-v "v-b construction recipe" sub-bullet, "the main assembly, landed"): the pinned witness
  (i) exactly. Construction deviation from the mapped plan (F9 re-derivation): one abstract padding
  lemma (`exists_injective_extension_of_isFin3SelectorOf`, 8-shape selector split) replaces the
  `fin_cases`-per-vertex skeleton; `exists_fin3_rank_injOn` unconsumed (retirement deferred).
  One new FRICTION `[idiom]` → TACTICS-QUIRKS § 101 (quantified `decide` whnf blow-up). Gates
  green (build warning-clean + lint); axioms clean (`propext`/`Classical.choice`/`Quot.sound`).
- **L5-cut-v-a landed** (2026-07-25, `not_pencilNondegFeasible_of_triangle_two_hubs`,
  `Motive.lean`, any field): the triangle-`≥2`-hub infeasibility finding as a lemma (`y, z`
  adjacent hubs, `x` the third vertex ⟹ `¬ PencilNondegFeasible K G`, by squeezing the triangle
  points into the `2`- or `1`-dim common perp of the hub normals against conjunct 2/4). Directly
  consumed by v-b/v-c. Supporting `linearIndependent_triple_of_linearIndepOn` /
  `finrank_toDualPerp_triple_eq` moved `Engine.lean → Motive.lean`. Full derivation: design doc.
- **Older W5-L5 / W0–W4 entries (one-lined; canonical detail in `notes/Phase39-design.md` + git).**
  v-b bridging/recipe (2026-07-25): the `cross₃`-of-basis + `Graph`/`Simple` bridging infra +
  padding-collision analysis. L5-cut-v assessment recon (2026-07-25, GO/route PINNED). W5-L5
  successor `pencil_conjecture_of_arms_pair` (`Pair2.lean`, node
  `thm:pencil-conditional-realization-pair` green, `hcutPendant3` carried). L5-cut-iv shell
  `pencilPair_of_not_twoEdgeConnected` + sub-cases 3/1(rank+glue)/2 (`Pair.lean`/`Pair2.lean`,
  the `Gᵢ⁺`/pendant producers). L5-cut-iii `exists_reposition_cross_incidences_avoiding`
  (`Arms.lean`), L5-cut-ii `IsNondegPencilRealization.mapSupport_screwEquivOfLinearEquiv`, L5-cut-i
  the `Gᵢ⁺` structure layer (`Motive.lean`/`Bricks.lean`). Cut-arm route recon + finding +
  restriction infra (`.mono`/`PencilHub.of_le`/`closed{Hub,}Nbhd_mono`). Base arm
  `pencilPair_of_ncard_le_two`; `PencilPair` route-(b′) restatement (user-adjudicated) +
  `not_simple_of_parallel`; blocker/parallel-class recons; loop arm `pencilPair_of_isLoopAt`.
  W5-L4 `exists_pencilSeed_of_nondeg` (`Reseed.lean`); `Pencil.lean`→`Pencil/` split; W5 design
  pass. W3: L7 `pencil_conjecture_of_arms` (node `thm:pencil-conditional-realization`, PROVISIONAL),
  L4 cut arm `hasPencilRealization_of_not_twoEdgeConnected` (node `lem:pencil-cut-case`), route
  recon, L1 `exists_isProperRigidSubgraph_of_three_le_degree`, L2 `Graph.pencil_reduction` (node
  `thm:pencil-reduction`). W2 `exists_extensor_two_pencils_iff`; W1
  `exists_concurrency_point_of_extensorInPanel_pair`; W0 statement layer + self-duality; opening
  recon (R1–R3). Promotions: TACTICS-GOLF §11/§22/§23, TACTICS-QUIRKS §99/§100/§101.

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
