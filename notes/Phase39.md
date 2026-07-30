# Phase 39 — PENCIL: the hinge-pencil molecular conjecture (work log)

**Status:** in progress — phase stays OPEN (2026-07-24/2026-07-30 user adjudications, quoted
verbatim in *Current state*). W0–W3 and W5-L0–L6 are all COMPLETE; the `hsplit` build sequence
(W5-L7c-1…6) is CLOSED IN FULL (2026-07-30), and `hfresh`'s mechanical counting discharge
(residue (iv)) landed the same day. Only three items remain, all carried by the landed successor
`pencil_conjecture_of_hcontract_hK_hbareSplit_of_card` (`Molecule/Pencil/Escape.lean`):
`hcontract` (W4), kernel `hK`, and kernel `hbareSplit` — see *Hand-off*.

## Current state

**The phase stays OPEN** — two 2026-07-24 user adjudications (verbatim, later supersedes
earlier) settled this: *"Let's leave the phase open and continue the work on the conjecture in
this phase. Unless there's a good reason to split here."*, then *"Let's end the loop after this
dispatch returns and you've confirmed its results; we'll begin the research on the conjecture in
a fresh session."* **2026-07-30 (verbatim):** *"Let's wrap up this session when we finish L6 and
leave the research core to a fresh session."* **2026-07-30 session check-in (verbatim, settled
the L7 recon's "Route options" and the L6a-safe-exists rigid-half open item):** kernel (K) route
— *"Route 3: build now"*; L6a-safe-exists rigid `k=0` half — *"Prove now"* (both since
discharged — see *Decisions made*).

W0–W3 and W5-L0–L6 are all COMPLETE (L6a-safe-exists closed in full both halves; L6b/L6d landed).
**The W5-L7 arc is now CLOSED**: L7a, L7b, and L7c-1…6 all landed (`Molecule/Pencil/Escape.lean`/
`Base.lean`) — the `hsplit` build sequence is discharged in full — and **`hfresh`'s mechanical
counting discharge (residue (iv)) also landed**: `freshEdgeSupply_of_card_lt_of_noRigid_of_
degree_two` supplies it from a `β`-cardinality headroom bound (the pencil-habitat analogue of
`Graph.freshEdgeSupply_of_card_lt`), and `pencil_conjecture_of_hcontract_hK_hbareSplit_of_card`
(`Escape.lean`) is the resulting consumer-facing headline, carrying exactly `hcontract` (W4),
`hK` (kernel (K)), and `hbareSplit` (kernel (K-bare)) — the three remaining open items, detailed
in *Hand-off*. File layout: `Molecule/Pencil.lean` split into
`Molecule/Pencil/{Statement,Arms,Motive,Chart,Engine,Reseed,Witness,Steer,Pair,Pair2,Escape,
Base}.lean`. Full per-leaf history: `notes/Phase39-design.md` §"W5 leaf decomposition" +
§"W5-L7 research recon"; this section stays a pointer, not a second copy.

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

- ~~W5-L5 cut arm (L5-cut-iv/v)~~ **CLOSED** (2026-07-25/29) — all four cut sub-cases discharge
  internally; the residual `hcutPendant3` DISCHARGED inline (v-g part 2, `Pair2.lean`). One
  residual note stands: feasibility propagation *as a proposition* is refuted for any purely
  combinatorial (`≤3`-closedHubNbhd) criterion (`not_pencilNondegFeasible_of_triangle_two_hubs`),
  but this doesn't touch L6's own habitat claim.
- ~~W5-L5 base-arm parallel-class blocker~~ **resolved** (2026-07-24) — user adjudicated route
  (b′) (Simple-condition `PencilPair`); base arm closed on top.
- ~~W5-L4 WF-conjunct / shared-`fill` blockers~~ **resolved** (2026-07-24) — motive gained its
  fourth conjunct; `fill` split into `fillHub`/`fillNbr`.
- ~~W5-L6 split-arm feasibility (safe-vertex existence)~~ **CLOSED** (2026-07-29/30) — both
  deficiency regimes' safe-vertex existence PROVEN minimality-free; the L6/L7 coupling is benign
  (KT Case III already splits a safe vertex, Lemma 6.13/4.6).
- ~~`hfresh`'s mechanical discharge~~ **CLOSED** (2026-07-30) — `freshEdgeSupply_of_card_lt_of_
  noRigid_of_degree_two` + `pencil_conjecture_of_hcontract_hK_hbareSplit_of_card` (`Escape.lean`).
- **Open: kernels (K) and (K-bare), and W4 (`hcontract`)** — the entire remaining work of the
  phase; see *Hand-off* for the per-item route and the `notes/Phase39-design.md` pointers.
- The full biconditional transport `ExtensorThroughPoint C q ↔ ExtensorInPanel (screwComplementIso
  C) q` (design doc's W0 pin) is landed only as its two forward implications; the reverse arms
  need a `complementIso` involution lemma, not in tree — deferred, not on any critical path.

## Hand-off / next phase

**The phase stays OPEN** (the 2026-07-24 adjudications — no phase-close; see *Current state*).

**`hsplit` is CLOSED IN FULL** (W5-L7c-1…6, all landed 2026-07-30 — one-line verdicts in
*Decisions made*; full detail `notes/Phase39-design.md` §"W5-L7 research recon" "L7c
decomposition"), and **`hfresh`'s mechanical discharge (residue (iv)) is CLOSED too** (same day).
The landed successor `pencil_conjecture_of_hcontract_hK_hbareSplit_of_card`
(`Molecule/Pencil/Escape.lean`) wraps `pencil_conjecture_of_hcontract_hK_hbareSplit` and carries
exactly three remaining open items — **next concrete commit: pick any one, none blocks another**:

- **`hcontract`** (W4) — the constrained-family Claim-6.4 analogue; not yet attacked (design doc
  §"W4 route (third core): cluster refutation + the constrained-family survivor (N3)"; the last
  W-level leaf, scheduled after W5 closes).
- **`hK`** (kernel (K), research) — the escape `≢ 0` uniformity kernel. **Routes 1 and 2
  (as pinned) are REFUTED** (2026-07-30 gate + follow-up recon: locality fails — the
  stress is globally supported and the escape's zero locus moves with the far graph at
  identical local data; the landed span device needs a spanning family the pin caps at 5).
  The follow-up **non-constancy recon returned PARTIAL** with a corank stratification:
  `index(G) ≥ 1` habitats get the escape *automatically* modulo a new seed-quality
  obligation (K-shared); the hard kernel narrows to **(K-tight)** — tight (`5|E| =
  6(|V|−1)`), both chain ends hubs, provably 2-connected — where no landed-brick route
  closes it; the one identified enabling technology is stress-as-chart-rational-function
  infrastructure. **User adjudication owed**: keep carrying `hK` (recommended, zero
  effort) vs. commission that infrastructure (research-scale) vs. literature hunt.
  Design doc §"W5-L7 research recon" "(K) route-1 gate" + "(K) non-constancy recon".
- **`hbareSplit`** (kernel (K-bare), research) — the bare-half-off-feasibility kernel. The
  numerics gate is SUPPORTED (parity with (K): certified bare-target attainment at every
  infeasible gadget tried, both deficiency branches), but the Lean discharge itself is open — the
  extension route, plus the def-equal branch's caveat (the re-inserted point must avoid the
  deleted hinge's line, an in-stratum genericity side condition) — design doc residue (ii).

Gates for any continuation: `lake build` (warning-clean) + `lake lint` when `.lean` is touched;
`blueprint/verify.sh` + `blueprint/lint.sh` (vocabulary gate bans "stratum"/"strata") when `.tex`
is touched.

## Adjacent directions (orientation only, not this phase)

ORIGAMI (`notes/Origami.md`, next queued) is the bar-joint-side
analog; the wider unqueued survey — incl. IDENT-PANEL, the nearest
neighbor — is `notes/IdeaBacklog.md`.

## Decisions made during this phase

Reverse-chronological, one line per landing; full derivations live in git and
`notes/Phase39-design.md` (per-decision pointer where the design doc has a named section).

- **(K) non-constancy recon — PARTIAL; kernel narrowed to (K-tight); adjudication owed**
  (2026-07-30, docs-only; exact-ℚ scripts `scratchpad/escape/n9.py`, untracked) — corank
  stratification by `index(G) = 5|E| − 6(|V|−1)` (N7's "nullity 1 general Case-III fact"
  CORRECTED — θ(4,4,3) is a both-ends-hubs corank-2 witness); `dim R_a ≥ 2` makes the escape
  automatic (boundary-load derivation, N9a-consistent, KT re-pin owed), so `index ≥ 1` trades
  the escape for (K-shared) and the hard kernel is (K-tight) — 2-connected, canonical-move
  numerics complete (N9b), but NO provable route in landed machinery. Design doc §"W5-L7
  research recon" "(K) non-constancy recon".
- **(K) route-1 gate FIRED — locality REFUTED, NO-GO** (2026-07-30, docs-only; exact-ℚ scripts
  `scratchpad/escape/localtest*.py`, untracked) — with identical radius-1 chain data the escape's
  zero locus moves with the far graph (within-habitat and cross-habitat; stress supported on every
  edge; sensitivity to a single distance-4 vertex move), killing route 1 and route 2's pointwise
  reuse; (K) reduced instead to *stress non-constancy* via the local 1-dim `S^⊥` lever. Design doc
  §"W5-L7 research recon" "(K) route-1 gate".
- **`hfresh`'s mechanical discharge LANDED — residue (iv) CLOSED** (2026-07-30, `Escape.lean`) —
  `freshEdgeSupply_of_card_lt_of_noRigid_of_degree_two` (the pencil-habitat analogue of
  `Graph.freshEdgeSupply_of_card_lt`, edge bound from `Graph.edgeBound_of_noRigid_of_degree_two`
  in place of minimality) plus the consumer-facing headline
  `pencil_conjecture_of_hcontract_hK_hbareSplit_of_card`, mirroring the panel spine's own
  `theorem_55_minimalKDof_k`/`theorem_55_d3` split; blueprint node
  `thm:pencil-conditional-realization-pair`'s `\lean{...}` list extended with the new name.
- **W5-L7c-5 + L7c-6 LANDED — `hsplit` CLOSED IN FULL** (2026-07-30, `Escape.lean`) —
  `pencilPair_of_splitOff_of_habitat` (the `5 ≤ |V|` producer, carrying `hK`/`hbareSplit` as
  given) and the successor wrapper `pencil_conjecture_of_hcontract_hK_hbareSplit` (dispatching
  `|V| ∈ {3,4}` to L7c-3/4, `≥5` to L7c-5); blueprint node
  `thm:pencil-conditional-realization-pair` restated with a `fmlnote` on kernels (K)/(K-bare).
  Design doc §"W5-L7 research recon" "L7c decomposition".
- **W5-L7c-3/L7c-4 base leaves LANDED + (K-bare) numerics gate PASSED** (2026-07-30, `Base.lean`,
  `pencilPair_of_habitat_ncard_eq_{three,four}`) — direct-witness `|V|=3`/`|V|=4` leaves (L7c-4
  needed a genuinely different per-vertex-normal + degree-3-exclusion construction, hence deferred
  to its own commit); the numerics gate SUPPORTED bare-target attainment at every infeasible
  gadget tried — **consequence: route (a), carry `hbareSplit`, is GO** (design doc residue (ii)).
  New FRICTION: L7c-3's "wedge-family independence via the join-detector" + `Graph`-namespaced
  resolution [idiom] entries; L7c-4's two [rescue] entries → TACTICS-QUIRKS §103/§104.
- **W5-L7c DECOMPOSED + L7c-1/L7c-2 plumbing LANDED** (2026-07-30) — design pass pinned six
  buildable leaves L7c-1…6 (bare-half-off-feasibility, residue (ii), needs a second kernel
  `hbareSplit`, adjudication owed at the time); L7c-2 =
  `exists_splitOff_data_of_degree_eq_two_of_twoEdgeConnected` (`ForestSurgery/Reduction.lean`,
  2EC-re-sourced), L7c-1 closed by reuse of the already-landed `simple_of_loopless_of_noRigid`
  (byte-identical body, no new lemma). **(K-bare) adjudicated "Numerics gate first"** (verbatim).
  Design doc §"W5-L7 research recon" "L7c decomposition" + residues (i)–(iv).
- **W5-L7b RE-PINNED (kernel (K) as `hK`) then LANDED, signature corrected** (2026-07-30) —
  `escapePoly` deleted (the "L3-style, buildable" sizing was refuted by a BLOCKED build: needs the
  global stress as a polynomial, no cofactor infra in tree); re-pinned split-data-free as
  `hasGenericPencilRealization_of_independent_pencilRow_target` (`Escape.lean`), (K) carried as the
  `hK` rank-increment implication (KT Claim 6.12 at that level); the build then BLOCKED first on
  the pinned `[Nonempty α]`, coordinator-adjudicated fix `[Inhabited α]` (`Graph.endsOf`'s
  statement-level occurrence needs it), landed same commit. Dispatch-log F9 (×2). Design doc
  §"W5-L7 research recon" "Lean decomposition".
- **2026-07-30 research day: recon isolates kernel (K); route 3 adjudicated; L7a LANDED; rigid
  `k=0` half PROVEN** (scripts `scratchpad/escape/*.py`; design doc §"W5-L7 research recon") — `M₁`
  escape confirmed pencil-generic across 5 habitats but genuinely generic (route (b) [(6.44)
  identity] REFUTED), isolating kernel **(K)**; user selected route 3 ("build now") + "Prove now"
  for the rigid half (verbatim, *Current state*); `hasGenericPencilRealization_of_splitOff_of_safe`
  (`Escape.lean`) chains the four landed L6 leaves into the split's generic realization;
  `edgeBound_of_noRigid_of_degree_two` + `exists_adjacent_degree_two_pair_of_noRigid_of_degree_two`
  (`ReducibleVertex.lean`, corollary of KT Lemma 3.4) close the rigid half minimality-free,
  covering both deficiency regimes with one lemma.
- **W5-L6b re-pinned triangle-free + L6b-i assembly LANDED** (2026-07-30) — a bank-authorized
  spike refuted the `hcard`-only pin (`not_pencilNondegFeasible_of_triangle_two_hubs`); the
  follow-up recon VERIFIED both habitat claims and re-pinned triangle-free;
  `pencilNondegFeasible_of_selectors_of_satisfiable` (`Steer.lean`) is the feasibility assembly
  from selectors + satisfiable-somewhere LI families, needing `[G.Loopless]`. Dispatch-log F9.
- **W5-L6b-ii (engine + callers) + L6b COMPLETE** (2026-07-30, `Witness.lean`/`Steer.lean`) —
  `exists_coord_linearIndepOn_pencilChartPoint_of_idx` (reusable char-free general-position
  engine, no config of its own) feeds the adjacent-pair caller `hsat_adj` and the per-body caller
  `hsat_pt`/`exists_idx_dtgt_triple`; headline
  `pencilNondegFeasible_of_ncard_closedHubNbhd_le_three_of_triangleFree` (`Steer.lean`) wires both
  through the L6b-i assembly. Reusable brick `exists_injOn_mapsTo_of_ncard_le` (FRICTION
  [mirror-candidate]); FRICTION: omega/`Set.ncard`-atom idiom.
- **W5-L6a (invariant, transfer, non-rigid safe-exists, L7 coupling) + L6d all LANDED**
  (2026-07-29/30) — the `≤3` closed-hub-neighbourhood bound is free from `PencilNondegFeasible K G`'s
  own antecedent (invariant SETTLED); the real gap was the `G⇒G′` transfer, fixed by splitting a
  **safe** vertex: `ncard_closedHubNbhd_splitOff_le_three_of_safe` (`Habitat.lean` — the dispatched
  bare-existential pin was FALSE, a 10-vertex counterexample, fixed with explicit `hab : a≠b`);
  non-rigid safe-vertex existence PROVEN minimality-free
  (`exists_adjacent_degree_two_pair_of_noRigid_of_deficiency_pos`,
  `ReducibleVertex.lean`/`Operations.lean`); L6/L7 coupling RESOLVED benign (KT Lemma 6.13/4.6
  already splits a safe vertex); `c4_isProperRigidSubgraph` + `splitOff_triangleFree_of_noRigid`
  (`Habitat.lean`, the `C₄` proper-rigid brick + triangle-freeness transfer, TACTICS-QUIRKS §46
  augmented). Dispatch-log F9 ×3 (bare pin, invariant re-route, coupling). (Rigid `k=0` half
  PROVEN separately, above.)
- **L5-cut-v-a…v-g all LANDED** (2026-07-25/29, `Motive.lean`/`Witness.lean`/`Steer.lean`/
  `Engine.lean`/`Pair2.lean`) — the full cut-arm sub-case (v) chain: v-a triangle-hub
  infeasibility (`not_pencilNondegFeasible_of_triangle_two_hubs`); v-b the somewhere-witness on
  `G`'s chart (`exists_coord_linearIndependent_pencilChartPoint_of_pendant_deg3`, new file
  `Witness.lean`; FRICTION [idiom] → TACTICS-QUIRKS §101); v-c/v-d the `H`-chart witness +
  `fillNbr` re-choice + flattening gadgets (TACTICS-QUIRKS §96); v-e the common-seed steering
  primitive + input-half assembly (`pencilNondegFeasible_induce_of_pendant_deg3`, FRICTION [idiom]
  → TACTICS-QUIRKS §102); v-f the output-half steering assembly
  (`exists_isNondegPencilRealization_induce_promotedNormal_of_pendant_deg3`, FRICTION
  [mirror-candidate] `extensor_pair_smul`); v-g (parts 1–2) the demoted-hub glue producer,
  discharging `hcutPendant3` inline over `[Infinite K]` — **L5-cut-v CLOSED in full**.
- **Older W5-L5 / W0–W4 entries (one-lined; canonical detail in `notes/Phase39-design.md` + git).**
  L5-cut-iv shell `pencilPair_of_not_twoEdgeConnected` + sub-cases (`Pair.lean`/`Pair2.lean`);
  L5-cut-i…iii the `Gᵢ⁺` structure layer + restriction infra (`Motive.lean`/`Bricks.lean`/
  `Arms.lean`). Base arm `pencilPair_of_ncard_le_two`; `PencilPair` route-(b′) restatement
  (user-adjudicated) + `not_simple_of_parallel`; loop arm `pencilPair_of_isLoopAt`. W5-L4
  `exists_pencilSeed_of_nondeg` (`Reseed.lean`); `Pencil.lean`→`Pencil/` split; W5 design pass.
  W3: L7 `pencil_conjecture_of_arms`, L4 cut arm `hasPencilRealization_of_not_twoEdgeConnected`,
  L1 `exists_isProperRigidSubgraph_of_three_le_degree`, L2 `Graph.pencil_reduction`. W2
  `exists_extensor_two_pencils_iff`; W1 `exists_concurrency_point_of_extensorInPanel_pair`; W0
  statement layer + self-duality; opening recon (R1–R3). Promotions: TACTICS-GOLF §11/§22/§23,
  TACTICS-QUIRKS §99/§100/§101.

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
