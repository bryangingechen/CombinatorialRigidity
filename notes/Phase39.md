# Phase 39 — PENCIL: the hinge-pencil molecular conjecture (work log)

**Status:** in progress — **W0–W3 all COMPLETE**; **W5 design settled**; **W5-L0 through W5-L4 all
COMPLETE**; **W5-L5 COMPLETE modulo TWO carried hypotheses** (loop/base/cut arms all landed against
the (b′) `PencilPair`, wired by the successor `pencil_conjecture_of_arms_pair` (`Pair2.lean`, node
`thm:pencil-conditional-realization-pair` green, now over `[Infinite K]`); **`hcontract`/`hsplit`
remain the only open hypotheses** — `hcutPendant3` DISCHARGED 2026-07-29, **L5-cut-v CLOSED**).
L5-cut-v-a…v-g all landed (`Motive.lean`/`Witness.lean`/`Engine.lean`/`Steer.lean`/`Pair2.lean`);
**v-g PART 2 LANDED** (2026-07-29, `Pair2.lean`: the inline sub-case-4 discharge
`hasGenericPencilRealization_pendant_deg3_of_IH` + the shell/successor rewire dropping
`hcutPendant3` and adding `[Infinite K]`, blueprint node restated) — per-leaf detail one-lined in
*Decisions made* + `notes/Phase39-design.md`. **L6/L8 are parallel combinatorial tracks buildable
now; L7 (the research core) is last; W4 after W5** (phase opened 2026-07-23, recon-first).
`Molecule/Pencil.lean` split into
`Molecule/Pencil/{Statement,Arms,Motive,Chart,Engine,Reseed,Witness,Steer,Pair,Pair2}.lean`
(2026-07-24/25/29 housekeeping).

## Current state

**The phase stays OPEN — do NOT run the close checklist.** Two 2026-07-24 user
adjudications (verbatim, later supersedes earlier) revised the same-day "wrap up"
one: *"Let's leave the phase open and continue the work on the conjecture in this
phase. Unless there's a good reason to split here."* (coordinator assessed: no
reason to split — the phase's charter is the conjecture itself), then *"Let's end
the loop after this dispatch returns and you've confirmed its results; we'll begin
the research on the conjecture in a fresh session."*

**W0–W3 all COMPLETE; W5 design settled; W5-L0–L4 all COMPLETE; W5-L5 closed modulo TWO carried
hypotheses** (loop, base, and cut arms all landed against `PencilPair`, and the successor assembly
`pencil_conjecture_of_arms_pair` wires them through `Graph.pencil_reduction`; two explicit
hypotheses remain open — `hsplit` (awaits W5-L6/L7/L8) and `hcontract` (a W4 obligation),
*Blockers*/*Hand-off*). **L5-cut-v CLOSED 2026-07-29**: the residual sub-case-4 hypothesis
`hcutPendant3` is discharged inline over `[Infinite K]` by `hasGenericPencilRealization_pendant_
deg3_of_IH` (`Pair2.lean`), so both `pencilPair_of_not_twoEdgeConnected` and
`pencil_conjecture_of_arms_pair` dropped it and gained `[Infinite K]`. Per-milestone detail for every
completed piece lives in *Decisions made* below (reverse-chronological, one entry per landing) and in
`notes/Phase39-design.md`; this section stays a pointer, not a second copy.

**The W3–W5 route recon** (`notes/Phase39-design.md` §W3–W5 route recon) set the attack
order **W3 → W5 → W4**: W3 route (a) refuted at K4; route **(b′)** adopted — induction on ALL
spanning multigraphs, dispatch made total by a min-degree-3 ⟹ proper-rigid-subgraph lemma,
leaves L0–L7 (all landed). **W5's device** (design pass, `notes/Phase39-design.md` §"W5 design
pass"): final motive = the conditioned pair `PencilPair` (further `Simple`-conditioned 2026-07-24,
route (b′)); device = the grade-0 molecular chart (`Molecule/Pencil/Chart.lean`) + the
rows-polynomial engine (`Molecule/Pencil/Engine.lean`) + the D6 re-seeding lemma
(`Molecule/Pencil/Reseed.lean`), leaves **L0–L8** (L0–L4 complete; L5 closed modulo
`hcontract`/`hsplit`, all L5-cut-v leaves landed; **L6 re-routed 2026-07-29 (L6a-as-pinned refuted,
then settled): the real work is the `G ⇒ G′` transfer at a *safe* split vertex, L6a-transfer LANDED
2026-07-30 (`Habitat.lean`). Safe-vertex existence + L7 coupling settled 2026-07-30: coupling benign
(KT splits safe); non-rigid safe-vertex existence LANDED (`ReducibleVertex.lean`/`Operations.lean`),
rigid (`k=0`) half a bounded `have`-hyp. L6b `hcard`-only pin refuted then re-pinned; the new
triangle-exclusion hypothesis L6d is VERIFIED (2026-07-30 habitat recon): `G′` is *fully*
triangle-free at any degree-2 split (induced-`C₄`-is-`D6`-rigid argument), so L6b is re-pinned with a
triangle-free hypothesis. **L6d LANDED 2026-07-30 (`Habitat.lean`): the `C₄` proper-rigid brick
`c4_isProperRigidSubgraph` + the transfer wrapper `splitOff_triangleFree_of_noRigid`, both over
`namespace Graph`; L6b is now the next buildable leaf (both its `hcard`/`htf` inputs are honest
producers in tree)**; L8 parallel; L7, the research core, last).

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

- ~~W5-L5 cut arm (L5-cut-iv/v)~~ **CLOSED** (L5-cut-iv 2026-07-25; L5-cut-v 2026-07-29; canonical
  record `notes/Phase39-design.md` §"W5 leaf decomposition" L5, per-leaf verdicts in *Decisions
  made*). All four cut sub-cases discharge internally; the residual sub-case-4 hypothesis
  `hcutPendant3` was DISCHARGED inline over `[Infinite K]` (v-g part 2, `Pair2.lean`). One residual
  open item stays bounded: feasibility propagation *as a proposition* — the triangle-hub mechanism
  (`not_pencilNondegFeasible_of_triangle_two_hubs`) refutes any purely combinatorial
  (`≤ 3`-closedHubNbhd) feasibility criterion, while leaving L6's habitat claim untouched (no
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
  new mathematics, N2 witnesses one instance), **W5-L8** (the k = 0 residue —
  emptiness route recommended), and W4's witness generality (unchanged, after W5).
- **W5-L6 split-arm feasibility — invariant SETTLED; coupling RESOLVED benign; safe-vertex
  existence half-proven** (2026-07-29 L6a re-route + 2026-07-30 safe-exists recon; canonical
  `notes/Phase39-design.md` §"W5 leaf decomposition" L6a). ≤ 3 on `G` is free from the split arm's
  `PencilNondegFeasible K G` antecedent (landed
  `ncard_closedHubNbhd_le_three_of_isNondegPencilRealization`); the transfer `G ⇒ G′` fails at
  "dangerous" split vertices (computer-verified gadget), so L7 must split a **safe** (adjacent-deg-2-pair
  endpoint) vertex. **2026-07-30 recon findings:** (ii) the L7 coupling is **benign** — KT's Case III
  (Lemma 6.13) splits a chain of ≥ 2 degree-2 vertices, i.e. a safe vertex, obtained from KT Lemma 4.6,
  so no W3-level minimality re-introduction is forced; (i) safe-vertex existence off minimality is
  **PROVEN + LANDED in Lean 2026-07-30 for non-rigid `G`** (`deficiency > 0`: the generalized counting
  `exists_adjacent_degree_two_pair_of_edgeBound`, the non-rigid brick
  `indep_matroidMG_of_noRigid_of_deficiency_pos`, and the composition
  `exists_adjacent_degree_two_pair_of_noRigid_of_deficiency_pos`, `ReducibleVertex.lean`/`Operations.lean`)
  and **OPEN only for rigid `G`** (`k = 0`, = classical KT Lemma 4.6 off `IsMinimalKDof 0`; decisive
  computational evidence incl. `S(Petersen)`, carry as `have`-hyp). **L6a-transfer LANDED 2026-07-30**
  (`Habitat.lean`, `ncard_closedHubNbhd_splitOff_le_three_of_safe`); L6b + L8 remain
  buildable now; the `k = 0` bound is bounded and non-blocking.
- The full biconditional transport `ExtensorThroughPoint C q ↔
  ExtensorInPanel (screwComplementIso C) q` (design doc's W0 pin) is
  landed only as its **two forward implications** (all the self-duality
  consumes). The reverse arms need a `complementIso` involution lemma,
  not in tree — deferred; not on any critical path.

## Hand-off / next phase

**The phase stays OPEN** (the two superseding 2026-07-24 adjudications — no phase-close).

**W5-L5 is closed modulo TWO carried hypotheses** (loop/base/cut arms + the successor
`pencil_conjecture_of_arms_pair`, `Pencil/Pair2.lean`, node
`thm:pencil-conditional-realization-pair` green over `[Infinite K]`; only `hcontract` (W4) and
`hsplit` (W5-L6/L7/L8) remain open — full detail in *Decisions made*, below). **L5-cut-v CLOSED
2026-07-29** (v-g part 2): `hcutPendant3` is discharged inline by
`hasGenericPencilRealization_pendant_deg3_of_IH` (`Pair2.lean`), so both
`pencilPair_of_not_twoEdgeConnected` and `pencil_conjecture_of_arms_pair` dropped it and gained
`[Infinite K]`.

**W5-L6a-transfer LANDED 2026-07-30** (`Molecule/Pencil/Habitat.lean`, new file wired into
`CombinatorialRigidity.lean`): `ncard_closedHubNbhd_splitOff_le_three_of_safe` supplies L6b's `hcard`
at `G′` from `G`'s. **Signature corrected** — the bare-existential pin was FALSE at `a = b` (self-loop
inflates a non-hub into a `G′`-hub; 10-vertex counterexample), fixed by the explicit `hab : a ≠ b`
(free at the L7 call site via `exists_splitOff_data_of_degree_eq_two`'s `eₐ ≠ e_b`); `{n}`/`hdeg`
dropped. Route: `hab` ⟹ `G′` loopless ⟹ `degree` monotone ⟹ hub-transfer, then the per-`w` case
split. Detail: *Decisions made* + `notes/Phase39-design.md` §"W5 leaf decomposition" L6a.

**W5-L6a-safe-exists non-rigid half LANDED 2026-07-30** (`ReducibleVertex.lean`/`Operations.lean`):
the generalized counting `exists_adjacent_degree_two_pair_of_edgeBound`, the non-rigid brick
`indep_matroidMG_of_noRigid_of_deficiency_pos` (Operations), and the composition
`exists_adjacent_degree_two_pair_of_noRigid_of_deficiency_pos` — a `∃` adjacent-degree-2-pair
(= a coordinator-safe vertex under 2EC) for the entire non-rigid (`deficiency > 0`) split-arm
habitat, with no minimality anywhere. The pinned `[DecidableEq β]`/`hnp` on the counting lemma were
dropped as inert (Decisions-made). The **rigid (`k = 0`) half stays a bounded `have`-hyp** (KT Lemma
4.6 off minimality; decisive `S(Petersen)` evidence, no counterexample; user call only whether to
prove it now).

**W5-L6b re-pinned + L6d VERIFIED (2026-07-30 habitat-foundations recon; canonical `notes/Phase39-
design.md` §"W5 leaf decomposition" L6b/L6d).** The `hcard`-only L6b pin was refuted (a two-adjacent-
hub triangle satisfies `hcard ≤ 3` yet is infeasible by the landed
`not_pencilNondegFeasible_of_triangle_two_hubs`); L6b now takes a triangle-free hypothesis. The recon
then VERIFIED both habitat claims: (Q1) triangle ⟹ proper rigid at `|V| ≥ 4` is already LANDED
(`Graph.triangle_isProperRigidSubgraph`, contrapositive ⟹ habitat triangle-free), and (Q2) the
transfer HOLDS — `G′` is *fully* triangle-free at ANY degree-2 split (a new `G′`-triangle would give
an induced `C₄` in `G`, and `C₄` is `D6`-rigid (`isKDof_zero_of_cycle`, `m=4`), a proper rigid
subgraph at `|V| ≥ 5`, contradicting `hnoRigid`). Exhaustive search (all `{2,3}`-degree habitats
`n ≤ 7`, sampled `n = 8`): zero counterexamples. So L6d is a THEOREM (not an existence gamble); safe
is **not** needed for it (only L6a-transfer needs safe). No route-breaker.

**W5-L6d LANDED 2026-07-30** (`Molecule/Pencil/Habitat.lean`, `namespace Graph`): the `C₄`
proper-rigid brick `c4_isProperRigidSubgraph` (an `m = 4` mirror of `triangle_isProperRigidSubgraph`,
`isKDof_zero_of_cycle` for `0`-dof, properness from `|V| ≥ 5`) + the transfer wrapper
`splitOff_triangleFree_of_noRigid` (`htf` at `G′`, its `hcard` sibling landed in L6a-transfer). Both
inputs to L6b are now honest producers in tree. Gates + axioms clean.

**Next concrete commit — build W5-L6b** (spike-first, per the design doc L6b decomposition): the
general-position feasibility criterion `pencilNondegFeasible_of_ncard_closedHubNbhd_le_three_of_
triangleFree` taking `hcard` (from L6a-transfer) + `htf` (from L6d). Split into **L6b-i** (the
selector-assembly `#1/#2`, prose-settleable — plus the missing `IsFin3SelectorOf`-existence brick)
and **L6b-ii** (the general-position `#3/#4/#5` moment-curve core — COMPILER-CHECKED SPIKE REQUIRED
before committing; the `htf` hypothesis strictly excludes the two-hub-triangle failure locus). Fully
parallel alternative: **W5-L8** (the `k = 0` residue, emptiness route).

**W5-L6 invariant SETTLED (2026-07-29 L6a recon; canonical `notes/Phase39-design.md` §"W5 leaf
decomposition" L6a).** The ≤ 3 closed-hub-neighbourhood bound on `G` is **not** a graph-combinatorial
fact (the refuted L6a's `2EC + no-rigid ⟹ ≤ 3` is false, computer-verified theta counterexample) — it
is **free from the split arm's own `PencilNondegFeasible K G` antecedent** via the LANDED
`ncard_closedHubNbhd_le_three_of_isNondegPencilRealization`, and where it fails `G` is infeasible so
the obligation is vacuous (this also moots the `(5,5,5)` borderline). The **real gap** is the transfer
`G ⇒ G′`: `splitOff` at a *dangerous* vertex (both neighbours hubs, one tight) makes a 4-member
neighbourhood, so `G′` is infeasible — computer-verified gadget. Fix: split a **safe** vertex.
Other buildable-now leaves (parallel pivots):
- **W5-L6b** (spike-first, takes `hcard` explicitly): the general-position witness seed →
  `PencilNondegFeasible K G′`. Its input type-matches L6a-transfer's output exactly. UNCHANGED by the
  re-route.
- **W5-L8** (the `k = 0` residue, emptiness route). Fully parallel.
- **W5-L6c** (`G′.Simple` = landed `splitOff_simple_of_noRigid_of_card`) — a citation, folded into L7.

**Safe-vertex existence + L7 coupling (2026-07-30 recon; canonical: design doc L6a).** (ii) *L6/L7
coupling* — **RESOLVED benign**: KT's Case III (Lemma 6.13) splits a chain of ≥ 2 degree-2 vertices =
a safe vertex (obtained from KT Lemma 4.6), so the rank argument *consumes* a safe vertex and no
W3-level minimality re-introduction is forced. (i) *safe-vertex existence off minimality* — **PROVEN
for non-rigid `G`** (`deficiency > 0` ⟹ `M(G̃)` independent, via `fundCircuit_inducedSpan_vertexSet_eq`
+ `circuit_induces_isRigidSubgraph` + `deficiency_le_deficiency_of_le_vertexSet_eq`), **OPEN only for
rigid `G`** (`k = 0` = KT Lemma 4.6 off `IsMinimalKDof 0`; = `corank ≤ 5`; decisive computational
evidence incl. `S(Petersen)`, no counterexample). Non-blocking: the `k = 0` edge bound is carried as a
`have`-hyp. **Remaining user call = only whether to prove the `k = 0` bound now or carry the have-hyp —
not a build-vs-rework decision.** Neither blocks L6a-transfer / L6b / L8 / the non-rigid discharger.
- **W5-L7** (the research core, last): the uniform escape certificate `r ⬝ Λ²Π̂(a) ≢ 0` on the
  chart — the genuinely new mathematics; N2 witnesses one instance.
- **W4** (after W5): the constrained-family Claim-6.4 analogue, `G′`-block witness confirmed by N3;
  discharges `hcontract`.

Discharging `hsplit` (L6/L7/L8) then `hcontract` (W4) removes the last two carried hypotheses of
`pencil_conjecture_of_arms_pair` and completes the conditional-realization successor. Full leaf
detail: `notes/Phase39-design.md` §"W5 leaf decomposition".

Gates for any continuation: `lake build` (warning-clean) + `lake lint` when `.lean` is touched;
`blueprint/verify.sh` + `blueprint/lint.sh` (vocabulary gate bans "stratum"/"strata") when `.tex`
is touched.

## Adjacent directions (orientation only, not this phase)

ORIGAMI (`notes/Origami.md`, next queued) is the bar-joint-side
analog; the wider unqueued survey — incl. IDENT-PANEL, the nearest
neighbor — is `notes/IdeaBacklog.md`.

## Decisions made during this phase

- **W5-L6d LANDED — the `C₄` proper-rigid brick + the triangle-freeness transfer** (2026-07-30,
  `Molecule/Pencil/Habitat.lean`, both in `namespace Graph`; canonical `notes/Phase39-design.md`
  §"W5 leaf decomposition" L6d). `c4_isProperRigidSubgraph` — the `m = 4` mirror of
  `triangle_isProperRigidSubgraph`: a chordless induced `C₄` in a simple `G` with `|V| ≥ 5` is a
  proper rigid subgraph, `0`-dof via `isKDof_zero_of_cycle` on `vtx = ![p,q,r,s]` (`3 ≤ m ≤ bodyBarDim
  n` both from `hD : 4 ≤ …`), `E(H) = range edge` by induced-edge antisymmetry (the two chords
  excluded by `hpr_nadj`/`hqs_nadj`, the four sides pinned by `Simple.eq_of_isLink`), properness from
  the `|range vtx| = 4 < 5` gap — so, unlike `cycle_isProperRigidSubgraph`, no vertex-closure hyp.
  `splitOff_triangleFree_of_noRigid` — the wrapper: a `G′`-triangle with no fresh edge is a
  `G`-triangle (⊥ via `triangle_isProperRigidSubgraph`/`hnoRigid`); with the fresh `e₀ = ab` its apex
  `c` and `{v,a,c,b}` form a chordless `G`-`C₄` (`vc ∉ E` from `deg_G v = 2`/`N(v) = {a,b}` inlined;
  `ab ∉ E` from the triangle brick) ⟹ `c4_isProperRigidSubgraph` ⟹ ⊥. Matched the pinned signatures
  verbatim. Both build subtleties routine + already-documented (defeq closes `![…]`-indexed `Fin 4`
  goals with no `simp`, TACTICS-QUIRKS §46 augmented; `rintro rfl` on `f = e₀` substitutes `e₀` away,
  §4 — used named `intro`+`▸`). Gates + axioms clean (`propext`/`Classical.choice`/`Quot.sound`).
- **W5-L6d VERIFIED + L6b re-pinned — the habitat-foundations recon (design-pass commit)** (2026-07-30;
  canonical `notes/Phase39-design.md` §"W5 leaf decomposition" L6b/L6d + the wiring). Settled the two
  questions the L6b refutation raised, grounded against LANDED bodies: (Q1) *triangle ⟹ proper rigid
  at `|V| ≥ 4`* — already LANDED as `Graph.triangle_isProperRigidSubgraph` (`Operations.lean:994`), so
  no-proper-rigid habitat is triangle-free at `|V| ≥ 4`. (Q2) *transfer to `G′`* — HOLDS, and gives
  *full* triangle-freeness of `G′` at ANY degree-2 split: a new `G′`-triangle `{a,b,c}` forces an
  induced `C₄` `{v,a,b,c}` in `G`, and `C₄` is `D6`-rigid (`isKDof_zero_of_cycle`, `m=4`; exact
  partition-deficiency `= 0`, independently re-checked) hence a proper rigid subgraph at `|V| ≥ 5` —
  ⊥ against `hnoRigid`. Exhaustive `{2,3}`-degree search (`n ≤ 7` + sampled `n = 8`): zero
  counterexamples; the naive "common neighbour ⟹ new triangle" worry is void (the common neighbour is
  the excluded `C₄`). L6d is a THEOREM, not an existence gamble; **safe not needed for L6d** (only for
  L6a-transfer). L6b re-pinned to take a triangle-free hypothesis (strictly stronger than the minimal
  `¬two-hub-triangle`, free here, and strictly easier for L6b-ii). Next buildable: L6d = the `C₄`
  brick `c4_isProperRigidSubgraph` + `splitOff_triangleFree_of_noRigid` (`Habitat.lean`). No Lean
  built (design pass); scratch search reverted, tree clean. Dispatch-log F9 instance — first
  *confirmed* (non-refuted) pin of the L6 habitat arc.
- **W5-L6b `hcard`-only pin REFUTED by the bank-authorized spike; L6d surfaced** (2026-07-30, no
  commit — spike left tree clean; coordinator salvage this commit). The spike (compiler-checked
  scratch, reverted) showed `hcard : ∀ v, closedHubNbhd ≤ 3 ⟹ PencilNondegFeasible K G` is FALSE: a
  two-adjacent-hub triangle satisfies `hcard` yet is infeasible by the landed
  `not_pencilNondegFeasible_of_triangle_two_hubs` (5-vertex witness `{u,v,w,u',v'}`). This was already
  implied by the *Blockers* triangle-hub note — an internal plan inconsistency, not new math; the L6b
  pin (from `6768bd33`) never reconciled against it. The chart **assembly** route is sound (v-e
  template composes); only the hypothesis is wrong. Corrected decomposition (design doc L6b): L6b gains
  a no-two-hub-triangle hypothesis; NEW obligation **L6d** (triangle-freeness transfer `G ⇒ G′`);
  L6b-i (assembly) + L6b-ii (spike-first `#3/#4/#5` core) + a missing `IsFin3SelectorOf`-existence
  brick. **Next: a habitat-foundations recon** verifying the habitat is triangle-free at `|V| ≥ 4` and
  that it transfers to `G′`, before re-pinning. Dispatch-log F9 instance (third optimistic-pin
  refutation in the L6 arc).
- **W5-L6a-safe-exists NON-RIGID HALF LANDED** (2026-07-30, `Induction/ReducibleVertex.lean` +
  `Induction/Operations.lean`): three decls discharging the whole non-rigid (`deficiency > 0`)
  split-arm safe-vertex obligation, no minimality anywhere. (i) `exists_adjacent_degree_two_pair_of_edgeBound`
  — a mechanical copy of `exists_adjacent_degree_two_pair`'s body with the `X₃₊` min-degree-3 bound
  re-sourced from 2EC (`two_le_degree_of_twoEdgeConnected`) and the KT-4.5(i) edge count taken as an
  explicit `hedge`; (ii) `indep_matroidMG_of_noRigid_of_deficiency_pos` (Operations) — `def(G̃) > 0 ⟹`
  `M(G̃)` free, via the three landed bricks (`fundCircuit_inducedSpan_vertexSet_eq` +
  `circuit_induces_isRigidSubgraph` + `deficiency_le_deficiency_of_le_vertexSet_eq`); (iii) the
  composition `exists_adjacent_degree_two_pair_of_noRigid_of_deficiency_pos` — freeness makes `E(G̃)` the
  base (`ground_indep_iff_isBase`), so `isBase_ncard_add_deficiency_eq` gives `(D−1)|E| + k = D(|V|−1)`
  and `hedge` is immediate from `k > 0`. **The pinned `[DecidableEq β]` + `hnp` on (i) were DROPPED as
  provably inert** (off minimality the only rigidity uses were the removed `no_rigid_edge_count` /
  `two_le_crossingEdges_of_isKDof_zero`; `IsMinimalKDof`'s type was what carried `matroidMG`/`DecidableEq β`,
  so both fall out — leaving a strictly more general statement, `classical` covering decidability). The
  rigid (`k = 0`) half stays a bounded `have`-hyp. Recurrence of the FRICTION `[idiom] unusedDecidableInType`
  pattern, resolved by the `classical`-conversion route now recorded there. Gates + axioms clean
  (`propext`/`Classical.choice`/`Quot.sound`).
- **W5-L6a-transfer LANDED + pinned signature CORRECTED (was false)** (2026-07-30,
  `Molecule/Pencil/Habitat.lean`, new file wired into `CombinatorialRigidity.lean`):
  `ncard_closedHubNbhd_splitOff_le_three_of_safe` — the safe-split `closedHubNbhd ≤ 3` transfer
  `G ⇒ G′`, the honest producer of L6b's `hcard` at `G′`. **The dispatched bare-existential pin was
  FALSE** (returned BLOCKED, coordinator-verified via Matroid `incFun_eq_two_iff`): the two
  existentials don't force `a ≠ b`, and at `a = b` the fresh `e₀` is a self-loop whose double-counted
  degree turns a non-hub `a` into a `G′`-hub, inflating a *neighbour's* closed hub-neighbourhood to
  `4` (explicit 10-vertex counterexample). Fix = explicit `hab : a ≠ b` (free at the L7 call site via
  `exists_splitOff_data_of_degree_eq_two`'s `eₐ ≠ e_b`); `{n}`/`hdeg` dropped (unused). Route: `hab`
  ⟹ `G′` loopless ⟹ `G′.degree x ≤ G.degree x` ∀`x` (`E(G′,x) ⊆ insert e₀ (E(G,x) \ {edge to v})`,
  `-1`/`+1` cancel; needs neither `e₀ ∉ E` nor `ab ∉ E`) ⟹ every `G′`-hub is a `G`-hub; then per `w`:
  non-hub via `ncard_closedNbhd_le_three_of_not_pencilHub`, hub via `⊆ G.closedHubNbhd w` (the sole
  new adjacency is `ab`, and a hub `w=a` with hub `b` contradicts `hsafe`). Output type-matches L6b.
  No new FRICTION (subst-direction gotcha hit + fixed via `▸`, already TACTICS-QUIRKS § 4). Gates +
  axioms clean. Dispatch-log F9 (BLOCKED-then-corrected).
- **W5-L6a-safe-exists SPLIT BY DEFICIENCY + L7 coupling RESOLVED benign** (2026-07-30 design-pass
  recon; canonical `notes/Phase39-design.md` §"W5 leaf decomposition" L6a + "Numerics index"). Settles
  the two 2026-07-29 user-adjudication flags. (1) **Coupling (ii) benign:** grounded against KT Lemma
  6.13, Case III splits a ≥ 2-chain endpoint = a coordinator-safe vertex (from KT Lemma 4.6) — the rank
  core *consumes* safety; no W3-level split-arm minimality re-introduction is forced. (2) **Existence (i)
  half-proven:** reduced `exists_adjacent_degree_two_pair` off `IsMinimalKDof 0` to one edge bound
  `(D−1)|E| < D(|V|−1)+(D−1)` (the landed degree double-count uses no minimality); the **non-rigid**
  case (`deficiency > 0`) is PROVEN minimality-free — `M(G̃)` independent via
  `fundCircuit_inducedSpan_vertexSet_eq` + `circuit_induces_isRigidSubgraph` +
  `deficiency_le_deficiency_of_le_vertexSet_eq` — leaving only the **rigid** (`k = 0`, = KT's own Case
  III) residue as a bounded `have`-hyp. Decisive exact-ℚ evidence (subdivision families +
  high-girth `S(Petersen)`): **no** counterexample. Re-pinned signatures + route + numerics in the
  design doc. No Lean built (design pass). Dispatch-log F9 instance (adjudication-flag resolution).
- **W5-L6 invariant SETTLED + route re-pinned** (2026-07-29; L6a proof-route recon this commit,
  after the same-day refutation of the bare-combinatorial L6a). Canonical:
  `notes/Phase39-design.md` §"W5 leaf decomposition" L6a "Re-route SETTLED". Findings: (1) the ≤ 3
  closed-hub-neighbourhood bound on `G` is **free** from the split arm's own `PencilNondegFeasible K G`
  antecedent (LANDED `ncard_closedHubNbhd_le_three_of_isNondegPencilRealization`, `Motive.lean:409`) —
  the refuted L6a's `2EC + no-rigid ⟹ ≤ 3` was the wrong target (false; theta counterexample), and
  where it fails `G` is infeasible so the split-arm obligation is vacuous (this moots the `(5,5,5)`
  borderline: theta has `closedHubNbhd(center) = 4` at every arc length ⟹ infeasible ⟹ vacuous).
  (2) The real gap is the transfer `G ⇒ G′`: `splitOff` at a *dangerous* vertex makes a 4-member
  neighbourhood ⟹ `G′` infeasible — computer-verified feasible/2EC/no-rigid gadget (`scratchpad/`).
  Fix: split a **safe** vertex. Re-pin: L6a → **L6a-transfer** (buildable now, combinatorial) +
  **L6a-safe-exists** (open). L6b/L6c/L8 unchanged; L6b's `hcard` input type-matches L6a-transfer's
  output. **⚠ Two coupled items flagged for user adjudication** (safe-vertex existence off minimality;
  L6/L7 rank-argument compatibility). Dispatch-log F9 instance.
- **L5-cut-v-g PART 2 LANDED — the inline sub-case-4 discharge + shell/successor rewire; L5-cut-v
  CLOSED** (2026-07-29, `Pair2.lean`; `hcutPendant3` DISCHARGED): new helper
  `hasGenericPencilRealization_pendant_deg3_of_IH` (`[Infinite K]`) closes the pendant deg-`3`
  sub-case from the IH — extract `u_c`'s two `V₁`-links from `G.degree u_c = 3`
  (`Graph.degree_eq_ncard_adj` + `Set.ncard_eq_two` on `N(G,u_c) \ {v_c}`), v-e feasibility → IH
  `H`-witness → v-f-6 promoted families → v-g-part-1 glue; rank forms coincide verbatim (no
  bridging). Both `pencilPair_of_not_twoEdgeConnected` (both `hdeg3` branches, one-liner each) and
  `pencil_conjecture_of_arms_pair` dropped the carried `hcutPendant3` and gained `[Infinite K]`;
  blueprint `thm:pencil-conditional-realization-pair` restated (over infinite field, antecedent (ii)
  dropped); `Motive.lean` L547 live cross-ref repointed. Added `import …Pencil.Steer` to `Pair2.lean`
  (acyclic). No new FRICTION (routine wiring). Gates + axioms clean.
- **L5-cut-v-g PART 1 LANDED — the demoted-hub glue producer** (2026-07-29, `Pair2.lean`):
  `hasGenericPencilRealization_of_isNondegPencilRealization_induce_pendant_deg3` — the `deg u_c = 3`
  companion of the sub-case-3 pendant producer, a faithful mirror taking the v-f-6 output
  (`hnd₁`/`hrank₁` + `hpromoted : ∀ v ∈ {u_c,w₁,w₂}, LinearIndepOn K normal₁ (G.closedHubNbhd v)`) as
  input, `[Field K]`-only glue. Three localized deltas from sub-case 3: (i) `u_c` is a definite
  `G`-hub / `H`-non-hub (`huc_Ghub`/`hdegH_uc`), replacing `pencilHub_iff_induce_of_degree_ne`; (ii)
  conjunct 3 splits — at the demoted triple `{u_c,w₁,w₂}` (where `G.closedHubNbhd v` contains the
  demoted `u_c`) it is `hpromoted`, elsewhere `G.closedHubNbhd v = H.closedHubNbhd v` (proof via
  `Graph.neighbor_eq_of_degree_eq_three`, `u_c ∉` since `v` not adjacent to `u_c`) transferring from
  `H`; (iii) conjunct 4 at `u_c` is vacuous, and `point v_c` dodges the single generator `point₁ u_c`
  (not a `≤ 2`-cover). Rank verbatim (`hlb₂ = 0`). **Scope-pin composition risk DISCHARGED** (green).
  No new FRICTION (mirror). Gates + axioms clean.
- **L5-cut-v-f-6 COMPLETE — the output-half steering assembly** (2026-07-29,
  `Molecule/Pencil/Steer.lean`): `exists_isNondegPencilRealization_induce_promotedNormal_of_pendant_deg3`
  — under the pendant deg-`3` config over `[Infinite K]`, from a generic `H := G.induce V₁` witness
  (`IsNondegPencilRealization` + deficiency-rank `hrank₁`, the sub-case-3 producer's input shape) it
  produces a nondegenerate `H`-realization at the target rank PLUS `∀ v ∈ {u_c, w₁, w₂}, LinearIndepOn
  K normal (G.closedHubNbhd v)`. Structural mirror of the v-e input-half assembly, adding: the rank
  rows steered alongside via ONE `exists_common_seed_pencilRow_and_polynomials` call (`hLI` = the
  flattening `pencilRow` subfamily from `exists_independent_pencilRow_subfamily_at_toCoord_of_reseed`;
  `P` = the standing point polys + the witness-(ii) promoted-normal polys over the index `(α ⊕ (α×α))
  ⊕ Fin 3`), the rank via v-f-4, and the promoted-family transfer to the re-chosen `seed'`
  (`linearIndepOn_pencilChartNormal_congr`). `hassigned` discharge = the inline `Fin 3`-selector-total
  pigeonhole at `u_c` (`Finset.card_eq_three`/`eq_univ_of_card`) + degree bookkeeping. **v-f-5 dropped**
  (unneeded — the normal conditions fold straight into the workhorse `P`). No new FRICTION (faithful
  v-e mirror). Gates green (build warning-clean + lint); axioms clean.
- **L5-cut-v-f-1…4 + input/normal-congr bricks LANDED** (2026-07-29, `Molecule/Pencil/Steer.lean`;
  canonical detail in `notes/Phase39-design.md` §"W5 leaf decomposition" L5-cut-v "v-f decomposition"):
  the output-half rank-transport chain the assembly above composes. v-f-1 link bridge
  (`pencilRow_mem_rigidityRows_of_mem_edgeSet`), v-f-2 row-span scaling invariance
  (`span_rigidityRows_eq_of_supportExtensor_proportional`), v-f-3 re-seeding proportionality
  (`exists_smul_supportExtensor_eq_pencilChartFramework_of_reseed`), v-f-4 output rank `le_antisymm`
  (`finrank_span_rigidityRows_pencilChartFramework_eq_of_independent_pencilRow`); the input bricks
  `pencilChartFramework_congr`, `span_rigidityRows_pencilChartFramework_eq_of_reseed`, the `hLI`
  producer `exists_independent_pencilRow_subfamily_at_toCoord_of_reseed`; the promoted-family
  `pencilChartNormal_congr` + `linearIndepOn_pencilChartNormal_congr`. General `BodyHingeFramework`
  panel-row machinery reused verbatim (no new import). FRICTION `[mirror-candidate]`:
  `extensor_pair_smul` (belongs in `Extensor.lean`, kept local pending the deep-rebuild-free mirror).
- **L5-cut-v-e COMPLETE — the input-half steering assembly** (2026-07-29,
  `Molecule/Pencil/Steer.lean`, imports `Pencil.{Reseed,Witness}` added):
  `pencilNondegFeasible_induce_of_pendant_deg3` — under the pendant deg-`3` config over `[Infinite K]`,
  `PencilNondegFeasible K G → PencilNondegFeasible K (G.induce V₁)`. Re-seed `G`'s witness
  (`exists_pencilSeed_of_nondeg`), feed the common-seed primitive one `pencilChartPoint`-LI set per
  condition over the index `α ⊕ (α×α) ⊕ Unit` (conjunct 3 = `{v}`; conjunct 5 = adjacent `{u,v}`;
  `hnbr_some` = the non-hub `closedNbhd v`; demoted triple = `{u_c,w₁,w₂}`) — standing ones satisfiable
  at the flattening `seed₀.toCoord`, the triple at witness (i)'s seed — re-extract, `fillNbr` re-choice
  → full `PencilChartWF`, then `isNondeg…_of_pencilChartWF` `.mono` to `H`, `u_c` the sole demotion
  (`degree_induce_eq_of_ne`), `hdemote` = the surviving demoted triple. Three local helpers:
  `pencilChartPoint_congr` (points ignore `fillNbr`), `linearIndepOn_triple_of_linearIndependent`
  (reverse of Motive's `…_of_linearIndepOn`), `linearIndepOn_nbrSlotPoint_isSome_of_pencilChartPoint`
  (the `hnbr_some` reindexing). FRICTION `[idiom]` → TACTICS-QUIRKS § 102 (`choose` tactic vs
  `.choose_spec` in `simp`); reverse-triple noted on the open `n`-ary `LinearIndepOn.pair_iff` entry.
  Gates + axioms clean.
- **L5-cut-v-e (primitive) — the common-seed chart-point steering primitive** (2026-07-29,
  `Steer.lean`): `exists_common_seed_linearIndepOn_pencilChartPoint` — finitely many
  `pencilChartPoint`-LI conditions each satisfiable somewhere share one common seed (v-d point gadget
  `ends := id` + `exists_common_eval_ne_zero_of_forall_exists`, whence `[Infinite K]`). The
  load-bearing "steer to a common seed" step consumed by the v-e assembly above.
- **L5-cut-v-d COMPLETE — post-steering `fillNbr` re-choice + `exists_fin3_rank_injOn` retired**
  (2026-07-29, `Molecule/Pencil/Steer.lean`): `exists_fillNbr_pencilChartWF_of_standing` closes
  `PencilChartWF`'s fourth conjunct from the four standing conjuncts
  (`pencilChartWF_standing_ofCoord_toCoord`) + each non-hub body's `some`-slot `nbrSlotPoint` LI, via
  a `fillNbr`-only re-choice (shared `hubNormal`/`fillHub`, so points are defeq and the standing
  conjuncts transfer). Core: the general `exists_extend_linearIndependent` (fill an LI partial
  family's free slots to a full LI family in dim `≥ n`; upstream-eligible, FRICTION
  `[mirror-candidate]`). **`exists_fin3_rank_injOn` RETIRED** same commit (extend-and-fill route, not
  the pigeonhole — unconsumed through v-a…v-d; tree-wide hygiene sweep done). Gates + axioms clean.
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
