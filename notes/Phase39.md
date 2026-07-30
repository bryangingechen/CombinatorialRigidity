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
*Decisions made* + `notes/Phase39-design.md`. **W5-L6 (habitat feasibility) COMPLETE 2026-07-30;
L8 buildable in parallel; L7 (the research core) is the last / critical path; W4 after W5** (phase
opened 2026-07-23, recon-first).
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

**2026-07-30 adjudication (this session, verbatim):** *"Let's wrap up this session when
we finish L6 and leave the research core to a fresh session."* L6 (habitat feasibility)
is now COMPLETE, so this session wraps here; **the fresh session begins at W5-L7 (the
research core — the uniform escape certificate `r ⬝ Λ²Π̂(a) ≢ 0`, the genuinely new
mathematics), with W5-L8 (`k=0` residue) buildable in parallel and W4 after W5.** The
phase stays OPEN (no phase-close).

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
`namespace Graph`. L6b-i LANDED 2026-07-30 (`Steer.lean`, the feasibility assembly
`pencilNondegFeasible_of_selectors_of_satisfiable`); L6b-ii char-free general-position CORE LANDED
2026-07-30 (`Witness.lean`, `exists_coord_linearIndepOn_pencilChartPoint_of_idx`); adjacent-pair
caller (`hsat_adj`) + per-body caller (`hsat_pt`) LANDED 2026-07-30, and **L6b COMPLETE 2026-07-30**
— headline `pencilNondegFeasible_of_ncard_closedHubNbhd_le_three_of_triangleFree` (`Steer.lean`)
wires the two callers + selectors through the L6b-i assembly. **The remaining W5 leaves are L8 (the
`k=0` residue), L7 (the research core, last), and W4 (after W5); L6a-safe-exists's rigid `k=0` half
stays a bounded have-hyp**).

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

**W5-L5 closed modulo TWO carried hypotheses** — loop/base/cut arms + successor
`pencil_conjecture_of_arms_pair` (`Pair2.lean`, node `thm:pencil-conditional-realization-pair` green
over `[Infinite K]`); only `hcontract` (W4) and `hsplit` (W5-L6/L7/L8) remain. Finished L6 landings
(one-line; detail in *Decisions made* + design doc §"W5 leaf decomposition"): **L6a-transfer**
(`ncard_closedHubNbhd_splitOff_le_three_of_safe`, `Habitat.lean`), **L6a-safe-exists non-rigid half**
(`exists_adjacent_degree_two_pair_of_noRigid_of_deficiency_pos`, `ReducibleVertex.lean`/`Operations.lean`;
rigid `k=0` half a bounded `have`-hyp), **L6d** (`c4_isProperRigidSubgraph` + `splitOff_triangleFree_of_noRigid`,
`Habitat.lean`), and **L6b COMPLETE** (`Witness.lean` callers + `Steer.lean` headline — see the
Decisions-made entry; the honest producer of the split arm's feasibility obligation, needing only
`hcard` from L6a-transfer and `htf` from L6d).

**Next concrete commit — one of the three remaining W5 leaves (all parallel):**
- **W5-L8** (the `k = 0` residue, emptiness route recommended — `notes/Phase39-design.md` §"W5 leaf
  decomposition" L8): the deficiency-`0` split-off bookkeeping / emptiness of the residue class.
- **W5-L7** (the research core, last — the uniform escape certificate `r ⬝ Λ²Π̂(a) ≢ 0` on the chart,
  the genuinely new mathematics; N2 witnesses one instance; couples benignly to the split arm per
  the 2026-07-30 recon).
- **W4** (after W5 — the constrained-family Claim-6.4 analogue, discharges `hcontract`).

L6a-safe-exists's **rigid `k=0` half** stays a bounded `have`-hyp (user call is only whether to prove
it now; nothing on the L7/L8 path blocks on it). With L6b done, the L6/L7 split-arm chain
(`PencilNondegFeasible K G` → L6a-transfer → L6d → **L6b** → `PencilNondegFeasible K G′` → IH + L6c →
`HasGenericPencilRealization K 3 G′` → L7 extension) has every combinatorial link but the L7 rank
extension itself.

**W5-L6 invariant SETTLED** (2026-07-29; design doc §"W5 leaf decomposition" L6a): the ≤ 3
closed-hub-neighbourhood bound is free from the split arm's `PencilNondegFeasible K G` antecedent
(`ncard_closedHubNbhd_le_three_of_isNondegPencilRealization`); the real gap was the `G ⇒ G′` transfer
(fixed by splitting a **safe** vertex, L6a-transfer). Safe-vertex existence + L7 coupling settled
(2026-07-30): coupling benign (KT Case III consumes a safe vertex); non-rigid existence proven, rigid
`k=0` a bounded `have`-hyp. **Remaining user call = only whether to prove the `k=0` bound now** — not a
build-vs-rework decision; nothing on the L6b/L8 path blocks on it. **L6c** = landed
`splitOff_simple_of_noRigid_of_card`, folds into L7.

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

- **W5-L6b COMPLETE — per-body caller `hsat_pt` + the feasibility headline** (2026-07-30,
  `Witness.lean` + `Steer.lean`; canonical `notes/Phase39-design.md` §"W5 leaf decomposition" L6b).
  Three pieces: (1) the three-set brick `exists_idx_dtgt_triple` (analogue of `exists_idx_dtgt_pair`
  for a non-hub centre + its ≤ 2 neighbours) — **DERIVATION GUARD met**: the tight `{a,b,w₁,w₂}`
  near-bijection onto `Fin 4` fits because `(Xa ∩ Xb).ncard ≤ 2` cancels and `dtgt b := idx a`
  collapses `Xv`-injectivity; (2) `exists_coord_linearIndepOn_pencilChartPoint_perBody` (+ private
  singleton helper) — hub/deg-`0` → singleton, deg-`1` → `exists_idx_dtgt_pair`, deg-`2` → the triple
  brick (its 8 overlap hyps from `htf` + `hcard`/`ncard_closedNbhd_le_three_of_not_pencilHub`); (3)
  headline `pencilNondegFeasible_of_ncard_closedHubNbhd_le_three_of_triangleFree` (`[G.Simple]` →
  `[G.Loopless]` via `.toLoopless`; `choose` selectors → two callers → L6b-i assembly). FRICTION:
  omega/`Set.ncard`-atom recurrence (`le_antisymm` workaround; [idiom] omega-atom entry). Gates +
  axioms clean.
- **W5-L6b-ii ADJACENT-PAIR CALLER LANDED — `hsat_adj` from `hcard` + `htf`** (2026-07-30,
  `Molecule/Pencil/Witness.lean`, `exists_coord_linearIndepOn_pencilChartPoint_adjacentPair`; canonical
  `notes/Phase39-design.md` §"W5 leaf decomposition" L6b-ii). Supplies the general-position core with
  a per-pair `idx`/`dtgt`: at adjacent `{u,v}`, `htf` confines `closedHubNbhd u ∩ closedHubNbhd v ⊆
  {u,v}` (a common third hub `w` closes a triangle `u–v–w`), so the two-set combinatorial core
  `exists_idx_dtgt_pair` injects `closedHubNbhd u` into a `3`-value palette avoiding `dtgt u = 2` and
  the disjoint remainder `closedHubNbhd v \ closedHubNbhd u` into the values avoiding `dtgt v` and the
  overlap's image — palette sizes matching by `hcard` (`≤ 3`), **uniformly, with no hub case split**
  (`|U∩V|` cancels in `(V\U).ncard = V.ncard − |U∩V|` vs palette `3 − |U∩V|`). Reusable brick
  `exists_injOn_mapsTo_of_ncard_le` (inject a finite set into a no-smaller one, via
  `Function.Embedding.nonempty_of_card_le`; upstream-eligible → FRICTION [mirror-candidate]). Combinatorial
  core compiler-verified standalone before integrating. `[G.Loopless]` (for `u ≠ v` via `IsLink.ne`);
  `open Classical in` for the statement-level `if G.Adj …`. Gates + axioms clean
  (`propext`/`Classical.choice`/`Quot.sound`). **Remaining L6b: the per-body `hsat_pt` (non-hub
  `closedNbhd v` is a non-`S`-separated 3-set — harder) + headline** (*Hand-off*).
- **W5-L6b-ii CORE LANDED — the char-free general-position engine** (2026-07-30,
  `Molecule/Pencil/Witness.lean`, `exists_coord_linearIndepOn_pencilChartPoint_of_idx`; canonical
  `notes/Phase39-design.md` §"W5 leaf decomposition" L6b-ii). v-b's construction extracted as a
  reusable lemma with NO configuration of its own: given `idx dtgt : α → Fin 4` with `idx` injective +
  avoiding `dtgt s` on each `G.closedHubNbhd s` for `s ∈ S` and `dtgt` injective on `S`,
  `∃ q, LinearIndepOn K (pencilChartPoint (ofCoord q) hubSel) S`. Route = v-b verbatim (`idx` → seed
  hub normals via `PencilSeed.ofCoord`; per-body `exists_injective_extension_of_isFin3SelectorOf`
  padding to an injective avoiding-`dtgt s` slot triple; `exists_smul_cross₃_pi_single` makes each
  point `cc • e_{dtgt s}` with `cc ≠ 0`; `linearIndepOn_smul_pi_single` + `.congr` from distinct
  targets). **DERIVATION GUARD met:** conclusion type-matches the L6b-i consumers (A)/(B) exactly (the
  `hsat_pt`/`hsat_adj` shape of `pencilNondegFeasible_of_selectors_of_satisfiable`). Needs no
  finiteness (`hHubSel` is a hypothesis; nothing in the body uses `[Finite _]`). Home = `Witness.lean`
  (with v-b, its extraction source); v-b/v-c left unrefactored (their `Fin 3`-vector conclusions
  differ in shape — refactor optional, deferred). No new FRICTION (faithful mirror, built first try;
  the `∀ s, ∃ x, s ∈ S → P` + `choose` idiom to avoid dependent choose is v-c's own pattern). Gates +
  axioms clean (`propext`/`Classical.choice`/`Quot.sound`). **Remaining L6b-ii: the per-set-shape
  `idx`/`dtgt` callers (A)/(B) from `hcard`+`htf` + headline wiring** (*Hand-off*).
- **W5-L6b-i LANDED — the pencil-feasibility assembly (compiler-checked spike, bank-authorized)**
  (2026-07-30, `Molecule/Pencil/Steer.lean`, `pencilNondegFeasible_of_selectors_of_satisfiable`;
  canonical `notes/Phase39-design.md` §"W5 leaf decomposition" L6b). Given global hub/neighbour
  selectors + the two satisfiable-somewhere chart-point-LI families (`{v}`/`closedNbhd v` per body;
  `{u,v}` per adjacent pair), produces `PencilNondegFeasible K G` — the L5-cut-v-e template
  `pencilNondegFeasible_induce_of_pendant_deg3` minus its `.mono` restriction (steer to common seed →
  reconstruct standing WF conjuncts → `fillNbr` re-choice → headline). **Home note:** lives in
  `Steer.lean`, NOT `Witness.lean` (the task's named target): the assembly needs Steer's common-seed
  primitive, and `Steer` imports `Witness`, so the headline cannot live in `Witness`. **Two spike
  findings that revise the design pin:** (1) the `IsFin3SelectorOf`-existence brick is NOT missing —
  it is the landed `exists_isFin3SelectorOf_of_ncard_le_three` (`Engine.lean:793`, `{s} (hfin) (hs)`);
  (2) the re-pinned headline signature is FALSE without looplessness — a loop `IsLink e v v` makes
  conjunct #5 `LinearIndependent ![point v, point v]` unsatisfiable, so `PencilNondegFeasible` is
  false; the assembly takes `[G.Loopless]` (the honest producer supplies `G′.Simple`, L6c). **L6b-ii
  (the two satisfiability families from `hcard`+`htf`) remains open** — spike-grounded as constructible
  via v-b's finite-`Fin 4` route (`htf` excludes the dependent loci; no route-breaker), a multi-commit
  generalization of v-b (see *Hand-off*). Friction review: none (faithful v-e mirror; only idiom is
  `open Classical in` for statement-level `if` decidability). Gates + axioms clean.
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
- **W5-L6b `hcard`-only pin REFUTED → habitat-foundations recon → L6b re-pinned triangle-free**
  (2026-07-30, two design-pass commits, both now superseded by the L6b-i/L6d landings above; canonical
  `notes/Phase39-design.md` §"W5 leaf decomposition" L6b/L6d). The bank-authorized spike refuted the
  `hcard`-only pin (a two-adjacent-hub triangle is `hcard ≤ 3` yet infeasible by
  `not_pencilNondegFeasible_of_triangle_two_hubs`); the follow-up recon then VERIFIED both habitat
  claims — (Q1) triangle ⟹ proper rigid at `|V| ≥ 4` is landed (`Graph.triangle_isProperRigidSubgraph`)
  and (Q2) `G′` is *fully* triangle-free at any degree-2 split (a `G′`-triangle forces an induced `C₄`,
  which is `D6`-rigid, ⊥ against `hnoRigid`; exhaustive `{2,3}`-degree search `n ≤ 8`, zero
  counterexamples) — so L6b took a triangle-free hypothesis and L6d became a THEOREM (safe not needed).
  Dispatch-log F9 instances (third optimistic-pin refutation, then first *confirmed* pin, of the L6 arc).
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
- **L5-cut-v-f (output-half steering, COMPLETE, one-lined; canonical `notes/Phase39-design.md`
  §"W5 leaf decomposition" L5-cut-v "v-f decomposition" + git).** v-f-6 assembly
  `exists_isNondegPencilRealization_induce_promotedNormal_of_pendant_deg3` (`Steer.lean`, the v-e
  mirror producing the `H`-realization at target rank + the promoted `∀ v ∈ {u_c,w₁,w₂}` normal-LI
  family, one `exists_common_seed_pencilRow_and_polynomials` call; v-f-5 dropped). v-f-1…4 rank-transport
  chain + input/normal-congr bricks (`pencilRow_mem_rigidityRows_of_mem_edgeSet`,
  `span_rigidityRows_eq_of_supportExtensor_proportional`,
  `exists_smul_supportExtensor_eq_pencilChartFramework_of_reseed`,
  `finrank_span_rigidityRows_pencilChartFramework_eq_of_independent_pencilRow`,
  `pencilChartFramework_congr`, `linearIndepOn_pencilChartNormal_congr`). FRICTION `[mirror-candidate]`
  `extensor_pair_smul` (kept local).
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
- **L5-cut-v-d + v-c (steering re-choice / flattening / gadgets / witness (ii), COMPLETE, one-lined;
  canonical `notes/Phase39-design.md` §"W5 leaf decomposition" L5-cut-v + git).** v-d
  `exists_fillNbr_pencilChartWF_of_standing` (`Steer.lean`, the `fillNbr`-only re-choice closing
  `PencilChartWF`'s fourth conjunct; core `exists_extend_linearIndependent`, FRICTION
  `[mirror-candidate]`; retired `exists_fin3_rank_injOn`); the `PencilSeed.toCoord` WF-flattening
  witnesses (`pencilChartWF_standing_ofCoord_toCoord`, `Fin.cons` motive → TACTICS-QUIRKS § 96); the
  extraction gadgets `exists_polynomial_ne_zero_of_linearIndependent_pencilChart{Point,Normal}`
  (`Engine.lean`). v-c witness (ii) `exists_coord_linearIndependent_pencilChartNormal_of_pendant_deg3`
  (`Witness.lean`, the v-b mirror on `H`'s chart; carries the pendant `hVG`, `v_c` a deg-`1` non-hub).
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
