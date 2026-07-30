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
`H := G.induce V₁`'s chart, reusing v-b's toolkit + combinatorics); **v-d COMPLETE** (2026-07-25
extraction gadget `Engine.lean`; 2026-07-29 WF-flattening bridge + `fillNbr` re-choice, new file
`Molecule/Pencil/Steer.lean`; the superseded `exists_fin3_rank_injOn` retired same commit); **v-e
COMPLETE** (2026-07-29, the input-half assembly `pencilNondegFeasible_induce_of_pendant_deg3`,
`Steer.lean`: steer `G`'s re-seeded witness to a common seed carrying the demoted triple alongside
every standing WF condition, `fillNbr` re-choice → full `PencilChartWF`, chart realization restricted
to `H := G.induce V₁`); **v-f-1…4 LANDED** (2026-07-29, the output-half rank-transport bricks,
`Steer.lean`); **v-f-6 input bricks LANDED** (2026-07-29, `Steer.lean`: the owed
`pencilChartFramework_congr` helper + the re-seed rank transport `hLI` producer
`exists_independent_pencilRow_subfamily_at_toCoord_of_reseed`); **v-f-6 normal-congr + promoted-family
transfer LANDED** (2026-07-29, `Steer.lean`: `pencilChartNormal_congr` +
`linearIndepOn_pencilChartNormal_congr`); **v-f-6 assembly proper + v-g next** — *Hand-off*.
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
  `pencilChartNormalPoly`/`nbrSlotPointPoly` mirror). **v-d WF-flattening witnesses + `fillNbr`
  re-choice LANDED, v-d COMPLETE** (2026-07-29, new file `Molecule/Pencil/Steer.lean`:
  `PencilSeed.toCoord` + coincidence + `pencilChartWF_standing_ofCoord_toCoord` for the four standing
  conjuncts, then `exists_fillNbr_pencilChartWF_of_standing` closing conjunct 4 by the general
  extension lemma `exists_extend_linearIndependent`). `exists_fin3_rank_injOn` (`Engine.lean`)
  **RETIRED** same commit (deletion-hygiene sweep done — the re-choice does not consume it; it uses
  the "extend an LI partial family by filling free slots" route, not the pigeonhole). **v-e COMPLETE
  (2026-07-29): input-half assembly `pencilNondegFeasible_induce_of_pendant_deg3` landed** (*Hand-off*).
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

**v-d/v-e COMPLETE — the input half is closed** (`Steer.lean`; *Decisions made*). `Steer.lean` now
carries the flattening bridge, `exists_extend_linearIndependent`, the `fillNbr` re-choice
`exists_fillNbr_pencilChartWF_of_standing`, the common-seed primitive
`exists_common_seed_linearIndepOn_pencilChartPoint`, and the assembled input half
`pencilNondegFeasible_induce_of_pendant_deg3` (its signature mirrors witness (i)'s config + `hVG`,
adds `[Infinite K]`, concludes `PencilNondegFeasible K (G.induce V₁)`).

**v-f RECONNED + compiler-spiked (2026-07-29) — GO, no obstruction.** The output-half rank-transport
is a faithful pencil-mirror of the landed panel lemma
`finrank_span_rigidityRows_ofNormals_of_isGenericNormals`; decomposed into six S=1 leaves (v-f-1…v-f-6),
each with an EXACT signature, in `notes/Phase39-design.md` §"W5 leaf decomposition" L5-cut-v **"v-f
decomposition"**. Load-bearing finding: the general `BodyHingeFramework` panel-row machinery (`panelRow`,
`panelRow_mem_rigidityRows_of_link`, `exists_independent_panelRow_subfamily_of_le_finrank`,
`finrank_span_rigidityRows_add_deficiency_le`) is REUSABLE on the chart verbatim — the Pencil import cone
already reaches it, so no new import and no re-proof of the extraction/B2 layer. A scratchpad spike built
the bridge (v-f-1), the row-span scaling invariance (v-f-2), and the full `le_antisymm` composition
(v-f-4) **sorry-free + axiom-clean**; the composition's only residual is the LI `pencilRow` subfamily at
the steered seed + nonzero hinges — both produced from landed bricks (v-b/v-c witnesses,
`exists_smul_eq_extensor_of_extensorThroughPoint_pair`, `exists_common_seed_pencilRow_and_polynomials`).

**v-f-1…4 LANDED (2026-07-29, `Steer.lean`; *Decisions made*).** The four genuinely-new rank bricks:
v-f-1 link bridge (`pencilRow_mem_rigidityRows_of_mem_edgeSet`), v-f-2 row-span scaling invariance
(`span_rigidityRows_eq_of_supportExtensor_proportional`), v-f-3 re-seeding proportionality
(`exists_smul_supportExtensor_eq_pencilChartFramework_of_reseed`), v-f-4 output rank `le_antisymm`
(`finrank_span_rigidityRows_pencilChartFramework_eq_of_independent_pencilRow`). The general
`BodyHingeFramework` panel-row machinery was reused verbatim (no new import).

**v-f-6 input bricks + normal-congr + promoted-family transfer LANDED (2026-07-29, `Steer.lean`;
*Decisions made*).** Rank transport: `pencilChartFramework_congr`, the v-f-2∘v-f-3 span-transfer
`span_rigidityRows_pencilChartFramework_eq_of_reseed`, and the `hLI` producer
`exists_independent_pencilRow_subfamily_at_toCoord_of_reseed` (an LI `pencilRow` subfamily of the
target size at the flattening `seed₁.toCoord`) — exactly the rank-rows input the assembly's
`exists_common_seed_pencilRow_and_polynomials` call consumes. Promoted-family transfer:
`pencilChartNormal_congr` (third `_congr` sibling — the normal reads `fillNbr` only through a non-hub
`cross₃` at unassigned slots, so a point-preserving `fillNbr` re-choice preserves it at any hub or
fully-assigned body) + `linearIndepOn_pencilChartNormal_congr` (the `LinearIndepOn` transfer of the
steered promoted families from `PencilSeed.ofCoord q` to the re-chosen `seed'`, given the
`fillNbr`-free condition `hassigned`).

**Next concrete commit — v-f-6 (the output-half assembly proper).** Input = the IH's *generic*
`H`-witness (unpacked `IsNondegPencilRealization (G.induce V₁) F₁ normal₁ point₁` + `hrank₁ :
finrank = target_H`, the sub-case-3 producer's shape). Distinct from v-e (which re-seeds `G`'s
feasibility witness): here the **rank rows** come from re-seeding the generic `H`-witness. Sketch:
`exists_pencilSeed_of_nondeg` on the `H`-witness → `hpt` (points reproduced up to a per-body scalar);
`exists_independent_pencilRow_subfamily_at_toCoord_of_reseed` (landed) → the `hLI` at
`N := target_H.toNat` (needs `0 ≤ target_H` + `Nat.card = target_H` bookkeeping, mirroring the panel
`finrank_span_rigidityRows_ofNormals_of_isGenericNormals`); then ONE
`exists_common_seed_pencilRow_and_polynomials` call (`ends := H.endsOf`) whose `P` = the standing
point conditions (each via `exists_polynomial_ne_zero_of_linearIndependent_pencilChartPoint`,
satisfiable at the flattening `pencilChartWF_standing_ofCoord_toCoord`) + the promoted normal
families (witness (ii) `v-c` `exists_coord_linearIndependent_pencilChartNormal_of_pendant_deg3`, via
`exists_polynomial_ne_zero_of_linearIndependent_pencilChartNormal`); at the common seed, reconstruct
standing WF + `fillNbr` re-choice (`exists_fillNbr_pencilChartWF_of_standing`, copy-adaptable from
v-e) → `IsNondegPencilRealization H`; rank via v-f-4
(`finrank_span_rigidityRows_pencilChartFramework_eq_of_independent_pencilRow` — feed the common-seed
`hLI` + nonzero hinges); the promoted families transferred to the re-chosen `seed'` via the landed
`linearIndepOn_pencilChartNormal_congr`. **The promoted-family transfer COMPOSES (verified this
dispatch — no obstruction):** its `hassigned` discharge for each `G.closedHubNbhd v`
(`v ∈ {u_c,w₁,w₂}`) is standard bookkeeping — every member is a `G`-hub, hence in `V₁` (`v_c` is a
non-hub, `hvc_nothub`); a member `≠ u_c` keeps its degree in `H` (`Graph.degree_induce_eq_of_ne`) so
stays an `H`-hub (premise vacuous); at `u_c` (the sole demotion) `nbrSel u_c` is total since
`H.closedNbhd u_c = {u_c,w₁,w₂}` has three members (a `Fin 3`-selector of a 3-element set is total —
a small pigeonhole `have`, not yet landed). Output: a generic realization of `H`
(= `HasGenericPencilRealization K n H`) PLUS `∀ v ∈ {u_c,w₁,w₂}, LinearIndepOn K normal
(G.closedHubNbhd v)`. **v-f-5** (the optional clean-mirror normal primitive
`exists_common_seed_linearIndepOn_pencilChartNormal`) may be folded in.
Then **v-g** (the sub-case-3-shaped glue — conjunct 3 at `u_c`/`w₁`/`w₂` from the steered promoted
families, `hlb₂ = 0` rank verbatim — plus the shell/successor rewire: discharge `hcutPendant3` in
`pencilPair_of_not_twoEdgeConnected` and `pencil_conjecture_of_arms_pair`, add `[Infinite K]` there,
and the blueprint restatement). Full leaf detail + exact signatures:
`notes/Phase39-design.md` §"W5 leaf decomposition" L5-cut-v "v-f decomposition".

**L6/L8 are parallel combinatorial tracks** buildable now (L6: habitat feasibility, the
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

- **L5-cut-v-f-6 (normal-congr + promoted-family transfer) LANDED** (2026-07-29,
  `Molecule/Pencil/Steer.lean`): the output-half assembly's promoted-family transfer.
  `pencilChartNormal_congr` (the third `_congr` sibling of `pencilChartPoint_congr`/
  `pencilChartFramework_congr`) — a point-preserving `fillNbr` re-choice preserves `pencilChartNormal
  G v` at any pencil hub (reads the shared `hubNormal`) or fully-assigned non-hub (its non-hub
  `cross₃` reads only `pencilChartPoint`s of selected neighbours, `fillNbr`-free), captured by the
  hypothesis `hassigned : ¬G.PencilHub v → ∀ i, (nbrSel v i).isSome`. `linearIndepOn_pencilChartNormal_congr`
  transfers the steered v-c families from `PencilSeed.ofCoord q` to the re-chosen `seed'`
  (`LinearIndepOn.congr` + pointwise). Composition of the `hassigned` discharge for the pendant config
  verified (analysis in *Hand-off*; all needed lemmas confirmed present) — no obstruction. No new
  FRICTION (mirrors the landed `pencilChartPoint_congr`). Gates green (build warning-clean + lint);
  axioms clean (`propext`/`Classical.choice`/`Quot.sound`).
- **L5-cut-v-f-6 (input bricks) LANDED — the re-seed rank transport** (2026-07-29,
  `Molecule/Pencil/Steer.lean`): the pieces the v-f-6 assembly needs before its steering call.
  `pencilChartFramework_congr` (the owed helper — framework reads the seed only through
  `pencilChartPoint`, so equal points ⟹ equal framework; structure-eta `calc`, no `@[ext]` on
  `BodyHingeFramework`); `span_rigidityRows_pencilChartFramework_eq_of_reseed` (v-f-2 ∘ v-f-3);
  `exists_independent_pencilRow_subfamily_at_toCoord_of_reseed` (the `hLI` producer: an LI
  `pencilRow` subfamily of the target size at the flattening `seed₁.toCoord`, via the general
  `exists_independent_panelRow_subfamily_of_le_finrank` + v-f-1). No new FRICTION (the one build-cycle
  was the TACTICS-QUIRKS § 508 ascription-doesn't-redirect class). Gates + axioms clean.
- **L5-cut-v-f-1…4 LANDED — the output-half rank-transport bricks** (2026-07-29,
  `Molecule/Pencil/Steer.lean`): **v-f-1** link bridge (`pencilRow_mem_rigidityRows_of_mem_edgeSet` +
  helper `pencilRow_eq_panelRow_pencilChartFramework`) — a genuine-edge chart `pencilRow` IS the chart
  framework's own `panelRow`, hence a rigidity row (landed general `panelRow_mem_rigidityRows_of_link`);
  **v-f-2** row-span scaling invariance (`span_rigidityRows_eq_of_supportExtensor_proportional`) — per-edge
  proportional support extensors ⟹ equal rigidity-row spans (`Submodule.span_singleton_smul_eq`);
  **v-f-3** the one new leaf, re-seeding proportionality
  (`exists_smul_supportExtensor_eq_pencilChartFramework_of_reseed`) — the re-seeded chart hinge is a
  nonzero multiple of the witness hinge, via `exists_smul_eq_extensor_of_extensorThroughPoint_pair` +
  extensor bilinearity (local `extensor_pair_smul`); **v-f-4** output rank `le_antisymm`
  (`finrank_span_rigidityRows_pencilChartFramework_eq_of_independent_pencilRow`) — LI `pencilRow`
  subfamily of size target + nonzero hinges ⟹ `finrank = target` (lower = v-f-1 + `finrank_span_eq_card`
  + `Submodule.finrank_mono`; upper = B2 `finrank_span_rigidityRows_add_deficiency_le`). The general
  `BodyHingeFramework` panel-row machinery reused verbatim (no new import, no re-proof). FRICTION
  `[mirror-candidate]`: `extensor_pair_smul` (belongs in `Extensor.lean`, kept local pending the
  deep-rebuild-free mirror). Gates green (build warning-clean + lint); axioms clean.
- **L5-cut-v-f RECONNED + compiler-spiked — output-half rank-transport, GO no obstruction** (2026-07-29,
  design-pass, docs-only; canonical record `notes/Phase39-design.md` §"W5 leaf decomposition" L5-cut-v
  "v-f decomposition"). The output half is a faithful pencil-mirror of the landed panel lemma
  `finrank_span_rigidityRows_ofNormals_of_isGenericNormals`; decomposed into six S=1 leaves with exact
  signatures. Load-bearing finding: the general `BodyHingeFramework` panel-row machinery (`panelRow`,
  `panelRow_mem_rigidityRows_of_link`, `exists_independent_panelRow_subfamily_of_le_finrank`, the B2
  bound) is reusable on the chart verbatim (cone already reaches it — no new import, no re-proof). A
  scratchpad spike built the bridge, the row-span scaling invariance, and the full `le_antisymm`
  composition sorry-free + axiom-clean; composition finding (4) composes exactly as pinned, residual =
  the LI `pencilRow` subfamily + nonzero hinges (both landed-brick-fed). No motive/IH change.
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
