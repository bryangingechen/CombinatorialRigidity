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
`hcontract`/`hsplit`, all L5-cut-v leaves landed; **L6 decomposed 2026-07-29 into L6a/L6b/L6c, next
commit = L6a**; L8 parallel; L7, the research core, last).

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

**W5-L5 is closed modulo TWO carried hypotheses** (loop/base/cut arms + the successor
`pencil_conjecture_of_arms_pair`, `Pencil/Pair2.lean`, node
`thm:pencil-conditional-realization-pair` green over `[Infinite K]`; only `hcontract` (W4) and
`hsplit` (W5-L6/L7/L8) remain open — full detail in *Decisions made*, below). **L5-cut-v CLOSED
2026-07-29** (v-g part 2): `hcutPendant3` is discharged inline by
`hasGenericPencilRealization_pendant_deg3_of_IH` (`Pair2.lean`), so both
`pencilPair_of_not_twoEdgeConnected` and `pencil_conjecture_of_arms_pair` dropped it and gained
`[Infinite K]`.

**Next concrete commit — pick up one of the three remaining W5 leaves (L6/L7/L8) or W4** (each still
gated on `hsplit`/`hcontract`). The natural first steps:
- **W5-L6** (habitat feasibility) — **decomposed 2026-07-29** into L6a (the `≤ 3`
  closed-hub-neighbourhood lemma), L6b (the general-position witness seed →
  `PencilNondegFeasible K G′`, spike-first), and L6c (`G′.Simple`, a citation to the LANDED
  `splitOff_simple_of_noRigid_of_card`, folded into L7). **L6a as first pinned is REFUTED
  (2026-07-29):** the bare `2EC + no-proper-rigid ⟹ ≤ 3` claim is FALSE (computer-verified theta-graph
  counterexample, all four hyps hold yet `closedHubNbhd v = 4`; the counterexample is strictly sparse,
  `f(V) = −3`, so the true habitat likely carries an omitted rigidity/tightness invariant). Full
  counterexample + candidate re-routes: `notes/Phase39-design.md` §"W5 leaf decomposition" L6a.
  **Next concrete commit: a dedicated L6a proof-route recon** — settle the correct invariant at the
  use-site `G′ = G.splitOff v a b e₀` (candidates: `G` rigid/spanning-circuit; 3-edge-connectivity;
  max-degree) and the L6→L7 `hcard` wiring, then re-pin L6a's signature. L6 feeds L7, NOT `hsplit`
  directly.
- **W5-L8** (parallel combinatorial track, buildable now, UNAFFECTED by the L6a refutation): the
  `k = 0` residue, emptiness route recommended. **L6b** (takes the `≤ 3` bound as an explicit
  `hcard` hypothesis) is likewise independently buildable now — either is a viable pivot if the L6a
  recon stalls.
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

- **W5-L6 decomposed (L6a/L6b/L6c), then L6a-as-pinned REFUTED** (2026-07-29; design pass `6768bd33`
  + coordinator salvage this commit). The L6 design-pass recon split habitat feasibility into L6a
  (the `≤ 3` closed-hub-neighbourhood combinatorial lemma), L6b (the witness seed →
  `PencilNondegFeasible K G′`, decoupled via an explicit `hcard` hypothesis), L6c (`G′.Simple` = the
  landed `splitOff_simple_of_noRigid_of_card`, a citation — a real simplification). The L6a build then
  **refuted** its own pinned signature with a computer-verified counterexample (theta graph, arcs
  `(6,6,6)`: 2EC + no-proper-rigid, yet four degree-3 hubs ⟹ `closedHubNbhd = 4`), returning BLOCKED
  with no commit — the bare `2EC + no-proper-rigid` hypotheses do NOT bound the closed hub
  neighbourhood. Canonical counterexample + candidate re-routes: `notes/Phase39-design.md` §"W5 leaf
  decomposition" L6a. **Next: a dedicated L6a proof-route recon** to settle the true use-site invariant
  (`G′ = G.splitOff v a b e₀`) — the counterexample is strictly sparse (`f(V) = −3`), so a
  rigidity/tightness invariant is the leading candidate. L6b/L8 unaffected. Dispatch-log F9 instance.
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
