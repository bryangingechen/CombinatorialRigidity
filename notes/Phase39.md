# Phase 39 — PENCIL: the hinge-pencil molecular conjecture (work log)

**Status:** in progress — phase stays OPEN (standing user adjudications of 2026-07-24 /
2026-07-30 / 2026-08-02, quoted verbatim in *Current state*). W0–W3 and the whole W5 arc
(L0–L7) are COMPLETE — `hsplit` CLOSED IN FULL and `hfresh`'s counting discharge landed
(2026-07-30). Only three items remain, all carried by the landed successor
`pencil_conjecture_of_hcontract_hK_hbareSplit_of_card` (`Molecule/Pencil/Escape.lean`):
`hcontract` (W4), kernel `hK`, and kernel `hbareSplit` — see *Hand-off*. **Thirty-two
kernel-(K) directions are now COMPLETE** (2026-08-05 → 08-19, ordinals 1–24; roster and
per-direction theorem chain in *Decisions made*). **The SIXTH and SEVENTH FAN-OUTS ARE
BOTH COMPLETE** (all ten directions LANDED 2026-08-19). Headline HITs: **route-ledger
entry 5 PROVEN in both halves**, the arc's first HIT (GBAL, discharging input (X));
**chart irreducibility PROVEN**, all consumers clean (CIRR); **the AA-glue configuration
NOT realizable at `n_hub = 8`, the (GR-38) kill a non-vacuous THEOREM there** (AGLU, a
HIT on the "not realizable" branch — though its dispatch-predicted binding-laminarity
consequence is itself REFUTED, 3 774 crossing pairs at `n_hub = 8`). Also landed:
§(K-frame) (FR-4) CLOSED (FRES); §(K-out) (OC-8) reshaped (OCON, ZNEQ); §(K-Λ) item
(vii) REALIZED (LTWO); (b′) OPEN/NOT-a-HIT with an exact `n_hub = 8` boundary (BALB);
input (Y) an honest MISS with substantial positive content (YLOC) — full detail in
*Decisions made*. **(GR-15) stays OPEN throughout; class uniformity untouched; no
g-flank at any of the thirty-two directions. E3 is ARMED (by GBAL) and has NOT fired.**
Direction codes are **multi-letter and topic-tagged from the fifth fan-out on**
(`notes/Pencil-labels.md` (L5)); grandfathered single letters are re-used across dates,
**always date those**.
**The doc-split AND discipline-distillation rounds are BOTH COMPLETE**
(all three slices, `notes/Pencil-structure.md`; the new `RESEARCH-ARC.md`
promotes this phase's dispatch discipline). **Next: UNROUTED** — the
kernel-(K) research step awaits a pick (candidates AGLU/ZNEQ, see
*Hand-off*); ZNEQ's `σ > 0` disproof hunt stays excluded pending user
adjudication.

## Current state

**The phase stays OPEN.** Standing user adjudications, verbatim (these are the live GO/NO-GO
constraints; the dated dispatch narrative is in *Decisions made* and git):

- **2026-07-24:** *"Let's leave the phase open and continue the work on the conjecture in this
  phase. Unless there's a good reason to split here."*
- **2026-07-30, kernel (K):** *"Route 3: build now"*, then on the (K) non-constancy options
  *"C: literature hunt + A"* — keep carrying `hK` as pinned; option B (commission the
  stress-function infrastructure) is **NOT** commissioned.
- **2026-07-30, kernel (K-bare):** *"C: cheap numerics extensions + A"* — keep carrying
  `hbareSplit` as pinned; option B (the insertion-calculus research) is **NOT** commissioned.
- **2026-08-02, W4:** route **3, packaging (b)** — the structure-theorem-pinned dispatch
  invariant, with (K-res) carried as a sibling of the byte-identical `hK` — **recorded as a
  decision, not built; W4 stays parked** while the (K)-family research continues.
- **2026-08-05, the standing reproducibility requirement:** *"in general, I would like all of
  the scripts we run to be committed for reproducibility"* — now a hard rule of the harness
  (`notes/scripts/README.md`); every script the project runs is tracked, probes included.
- **2026-08-05…07, second through fifth fan-outs (all COMPLETE; user-adjudicated).**
  T/R/M, G/Q/O, E/J, PEX/TCOL; route σ / W4 / the (FR-6) follow-ons not selected at any of
  them; cap lifted, rescue §1 pre-authorized (`notes/Pencil-fanout-archive.md` §§"Second"–"Fifth").
- **2026-08-07, delegation adjudication (binds from the SIXTH direction on).** Asked at the
  session-start check-in what to do once TCOL lands, the user selected **"Keep going on my
  own judgment"** — *"After landing TCOL I pick the next direction from the hand-off's
  candidate list and continue dispatching without checking in."* This delegates **selection
  only** and changes **no** standing constraint (phase OPEN; Lean hold stands; W4 PARKED;
  `hK`/`hbareSplit` pinned; option B un-commissioned), the same check-in's top-rung/cap/
  rescue calls unchanged; the SIXTH–ELEVENTH picks under it are one-lined in *Decisions made*.
- **2026-08-12, seventh-direction delegation (refines the above; changes no standing
  constraint).** The user, verbatim: *"Let's have a fable subagent make the decision / do a
  reprioritization and then follow its guidance."* — the precedent that the pick may itself
  be delegated to a **top-rung fable recon**. Its verdict (GCAP) was verified, accepted and
  LANDED 2026-08-13 (`notes/Pencil-fanout-archive.md` §"Seventh direction"). Same check-in: top rung
  = fable (opus only if the weekly limit runs out); cap **lifted**; rescue §1 mechanical
  fixups **pre-authorized** — all still binding.
- **2026-08-13, phase-shape adjudication, then ninth- through fourteenth-direction
  selections (none changed a standing constraint; full detail `notes/Pencil-fanout-archive.md`
  §§"Ninth"–"Fourteenth direction", the fable/opus rung deviation in
  `notes/dispatch-log.md`).** Offered a handoff-to-fresh-session option after GUNIF's
  refutation, the user **RESOLVED: the research arc CONTINUES**, selection falling back to
  the standing 2026-08-07 delegation. Ninth–eleventh **re-delegated to a top-rung fable
  recon** — **GEXIST**/**GORIENT**/**GDEV** verified and ACCEPTED, landed 08-13/13/15.
  Twelfth **BROKE the fable-recon streak** — coordinator-authored prep from GDEV's
  routing clause, no independent ranking of the losers — **GADM** PREPPED and LANDED
  08-17. Thirteenth **returned to the fable-recon shape** — **GPSA** (entry 5 BOTH
  halves) verified and ACCEPTED, **including its OVERRIDE of GADM's shift-metric routing
  clause** (every GADM bar upheld). Fourteenth had **no selection pass** — GPSA's own
  landed otherwise-clause routed it deterministically to the stuck blocking configuration,
  dispatched at **opus** against a top-rung-mapped task (a logged deviation) — **GDESC**
  LANDED 08-18; the **FIFTEENTH was left un-dispatched**, its routing a coordinator/user
  call between input (X) and (a′).
- **2026-08-19, sixth-fan-out dispatch — a NEW shape (user-adjudicated multidispatch;
  changes no standing constraint).** Asked how to proceed with the unrouted fifteenth, the
  user elected a **multidispatch of five concurrent opus directions**, verbatim: *"I'd like
  to try a multidispatch of opus agents here. Keep an eye on the 5h session limits and
  let's dispatch as many agents as we can on independent directions so that we can
  maximize the number of ideas we make progress on at once without getting interrupted."*
  Five directions dispatched concurrently — **GBAL**/**GLAW** (compute-licensed tier),
  **OCON**/**LTWO**/**FRES** (derivation-first tier), tier split and label reservations
  coordinator-set (`notes/Pencil-fanout-archive.md` §"Sixth fan-out"). **All five LANDED
  2026-08-19; the fan-out is COMPLETE** — verdicts in the header and *Decisions made*.

- **2026-08-19, seventh-fan-out dispatch — the multidispatch shape RE-ELECTED (changes no
  standing constraint).** Offered four ways to make the twentieth pick (fable recon /
  coordinator prep / multidispatch again / coordinator picks under the 2026-08-07
  delegation), the user chose **"Multidispatch fan-out again"** — over a coordinator
  recommendation *against* it on a 92 % `weekly_scoped` reading, which the user then
  overturned with the fact that settled it, verbatim: *"weekly_scoped is only for fable so
  multidispatch should be OK."* Five directions dispatched concurrently at **opus** —
  **YLOC**/**BALB**/**AGLU** (§(K-grid)), **ZNEQ** (§(K-out)), **CIRR** (new §(K-chart)) —
  tier split, direction selection and label reservations **coordinator-set**, so the
  twelfth's disclosure applies: **no independent top-rung ranking of the losers**, itemized
  in `notes/Pencil-fanout.md` §"Seventh fan-out". Same check-in: rungs **sonnet + opus only,
  top rung = opus** (fable conserved), cap **lifted**, rescue §1 fixups **pre-authorized**.
  One coordinator sharpening is recorded there and **overrides GLAW's landed routing
  clause** (routing only, not its mathematics): GLAW recommended matching-flexibility
  toggles for input (Y) **blind to GBAL**, which discharged the sibling input (X) by an
  instrument that dissolves the matching apparatus — so YLOC is specced on **GBAL's
  instrument at the chunk level** instead. **All five LANDED 2026-08-19; the fan-out is
  COMPLETE** — verdicts in the header and *Decisions made*.

**Kernel-(K) research arc — forty-nine docs+scripts-only dispatches, plus seven
strategy-only passes** (2026-08-02 → 08-19). Which pass was which is one-lined in *Decisions
made*; the rule is that the **dispatch** count moves only on a landing (GBAL/GLAW/FRES/OCON/
LTWO are the fortieth through forty-fourth; CIRR the forty-fifth; YLOC the forty-sixth; BALB
the forty-seventh; ZNEQ the forty-eighth; AGLU the forty-ninth), and a **user call on dispatch
*shape*** — either multidispatch election, or a coordinator-authored pick like the twelfth's —
contributes **no** strategy pass.
Canonical homes: workbook `notes/Pencil-informal.md` (**State of (K)** map = entry point),
`notes/Pencil-W4-informal.md` (W4-residual), `notes/Pencil-strategy.md` (strategy). Net
effect: **disproof risk removed**, every refuted route/gap has a successor in the gap map,
several structural positives proven, and **route-ledger entry 5 is PROVEN, the arc's first
HIT**; **class uniformity of the escape remains untouched by all forty-nine.**
**Doc-debt round CLOSED — `notes/Pencil-cleanup.md`** (2026-08-13, category D only; D-5 a
watch item; the D-2 fix's regression history is in `notes/check-gapmap-cells.py`'s docstring).

> **The one live candidate, and it is NOT settled — `notes/Pencil-informal.md` §(K-σ)** (the
> canonical home for the four obligations, the `--hunt` findings, the validation scope and the
> *Field scope* caveat; the *Hand-off* blockquote carries the forward half — neither restated
> here). **Route σ** = route A at the dual seed `σu` (the polarity replaces every body's point
> by its own panel normal); it would close (K-tight) on the hard stratum, *length-free*, via
> `Λ²Π̂(b) + Λ²Π̂(c) + α_{pt(b)} = K⁶`. **Offered for adjudication**, resting on four
> obligations (the first shrunk to two conditions) and **no longer field-blocked** (§(K-clos):
> the polarity generalizes, `ℝ` the *narrowest* field choice). Standing consequences: no
> gap-map status moves on its account; `hK`/`hbareSplit` stay pinned; **W4 PARKED**; the phase
> does **not** close.

The other candidate continuations, unselected (items (a)/(g) are **DONE** as second-fan-out
directions M and R); each has a canonical home carrying the detail, not restated here:
**(b)** **(K-wit)**, the pitch route's single live form at companion splits (§(K-Λ); its
(OC-8) residue reduces to `Z ≠ ∅` + chart irreducibility (**DONE**, CIRR) + one rigid chart
point — `Z ≠ ∅` itself **FACTORS** (**DONE**, ZNEQ): a necessary-for-`hK` half dominated
by §(K-grid) (GR-10), and a target-rank half open at the same shape as (OC-19)(c)); **(c)** the **W4 build**,
decomposed and buildable, **PARKED** by the Lean hold; **(d)** the companion-length dichotomy
frame (§(K-dom) *D7*) + the unprobed `k ≥ 4` parallel-edge item (§(K-pure) *P4*); **(e)**
§(K-Λ) item (vii)'s residual — since LTWO a **named, non-empty, floor-classified** family (the
uniform `g₁₄` statement over every two-hub-interior class shape's chart); **(f)** strategy
§4.6's shortlist, **partially superseded** for the tight stratum; U3 still unrun.

**Read `notes/Pencil-strategy.md` before choosing anything else** — the post-fan-out strategic
record (why class uniformity resists, what the KT formalization yielded, the candidate stronger
invariants with **C1 run and struck**, §5's symbolic assessment); its header is its own table of
contents. **Its §4.6** is the entry point for any attack on the crux: six refutations plus the
ranked `U1`–`U3` shortlist, each with its cheapest decisive experiment.

**Any (K)- or W4-side numerics dispatch starts from `notes/scripts/README.md`** (a symbolic
one also from `notes/scripts/m2/README.md`); detail in *Blockers*.

File layout: `Molecule/Pencil.lean` split into `Molecule/Pencil/{Statement,Arms,Motive,Chart,
Engine,Reseed,Witness,Steer,Pair,Pair2,Escape,Base}.lean`; per-leaf history
`notes/Phase39-design.md` §"W5 leaf decomposition" + §"W5-L7 research recon".

## The question

KT's theorem (formalized: `molecular_conjecture`, Phases 17–26; the multigraph/coplanar-model
strengthening, Phase 35) says the generic body-hinge rank in `ℝ³` is already achieved on the
*panel* stratum — each body's hinges coplanar — and, by projective duality (Phase 25), on the
*molecular* stratum — each body's hinges concurrent. PENCIL asks about the **intersection
stratum**: each body's hinges both concurrent *and* coplanar, i.e. a **pencil** of lines through
a point in a plane. Does a pencil realization generic in that stratum still achieve the generic
body-hinge rank (Tay's tree-packing count; `5G` ⊇ 6 edge-disjoint spanning trees at `d = 3` via
KT Cor. 5.7)?

In the `G²` molecular reading (Phase 25/26 modelling) the hinges at the body of atom `v` are the
bond lines through `p(v)` — concurrency is automatic — so the pencil condition says **`v`'s
bond-star is coplanar**. Chemically: sp²/planar-bonded atoms, i.e. *does the molecular count
stay valid for molecules with planar-bonded atoms?* The condition only bites at bodies of degree
`≥ 3`.

Trivial direction: pencil ⇒ panel per body, so pencil rank ≤ generic (KT). The content is the
lower bound. The all-bodies statement is the strongest form: any mixed version follows by rank
lower-semicontinuity. The queue entry hoped for a warmup; the opening recon **refuted the warmup
premise** — the carrier material is all in-tree, but three KT proof steps consume panel-only
freedom the pencil pin removes. As of 2026-07-23 no literature result on this stratum was found
(Jordán 2016 and the KT paper are silent) — **this is new mathematics**, and the two subsequent
literature hunts (2026-07-30 rigidity-side, 2026-08-05 Δ-matroid-side) are both MISSes for
**complementary** reasons (§(K-Δ)).

## Opening recon verdicts (R1–R3, landed 2026-07-23)

Full record, grounding, and the W0–W5 decomposition: **`notes/Phase39-design.md`**.
One-liners, kept because each still constrains statements: **R1** — statement pinned in the
Phase-35 containment model + `ExtensorThroughPoint` (dual of `ExtensorInPanel`); satisfiable
for every graph; self-dual on-stratum via `screwComplementIso` (§(K-clos) (AC-1)). **R2** —
survives all exact-rational rank tests; the queued warmup claim is *bar-joint-side*,
**false** for body-hinge on dense graphs. **R3** — KT Lemma 6.2 / Case II survive with
pinned choices; three open cores (outer Thm-5.6 strip-extend, Case-I glue Claim 6.4,
Case III Claim 6.12 span break).

## Blockers / open questions

**All W5 blockers are CLOSED** (2026-07-24 → 07-30; verdicts one-lined in *Decisions made*, full
record in `notes/Phase39-design.md` + git). **One residual note from the L5 cut arm still
stands** because it constrains future statements: feasibility propagation *as a proposition* is
refuted for any purely combinatorial (`≤3`-closedHubNbhd) criterion
(`not_pencilNondegFeasible_of_triangle_two_hubs`).

- **Open: kernels (K) and (K-bare), and W4 (`hcontract`)** — the entire remaining work of the
  phase; see *Hand-off* for the per-item route and the `notes/Phase39-design.md` pointers. W4 is
  fully decomposed (recons of 2026-07-30): buildable leaves W4-L4b/L1/L2/L3′/L5 plus the carried
  `hKc`/`hbareContract`/`hnoGood'`; the build sequence awaits commissioning. **`hnoGood'` is
  known NON-vacuous** (2026-08-02) — branch 4 needs content; routes in
  `notes/Pencil-W4-informal.md` §"`hnoGood'` vacuity", adjudication owed. **(SAFE-RES) is
  REFUTED** (same day); routes 1/3 now cost §(SAFE-RES)'s (T) + (V) + the reduced (E), with (T) a
  genuine research gap, plus **one** widened kernel (K-res).
- The full biconditional transport (design doc's W0 pin) is landed only as its two forward
  implications; the reverse arms need a `complementIso` involution lemma, not in tree —
  deferred, **off every critical path** (§(K-σ) *Step σ6*).
- **Harness debt — CLEARED, round CLOSED** (2026-08-06, S1–S4; canonical home
  `notes/scripts/README.md` — read before any numerics dispatch; treat any un-repointed
  copy of a lifted prohibition as stale).

## Hand-off / next phase

**The phase stays OPEN** (the 2026-07-24 adjudication — no phase-close; see *Current state*).

**The sixth AND seventh fan-outs are both COMPLETE — all ten directions LANDED
2026-08-19**; verdicts in the top `**Status:**` paragraph and the merged rollup in
*Decisions made*, per-direction detail in `notes/Pencil-fanout-archive.md` §"Sixth
fan-out" and `notes/Pencil-fanout.md` §"Seventh fan-out", labels claimed in
`notes/Pencil-labels.md` — **none of it
restated here.** No standing constraint moved: phase OPEN, Lean hold STANDS, W4 PARKED,
`hK`/`hbareSplit` pinned, option B un-commissioned.

**CIRR (twenty-fourth), YLOC (twentieth), BALB (twenty-first), ZNEQ (twenty-third) and
AGLU (twenty-second) all LANDED 2026-08-19** — CIRR a HIT, YLOC an honest MISS with
substantial positive content, BALB OPEN/NOT-a-HIT with its decomposition half proven and
half refuted at an exact `n_hub = 8` boundary, ZNEQ OPEN/NOT-an-independent-gap (input (a)
`Z ≠ ∅` factors: a necessary-for-`hK` half dominated by §(K-grid) (GR-10), a target-rank
half open at (OC-19)(c)'s shape), AGLU a HIT on the "not realizable" branch (the AA-glue
configuration NOT realizable at `n_hub = 8`, the (GR-38) kill a non-vacuous THEOREM there
— but the dispatch's own predicted binding-laminarity consequence REFUTED, 3 774
crossing pairs, pushing the open case to `n_hub ≥ 10`); canonical homes new §(K-chart)
and §(K-out) *Steps O19–O24* (`notes/Pencil-informal.md`), §(K-grid) *Steps G80–G97*
(now `notes/Pencil-informal-grid.md`), verdicts in `notes/Pencil-fanout.md`
§§"Twenty-fourth"/"Twentieth"/"Twenty-first"/"Twenty-third"/"Twenty-second direction" —
**not restated here**. **The doc-split AND discipline-distillation rounds are now
BOTH COMPLETE; the next concrete task is UNROUTED (below).**

**E3 is ARMED** (GBAL's entry-5 HIT) but **not fired by any of the ten** (a′ not hit,
only its pinned route demoted by YLOC; firing is the coordinator's action). **"Chart
irreducibility, un-owned" is now CLOSED** (CIRR, a HIT, §(K-chart)). Ledger attack (c),
**AA-glue realizability, is now SETTLED NEGATIVE at `n_hub = 8`**.

**Next research step: UNROUTED, awaiting a pick — no candidate pre-selected.**
Strongest candidates: **AGLU's `n_hub ≥ 10` three-template question**
((GR-76)(iv), cheap, sharply specced) and **ZNEQ's cross-pool re-keying**
(combinatorial, no new math — `notes/Pencil-fanout.md` §"Twenty-third
direction", `notes/Pencil-informal.md` §(K-out) (OC-28)). Also queued: (OC-19)
input (c) class-uniformly — OCON's #1 by value, **(GR-15)-flavoured**, needs a
chunk-level instrument for (Y) first (YLOC's attempt DEMOTED BY WITNESS,
successor routing in *Decisions made*); §(K-out) items 3/4; **(d′)**. **Not
eligible:** route σ's Lean half and the W4 build, BLOCKED by the standing
2026-08-05 Lean hold.

**Awaiting user adjudication, NOT in the standing 2026-08-07 delegation's dispatchable
pool — carried forward unchanged.** ZNEQ names a `σ > 0`-everywhere
hunt at class shapes whose `H` carries a short theta sub-multigraph — a hit is a
**PENCIL event** (`hK` FALSE there), which the direction-A pivot rule
(`notes/Pencil-fanout-archive.md` §"Direction A") makes *"a phase-redefining event for the user to
adjudicate, not a result to build on"* — excluded until adjudicated. **A
wave-closing exception-log commit to `notes/dispatch-log.md`
is owed and is the coordinator's, not a build agent's** — not made in this commit.

**The doc-split AND discipline-distillation rounds are both COMPLETE —
`notes/Pencil-structure.md`** (all three slices LANDED 2026-08-19). Discipline
distillation promoted this phase's research-arc discipline into the new
read-on-demand root manual **`RESEARCH-ARC.md`** (alongside `CLEANUP.md`,
`PHASE-BOUNDARIES.md`; linked from `CLAUDE.md` and
`.claude/commands/coordinate-phase.md`) — six items ready, three candidates
watched not promoted (`notes/dispatch-log.md` F18–F21), three genuinely
unsettled and deferred with the question stated; full detail there, not
restated here. **No structural work is queued; the research step above is
the only open task.**

**`hsplit` is CLOSED IN FULL** (W5-L7c-1…6, landed 2026-07-30) and **`hfresh`'s mechanical
discharge (residue (iv)) is CLOSED too**. The landed successor
`pencil_conjecture_of_hcontract_hK_hbareSplit_of_card` (`Molecule/Pencil/Escape.lean`) wraps
`pencil_conjecture_of_hcontract_hK_hbareSplit` and carries exactly three open items, below.

> **Route σ's remaining substance is its parked LEAN half** (obligation 1; the numerics half is
> DONE — §(K-σ) *Steps σ3–σ5*, one-lined in *Decisions made*; obligation 1 shrank to two
> conditions and **(σ7)** is proven). When adjudicated open, the smallest concrete commit steers
> to a common seed via the landed `exists_common_seed_pencilRow_and_polynomials`
> (`Engine.lean:476`; the chart is **total**), carrying two design decisions: (a) which maximal
> minor per LI conjunct (the dual conjuncts are unions of basic opens); (b) which FIELD —
> settled per *Current state*'s §(K-clos) note (`ℝ` the narrowest option), still a user call
> as scope. **`exists_pencilSeed_of_nondeg`
> (`Reseed.lean:65`) is NOT the bridge** (circular). Route σ faces exactly **one** crux (the
> workbook's two kills of M₁ share one stated reason — the `hinge(vb) := q(ab)` pinning).
> **BLOCKED by the standing 2026-08-05 Lean-hold adjudication (general, not W4-scoped)**; does
> not open without a fresh user adjudication.
>
> **The FIRST through NINETEENTH directions are ALL COMPLETE, the NINTH through SIXTEENTH
> landing the theorem block (GR-32)–(GR-60)** — ordinals were assigned at dispatch, so
> landing order differs from ordinal order; roll call, dates and full detail one-lined in
> *Decisions made*, the delegations that picked them in *Current state*'s dated bullets.
> **No g-flank found by any of them; (GR-15) stays OPEN, modulo (GR-4′); no status moves.**
> Every TERMINATION check fired nothing except arming E3 (E1/E2 NO throughout).
> **Two durable negatives from the same adjudication — do not re-run:** §4.6's shortlist is
> **partially superseded** for the tight stratum (U2 delivered by (GR-16)'s reduction; U3's
> negative-form insight already exploited); the symbolic meta-option ("upgrade §(K-Λ) via
> M2") is **landed, not pending** (`m2/lambda0.m2`) — only §5.3 item (i) remains, ruled out by
> §5.3's own local-frame feasibility boundary.
> **Coordinator hand-off note, unresolved:** whether (GR-15) ("every tight class shape") also
> covers the `W19`-type **(K-res)** sibling habitat — pin it when the tight side closes.
> **Not selected at the 2026-08-07 adjudication, so not open:** the **(FR-6) follow-ons**
> ((ii)/(iv) open and un-commissioned; **(iii)** struck as unnecessary by (OC-17), no bar
> crossed), the unselected leads (b)–(f) above, and route σ / W4. **Deliberate non-goals —
> do not re-derive, re-sweep, or re-open:** (Λ0), (Λ1), the `g₁₄` clause, §(K-ind), §(K-Δ),
> §(K-clos)'s field question, §(K-ann)'s settled batch ((ANH-1)–(ANH-6), (SD-6)) and
> §(K-out)'s settled batch ((OC-1)–(OC-7); pinned, disjoint pools) — including "does the
> polarity generalize?", (D2)'s far block, POOL-G/POOL-S, a counting/matroid route to
> (OUT)'s hypothesis ((OC-3) refutes the whole class), or `lambda.py`'s figures (one
> carve-out, slice **S3**, is spent). Standing constraints — W4 PARKED, `hK`/`hbareSplit`
> pinned, option B un-commissioned — all unchanged; see *Current state*.

The three carried items:

- **`hcontract`** (W4) — **fully decomposed, buildable, and PARKED.** Canonical home:
  `notes/Phase39-design.md` §"W4 decomposition recon" + §"W4-L4 identification recon" (leaf
  list there), residual mathematics `notes/Pencil-W4-informal.md`. State: the L4 verdict
  trades minimality for the pencil habitat's `hcard` bound, so the co-1 case closes
  minimality-free and KT's non-simple-contraction trigger reduces to it; residual carry
  narrows to **`hnoGood'`**, whose vacuity conjecture is **REFUTED** (2026-08-02, `|V| = 19`),
  so branch 4 needs content. **Route ADJUDICATED (2026-08-02): route 3, packaging (b)** — the
  structure-theorem-pinned dispatch invariant (§(SAFE-RES)'s (C7)/(C8) split, collision with
  §(K-slide-comb) registered in `notes/Pencil-labels.md`), with **(K-res)** a sibling of the
  byte-identical `hK`. **Recorded, not built — W4 stays parked**; when commissioned the next
  commit is **W4-L4b** (`exists_degree_two_of_co1_rigid`, pinned + spike-elaborated), then
  order-flexibly W4-L1/L2/L3′/W4-L5. Gates N8/N9(+rank-29 control)/N10/N10b all PASSED
  (`notes/scripts/w4/hybrid_gates.py`).
- **`hK`** (kernel (K), research) — the escape `≢ 0` uniformity kernel, the phase's hardest
  open item. **Standing adjudication ("C: literature hunt + A", 2026-07-30): keep carrying
  `hK` as pinned; option B NOT authorized.** Both literature hunts are MISSes (2026-07-30
  rigidity-side; 2026-08-05 Δ-matroid-side, §(K-Δ)). Since the 2026-08-02 W4 route-3(b)
  adjudication `hK` also carries **(K-res)** as a byte-identical sibling habitat. **The
  mathematics is NOT restated here** — canonical home `notes/Pencil-informal.md`'s **State of
  (K)** gap map (one row per gap: status, what would close it, the uncovered-shape list, a
  *settled, do not re-derive* block); read that map, not this bullet, before any (K) work.
- **`hbareSplit`** (kernel (K-bare), research) — the bare-half-off-feasibility kernel, **carried
  as pinned** (the standing GO, "C: cheap numerics extensions + A", verbatim 2026-07-30; option B
  NOT commissioned), with its **extension route recon'd NO-GO on landed machinery** the same day.
  Minimal open statement: **(K-bare-ext)**; status row in the workbook's *State of (K)* map, full
  record in the design doc §"(K-bare) extension-route recon", numerics
  `notes/scripts/kbare/{danger,optc}.py`.

Gates for any continuation: `lake build` (warning-clean) + `lake lint` when `.lean` is touched;
`blueprint/verify.sh` + `blueprint/lint.sh` (vocabulary gate bans "stratum"/"strata") when `.tex`
is touched; **when `notes/scripts/` is touched**, figure invariance proportionate to what the
commit modifies (`git diff --name-only -- '*.py' '*.m2'` empty ⇒ that check IS the discharge,
stated in the commit message) — canonical home `notes/scripts/README.md` *Hard rule — figures do
not move*; a **symbolic** dispatch adds `notes/scripts/m2/README.md`;
**`notes/check-gapmap-cells.py` before any gap-map edit** — the cap-exhaustion hazard this
guards against is now a standing, harness-wide rule (`notes/scripts/README.md` §4 convention
8, promoted 2026-08-19 after a second instance; not restated here); bump a row's cap only
with a dated one-line reason, never a silent regrowth.

## Adjacent directions (orientation only, not this phase)

ORIGAMI (`notes/Origami.md`, next queued) is the bar-joint-side analog; the wider unqueued
survey — incl. IDENT-PANEL, the nearest neighbour — is `notes/IdeaBacklog.md`.

## Decisions made during this phase

Reverse-chronological, one line per landing; full derivations live in git,
`notes/Phase39-design.md`, and (for the (K) arc) the workbook section named in each entry, which
is the canonical home a successor reads.

- **Doc-split + discipline-distillation rounds COMPLETE (2026-08-19, all three
  slices)** — §(K-grid) → `Pencil-informal-grid.md`; `Pencil-fanout.md`'s
  ordinals 1–19 → `Pencil-fanout-archive.md`; this phase's research-arc
  discipline promoted to the new root manual `RESEARCH-ARC.md`. Verbatim
  relocations, repointed, `check-gapmap-cells.py` clean; detail
  `notes/Pencil-structure.md`.
- **The FIRST through TWENTY-FOURTH fan-outs/directions — all LANDED 2026-08-05…08-19**
  (canonical homes: §(K-chart)/§(K-out) *Steps O19–O24* in the workbook, §(K-grid)
  *Steps G80–G97* now `notes/Pencil-informal-grid.md` — and `notes/Pencil-labels.md`
  registry, full per-direction label detail there, not restated here; drivers
  `w4/{cflank,gcap,gunif,gexist,gorient,gdev,gadm,gpsa,gdesc,gbal,glaw,ocon,ltwo,cirr,
  yloc,balb,zneq,aglu}.py`, FRES no driver). Thirty-two directions total (thirteen in
  the first five fan-outs, one per ordinal from the sixth on): CFLANK/GCAP/GUNIF closed
  TCOL's flank sites as routes then REFUTED each other's `g ≤ 1` cap (route DEAD);
  GEXIST/GORIENT honest MISSes re-anchoring the target on bounded-deviation selection;
  GDEV a REFUTATION-with-successors; GADM an honest MISS carrying the shift-metric
  UNBOUNDED (routing overridden by GPSA); GPSA proves entry 5's parity half; GDESC
  RESHAPES the balance half into input (X); **GBAL PROVES it** (the balance theorem —
  entry 5 in BOTH halves, the arc's first HIT, discharging (X)); **GLAW** an honest MISS
  on **(a′)** (exhaustive `n_hub ≤ 6` verification, the per-matching variant REFUTED,
  residual input (Y) named); **OCON** an honest MISS freeing (OC-8)'s hard-stratum
  qualifier; **LTWO** realizes §(K-Λ) item (vii) at a proven size floor; **FRES** closes
  §(K-frame) (FR-4)'s named gap with no rider — **the sixth fan-out's five, COMPLETE**;
  then, **the seventh fan-out's five, also COMPLETE**: **CIRR** a HIT — chart
  irreducibility proven once, all four consumers clean; **YLOC** an honest MISS with
  substantial positive content — GBAL's chunk-level instrument for (Y) DEMOTED BY
  WITNESS, its own predicted obstruction REFUTED as stated, a collision bound and a fit
  identity the residue; **BALB** OPEN/NOT-a-HIT — price half PROVEN outright, imbalance
  ceiling a THEOREM at `n_hub ≤ 6` FALSE from `n_hub = 8` at an exact V8 witness,
  availability EXHAUSTIVE on the stratum but REFUTED there too, repaired at price 0;
  **ZNEQ** OPEN/NOT-an-independent-gap — input (a) `Z ≠ ∅` FACTORS into a half dominated
  by (GR-10) and a target-rank half one split down from (K-tight) *Step 2*; **AGLU** a
  HIT on the "not realizable" branch — the AA-glue configuration pinned to a single
  template and proven NOT realizable at `n_hub = 8`, EXHAUSTIVE with no cap, the (GR-38)
  kill a non-vacuous THEOREM there — but its own predicted binding-laminarity
  consequence REFUTED (3 774 crossing pairs), a general-`n` charge pushing the open case
  to `n_hub ≥ 10`. Three cross-direction convergences (OCON/FRES, YLOC/BALB, CIRR/ZNEQ);
  two coordinator-predicted obstructions refuted (YLOC's, AGLU's). Headline positives
  (GR-9)/(FR-R1) PROVEN, entry 5 PROVEN (GBAL, a HIT), (GR-15) OPEN throughout;
  uniformity untouched; E1/E2 never fired, **E3 ARMED by GBAL, not fired**.

- **The 2026-08-05 research cluster, one-lined** (all same day; full detail
  `Phase39-design.md` + git, workbook sections named): notes reorganization
  (`Pencil-labels.md`; design doc **FROZEN**) + class-uniformity recon (5 REFUTED, 3
  ranked, strategy **§4.6**); route σ a **CANDIDATE** (obligation 1 DONE); (K-ind) and the
  Δ-matroid lead **BOTH REFUTED**; the §(K-Λ) triad settled ((Λ0)/(Λ1) PROVEN via M2); the
  sixth–ninth dispatches found the conjecture HOLDS at every uncovered flank, the pure
  condition WRONG INVARIANT, dominance HOLDS but NOT a route; **(K-slide-comb) REFUTED**.

- **Pre-fan-out arc, one-lined (2026-07-24 → 08-04; full detail `Phase39-design.md` + git)**:
  W0–W3/W5 CLOSED `hsplit` IN FULL and isolated kernel **(K)** (route-1 locality REFUTED);
  corank stratification fixed to **(K-tight)**, W4 decomposed and (K-bare-ext) NO-GO'd,
  setting this phase's standing adjudications (quoted in *Current state*); 2026-08-02
  priced the kernel-widening to **(K-res)** and REFUTED **(SAFE-RES)**/`hnoGood'` vacuity;
  (K-tight) re-pinned against KT pp. 684–691; 2026-08-04 proved (K-slide) (S1) and closed
  (K-pitch) at θ(3,3,6).

- **Promoted out of this phase** (pointers only): TACTICS-GOLF §11/§22/§23; TACTICS-QUIRKS
  §46/§96/§99–§104; FRICTION `exists_injOn_mapsTo_of_ncard_le` + `extensor_pair_smul`
  [mirror-candidate] and the omega/`Set.ncard`-atom idiom.

## Citations (transcribed, project-canonical sources)

- Katoh–Tanigawa, *A proof of the molecular conjecture*, Discrete Comput. Geom. **45** (2011) —
  the KT pointers in this note (Cor. 5.7, Thm 5.5, Lemma 6.13, the Case I/II/III split) are
  transcribed from `notes/Pencil.md`'s 2026-07-23 survey against the project-canonical source
  (ROADMAP *References*); pointer verification history: `notes/Phase35.md` *Citations*,
  `notes/Phase23-cleanup.md`. The (K-tight) re-pin (2026-08-02) verified pp. 681–691 directly
  against the `.refs` copy — workbook §(K-tight) *Step 0*. **KT Thm 4.9 is cited by the
  *molecular* side only**: the pencil induction is `Graph.pencil_reduction`, not
  `minimal_kdof_reduction` (§(K-ind) *Verification*).
- Jordán 2016 (MSJ Memoirs 34) — checked silent on the pencil stratum in the 2026-07-23 survey,
  re-confirmed by the 2026-07-30 (K) literature hunt.
- The 2026-07-30 (K) literature hunt (option C) verified six project-new sources against the
  `.refs` copies / primary metadata, all MISSes on the (K-tight) crux — White–Whiteley 1987 and
  1983, Whiteley 1988 and 1999, Schulze–Tanigawa, Garamvölgyi. **The full verified bibliography,
  with per-source venue data and the reason each is a MISS, is `notes/Phase39-design.md` §"(K)
  literature hunt" — the canonical home; it is not duplicated here** (same pointer discipline as
  the Δ-matroid bibliography below).
- White–Whiteley 1987 (op. cit.) §2 — verified against the `.refs` copy (2026-08-04, the
  (K-slide-cl) development): Proposition 2.6, Corollary 2.7, Theorem 2.18 (the technique the
  tetrahedral collapse instantiates), Corollary 2.19 (Tay's count).
- **The 2026-08-06 direction-T landing** (§(K-grid)) verified one project-new source against
  publisher metadata (Smith ScholarWorks record + arXiv listing), cited as context only (nothing
  in §(K-grid) is derived from it): **Gilbert–Polster–Tymoczko**, *Generalized splines on
  arbitrary graphs*, Pacific J. Math. **281** (2016), no. 2, 333–364 (arXiv:1306.0801).
  Whiteley 1996 (op. cit. below) is re-used for the matroid-union context, no new section pointer.
- Whiteley, *Some matroids from discrete applied geometry*, in Matroid Theory
  (Bonin–Oxley–Servatius, eds.), Contemp. Math. **197**, AMS 1996, 171–311 — §12.2's screw-center
  description of body-hinge motions verified against the `.refs` copy (2026-08-04, the (K-pitch)
  development); volume/pages verified against AMS metadata.
- The 2026-08-05 (K-slide-comb) pass reuses the project-canonical **Edmonds 1965** (verified in
  Phase 12) and the **Tutte 1961 / Nash-Williams 1961** tree-packing pair (Phase 13). One
  project-new source, verified against publisher metadata: **Grünbaum**, *Acyclic colorings of
  planar graphs*, Israel J. Math. **14** (1973) 390–408, DOI 10.1007/BF02764716. Brooks' theorem
  is cited by name only (classical).
- **The 2026-08-05 broad class-uniformity recon** (`notes/Pencil-strategy.md` §4.6) verified one
  project-new source against publisher metadata + the arXiv preprint listing, **no section pointer
  asserted**: **Scott**, *Grassmannians and Cluster Algebras*, Proc. London Math. Soc. **92**
  (2006), no. 2, 345–380, DOI 10.1112/S0024611505015571 (preprint arXiv:math/0311148) — the
  finite-type Grassmannian classification. Its `D₄`/`A_{n−3}` labels state the *refuted* proposal
  only, never a load-bearing step; **White–Whiteley 1987** (below) is re-used by name for the pure
  condition, with no new section pointer.
- **The 2026-08-05 Δ-matroid literature hunt** (§(K-Δ)) verified ~20 project-new sources —
  Bouchet, Dress–Havel, Wenzel, Gelfand–Serganova, Borovik–Gelfand–White, Vince(–White), Rincón,
  Jin–Kim, Baker–Jin, Geelen–Iwata–Murota, Bouchet–Cunningham, Koana–Wahlström, Moffatt, Chun et
  al., Kung, and Cruickshank–Jackson–Jordán–Tanigawa (arXiv:2508.11636, the corroborating
  negative). **The full verified bibliography, with its two caught hallucinated attributions and
  one deliberately omitted volume number, is `notes/Pencil-informal.md` §(K-Δ) *Sources* — the
  canonical home; it is not duplicated here.**
