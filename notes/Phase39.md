# Phase 39 — PENCIL: the hinge-pencil molecular conjecture (work log)

**Status:** in progress — phase stays OPEN (standing user adjudications of 2026-07-24 /
2026-07-30 / 2026-08-02, quoted verbatim in *Current state*). W0–W3 and the whole W5 arc
(L0–L7) are COMPLETE — `hsplit` CLOSED IN FULL and `hfresh`'s counting discharge landed
(2026-07-30). Only three items remain, all carried by the landed successor
`pencil_conjecture_of_hcontract_hK_hbareSplit_of_card` (`Molecule/Pencil/Escape.lean`):
`hcontract` (W4), kernel `hK`, and kernel `hbareSplit` — see *Hand-off*. **Thirty-two
kernel-(K) directions are now COMPLETE** (2026-08-05 → 08-19, ordinals 1–24; roster and
per-direction theorem chain in *Decisions made*). **The SIXTH and SEVENTH FAN-OUTS ARE
BOTH COMPLETE** (all ten directions LANDED 2026-08-19). **The arc's HITs through ordinal 24:**
route-ledger **entry 5 PROVEN in both halves** (GBAL, discharging input (X)); **chart
irreducibility PROVEN** (CIRR); the **AA-glue configuration NOT realizable at `n_hub = 8`**
(AGLU). Everything else an honest MISS or an OPEN reshape; verdicts in *Decisions made* and
`notes/Pencil-fanout{,-archive}.md`, **not restated here**. **(GR-15) stays OPEN
throughout; class uniformity untouched; no g-flank at any of the thirty-two directions.
E3 is ARMED (by GBAL) and has NOT fired.** Direction codes are **multi-letter and
topic-tagged from the fifth fan-out on** (`notes/Pencil-labels.md` (L5)); grandfathered
single letters are re-used across dates, **always date those**.
**The doc-split AND discipline-distillation rounds are BOTH COMPLETE**
(all three slices, `notes/Pencil-structure.md`; the new `RESEARCH-ARC.md`
promotes this phase's dispatch discipline). **Next: the EIGHTH FAN-OUT is
PREPPED AND DISPATCHED** (2026-08-19) — five concurrent opus directions,
ordinals 25–29: **GTMPL** / **GFLOW** / **GCOLL** (§(K-grid)) and **OSCHU** /
**SIGZ** (§(K-out)); specs, roster, tier split, label reservations and the
losers' ranking all in `notes/Pencil-fanout.md` §"Eighth fan-out", not restated
here. **GTMPL, GFLOW, SIGZ and OSCHU have LANDED** (the arc's thirty-third through
thirty-sixth directions) — attack (c)'s AA-glue case settled at an **exact
`n_hub` boundary**; **(b′) given its first proven `n`-free constant** (at 12,
not 2); the **authorized `σ > 0` disproof hunt a NO HIT** that nonetheless
**kills the counting route to a disproof** as a theorem, the pivot rule never
triggering; and **(a₁) half-proven, half-reduced to one 3×3 determinant**.
Verdicts one-lined in *Decisions made*, detail in the fan-out doc. **GCOLL
alone is in flight. The next concrete task is verifying and landing it, then
the wave-closing exception-log commit.**

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
- **2026-08-13, phase-shape adjudication, then the ninth- through fourteenth-direction
  selections (none changed a standing constraint).** Offered a handoff-to-fresh-session
  option after GUNIF's refutation, the user **RESOLVED: the research arc CONTINUES**,
  selection falling back to the standing 2026-08-07 delegation. **Selection shapes, which is
  what this bullet is canonical for:** ninth–eleventh **top-rung fable recon**
  (GEXIST/GORIENT/GDEV, verdicts verified and ACCEPTED); twelfth **coordinator-authored
  prep**, breaking the streak, with no independent ranking of the losers (GADM); thirteenth
  **back to the fable recon** (GPSA, whose ACCEPTED verdict **overrode** GADM's shift-metric
  routing clause); fourteenth **no selection pass at all** — GPSA's own landed
  otherwise-clause routed it deterministically (GDESC, dispatched opus against a
  top-rung-mapped task, a logged deviation) — and the **fifteenth left un-dispatched**.
  Per-direction verdicts, dates and detail: `notes/Pencil-fanout-archive.md`
  §§"Ninth"–"Fourteenth direction"; the rung deviation in `notes/dispatch-log.md`.
- **2026-08-19, sixth-fan-out dispatch — a NEW shape (user-adjudicated multidispatch;
  changes no standing constraint).** Asked how to proceed with the unrouted fifteenth, the
  user elected a **multidispatch of five concurrent opus directions**, verbatim: *"I'd like
  to try a multidispatch of opus agents here. Keep an eye on the 5h session limits and
  let's dispatch as many agents as we can on independent directions so that we can
  maximize the number of ideas we make progress on at once without getting interrupted."*
  Five dispatched concurrently — **GBAL**/**GLAW** (compute-licensed), **OCON**/**LTWO**/
  **FRES** (derivation-first), tier split and label reservations coordinator-set. **All five
  LANDED 2026-08-19; COMPLETE** — `notes/Pencil-fanout-archive.md` §"Sixth fan-out".

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
  **One coordinator sharpening overrode GLAW's landed routing clause** (routing only, not
  its mathematics) and was then **SPLIT, not simply upheld, by YLOC's landing** — recorded
  in full at `notes/Pencil-fanout.md` §"The coordinator's one routing sharpening" and
  §"Twentieth direction", not restated here. **All five LANDED 2026-08-19; COMPLETE.**

- **2026-08-19, EIGHTH-fan-out dispatch — the multidispatch shape RE-ELECTED a third time,
  AND the first standing-constraint move since 2026-08-05.** Offered four ways to make the
  twenty-fifth pick (top-rung recon / coordinator prep / multidispatch again / a user-named
  single direction), the user selected **"Multidispatch fan-out again"** — an option
  selection, not free text, and against a coordinator recommendation *for* the recon shape.
  Five dispatched concurrently at **opus**: **GTMPL** / **GFLOW** / **GCOLL** (§(K-grid)),
  **OSCHU** / **SIGZ** (§(K-out)). Tier split, direction selection and label reservations
  **coordinator-set**, so the twelfth's disclosure applies for the **third consecutive
  wave** — **no independent top-rung ranking of the losers**, itemized in
  `notes/Pencil-fanout.md` §"Not selected — the eighth fan-out's losers"; what is *not* the
  coordinator's is the candidate **pool**, since each of the five is a successor named by a
  landed direction's own hand-off. Same check-in: rungs **sonnet + opus only, top rung =
  opus** (fable conserved, `weekly_scoped` 92 %), cap **lifted**, rescue §1 fixups
  **pre-authorized**. **The standing-constraint move:** on ZNEQ's carried `σ > 0` hunt the
  user selected **"Authorize the hunt"**, whose offered terms — accepted as the terms of the
  authorization — read *"Add it to the dispatchable pool. If it hits, `hK` is false at those
  shapes and the phase's target needs redefinition — you would adjudicate that at the
  return."* The item therefore **leaves the awaiting-adjudication pool** and is direction
  **SIGZ**, with the direction-A pivot rule in force and the adjudication moved from
  *before* the dispatch to *at the return*. **Everything else stands unchanged:** phase
  OPEN, the 2026-08-05 Lean hold, W4 PARKED, `hK`/`hbareSplit` pinned, option B
  un-commissioned.

**Kernel-(K) research arc — forty-nine docs+scripts-only dispatches landed, five more
dispatched and IN FLIGHT (the eighth fan-out), plus seven strategy-only passes**
(2026-08-02 → 08-19). Which pass was which is one-lined in *Decisions
made*; the rule is that the **dispatch** count moves only on a landing (GBAL/GLAW/FRES/OCON/
LTWO are the fortieth through forty-fourth; CIRR the forty-fifth; YLOC the forty-sixth; BALB
the forty-seventh; ZNEQ the forty-eighth; AGLU the forty-ninth; the eighth fan-out's five
become the **fiftieth through fifty-fourth as they land**, not before), and a **user call on
dispatch *shape*** — either multidispatch election, or a coordinator-authored pick like the
twelfth's — contributes **no** strategy pass, so the 2026-08-19 eighth-fan-out check-in adds
none even though it moved a standing constraint.
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
> here). **Route σ** = route A at the dual seed `σu`; it would close (K-tight) on the hard
> stratum, *length-free*, via `Λ²Π̂(b) + Λ²Π̂(c) + α_{pt(b)} = K⁶`. **Offered for
> adjudication**, resting on four obligations (the first shrunk to two) and **no longer
> field-blocked** (§(K-clos): the polarity generalizes, `ℝ` the *narrowest* choice). It moves
> no gap-map status and changes no standing constraint.

The other candidate continuations, unselected — items (a)/(g) **DONE** (second-fan-out
directions M and R), each with a canonical home carrying the detail: **(b)** **(K-wit)**, the
pitch route's single live form at companion splits (§(K-Λ)) — its (OC-8) residue now reduces
to chart irreducibility (**DONE**, CIRR) plus input (a), which itself **FACTORS** (**DONE**,
ZNEQ) into a dominated half and the target-rank half **OSCHU attacks this wave**; **(c)** the
**W4 build**, decomposed and buildable, **PARKED** by the Lean hold; **(d)** the
companion-length dichotomy frame (§(K-dom) *D7*) + the unprobed `k ≥ 4` parallel-edge item
(§(K-pure) *P4*); **(e)** §(K-Λ) item (vii)'s residual, since LTWO a named, non-empty,
floor-classified family; **(f)** strategy §4.6's shortlist, **partially superseded** for the
tight stratum, U3 still unrun. **The eighth fan-out's own ranking of what it did not pick is
`notes/Pencil-fanout.md` §"Not selected — the eighth fan-out's losers", not this list.**

**Read `notes/Pencil-strategy.md` before choosing anything else** — the strategic record (why
class uniformity resists, the candidate stronger invariants with **C1 run and struck**, §5's
symbolic assessment); its header is its own contents table, and **its §4.6** is the entry
point for any attack on the crux.

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
  phase, with the per-item route in *Hand-off*'s three carried items and **not duplicated
  here.** Two W4 facts that constrain future statements: **`hnoGood'` is known NON-vacuous**
  (2026-08-02), so branch 4 needs content (routes in `notes/Pencil-W4-informal.md`
  §"`hnoGood'` vacuity"; adjudication owed), and **(SAFE-RES) is REFUTED** the same day, so
  routes 1/3 cost (T) + (V) + the reduced (E) — (T) a genuine research gap — plus **one**
  widened kernel (K-res).
- The full biconditional transport (design doc's W0 pin) is landed only as its two forward
  implications; the reverse arms need a `complementIso` involution lemma, not in tree —
  deferred, **off every critical path** (§(K-σ) *Step σ6*).
- **Harness debt** — the S1–S4 round is CLOSED (2026-08-06), but **two new dated UNPAID
  items** stand, both sideways-import move-downs recorded rather than paid because the target
  is a landed file a concurrent direction imports: `ocon.meet` (ZNEQ) and `aglu.py`'s seven
  combinatorial devices (GTMPL). Canonical home `notes/scripts/README.md` *Harness debt* —
  read before any numerics dispatch. Cheapest discharge: fold both once the wave is complete.

## Hand-off / next phase

**The phase stays OPEN** (the 2026-07-24 adjudication — no phase-close; see *Current state*).

**The sixth AND seventh fan-outs are both COMPLETE — all ten directions LANDED
2026-08-19**; verdicts in the top `**Status:**` paragraph and the merged rollup in
*Decisions made*, per-direction detail in `notes/Pencil-fanout-archive.md` §"Sixth
fan-out" and `notes/Pencil-fanout.md` §"Seventh fan-out", labels claimed in
`notes/Pencil-labels.md` — **none of it
restated here.** No standing constraint moved: phase OPEN, Lean hold STANDS, W4 PARKED,
`hK`/`hbareSplit` pinned, option B un-commissioned.

**The seventh fan-out's five verdicts** (CIRR a HIT; YLOC an honest MISS with substantial
positive content; BALB OPEN/NOT-a-HIT, half proven / half refuted at an exact `n_hub = 8`
boundary; ZNEQ OPEN/NOT-an-independent-gap; AGLU a HIT on the "not realizable" branch, with
its own predicted binding-laminarity consequence REFUTED) are in the top `**Status:**`
paragraph and, per-direction, in `notes/Pencil-fanout.md` §§"Twentieth"–"Twenty-fourth
direction"; canonical mathematical homes are the new §(K-chart) and §(K-out) *Steps
O19–O24* (`notes/Pencil-informal.md`) and §(K-grid) *Steps G80–G97*
(`notes/Pencil-informal-grid.md`) — **none of it restated here.**

**E3 is ARMED** (GBAL's entry-5 HIT) but **not fired by any of the ten** (a′ not hit,
only its pinned route demoted by YLOC; firing is the coordinator's action). **"Chart
irreducibility, un-owned" is now CLOSED** (CIRR, a HIT, §(K-chart)). Ledger attack (c),
**AA-glue realizability, is now SETTLED NEGATIVE at `n_hub = 8`**.

**THE NEXT CONCRETE TASK — verify and land the EIGHTH FAN-OUT's four remaining returns, one
serial coordinator commit per direction.** Five concurrent opus directions were prepped and
dispatched 2026-08-19 (ordinals 25–29); **GTMPL has LANDED** and four are in flight. Every
spec, bar, rider, tier assignment and label reservation is in `notes/Pencil-fanout.md`
§"Eighth fan-out" and **not restated here**:

| direction | owning § | target in one line |
|---|---|---|
| ~~**GTMPL**~~ | §(K-grid) | **LANDED** — attack (c)'s AA-glue case settled at an exact boundary (`≤ 14` impossible, 16 realized) |
| ~~**GFLOW**~~ | §(K-grid) | **LANDED** — (b′) a HIT at a different constant: gap `≤ 12` modulo (R1), constant 2 open with (C2) its residual |
| **GCOLL** | §(K-grid) | **(GR-64)(R2)** — every habitat shape carries an anchor matching with `B(M) = 0` |
| ~~**OSCHU**~~ | §(K-out) | **LANDED** — (a₁) half-proven, half-reduced to one 3×3 determinant; the (a₂) leg a HIT correcting an arc-wide figure |
| ~~**SIGZ**~~ | §(K-out) | **LANDED** — NO HIT; the counting route to a disproof DEAD as a theorem, `P21`'s mechanism located as a sampler artifact |

**Landing obligations.** §(K-grid)'s cell was recomputed at GTMPL's landing (1706 → 1730
words *while absorbing six new labels*, i.e. the pre-existing content compressed ~13 %; 79
labels in, 85 out, **zero dropped**, scripted set-diff; cap unbumped) — and GFLOW then
consumed 289 of the 305 words that bought, so the cell now sits at **2019 of 2035**.
**GCOLL's landing therefore owes a genuine recompute of the §(K-grid) cell before adding its
own content** — 16 words is not headroom, and the rule stays **recompute, never bump**.
§(K-out)'s cell was recomputed **twice in one day** (649 → 431 words of pre-existing content
at SIGZ, a further ~65 off the oldest material at OSCHU) and then, the section having
absorbed **eleven** new theorems ((OC-29)–(OC-39)), its cap was **deliberately bumped
800 → 950** with the reason recorded in `notes/check-gapmap-cells.py` — recompute first,
twice, then bump, the script's own sanctioned order. A **wave-closing exception-log commit** to
`notes/dispatch-log.md` is owed at the end, **the coordinator's**; its rows are the two
defective inherited spec clauses (GTMPL's, GFLOW's), the two sibling-import debt items, and
the unescaped-pipe gate degradation this landing introduced and repaired.

**Queued behind the wave:** (OC-19) input (c) class-uniformly (OCON's #1 by value,
**(GR-15)-flavoured**, still waiting on a chunk-level instrument for (Y) — **GCOLL is this
wave's bet on that supply line**); §(K-out) hand-off **item 3**; **(d′)**, lowest-value for
a third wave and a candidate to strike rather than dispatch; and, new from GTMPL, **redoing
(GR-79)–(GR-82) with a one-unit defect budget** to finish attack (c). **Not eligible:**
route σ's Lean half and the W4 build, BLOCKED by the standing 2026-08-05 Lean hold.

**Nothing is awaiting user adjudication as of 2026-08-19.** The one item that was —
ZNEQ's `σ > 0`-everywhere hunt at class shapes whose `H` carries a short theta
sub-multigraph — is **AUTHORIZED** and dispatched as **SIGZ**; the direction-A pivot rule
(`notes/Pencil-fanout-archive.md` §"Direction A") stays in force, so a hit is *"a
phase-redefining event for the user to adjudicate, not a result to build on"* — **the
adjudication now happens at the return, not before the dispatch** (the terms the user
accepted, quoted in *Current state*'s 2026-08-19 eighth-fan-out bullet). **A hit therefore
stops the loop and goes to the user**; it does not move a gap-map status by itself.

**One structural item IS queued, recorded rather than improvised.** This note has sat at
~510–530 lines through the eighth fan-out's landings, past its ~500-line tripwire, and three
compression passes have each found genuine duplication and each been undone by the next
landing. The residual bulk is **not** duplication: it is *Current state*'s eight dated
adjudication bullets, whose verbatim user quotes are **canonically** here
(`notes/CLAUDE.md`: selection provenance is not duplicated into the fan-out doc). The honest
fix is therefore a **doc split** — the bullets covering archived ordinals 1–19 move to a
`notes/Pencil-adjudications.md` with a pointer, on the `Pencil-fanout-archive.md` precedent —
and that is a structural round, deliberately **not** attempted mid-wave while concurrent
directions are returning. Queue it for after the eighth fan-out closes.

**No other structural or doc work is queued** — the doc-split and discipline-distillation rounds
are both COMPLETE (`notes/Pencil-structure.md`, all three slices; `RESEARCH-ARC.md` is the
promoted manual, six items ready / three watched / three deferred, detail there and in
`notes/dispatch-log.md` F18–F21). **The eighth fan-out is the only open work.**

**`hsplit` is CLOSED IN FULL** (W5-L7c-1…6, landed 2026-07-30) and **`hfresh`'s mechanical
discharge (residue (iv)) is CLOSED too**. The landed successor
`pencil_conjecture_of_hcontract_hK_hbareSplit_of_card` (`Molecule/Pencil/Escape.lean`) wraps
`pencil_conjecture_of_hcontract_hK_hbareSplit` and carries exactly three open items, below.

> **Route σ's remaining substance is its parked LEAN half** (obligation 1, shrunk to two
> conditions, **(σ7)** proven; the numerics half is DONE — §(K-σ) *Steps σ3–σ5*). When
> adjudicated open, the smallest commit steers to a common seed via the landed
> `exists_common_seed_pencilRow_and_polynomials` (`Engine.lean:476`, chart **total**),
> carrying two design decisions — which maximal minor per LI conjunct, and which FIELD (`ℝ`
> the narrowest, still a user call as scope). **`exists_pencilSeed_of_nondeg`
> (`Reseed.lean:65`) is NOT the bridge** (circular); exactly **one** crux remains (the
> `hinge(vb) := q(ab)` pinning). **BLOCKED by the standing 2026-08-05 Lean hold**; does not
> open without a fresh user adjudication.
>
> **Directions 1–24 are ALL COMPLETE** — roll call and dates one-lined in *Decisions made*,
> per-direction detail in `notes/Pencil-fanout{,-archive}.md`, the delegations that picked
> them in *Current state*'s dated bullets. **No g-flank found by any of them; (GR-15) stays
> OPEN, modulo (GR-4′).** Every TERMINATION check fired nothing except arming E3.
> **Two durable negatives from the 2026-08-07 adjudication — do not re-run:** §4.6's shortlist is
> **partially superseded** for the tight stratum (U2 delivered by (GR-16)'s reduction; U3's
> negative-form insight already exploited); the symbolic meta-option ("upgrade §(K-Λ) via
> M2") is **landed, not pending** (`m2/lambda0.m2`) — only §5.3 item (i) remains, ruled out by
> §5.3's own local-frame feasibility boundary.
> **Coordinator hand-off note, unresolved:** whether (GR-15) ("every tight class shape") also
> covers the `W19`-type **(K-res)** sibling habitat — pin it when the tight side closes.
> **Not open, and not re-litigated per wave:** the **(FR-6) follow-ons** ((ii)/(iv)
> un-commissioned; **(iii)** struck by (OC-17)), the unselected leads (b)–(f) above, and
> route σ / W4. The **current** losers ranking is `notes/Pencil-fanout.md` §"Not selected —
> the eighth fan-out's losers", not this clause. **Deliberate non-goals — do not re-derive,
> re-sweep, or re-open:** (Λ0), (Λ1), the `g₁₄` clause, §(K-ind), §(K-Δ), §(K-clos)'s field
> question, §(K-ann)'s settled batch ((ANH-1)–(ANH-6), (SD-6)) and §(K-out)'s settled batch
> ((OC-1)–(OC-7); pinned, disjoint pools) — including "does the polarity generalize?",
> (D2)'s far block, POOL-G/POOL-S, a counting/matroid route to (OUT)'s hypothesis ((OC-3)
> refutes the whole class), or `lambda.py`'s figures (slice **S3**'s carve-out is spent).

The three carried items:

- **`hcontract`** (W4) — **fully decomposed, buildable, and PARKED** by the Lean hold. Route
  **ADJUDICATED 2026-08-02: route 3, packaging (b)**, with **(K-res)** a byte-identical
  sibling of `hK`; residual carry narrows to **`hnoGood'`**, whose vacuity conjecture is
  **REFUTED** (`|V| = 19`), so branch 4 needs content. When commissioned the next commit is
  **W4-L4b** (`exists_degree_two_of_co1_rigid`, pinned + spike-elaborated), then
  order-flexibly W4-L1/L2/L3′/L5; gates N8/N9/N10/N10b all PASSED. Canonical homes:
  `notes/Phase39-design.md` §§"W4 decomposition recon"/"W4-L4 identification recon" (the leaf
  list) and `notes/Pencil-W4-informal.md` (the residual mathematics) — **not restated here.**
- **`hK`** (kernel (K), research) — the escape `≢ 0` uniformity kernel, the phase's hardest
  open item, and what the whole research arc attacks. **Standing adjudication ("C: literature
  hunt + A", 2026-07-30): carry `hK` pinned; option B NOT authorized**; both literature hunts
  are MISSes, and since 2026-08-02 it also carries **(K-res)**. **The mathematics is NOT
  restated here** — canonical home is `notes/Pencil-informal.md`'s **State of (K)** gap map
  (per gap: status, what would close it, uncovered shapes, a *settled, do not re-derive*
  block). Read that map, not this bullet, before any (K) work.
- **`hbareSplit`** (kernel (K-bare), research) — the bare-half-off-feasibility kernel,
  **carried as pinned** ("C: cheap numerics extensions + A", 2026-07-30; option B NOT
  commissioned), extension route recon'd **NO-GO on landed machinery**. Minimal open
  statement **(K-bare-ext)**; status row in the gap map, full record in the design doc
  §"(K-bare) extension-route recon", numerics `notes/scripts/kbare/{danger,optc}.py`.

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
- **The EIGHTH FAN-OUT, landing as it goes** (ordinals 25–29; specs and per-direction
  verdicts `notes/Pencil-fanout.md` §"Eighth fan-out", **not restated here**; drivers
  `w4/{gtmpl,gflow,gcoll,oschu,sigz}.py`).
  **25 GTMPL** — attack (c)'s AA-glue case settled at an **exact `n_hub` boundary**: two new
  `n`-free charges (GR-80)/(GR-81) chain to `n_hub ≥ 16` (GR-82), killing the three
  (GR-76)(iv) templates; (GR-83)'s `n_hub = 16` witness has the (GR-38) kill **FAILING**;
  (GR-84) kills even (GR-75)(iii)'s uncrossing from 16. A finite bound, not a contradiction
  — the `slack + defect(T) = 1` residual stays open at `n_hub ≥ 10`; (GR-76)(iii)
  **superseded, not refuted**.
  **26 GFLOW** — **(b′) a HIT at a different constant**: Clause A′ sub-clause 1 **PROVEN**
  (GR-87), sub-clause 2 **REFUTED as posed** (GR-88) while Clause A′ itself survives, so the
  residual becomes a **selection** clause (C2); (GR-86)'s repair-chain price telescopes,
  giving (GR-89) `d_adm − d_par ≤ 4·min(k, ⌊n_hub/4⌋) ≤ 12`, `n`-free, **modulo (R1)**.
  **(b′) at 2 stays OPEN.**
  **29 SIGZ** — the authorized disproof hunt: **NO HIT**, and the pivot rule never
  triggered. (OC-35)/(OC-36) recast the pencil self-stress space as a **Kirchhoff flow on
  topological paths** with `corank R(F) = Σδ + ρ − slack` in closed form, and **(OC-37)** is
  the theorem: at a class shape `slack ≥ 0` with equality only at cycles/bouquets, so **no
  `H`-supported stress in the habitat is combinatorially forced — the counting route to a
  disproof is DEAD** (enumerated, no cap; the theta bound `Σ min(ℓᵢ,6) ≥ 13` tight).
  **(OC-38)** locates `P21`'s mechanism as **one unit short** of the class *and* on the
  `plane_basis` degeneracy locus (a set equality), which **corrects (OC-28)(iv)'s
  quantitative reading at all six sites** — the *proper-open* claim itself stands.
  **(OC-39)** certifies `{σ = 0} ≠ ∅` at 3368/3368 class pairs.
  **28 OSCHU** — **(a₁) half-proven, half-reduced to one determinant.** (OC-29): the Schubert
  4-space is §(K-out)'s **own** hub pencils `L_b ⊕ L_c`, so `dimK ≥ 1` always; (OC-30) pins
  the bad set exactly; **(OC-31)**: at every target-rank chart point of the **whole graph
  `G`** the tower gives `C(vb) ∈ L_b`, `C(ac) ∈ L_c` free, forcing `dimK ≤ 2` — so **`hK` at
  ONE `G`-point kills (OC-26)(ii)'s `dimK ≥ 3` disjunct at every eligible split at once** —
  and (OC-32) makes the bound exact; **(OC-33)** reduces the survivor to **one 3×3
  determinant** `rank(Q|_D) = 3`, whose cheapest attack stops on a **field** obstruction
  (needs exact `ℚ(i)`, a design item). **(OC-34)**: the (a₂) re-keying is a HIT and corrects
  an arc-wide figure — §(K-grid)'s 907 *labelled* shapes are only **75 classes** covering
  **19** of §(K-out)'s **174**; the other **155 certified directly**, so the `s₀` half is free
  at all 174 **without** (GR-10).
  **All four corrected a defective spec clause** — GTMPL an empty "is it fully-good?"
  branch, GFLOW the "min-cost flow, hence polynomial" instrument, OSCHU both an inherited
  "equivalently `dimK ≤ 1`" (sufficient, not equivalent) and the coordinator's own
  "CONDITIONAL on (GR-10)" (wrong at directly-certified shapes), SIGZ the coordinator's own
  over-strong "(a₂) free unconditionally" (only the counting half closes) — **five clauses
  across four landings**, three inherited from landed hand-offs and two written at prep.
  E1/E2/E3 NO at all four; **E3 stays ARMED**.

- **Directions 1–24 — ALL LANDED 2026-08-05…08-19** (thirteen across the first five
  fan-outs, one per ordinal from the sixth on; drivers `w4/{cflank,gcap,gunif,gexist,
  gorient,gdev,gadm,gpsa,gdesc,gbal,glaw,ocon,ltwo,cirr,yloc,balb,zneq,aglu}.py`, FRES no
  driver). **Per-direction verdicts are NOT restated here** — canonical homes
  `notes/Pencil-fanout{,-archive}.md`, the workbook sections each names, and
  `notes/Pencil-labels.md`. **Net: three HITs** — entry 5 PROVEN both halves (GBAL,
  discharging (X)); chart irreducibility PROVEN (CIRR); AA-glue NOT realizable at
  `n_hub = 8` (AGLU) — the rest honest MISSes or OPEN reshapes, each with a named
  successor. **Cross-cutting:** three cross-direction convergences (OCON/FRES, YLOC/BALB,
  CIRR/ZNEQ) and **two coordinator-predicted obstructions refuted** by the directions they
  primed — both `RESEARCH-ARC.md` watch items. (GR-9)/(FR-R1) PROVEN; **(GR-15) OPEN
  throughout; E1/E2 never fired; E3 ARMED by GBAL, not fired.**

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
