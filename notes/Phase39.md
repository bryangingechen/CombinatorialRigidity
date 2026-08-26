# Phase 39 — PENCIL: the hinge-pencil molecular conjecture (work log)

**Status:** in progress — the phase stays OPEN (2026-07-24 adjudication). The
target is **`PencilPair K 3 G`**, and the landed successor
`pencil_conjecture_of_hcontract_hK_hbareSplit_of_card`
(`Molecule/Pencil/Escape.lean`) derives it from exactly **three carried
items**: **`hcontract`** (W4 — build parked by the Lean hold, four informal
costs NOT parked), **`hK`** (kernel (K)), **`hbareSplit`** (kernel (K-bare)).
Everything else in the phase is closed: W0–W3 and the whole W5 arc (L0–L7),
with **`hsplit` CLOSED IN FULL** and `hfresh`'s counting discharge landed
(2026-07-30).

**The kernel-(K) research arc: 51 directions COMPLETE** (2026-08-05 → 08-26,
ordinals 1–43), plus eight strategy-only passes and two architecture probes.
Ordinals 42–43 are LANDED, so the arc stands at **51 directions COMPLETE**;
**ordinal 44 (BTWOCUT) is IN FLIGHT** at the strengthened 2-cut lemma, which
**is** (BE-14).
**Per-direction verdicts are NOT restated here** — each has a landing write-up
at `notes/Pencil-fanout.md` §"<CODE>" and a canonical mathematical home in the
workbooks. **The arc's standing result, unchanged by all 47: `hK` is not
closer.** **(GR-15)** — the single open gap the whole §(K-grid) chain reduces
to — is **untouched**; **class uniformity of the escape is untouched**; no
g-flank was found by any direction; **E3 is ARMED (by GBAL) and has never
fired**.

**What the arc did buy**, in one line each: route-ledger **entry 5 PROVEN**
(GBAL) and **chart irreducibility PROVEN** (CIRR); **(GR-R1) PROVEN** (GFLIP)
and **(GR-C2) settled both ways** (GCHEAP), making (b′) at the constant 2 a
theorem on the `n_hub ≤ 6` stratum; **input (a) at all 174 certified classes**
(OQRANK); the **(b′) price form REFUTED** (GHWIT) and then shown to be a
statement **the ledger never consumed** (GMINM — (b′) has three inequivalent
readings and the consumers run on the difference of minima); the **geometric
disproof route free by an argument** on everything searched (OGEOM); and, at
the arc's first-ever look at `hbareSplit`, **bare realizability proved
UNCONDITIONAL** plus the first pencil-stratum rank cap produced by an argument
(BATTAIN, (BE-11)/(BE-13)).

**NEXT CONCRETE TASK — verify and land BTWOCUT (ordinal 44, IN FLIGHT), then the
queued (K-res) scoping slice.** BTWOCUT is dispatched at the **STRENGTHENED 2-cut
composition lemma, the ONLY thing between the arc and (BE-14)** — spec at
`notes/Pencil-fanout.md` §"BTWOCUT". **Its selection was forced, not ranked:** by
BINDUC's exhaustive decomposition no other candidate exists, and proving it
discharges `hbareSplit` *and* `PencilPair`'s unconditional conjunct as a
standalone theorem. **If it returns a HIT shape 1, the phase-boundary
consequences are the USER's call** — whether Phase 39 closes and a successor
opens for the Lean is a `PHASE-BOUNDARIES.md` event against the standing
2026-07-24 no-split adjudication, surfaced with a commit-count estimate, never
taken unilaterally; the 2026-08-05 Lean hold binds regardless of how good the
news is.

**The lemma, for reference —** BINDUC reduced (BE-14) to an
exhaustive decomposition whose base is **free** and whose 1-cut layer is
**done**, leaving one lemma: *attains ⟺ `dim(ρ̄₁+ρ̄₂) = min(δ₁+δ₂,6)`* across a
2-cut, which needs (a) the induction to carry a **strengthened** statement
(welded-framework attainment, since `ρ_i ≤ δ_i` always) and (b) a general-position
input the residual gauge group provably cannot supply (dim 7/5 against
`Gr(3,6)`'s 9). Its free sub-cases are proved. **Then** the queued **(K-res)
scoping slice**, then the next pick.

**BINDUC LANDED 2026-08-26 — the arc's biggest single advance on the phase
target.** **3-connected ⇒ `def₂ = 0`** in four elementary lines (exhaustive at
226 891 graphs, bound tight), so `def₃ = 0` and the **flat witness** attains in
closed form: **the base of the induction is FREE, and BATTAIN's declined
`def₂ = def₃` slice covers the whole of it.** Contrapositive: **`def₂ > def₃`
forces a cut of size `≤ 2`.** BZAVOID's asserted 2-cut `− 6` is **REFUTED**
(negative at 87 % of 10 804 gluings) and replaced by an exact `max`-law. A new
**hub-plane construction** proves (BE-14) at **5 824** further graphs, **2 441
beyond every witness the arc had**. On the disproof side the new-cap mechanism the
spec asked for **exists, is strictly more general than BZAVOID's, and fires
empty** (25 270 instances) — **which is also a SCOPE CORRECTION to (BE-15)(ii)**,
see the note below.

**ZJACOB LANDED 2026-08-26**: (ZH-4) **REFUTED by an EQUIVALENCE** — the corank
stratification makes *"LCI of the expected codimension"* ⟺ `B_0 ≠ ∅` ∧
`codim B_k ≥ k`, and `B_0 ≠ ∅` **IS** properness, so the route's hypothesis
contains its conclusion. Its refutation **absorbs (ZH-3)**, leaving §9 with
**exactly one dispatchable candidate** ((ZH-2), stratified only).

> **SCOPE CORRECTION to the BZAVOID landing, made at the BINDUC landing and
> recorded here because the coordinator's own prose carried the over-reach.**
> (BE-15)(ii) was landed and reported as closing the falsification arm *"by an
> argument at every graph, cap-free"*. That holds for the **TRIANGLE-forced**
> mechanism only: (BE-15)'s propagation rule is *adjacent-pair* forcing, while
> the **general** rule fires once a closed neighbourhood holds three independent
> pinned points and needs **no triangle** (`K_{3,3}` is forced flat and
> triangle-free), so the forced classes can be strictly coarser and the
> *"triangle-covered ⇒ `def₂ = 0`"* step does not reach them. The general
> mechanism is closed only as **MEASURED**. Corrected in place at the workbook
> claim, the gap-map row, the fan-out header and here; **a proof of (BE-23)(ii)
> is the named target that would restore it in full**, and it is the disproof
> side's highest-value single search. **Still queued behind them: the (K-res) scoping slice**
(one direction — does (GR-15)/§(K-grid) transport to the `W19`-type (K-res)
habitat? — the user's 2026-08-26 adjudication, and the retirement of the stale
*"pin it when the tight side closes"* deferral), **deferred once by the
2026-08-26 max-impact directive, not dropped.**
**ZSHEAR** — the §9 shelf's first direction ever — refuted **(ZH-1)** by
**gauge-triviality**: the Witt shear *is* the translation subgroup of `PGL(4)`
on line coordinates, `Q` is its own defining invariant, and the §(K-tight)
criterion matrix is literally the same matrix in the pushed basis, so the
mechanism is vacuous; the candidate is **STRUCK**, the owed §2.5 filter check is
**DISCHARGED**, and the durable residue is that `Q(r̃) ≠ 0` is `PGL(4)`-invariant,
so **no gauge-fixing can ever supply it**. **BZAVOID LANDED 2026-08-26** and did three things: the spec's commissioned
falsification arm came back **empty BY AN ARGUMENT at every graph**, so
BATTAIN's triangle-free premise is a special case rather than the reason
((BE-15)); the pencil stratum is **IDENTIFIED as the planar-atom molecular
stratum**, which makes (BE-14) **existential rather than generic** — one witness
per graph settles that graph ((BE-16)); and **two routes are CLOSED**, the
landed Phases-24–26 `G²` apparatus and the coordinator's own transversality
count ((BE-17)/(BE-16)(iv)). **(BE-14) is reduced to 2-connected graphs and
still OPEN**; `hbareSplit` untouched and pinned; nothing refuted.

> **BOTH ADJUDICATIONS ARE DISCHARGED** (opened 2026-08-26 at the BATTAIN
> landing, answered the same day at the ninth check-in; verbatim record in
> *Current state*). **(1) (K-res)** — the user selected the **cheap scoping
> slice**, not the wave and not a re-deferral: one direction asking whether
> (GR-15)/§(K-grid) transports to the `W19`-type (K-res) habitat, which retires
> the stale *"pin it when the tight side closes"* deferral without committing a
> wave at an `hK`-class kernel. **Queued behind the two in flight.**
> **(2) The (BE-14) slice shape** — the user selected the **full statement**,
> declining BATTAIN's `def₂ = def₃` proof-of-concept on the ground that it does
> not discharge `hbareSplit`. Dispatched as **BZAVOID**. **Nothing now awaits
> adjudication.**

**Conventions.** Direction codes are multi-letter and topic-tagged from the
fifth fan-out on (`notes/Pencil-labels.md` (L5)); grandfathered single letters
are re-used across dates, so **always date those**. The doc-split and
discipline-distillation rounds are both COMPLETE (`notes/Pencil-structure.md`;
`RESEARCH-ARC.md` is the promoted manual). Both architecture probes are landed
(KBARE-FALSIFY, C3-AVOID). File layout: `Molecule/Pencil.lean` split into
`Molecule/Pencil/{Statement,Arms,Motive,Chart,Engine,Reseed,Witness,Steer,Pair,
Pair2,Escape,Base}.lean`; per-leaf history `notes/Phase39-design.md`.

**Canonical homes — read these, not a summary of them.** The **State of (K)**
gap map in `notes/Pencil-informal.md` is the phase's status object and is
authoritative for every status word; `notes/Pencil-informal-grid.md` owns
§(K-grid); `notes/Pencil-strategy.md` owns the option board (§8) and the
unpriced §9 shelf **(ZH-1)–(ZH-6)**, which stays ineligible;
`notes/Pencil-fanout.md` owns dispatch specs and landing write-ups;
`notes/Pencil-adjudications.md` owns the archived verbatim user calls.


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
- **2026-08-05 → 08-19, the selection history for ordinals 1–19, archived.** The
  dated adjudication/delegation bullets that picked the second through sixth
  fan-outs and the single directions between them (2026-08-05…07, 2026-08-07,
  2026-08-12, 2026-08-13, and the 2026-08-19 sixth-fan-out dispatch) moved
  **verbatim** to `notes/Pencil-adjudications.md` (2026-08-19, the phase-note
  doc split, `notes/Pencil-structure.md`); none of them changes a standing
  constraint. Read there for the exact quotes.

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

- **2026-08-19, post-wave adjudication (two calls; neither changes a kernel constraint).** With
  the eighth fan-out closed and the phase UNROUTED, the user was offered four next steps
  (clear the structural items / pick a direction / pause / a ninth fan-out) and selected
  **"Clear the two structural items first"** — so the doc split and the harness move-down
  round precede any further research pick. Asked separately about `closure.Gauss` — the exact
  `ℚ(i)` class OSCHU's residual route needs, deliberately kept private to `closure` because
  moving it "would re-baseline the whole chain" — the user selected **"Move `Gauss` down to
  `exactcore`"**, over the offered alternatives of deciding later or keeping the route
  ℚ(i)-local. That is a **design decision**, recorded in `notes/scripts/README.md` *Harness
  debt* item 3 with the binding constraint that **figures do not move** (a re-export from
  `closure`, the `star_span_ranks` precedent). Phase OPEN, Lean hold, W4 PARKED,
  `hK`/`hbareSplit` pinned, option B un-commissioned — all unchanged. **Both calls are now
  DISCHARGED:** slice 1 landed 2026-08-19, slice 2 (the move-down round, `Gauss` included)
  landed 2026-08-20 — so the research pick this adjudication deferred is live again.

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

- **2026-08-20, the GFLOW bare-token collision — RENAME, not qualify.** HEAD's landing
  recorded GFLOW's three residual clauses (GR-89)'s bare `(R1)`/`(C1)`/`(C2)` as
  **"Disposition: QUALIFY, do not rename"**, with the rename left open for the user as one
  of a small option selection. The user selected, verbatim, **"Rename to
  (GR-R1)/(GR-C1)/(GR-C2)"** — *"Follows the direction-A precedent (bare (R1)/(R2) →
  (ANH-R1)/(ANH-R2) at landing). They are only three commits old, so the repoint is
  small."* An option selection, not free text, so the QUALIFY disposition is superseded:
  GFLOW's three tokens are `(GR-R1)`/`(GR-C1)`/`(GR-C2)` everywhere in the corpus now,
  verified 0-hit before minting; `notes/Pencil-labels.md`'s collision record is
  ADJUDICATED/RENAMED. Everything else stands unchanged.

- **2026-08-20, probe KBARE-FALSIFY landed — a T1 hit, and no standing constraint
  moves.** The commissioned falsification hunt for `hbareSplit` returned a **HIT at
  tier T1**: **(K-bare-ext) is REFUTED as stated** (`notes/Pencil-informal.md`
  §(K-bare-ext) *Steps BE1–BE8*; driver `notes/scripts/kbare/breakhunt.py`). What
  that does and does not mean, stated here because the distinction is the whole
  point of the tiering: `hbareSplit`'s consequent `HasPencilRealization K 3 G` is an
  **existential** over frameworks, and both danger gadgets **attain** their bare
  target, so the **kernel is untouched** — what died is route A's *fixed-seed*
  strategy, i.e. the `∀`-over-seeds shape of its discharge statement. The
  2026-07-30 (K-bare) adjudication (*"C: cheap numerics extensions + A"*) therefore
  **stands unchanged**: `hbareSplit` carried as pinned, option B still
  un-commissioned. **One correction the probe returned about the tier semantics,
  recorded because it changes who a future T2 decides:** `PencilPair`
  (`Motive.lean:160`) carries `HasPencilRealization K n G` as an **unconditional**
  second conjunct, so a T2 witness would make **`PencilPair K 3 G` itself false** at
  that `G` — the phase's *target motive*, not merely the induction that reaches it.
  Stated precisely, because the loose form of this claim misleads: the landed
  `pencil_conjecture_of_hcontract_hK_hbareSplit_of_card` **derives** `PencilPair K 3 G`
  from the three carried hypotheses, so a T2 witness does **not** break that theorem —
  it proves **`hbareSplit` false**, leaving the theorem true and unusable. What makes a
  T2 a **PENCIL event**, with the direction-A pivot rule in force, is the *other* half:
  `PencilPair K 3 G` failing at a `G` in scope refutes **what** the phase is trying to
  prove, not merely **how**. Either way this is not the "phase-shape event, not a PENCIL
  event" the probe's own spec predicted (corrected in the spec too). No T2 candidate exists in the arc's gadget
  stock and none is producible by this harness (T2 is a universal non-existence over
  frameworks), so nothing turns on it operationally.

- **2026-08-25, the research pick — shape adjudicated: SINGLE DIRECTION, CHEAPEST FIRST
  (changes no standing constraint).** At the session check-in the user was offered four
  shapes for the standing pick (single direction cheapest-first / ninth multidispatch
  fan-out / top-rung recon-first / a user-named direction) and selected **"Single
  direction, cheapest first"** — an option selection, not free text — which resolves to
  **(GR-R1)** by §8.1's own ranking, dispatched as **GFLIP** (ordinal 30) at top rung
  (`recon-fable`). Same check-in: rungs **all four dispatchable, fable included** (the
  first session since the sixth fan-out with fable unconserved), cap **lifted**, rescue
  §1 fixups **pre-authorized**. Both probe verdicts (KBARE-FALSIFY's T1 hit, C3-AVOID's
  C3 NO-GO) were surfaced at this check-in, discharging the "mention at next check-in"
  flag. **Everything else stands unchanged:** phase OPEN, the 2026-08-05 Lean hold, W4
  PARKED, `hK`/`hbareSplit` pinned, option B un-commissioned.

- **2026-08-25 (second check-in), the next research pick — the same shape RE-ELECTED
  (changes no standing constraint).** With GFLIP landed the same day, the user was
  offered four shapes for the next standing pick (single direction cheapest-first /
  ninth multidispatch fan-out / top-rung recon-first / a user-named direction) and
  selected **"Single direction, cheapest first"** — an option selection, not free
  text — which resolves to **(GR-C2)** by §8.1's own ranking ((GR-R1) struck by
  GFLIP), dispatched as **GCHEAP** (ordinal 31) at top rung (`recon-fable`). Same
  check-in: rungs **all four dispatchable, fable included**, cap **lifted**, rescue
  §1 fixups **pre-authorized**. Before the prep, the coordinator had GFLIP's
  harness-debt item paid (the `w4/` balance layer → `gridbal_common`, one sonnet
  dispatch, 2026-08-25 — `notes/scripts/README.md` *Harness debt*). **Everything
  else stands unchanged:** phase OPEN, the 2026-08-05 Lean hold, W4 PARKED,
  `hK`/`hbareSplit` pinned, option B un-commissioned.

- **2026-08-25 (third check-in), the pick after GCHEAP — RECON-FIRST elected, then
  the recon's front-runner (changes no standing constraint).** With GCHEAP landed,
  the user was offered four shapes (single direction front-runner-first / ninth
  fan-out / top-rung recon-first / pause) and selected **"Top-rung recon-first"** —
  an option selection — producing the **eighth strategy-only pass** (`f72cbb35`,
  fable): strategy §8 re-ranked, each top-3 candidate's inputs re-derived at its
  owning workbook step (the F22 guard), (K-bare) given its first board row. Offered
  the re-ranked top three plus pause, the user then selected **"Rank 1: O29 ℚ(i)
  leg"** — an option selection — dispatched as **OQRANK** (ordinal 32) at top rung
  (`recon-fable`). A recon-flagged stale evidence sentence in this note's
  `hbareSplit` bullet was corrected by a coordinator commit (`fbe7da83`).
  **Everything else stands unchanged:** phase OPEN, the 2026-08-05 Lean hold, W4
  PARKED, `hK`/`hbareSplit` pinned, option B un-commissioned.

- **2026-08-25 (fourth check-in), the pick after OQRANK — the front-runner shape
  elected (changes no standing constraint).** With OQRANK landed, the user was
  offered four shapes (single direction front-runner-first / single direction at
  (K-bare)'s rank-3 shape / ninth multidispatch fan-out / top-rung recon-first)
  and selected **"Single direction, front-runner-first"** — an option selection,
  not free text — which resolves to **(GR-104)(i)**, the price form: the
  2026-08-25 re-rank's rank 2 and its highest unlanded entry (rank 1, the O29
  ℚ(i) leg, landed as OQRANK the same day). Dispatched as **GPRICE** (ordinal
  33) at top rung (`recon-fable`). Same check-in: rungs **all four dispatchable,
  fable included**, cap **lifted**, rescue §1 fixups **pre-authorized**.
  **Everything else stands unchanged:** phase OPEN, the 2026-08-05 Lean hold, W4
  PARKED, `hK`/`hbareSplit` pinned, option B un-commissioned.

- **2026-08-25 (fifth check-in), the pick after GPRICE — the front-runner shape
  RE-ELECTED, and the harness debt paid first (changes no standing constraint).**
  With GPRICE landed, the user was offered four shapes (single direction
  front-runner-first → (GR-108) / single direction at (K-bare)'s rank-3 shape /
  ninth multidispatch fan-out / top-rung recon-first) and selected **"Single
  direction, front-runner-first → (GR-108)"** — an option selection, not free
  text — which resolves to **(GR-108), the balance law**: GPRICE's residual #1,
  the head of *Step G129*'s successor order and the first entry of *Hand-off*'s
  candidate list (the 2026-08-25 re-rank's ranks 1 and 2 both landed the same
  day). Dispatched as **GBLAW** (ordinal 34) at top rung (`recon-fable`). Asked
  separately about the recorded harness debt, the user selected **"Pay first,
  one sonnet dispatch"** — GCHEAP's residual sibling imports and GPRICE's five
  consumer arrivals, paid together per the GPRICE item's own instruction
  (`782e8bcd`, before the GBLAW prep). Same check-in: rungs **all four
  dispatchable, fable included**, cap **lifted**, rescue §1 fixups
  **pre-authorized**. **Everything else stands unchanged:** phase OPEN, the
  2026-08-05 Lean hold, W4 PARKED, `hK`/`hbareSplit` pinned, option B
  un-commissioned.

- **2026-08-26 (sixth check-in), the pick after GBLAW — the front-runner shape
  RE-ELECTED (changes no standing constraint).** With GBLAW landed, the user
  was offered four shapes (single direction front-runner-first → existential
  escape / single direction at (K-bare)'s rank-3 shape / top-rung recon-first
  (a ninth strategy pass) / ninth multidispatch fan-out) and selected
  **"Single direction, front-runner-first → existential escape"** — an option
  selection, not free text — which resolves to **existential escape**
  ((GR-112)(v)'s hypothesis): GBLAW's sharpened residual #1, the head of
  *Step G134*'s successor order and the first entry of *Hand-off*'s candidate
  list. Dispatched as **GXESC** (ordinal 35) at top rung (`recon-fable`).
  Session config carried from the fifth check-in (all four rungs, cap lifted,
  fixups pre-authorized). **Everything else stands unchanged:** phase OPEN,
  the 2026-08-05 Lean hold, W4 PARKED, `hK`/`hbareSplit` pinned, option B
  un-commissioned.

- **2026-08-26 (seventh check-in), the pick after GXESC — the front-runner shape
  RE-ELECTED, and FABLE CONSERVED (the first session-config move since
  2026-08-25; no kernel constraint moves).** With GXESC landed, the user was
  offered four shapes (single direction front-runner-first → the half-witness
  clause / single direction at (K-bare)'s rank-3 shape / top-rung recon-first (a
  ninth strategy pass) / ninth multidispatch fan-out) and selected **"Single
  direction, front-runner-first → (GR-117)(iii)"** — an option selection, not
  free text — which resolves to the **half-witness clause**: GXESC's reshaped
  residual, the head of *Step G139*'s successor order and the first entry of
  *Hand-off*'s candidate list. Dispatched as **GHWIT** (ordinal 36).
  **The config move, recorded because it changes the calibration baseline:**
  asked in the same check-in which rungs are dispatchable, the user selected
  only **cap lifted** and **rescue §1 fixups pre-authorized**, leaving *"all
  four rungs dispatchable"* **unselected** — so **fable is conserved this
  session: sonnet + opus only, top rung = opus** (`weekly_scoped` at 92 %
  critical corroborates the reading), and GHWIT dispatches at **`recon-opus`**,
  the playbook's nearest-available substitute at or above the mapped rung. It is
  **the first of the seven single directions GFLIP–GHWIT not to run at
  `recon-fable`**; the six predecessors' returns are the calibration baseline,
  so a thinner return is a rung artifact to report rather than a property of the
  target. **Everything else stands unchanged:** phase OPEN, the 2026-08-05 Lean
  hold, W4 PARKED, `hK`/`hbareSplit` pinned, option B un-commissioned.

- **2026-08-26 (seventh check-in, second call), the DELEGATION WIDENS — the
  coordinator picks each direction for the rest of the session, and the
  selection criteria move toward falsification.** Unprompted free text, quoted
  verbatim because it supersedes the *shape*-only half of the standing
  2026-08-07 delegation for this session: *"For this session, I'd like to
  coordinator to choose the next direction after each subagent returns. We
  should aim to explore different paths rather than getting bogged down in
  directions which might never pan out. Think also about whether there are
  examples we can build that could kill off whole directions of the current
  proof strategy (or even be a counterexample to what we're trying to prove)."*
  Three consequences, none of them a kernel-constraint move: **(1)** the *pick*
  as well as its shape is coordinator-set for the rest of this session — the
  per-pick check-in lapses, and the twelfth's disclosure (no independent
  top-rung ranking of the losers) applies to every pick made under it;
  **(2)** **diversification is now a selection criterion** — the arc's recent
  concentration is the thing being corrected (**six of the last seven
  directions are §(K-grid)**, four of them consecutively on the (GR-104)(i)
  price-form thread GPRICE → GBLAW → GXESC → GHWIT, a thread `notes/Pencil-strategy.md`
  §8's own re-rank calls *"a residual-of-a-residual inside the (a′)/(b′)
  ledger"* that *"does not touch a named `hK` gap"*); **(3)** **§8.5's category
  — "test the architecture instead of extending it" — is promoted from a board
  row to a standing preference**, which is what §8.5's own header already
  recommended (*"the move this board's own risk analysis recommends before more
  `hK` spend"*). The direction-A pivot rule is unaffected and still binds: a
  disproof-side hit is a phase-redefining event for the **user** to adjudicate,
  surfaced not built on. **Everything else stands unchanged:** phase OPEN, the
  2026-08-05 Lean hold, W4 PARKED, `hK`/`hbareSplit` pinned, both option Bs
  un-commissioned, (K-res) still a user call.

- **2026-08-26 (seventh check-in, third call), the DIRECTION-A PIVOT RULE's stop
  clause is PRE-ADJUDICATED — a confirmed disproof is worked up, not surfaced for
  a decision.** Asked whether a disproof would not simply have an obvious
  response, the user settled it, verbatim: *"OK, if there is a confirmed
  disproof, then it does reverse what the result of this phase; however, I think
  the steps we would take are clear, right? We should clean up that disproof and
  prepare it for formalization (probably in the next phase)."* This **supersedes
  the stop-and-adjudicate half** of the Direction-A pivot rule
  (`notes/Pencil-fanout-archive.md` §"Direction A") and of the 2026-08-19 SIGZ
  authorization terms: on a confirmed half-2 disproof the loop does **not** halt
  for a user decision — the coordinator works the disproof up to a
  formalization-ready informal statement inside this phase, under the standing
  Lean hold (so: workbook + drivers + a corrected statement, **no `.lean`**), and
  the Lean lands in a successor phase. **What the pre-adjudication does NOT
  cover, and what still comes to the user:** (i) the **classification** — half 1
  (the `hK` *pin* fails: a re-pin, explicitly *"not a disproof of the
  conjecture"*) versus half 2 (the conjecture itself fails) versus a T1-style
  *route* refutation; the coordinator reports which landed rather than the flat
  word "disproof", the KBARE-FALSIFY precedent being a direction whose own spec
  mis-predicted its own category; (ii) **"confirmed"** — a first return is not
  confirmed; the bar is the (GR-83)/(GR-113) one that GXESC's witnesses cleared
  (every figure re-derived through three independent exact models, two of them
  landed), and `RESEARCH-ARC.md` item 4 binds: the corrective mechanism is the
  **next pass**, not coordinator scrutiny, so a confirming pass is priced into
  the work-up; (iii) the **phase boundary** — whether Phase 39 closes and a
  successor opens for the Lean is a `PHASE-BOUNDARIES.md` event against a
  standing 2026-07-24 no-split adjudication, so it is surfaced with a
  commit-count estimate, not taken unilaterally. **Everything else stands
  unchanged:** phase OPEN, the 2026-08-05 Lean hold, W4 PARKED, `hK`/`hbareSplit`
  pinned, both option Bs un-commissioned, (K-res) still a user call.

- **2026-08-26 (eighth check-in), the SELECTION CRITERION MOVES — prioritize by
  distance to the PHASE TARGET.** After a walk-through of where OGEOM sat in the
  (K) work and what a disproof of its residual would and would not mean, the
  user directed, verbatim: *"I think we should be prioritizing work that makes
  headway on the phase target one way or the other."* This **supersedes the
  board's cheapest-decisive-first convention** as the ordering criterion for
  picks made under the widened delegation. The coordinator's audit, recorded
  because the finding is structural: the docs were **not** emphasizing
  target-moving work, and the miss was systematic — *Hand-off*'s candidate list
  was ordered by the previous direction's **successor order** (which
  mechanically chases residuals; five directions on the (b′) price form is what
  that produces), W4's four informal costs sat unranked in option-board §8.5
  rather than anywhere a reader looks for the next build, **(K-res) appeared in
  the dispatch docs only as a bar** (excluded from eight consecutive specs), and
  §8's ranking criterion measures the *direction*, not its distance to the
  target. **Acted on at the BATTAIN landing:** *Hand-off*'s candidate list is
  re-ordered by target distance, with the three carried items at its head. **Not
  acted on, and still a user call: (K-res)** — wave-sized, never attacked, and
  the thing route 3 **cannot close without**; its "pin it when the tight side
  closes" deferral is now stale by the note's own admission. **Everything else
  stands unchanged:** phase OPEN, the 2026-08-05 Lean hold, W4 PARKED,
  `hK`/`hbareSplit` pinned, both option Bs un-commissioned.

- **2026-08-26 (ninth check-in), BOTH OPEN ADJUDICATIONS DISCHARGED, the pick made,
  and a USER-INITIATED SIDE LINE opened — the first direction the §9 external shelf has
  ever produced.** Four calls, none of them a kernel-constraint move.
  **(1) The (BE-14) slice shape** (the adjudication BATTAIN's landing opened): offered the
  full statement, BATTAIN's `def₂ = def₃` proof-of-concept, W4's three informal costs, or
  diversification off the carried items, the user selected **"(BE-14) full statement —
  hbareSplit"** — an option selection, not free text — so the proof-of-concept is
  **declined**, on the ground the offer itself named: it does not discharge `hbareSplit`
  (DZ has `def₂ = 11`). Dispatched as **BZAVOID** (ordinal 40) at `recon-opus`. The option
  set was coordinator-authored, so the twelfth's disclosure applies to the **alternatives**;
  the **pick between them is the user's**, which makes this the first non-coordinator pick
  since the 2026-08-26 delegation widened.
  **(2) (K-res)** (the other open adjudication): offered the full wave, a cheap scoping
  slice, or keeping it a bar, the user selected **"Cheap scoping slice only"** — one
  direction asking whether (GR-15)/§(K-grid) transports to the `W19`-type (K-res) habitat.
  This **retires the stale "pin it when the tight side closes" deferral** without
  commissioning a wave at an `hK`-class kernel, and it **is not** option B by another name.
  **Queued behind the two in flight; nothing now awaits adjudication.**
  **(3) The side line, unprompted free text, quoted verbatim because it opened a shelf that
  had been ineligible since 2026-08-21:** *"I'm also curious about whether the ideas
  inspired by Zheng's body-pin project are worth pursuing. Perhaps we can look at that on
  the side?"* Answered by dispatching **ZSHEAR** (ordinal 41) concurrently with BZAVOID at
  `recon-opus`, scoped to **(ZH-1) alone** — §9.3's own cheapest-decisive-first head, the
  only one of the six with an adversarial bed already in tree (§(K-flank) *Step F5(d)*'s
  five *proven* escape failures at `P21`) — plus the **owed §2.5 counting-saturation filter
  check on (ZH-2)/(ZH-3)**, which §8's board had recorded as *"a cheap prose-only slice and
  worth running opportunistically"*. **The provenance bar is unchanged and is the hard bar:**
  the source is unrefereed, its own acknowledgment credits an AI assistant with the proof
  details and the Lean verification, and neither paper nor repository has been independently
  checked — it is an **idea source, never a citation**, and no theorem of it may be
  imported. (ZH-4)/(ZH-5) stay unopened, (ZH-6) stays write-up material, and
  **the shelf stays off §8's board either way**. Non-collision with BZAVOID is structural:
  different sections, disjoint tags (`BE-` vs `SH-`), serial coordinator landing.
  **(4) Session config — fable CONSERVED for the second consecutive session.** The user
  selected **cap lifted**, **rescue §1 fixups pre-authorized**, and **"coordinator picks
  each direction this session"** (re-electing the 2026-08-26 widening, so the per-pick
  check-in lapses again), leaving *"all four rungs dispatchable"* **unselected** — so
  **sonnet + opus only, top rung = opus**, `weekly_scoped` at 92 % critical corroborating,
  `weekly_all` at 77 % (below the 80 % stagger line, which is what licenses the concurrent
  pair rather than a stagger). **Everything else stands unchanged:** phase OPEN, the
  2026-08-05 Lean hold, W4 PARKED, `hK`/`hbareSplit` pinned, both option Bs
  un-commissioned.

- **2026-08-26 (tenth check-in), the SELECTION CRITERION SHARPENS AGAIN and the
  Zheng line becomes a standing second lane.** Unprompted free text, quoted
  verbatim: *"Let's continue with 2 dispatches in parallel one on the direction
  that is most likely to have most impact towards either proving or disproving
  the target theorem and one continuing the Zheng line."* Three consequences,
  none a kernel-constraint move. **(1)** The criterion is now **max impact on
  proving or disproving `PencilPair K 3 G`** — sharper than the eighth
  check-in's *distance to the phase target*, since it counts **either
  direction** explicitly; the coordinator's pick under it is **BINDUC**, on the
  ground that (BE-14) is the only statement on the board that removes a
  **carried item** (`hbareSplit` plus `PencilPair`'s unconditional conjunct),
  with the honest limit recorded in the spec that it leaves `hK` and `hcontract`
  standing. **(2)** The **Zheng line is a standing second lane**, not a one-off
  side quest — the shelf that was ineligible on 2026-08-21 and produced its
  first direction this morning now gets a successor by user direction; the pick
  within it is **forced by §9.3's own updated order** (head (ZH-4) after ZSHEAR
  struck (ZH-1)), so it is not a coordinator ranking. **(3)** The **(K-res)
  scoping slice is deferred one round, not dropped** — it stays the queued item
  behind this pair. **Headroom disclosed rather than glossed:** `weekly_all` was
  at **79 %**, just under the playbook's 80 % stagger line, so the concurrent
  pair is licensed but the round *after* it will likely need staggering; said
  here because the next coordinator should not have to rediscover it.
  **Everything else stands unchanged:** phase OPEN, the 2026-08-05 Lean hold, W4
  PARKED, `hK`/`hbareSplit` pinned, both option Bs un-commissioned.

- **2026-08-26 (eleventh check-in), the HEADROOM RULE RE-CALIBRATED — measured,
  not argued — and one more dispatch authorized before a session break.** Asked
  whether to break or continue, the user first corrected the coordinator's
  standing caution, verbatim: *"I think the guidance not to fan out when
  weekly_all > 80% was when we were using fable subagents. With opus we can
  probably go a bit further before sticking to single dispatches."* **The
  coordinator measured rather than debating, and the correction is confirmed on
  the stronger of its two halves:** `weekly_scoped` sat at **92 % for the entire
  session and did not move a single point across four opus recons**, so it tracks
  **fable only** — exactly the 2026-08-19 finding, now established by measurement
  instead of assertion. Applied literally, `.claude/commands/coordinate-phase.md`'s
  *"above ~80 % on **either** limit, stagger"* would have blocked every fan-out
  this session, **including the pair that produced the arc's biggest advance**;
  the rule as written is mis-calibrated for opus work and should be read as
  *"above ~80 % on the limit the dispatched rung actually consumes."* On the half
  that does bind: `weekly_all` moved **77 → 79 → 81 %**, i.e. **1–2 points per
  pair-round**, leaving on the order of eight to twelve pair-rounds before the
  14-hour reset — so the coordinator's *"the next round should stagger"* was
  **over-conservative and is withdrawn**. Asked then whether to break, the
  coordinator recommended **one more dispatch, bounded** — the 2-cut lemma, specced
  while the just-verified detail (the criterion, both named needs, the free
  sub-cases, the (BE-15) scope correction) was still in hand rather than
  re-derived from the docs — and the user selected **"proceed with your
  suggestion"**. So: **BTWOCUT dispatched, then a session break.** Separately, and
  closing an item `f3ded610`'s message had left open for the user: asked about
  rewriting `d87693ae`'s message, the user answered *"Don't worry about
  d87693ae's commit message; it's fine to just leave it and not track it any
  more."* — **the item is closed and is not tracked anywhere.** **Everything else
  stands unchanged:** phase OPEN, the 2026-08-05 Lean hold, W4 PARKED,
  `hK`/`hbareSplit` pinned, both option Bs un-commissioned, (K-res) queued.

**Kernel-(K) research arc — sixty-eight docs+scripts-only dispatches landed, plus eight
strategy-only passes** (2026-08-02 → 08-26) — and, **outside** that count because they test
the architecture rather than the (K) crux, the **two probes**: **KBARE-FALSIFY**
(2026-08-20) and **C3-AVOID** (2026-08-24), both landed. Which pass was which is one-lined in *Decisions
made*; the rule is that the **dispatch** count moves only on a landing (GBAL/GLAW/FRES/OCON/
LTWO are the fortieth through forty-fourth; CIRR the forty-fifth; YLOC the forty-sixth; BALB
the forty-seventh; ZNEQ the forty-eighth; AGLU the forty-ninth; the eighth fan-out's five
the **fiftieth through fifty-fourth**, all landed 2026-08-19; **GFLIP the fifty-fifth**,
**GCHEAP the fifty-sixth**, **OQRANK the fifty-seventh**, **GPRICE the fifty-eighth**,
all 2026-08-25, and **GBLAW the fifty-ninth**, **GXESC the sixtieth**, **GHWIT the sixty-first** **GMINM the sixty-second**, **OGEOM the sixty-third**, **BATTAIN the sixty-fourth** and **BZAVOID the sixty-fifth**, **ZSHEAR the sixty-sixth**, **ZJACOB the sixty-seventh** and **BINDUC the sixty-eighth**, all 2026-08-26), and a **user call on
dispatch *shape*** — either multidispatch election, or a coordinator-authored pick like the
twelfth's — contributes **no** strategy pass, so the 2026-08-19 eighth-fan-out check-in adds
none even though it moved a standing constraint.
Canonical homes: workbook `notes/Pencil-informal.md` (**State of (K)** map = entry point),
`notes/Pencil-W4-informal.md` (W4-residual), `notes/Pencil-strategy.md` (strategy). Net
effect: **disproof risk removed**, every refuted route/gap has a successor in the gap map,
several structural positives proven, and **route-ledger entry 5 is PROVEN, the arc's first
HIT**; **class uniformity of the escape remains untouched by all sixty.**
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
  (2026-08-02), so branch 4 needs content, and **(SAFE-RES) is REFUTED** the same day, so the
  adjudicated route 3 costs (T) + (V) + the reduced (E) plus **one** widened kernel (K-res)
  (`notes/Pencil-W4-informal.md` §§"`hnoGood'` vacuity"/"(SAFE-RES)"). **No adjudication is
  owed here** — route 3, packaging (b) was adjudicated the same day, 2026-08-02; a stale
  "adjudication owed" flag stood in this bullet for eighteen days and is corrected 2026-08-20.

- **What the Lean hold parks, and what it does NOT — corrected 2026-08-20, because this
  bullet read as though it parked all of W4.** The hold parks **Lean**: the W4 build (W4-L4b
  onward), the `noRigid`-free Lean leaf (E) reduced to, and route σ's steering commit. It does
  **not** park route 3's other four costs, every one **informal mathematics dispatchable
  today** — which the hold's own wording ("hold off on more Lean until we have an informal
  proof") is an argument *for*: **(T)** `G` triangle-free, *"a genuine research gap, not a
  numerics gap"*, landed-**invisible** because the search's own feasibility certificate (L6b)
  requires triangle-freeness, so a triangle-carrying residual can never appear in a certified
  sweep; **(V)** the local choice, elementary given (E) and (T) but needing two `C₄`-carrying
  branch shapes ruled out at *every* `≥ 2`-interior branch; **(E-loc)**, the combinatorial gap
  (E) reduced to (255/255, unproven); and **(K-res)**, a kernel of `hK`'s difficulty class on
  the complementary habitat whose proof route is *strictly harder* (its habitat sits wholesale
  in the `dim R_a = 1` stratum where the (K) recon found no landed-brick route). **(K-res) has
  never been attacked** — it appears in the dispatch docs only as a **bar**, excluded from
  eight consecutive direction specs with one deferral, *"pin it when the tight side closes"*,
  sound when the tight side looked close and now eighteen days and thirty-seven directions old.
  **(T)/(V)/(E-loc) are slice-sized and need no adjudication; (K-res) is wave-sized and is a
  user call.**

- **Doc debt — REMEASURED 2026-08-26, and the figure the 2026-08-20 entry carried is now
  badly stale: this note is 1 127 lines against the ~500 tripwire, not "6xx".** It has
  nearly doubled in six days, and the mechanism is visible in the section counts: *Current
  state* **409** and *Hand-off* **318**, against a finished part (*Decisions made*) of
  **169**. So the diagnosis the 2026-08-20 entry recorded still holds on CLAUDE.md's actual
  test — the note is genuinely **forward**-weighted, the overage is not bloat, and one-lining
  settled entries will not fix it — but the **scale** has changed: what was a 1.3× overage is
  now 2.3×, driven almost entirely by *Current state*'s per-check-in dated bullets, which now
  run nine deep at ~25 lines each. **The relief is still a NAMED slice, and it is now the
  larger of the two halves.** (i) The 2026-08-20 plan stands: move *Current state*'s SPENT
  dated wave bullets — the seventh-fan-out dispatch, the post-wave adjudication (both calls
  DISCHARGED) and the eighth-fan-out dispatch (its `σ > 0` authorization spent on SIGZ) —
  **verbatim** to `notes/Pencil-adjudications.md`, leaving thin pointers. (ii) **New, and
  the bigger win: the per-check-in bullets for picks whose direction has LANDED are spent
  the moment the landing write-up exists** — GFLIP through BATTAIN are eight such bullets,
  and each one's durable content is a single sentence ("shape X elected, resolved to
  direction Y, dispatched at rung Z") plus its config delta. Collapse them to that, verbatim
  copies to `notes/Pencil-adjudications.md`. Deliberately **not** done piecemeal by a
  coordinator commit: *Hand-off* cites the eighth-fan-out bullet **by name** for the
  authorization's accepted terms, and slice 2's own experience was that repointing is where
  this doc set breaks (68 cross-references in one slice), so it wants a scoped dispatch that
  greps the tree. Until then the overage is **acknowledged, not silent**; full relief remains
  phase close.
- The full biconditional transport (design doc's W0 pin) is landed only as its two forward
  implications; the reverse arms need a `complementIso` involution lemma, not in tree —
  deferred, **off every critical path** (§(K-σ) *Step σ6*).
- **Harness debt — both rounds PAID** (S1–S4 CLOSED 2026-08-06; the five sideways-import
  move-downs of the sixth-to-eighth fan-outs PAID 2026-08-20 by slice 2), with **one item
  left open on purpose**: `zneq.ledger`, a seventh name the round found mis-listed across
  two copies of the same debt entry, deferred to a commit that can re-run `oschu --gtarget`
  / `--census1` / `--census2` (figure invariance is discharged by re-running, not by
  inspection). Canonical home `notes/scripts/README.md` *Harness debt* — read before any
  numerics dispatch: it also carries the two deliberately-unfixed *Recorded observations*
  and the rule for a dispatch that trips §2 rule 2 again (record the item naming every
  consumer; do **not** modify the landed file).

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

**THE EIGHTH FAN-OUT IS COMPLETE** — all five directions (ordinals 25–29) verified and
landed 2026-08-19, one serial coordinator commit each, plus the wave-closing exception-log
commit. Results are one-lined in *Decisions made*; every spec, bar, rider, tier assignment,
label reservation and per-direction write-up is in `notes/Pencil-fanout.md` §"Eighth
fan-out", and the wave's process exceptions in `notes/dispatch-log.md` (five rows, **F22–F24**)
— **none of it restated here.** Both gap-map recomputes were done and both caps then bumped
*after* — never instead of — the recompute, with reasons in
`notes/check-gapmap-cells.py` itself.

**THE CANDIDATE LIST lives in `notes/Pencil-strategy.md` §8 — the option board** (new
2026-08-20): every live route priced in one place, with the two filters that kill most
candidates on sight (growing-ground-set; counting saturation, now closed in **both**
directions by (OC-3)/(OC-37)). **Not restated here.** Cheapest entry: **(GR-R1)**
(§(K-grid)), which upgrades (b′)'s `≤ 12` to a theorem — renamed from bare `(R1)` at
the 2026-08-20 adjudication, `notes/Pencil-labels.md`. **Not eligible:**
route σ's **obligation 1** and the W4 **build** — those, and only those, are held by the hold.

**A SEPARATE, UNPRICED SHELF opened 2026-08-21 — `notes/Pencil-strategy.md` §9**, six
candidates **(ZH-1)–(ZH-6)** from a project-new *unrefereed* external source (Zheng's
body–pin preprint) whose Split–Klein form is **the same quadratic form** as
§(K-pitch)'s pitch quadric `Q`. **Deliberately not on §8's board and NOT a next task**
(source unchecked; (ZH-2)/(ZH-3) owe a §2.5 filter check; idea source, never a
citation). **Not restated here** — strategy §9 owns provenance, caveats and order.

**PROBE KBARE-FALSIFY IS LANDED (2026-08-20) — a T1 HIT.** (K-bare-ext) is **refuted as
stated**; `hbareSplit` is **untouched** and still carried as pinned. Verdict, mechanism, the
three enabling results and every figure are in `notes/Pencil-informal.md` §(K-bare-ext)
*Steps BE1–BE8*, the landing record in `notes/Pencil-fanout.md` §"Two probes SPECCED and
AUTHORIZED 2026-08-20", the label namespace closed as *used* in `notes/Pencil-labels.md`, the
six driver rows in `notes/scripts/README.md` §3 — **none of it restated here.** Its one new
**UNPAID** *Harness debt* item (the `kbare/` sibling imports, every consumer named) is the
second outstanding item in that section. **What the hit leaves for whoever picks up
`hbareSplit`:** the live statement is the **`∃`-seed form plus a seed-repair (deformation)
obligation** inside `HasPencilRealization K 3 G′`'s attainment locus — with **no chart**,
the habitat being infeasible by hypothesis — or, the probe's own suggestion, **bypass the
antecedent** and prove `HasPencilRealization K 3 G` directly on the habitat (strictly
stronger, but seed-free, and the hit says the antecedent supplies an object route A cannot
use). Neither is commissioned; option B stays un-commissioned.

**PROBE C3-AVOID IS LANDED (2026-08-24) — the gate is DECIDED, and board option C3 is
NO-GO as a crux-avoidance route.** The whole mathematics lives in
`notes/Pencil-strategy.md` §4.7 — labels (AV-1)–(AV-8), *Steps AV1–AV6*, driver
`notes/scripts/w4/avoidgen.py` (seven modes), the landing record in
`notes/Pencil-fanout.md` §"Probe C3-AVOID", the namespace closed in
`notes/Pencil-labels.md` — **none of it restated here.** Three things a successor needs:
the **threshold is exactly `|S| ≤ 2`** and no structural hypothesis on `S` lifts it (the
obstruction is a cardinality conservation law), the **parameter** is `μ(G) = |E| − |V| + 1`
with exact ceiling `capacity ≤ 2 μ`, and the **live successor** is (AV-7)'s unpriced arm —
even a passed gate is *necessary, not sufficient*, because `splitOff` rewires both
neighbours' incidences and every capacity unit above 2 is bought by a **Case-I gluing**
whose pencil-compatibility is geometry the probe was barred from. **§(K-avoid) was never
opened** and no gap-map status moved.

**THE NEXT CONCRETE TASK — the STRENGTHENED 2-CUT COMPOSITION LEMMA.** After
BINDUC, item 1 below is **one lemma from done**, and the lemma is named exactly:
across a 2-cut `{u,v}`, *attains ⟺ `dim(ρ̄₁+ρ̄₂) = min(δ₁+δ₂,6)`* — requiring
**(a)** the induction to carry a **strengthened** statement (welded-framework
attainment, because `ρ_i ≤ δ_i` always, so (BE-14) itself is not what recurses)
and **(b)** a general-position input the residual gauge group **provably cannot
supply** (dim 7 adjacent / 5 non-adjacent against `Gr(3,6)`'s 9). Free sub-cases
already proved: `δ₁ = δ₂ = 0`, and one-rigid-side, where the criterion collapses
to `ρ = δ` with no general position at all. **Everything else in the
decomposition is closed** — base `{3-connected}` (free, (BE-20)) ∪
`{max deg ≤ 2}` ∪ `{def₂ = def₃}`, plus 1-cuts ((BE-18)) — and the decomposition
is exhaustive, so this lemma **is** (BE-14). BINDUC's own successor ranking, in
order: (1) this lemma; (2) a direct point-side proof of the flat law, removing
(BE-20)(ii)'s inherited (BE-13) ingredient — small and self-contained; (3) a
proof of (BE-23)(ii) (*forced flat ⇒ `def₂ = def₃`*), which would close the
disproof side the way (BE-15)(ii) closed the triangle case.

**ZJACOB LANDED 2026-08-26** (§(K-jac) *Steps JC1–JC5*; write-up
`notes/Pencil-fanout.md` §"ZJACOB") — **not restated here.** Two consequences for
future picks. **(1) The Zheng shelf is nearly spent:** (ZH-1) and (ZH-4) struck,
(ZH-3) struck-by-absorption (it *is* (ZH-4)'s hypothesis), (ZH-5) a design note,
(ZH-6) write-up material — **only (ZH-2), stratified, remains dispatchable**, and
the shelf stays off §8's board. **(2) A durable negative worth not re-deriving:**
the determinantal / scheme-theoretic package is a **conservation law** — it
converts expected codimension *into* structure and has **no theorem producing
it** over a non-generic base. Any future route that proposes to get properness
from a codimension count, a Jacobian criterion, or Cohen–Macaulayness is
answered by §(K-jac) before it starts.

**THEN — the (K-res) SCOPING SLICE**, deferred one round by the max-impact
directive and NOT dropped. One direction: *does (GR-15)/§(K-grid) transport to
the `W19`-type (K-res) habitat?* This is the
user's 2026-08-26 adjudication (offered the full wave, the cheap scoping slice,
or a re-deferral, they chose the **scoping slice**), and it retires the stale
*"pin it when the tight side closes"* deferral — the coordinator hand-off note
that has sat unresolved in this section since the arc opened — **without**
commissioning a wave at an `hK`-class kernel. After it, pick the next off the
target-ordered list below.

**Both 2026-08-26 dispatches are LANDED; nothing is in flight.** ZSHEAR's
verdict and shelf effects are in *Decisions made* and
`notes/Pencil-fanout.md` §"ZSHEAR" — **not restated here.** One line matters for
future picks: **the §9 shelf is now one-for-one** (one direction spent, (ZH-1)
struck), its owed filter checks are **DISCHARGED**, and §9.3's head is **(ZH-4)**
— still off §8's board, still an idea source and never a citation.

**BZAVOID LANDED 2026-08-26** (§(K-bare-ext) *Steps BE14–BE18*; landing record
`notes/Pencil-fanout.md` §"BZAVOID") — **none of it restated here.** What it
changes for item 1 below, and only that: **(BE-14) is now known to be an
EXISTENTIAL, not a genericity claim** — the pencil stratum *is* the planar-atom
molecular stratum ((BE-16)), `rank ≤ target` is universal, so **one coplanar-star
point configuration per graph settles that graph**, and the residual is *"∀ `G`
2-connected, ∃ `p : V → P³` with every closed star coplanar and adjacent points
distinct, at which the molecular body-hinge matrix has rank
`6(|V|−1) − def₃(G)`"*. **Three things are now closed and must not be
re-attempted:** the forced-degeneration cap as a refutation route for **any**
graph ((BE-15), cap-free); the landed Phases-24–26 `G²` molecule apparatus,
whose general-position gate is the **literal negation** of the pencil condition
((BE-17)); and the **transversality/dimension count** ((BE-16)(iv)). **Still
unclaimed:** the declined `def₂ = def₃` slice — BZAVOID's free corollary proves
only the strictly smaller *forced-triangle* subclass. **Ranked successors, in
BZAVOID's own order:** (1) an **inductive construction on the point side**
(1-cuts done by (BE-18); 2-cuts asserted routine, unproved); (2) the
`def₂ = def₃` closed-form slice as a base case; (3) a **flat-star dictionary** —
re-prove `molecular_finrank_motions_eq_square_ker`'s surjectivity under a
hypothesis admitting coplanar stars, which would revive route 2.

**The list below is ordered by DISTANCE TO THE PHASE TARGET** (the 2026-08-26
directive, *Current state*'s eighth-check-in bullet), replacing the
previous-direction's-successor-order convention that produced five consecutive
directions on a ledger residual the ledger does not consume.

**The target is `PencilPair K 3 G`, and exactly three carried items stand
between the landed theorem and it. Rank accordingly.**

1. **`hbareSplit` via (BE-14), direct attainment** — *the pencil stratum
   attains `6(|V|−1) − def₃(G)`*, hard step isolated to **`Y° ⊄ Z(G)`**
   (§(K-bare-ext) *Step BE13*, BATTAIN). **The most target-moving statement
   the arc currently owns:** seed-free, induction-free, never uses
   `¬PencilNondegFeasible`, and it discharges `hbareSplit` **and**
   `PencilPair`'s unconditional conjunct at once, as a **standalone theorem**
   (the phase's own 2026-08-05 bar). Dearer in absolute terms, cheaper in
   structure. **Proof-of-concept slice, offered by BATTAIN:** (BE-14)
   restricted to `def₂ = def₃`, where the cone attains by (BE-13) in closed
   form — the arc's first *proved* `HasPencilRealization` result; it does not
   discharge `hbareSplit` (DZ has `def₂ = 11`).
2. **`hcontract` via W4's informal costs — dispatchable TODAY, and the hold is
   an argument FOR them, not against.** The hold parks Lean; it does **not**
   park route 3's other four costs (*Blockers*, "What the Lean hold parks, and
   what it does NOT"). **(T)** `G` triangle-free — *"a genuine research gap,
   not a numerics gap"* and **landed-invisible**, since the search's own
   feasibility certificate requires triangle-freeness, so no certified sweep
   can ever surface a triangle-carrying residual; **(V)** the local choice;
   **(E-loc)** the combinatorial gap (255/255, unproven). **All three are
   slice-sized and need no adjudication.**
3. **`hcontract` via (K-res) — the structural blocker, and a USER CALL.** Route
   3 **cannot close without it**; it has **never been attacked**, appearing in
   the dispatch docs only as a **bar** across eight consecutive specs behind a
   *"pin it when the tight side closes"* deferral this note itself now calls
   stale. Wave-sized. **Do not commission it without the user.**
4. **`hK` via (GR-15)** — the phase's hardest item, untouched by all
   forty-seven directions, and the only one of the three with no named
   next slice. Everything in §(K-grid)/§(K-out) below is *support* for this,
   not progress on it.

**Below the carried items — support work, explicitly ranked lower now.**
OGEOM's successors (the unsearched `n(F°) ≥ 6` frontier; the Kirchhoff-
injectivity sentence) are **disproof-risk reduction**, which by (OC-24) *"can
never be the binding obstruction"*; the grid-side residual (*is the ledger gap
ever `≥ 3`?*) is ledger bookkeeping; OQRANK's residuals and the `2k ∈ {4,6}`
corner likewise. **Do not re-open** per-matching (b′) or the `min_M` reading —
refuted and proven respectively.

**OGEOM is LANDED****OGEOM is LANDED** (§(K-out) *Steps
O42–O46*): no disproof witness, the geometric route free **by an argument**
on everything searched, and §8.5's row **narrowed, not closed**. Its own
successors, in order: **(1)** the unsearched cells — `n(F°) = 4` and `5` at
`|E°| ≥ 9` (a **compute** job, `--huntn` already takes a cell range and slice
index) and **every `n(F°) ≥ 6`** (an **ideas** job, since the budget bounds
`|E(F°)|` but not `n(F°)`); **(2)** the shape-free residual — *is the
Kirchhoff map `⊕_Q S_Q^⊥ → (K⁶)^nodes` injective at the generic chart point
of every live core?* — the first single-sentence form the geometric half has
ever had. Off §(K-out), the standing candidate is **(K-bare)** at the
seed-free shape: **46 directions on `hK`, still zero on (K-bare)**, the
arc's starkest imbalance and untouched by every direction to date. GMINM
is LANDED (§(K-grid) *Steps G145–G148*) and its finding re-prices the grid
thread: the ledger consumes **(L)**, the difference of minima, so the
per-matching statement four directions attacked is not the consumed one
((GR-127)). **Do not re-open (P) or (m)** — the first is refuted, the second
proven. The remaining grid-side statement is new and unattacked: **is the
ledger gap ever `≥ 3`?** Off-grid, the standing candidates are §8.5's open
**geometric route to a disproof** and **(K-bare)** at the seed-free shape
(45 directions on `hK`, still zero on (K-bare)). **GHWIT is LANDED** (§(K-grid) *Steps G140–G144*;
landing record `notes/Pencil-fanout.md` §"GHWIT"), and it **refuted
(GR-104)(i) at `2k = 2`** — so the whole GPRICE → GBLAW → GXESC → GHWIT
price-form thread is **closed negatively**, its mechanism theorems standing
and its target dead. **Do not re-open the constant 2 per-matching.**

**GHWIT's own two successors, in order.** (1) **The ledger-side routing
call** — the ceiling **4** is proven ((GR-86)) and now *attained*
((GR-122)), so the question is whether (b′)'s downstream consumers can run
at 4; this is a **ledger** question, not a grid one, and is the
coordinator's to route. (2) **The untested `min_M` reading** — at
`refut20`'s shape 25 of 26 matchings have `O ⊄ M` and satisfy (GR-104)(i)
outright by (GR-107)(iii), and (GR-59) is the standing precedent that
`min_M` can be load-bearing where the per-matching form is refuted; the
sweep is cheap and well-posed. (3) The exact `n` of the first clause
failure (16, 18 or 20).

**The wider candidate list** — the 2026-08-25 re-ranked board
(`notes/Pencil-strategy.md` §8, the canonical home) with its rank-1 and
rank-2 slots landed (OQRANK / GPRICE) and its head now in flight:
**(K-bare) at the seed-free direct-attainment shape** (rank 3 — the
KBARE-FALSIFY successor priced on §8.4's board; NOT option B, which stays
un-commissioned; this is where the standing attention asymmetry says a
dispatch soon belongs), then OQRANK's residuals — **the
wall-avoiding-colouring existence** ((OC-44)(iii)) and **the second
confinement's mechanism** — then the `2k ∈ {4, 6}` `O ⊄ M` corner of
(GR-104)(i), the one-unit-defect redo of (GR-79)–(GR-82), GCOLL's collision
dominance, and (OC-19) input (c) class-uniformly — the *shape* of each pick
stays a user call under the standing 2026-08-07 delegation. Recorded debt:
GBLAW's five `gprice`-device arrivals joined `zneq.ledger`, the `kbare/`
set and OQRANK's two arrivals (`notes/scripts/README.md` *Harness debt*,
coordinator-paid between waves like their predecessors). **GCHEAP's
residual sibling imports and GPRICE's five consumer arrivals are now PAID**
(2026-08-25, paid together per the GPRICE item's own instruction — nine
devices joined the (GR-49)/(GR-50) z-form and pattern/cube-combinatorics
groups already in `gridbal_common`, `perfect_matchings`/`cubic_habitat`
catalogued in §1 in place; `notes/scripts/README.md` *Harness debt*).
Remaining recorded debt: `zneq.ledger` (deliberately deferred), the
`kbare/` sibling-import set, and OQRANK's two arrivals
(`out_classes`/`shape_key`/`tree_triple`) — all still coordinator-paid
between waves.

**SUPERSEDED 2026-08-26 — two items now await user adjudication** ((K-res)'s
commissioning and the (BE-14) slice shape; both stated in the top `**Status:**`
block, not restated here). The paragraph below records the 2026-08-19 state and
the SIGZ authorization, which still binds on its own terms.

**As of 2026-08-19, nothing was awaiting adjudication.** The one item that was —
ZNEQ's `σ > 0`-everywhere hunt at class shapes whose `H` carries a short theta
sub-multigraph — is **AUTHORIZED** and dispatched as **SIGZ**; the direction-A pivot rule
(`notes/Pencil-fanout-archive.md` §"Direction A") stays in force, so a hit is *"a
phase-redefining event for the user to adjudicate, not a result to build on"* — **the
adjudication now happens at the return, not before the dispatch** (the terms the user
accepted, quoted in *Current state*'s 2026-08-19 eighth-fan-out bullet). **Superseded
2026-08-26 as to the stop clause** (*Current state*, the seventh check-in's third bullet):
a **confirmed** hit is now **worked up in-phase toward formalization** rather than halted
for a user decision — what still goes to the user is the half-1/half-2/route
**classification**, the confirming pass behind the word "confirmed", and the phase-boundary
call. It does not move a gap-map status by itself.

**BOTH STRUCTURAL ROUNDS ARE COMPLETE — nothing structural is queued.** Round 1 (doc-split
slices 1–2 + discipline-distillation slice 3, `RESEARCH-ARC.md` the promoted manual) and
round 2 (slice 4 the phase-note split, **slice 5/"slice 2" the harness move-down round,
2026-08-20** — all five debt items paid, no recorded figure moved) are both closed;
`notes/Pencil-structure.md` and `notes/scripts/README.md` *Harness debt* carry the records,
`notes/dispatch-log.md` F18–F21 the process findings. **One consequence for the pick:**
OSCHU's `rank(Q|_D) = 3` residue is no longer blocked on the harness — exact `ℚ(i)`
(`exactcore.Gauss`) is now a base-layer primitive.

**THE STANDING RESEARCH-PICK DELEGATION — WIDENED, and re-elected for the
current session.** Since the 2026-08-26 seventh check-in's second call the
coordinator picks **both the shape and the direction**, with the per-pick
check-in lapsed; the ninth check-in re-elected that for this session. The one
exception in the run so far is **BZAVOID**, which the *user* picked between
coordinator-authored options (*Current state*, ninth check-in). Two selection
criteria bind on top of the delegation: **distance to the phase target** (the
eighth check-in, superseding cheapest-decisive-first) and **falsification /
architecture-testing as a positive criterion** (the seventh check-in's second
call).

**`hsplit` is CLOSED IN FULL** (W5-L7c-1…6, landed 2026-07-30) and **`hfresh`'s mechanical
discharge (residue (iv)) is CLOSED too**. The landed successor
`pencil_conjecture_of_hcontract_hK_hbareSplit_of_card` (`Molecule/Pencil/Escape.lean`) wraps
`pencil_conjecture_of_hcontract_hK_hbareSplit` and carries exactly three open items, below.

> **Route σ rests on FOUR obligations, and only the first is Lean.** Corrected 2026-08-20:
> the earlier wording here named obligation 1 alone ("route σ's remaining substance is its
> parked Lean half") and so read as though the hold parked the whole route. Canonical
> statement of all four: §(K-σ) *Step σ5*; priced in `notes/Pencil-strategy.md` §8.4.
> **Obligation 1 is genuinely the hold's** — §(K-σ)'s own verdict is *"Lean engineering
> against a landed pattern, **not new mathematics**"*, with two design decisions (which
> maximal minor per LI conjunct; which FIELD, `ℝ` the narrowest by (AC-7)). Smallest commit
> when opened: `exists_common_seed_pencilRow_and_polynomials` (`Engine.lean:476`, chart
> **total**); **`exists_pencilSeed_of_nondeg` (`Reseed.lean:65`) is NOT the bridge**
> (circular). **Obligations 2–4 are NOT Lean, NOT blocked, and NOT in flight**, and two are
> decision-relevant *before* any Lean is commissioned: **(2)** scope — the `dim R_a = 0`
> stratum untouched and the **(K-res)** habitat unsampled, so **route σ is not a route to
> (K-res)** even fully built; **(3)** (σ6)'s failure direction **unwitnessed**
> (`predAfalse = 0/47`); **(4)** the branch it closes has **never been observed nonempty**, so
> its value is **insurance, not repair**.
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

- **`hcontract`** (W4) — the **build** is fully decomposed, buildable, and PARKED by the Lean
  hold; **four of route 3's other costs are informal and NOT parked** — see *Blockers*'
  "What the Lean hold parks, and what it does NOT", the canonical scope statement. Route
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
  statement **(K-bare-ext)**, the arbitrary-seed insertion lemma; status row in the gap map,
  full record in the design doc §"(K-bare) extension-route recon", numerics
  `notes/scripts/kbare/{danger,optc}.py`.
  **Why it is *carried* rather than proven or disproven.** The recon answers this in full
  (design doc §"(K-bare) extension-route recon") and the answer is **not** "nobody tried": the
  NO-GO is **definitional** — `PencilNondegFeasible` *is* "a nondegenerate realization exists",
  so at `¬PencilNondegFeasible` the chart/reseed/engine apparatus has **nothing to consume** on
  either side of the split, leaving only the 2–3-dim `pt(v)` placement freedom — and the one
  identified calculus is unlanded, needs the owed **KT pp. 684–691 re-pin** first, and was built
  for chart-*generic* seeds. **That research is option B, declined 2026-07-30.** Versus `hK`:
  easier on uniformity, **harder on the seed side**, habitat reaching **corank 2** (DZ), so
  `¬Feasible` buys no corank control. Evidence is **strong but sample-scoped** (at DZ the
  original sweep saw 0/15 off-line failures with every on-line placement failing by exactly
  1 — but KBARE-FALSIFY later **constructed** an off-line failure there, rank 113,
  correcting option-C C3's "failure set is exactly the line": the sample record stands, the
  locus claim does not — gap-map row (K-bare)) — still a well-evidenced statement with an
  un-commissioned proof route, not a hedge on a doubtful one. **The live
  asymmetry:** both kernels' option Bs were declined, but `hK` absorbed thirty-nine directions
  of other attacks and (K-bare) **none** — *"open, nothing being developed"*, in the gap map's
  own words. That gap is dispatch attention, not adjudication; the 2026-08-25 board re-rank
  prices its cheapest shape at **rank 3** (strategy §8.4, the (K-bare) development row).

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

- **Direction BINDUC (ordinal 42, 2026-08-26, opus, docs+scripts only) — the
  induction's BASE IS FREE, BZAVOID's 2-cut `− 6` is REFUTED, and (BE-14) is ONE
  LEMMA away.** (BE-20): **3-connected ⇒ `def₂ = 0`** — 3-edge-connectivity gives
  `|∂S| ≥ 3`, so `2d(P) ≥ 3q` and `partitionDef₂ ≤ −3` for every `q ≥ 2` —
  hence `def₃ = 0` and the **flat witness** (all points distinct in one plane,
  the legal dual of BATTAIN's chart-illegal coincident cone) attains in closed
  form; exhaustive at **226 891** 3-connected labelled graphs with the bound
  measured **tight** at `−3`. So the declined `def₂ = def₃` slice **covers the
  entire base**, and the contrapositive **`def₂ > def₃` ⇒ a cut of size `≤ 2`**
  reframes the problem. (BE-21): the inherited `− 6` is **REFUTED** — it goes
  negative, impossible since `def₃ ≥ 0`, at 87 % of 10 804 gluings — replaced by
  `def₃(G) = max(g₁+g₂, f₁+f₂−6)`, both directions proved, both branches needed.
  (BE-22): the rank half reduces to **attains ⟺ `dim(ρ̄₁+ρ̄₂) = min(δ₁+δ₂,6)`**,
  needing a **strengthened** inductive statement plus general position the
  residual gauge group cannot supply; free sub-cases proved. (BE-23): the
  decomposition is **exhaustive** — base `{3-connected}` ∪ `{max deg ≤ 2}` ∪
  `{def₂ = def₃}`, plus 1-cuts, plus the one open 2-cut step — and a new
  **hub-plane construction** proves (BE-14) at **5 824** graphs, **2 441 with
  `def₂ > def₃`** where the flat witness misses, each a per-graph theorem.
  **Disproof side:** the new-cap mechanism **exists**, is **strictly more general**
  than BZAVOID's (needs three shared independent points, not a triangle;
  `K_{3,3}` is forced flat and triangle-free), and **fires empty** at 25 270
  forced-flat instances under an over-claiming closure — MEASURED, reported as a
  candidate. **That generality is also a SCOPE CORRECTION to (BE-15)(ii)** (see
  the *Hand-off* blockquote): its cap-free closure covers the triangle mechanism,
  not the general one. **It also corrected the coordinator's own spec:** the
  landed induction principle's `hcontract` is *not* byte-for-byte the phase's
  parked item — the phase's quantifies over `Loopless` with a weaker IH and is
  **strictly stronger** — though the trap conclusion stands, since the principle
  cannot reach `∀ G`. **(BE-14) OPEN; `hbareSplit` untouched; not a PENCIL
  event.** Detail: §(K-bare-ext) *Steps BE19–BE23*; landing record
  `notes/Pencil-fanout.md` §"BINDUC".

- **Direction ZJACOB (ordinal 43, 2026-08-26, opus, docs+scripts only, the Zheng
  line's SECOND direction) — (ZH-4) REFUTED by an EQUIVALENCE rather than an
  obstruction, and the refutation ABSORBS (ZH-3).** (JC-1): the polynomial
  presentation of the motion cone (`dominance.motion_system`, not the `rref`-built
  5-row model) has Jacobian **`[0 | A(y)]`** at the zero section — 108/108
  `y`-entries identically zero in `ℚ[pts]`, fibre block 240/240 against an
  independent build — so *"generically smooth along the zero section"* unfolds
  **with no computation in between** to *"the rank attains target generically"*;
  the inclusion `Sing 𝒞 ∩ Z ⊆ D_1` is unconditional, but the reverse — the half
  the route needs — is conditional. (JC-2), the load-bearing step: the corank
  stratification gives `dim 𝒞 = max_{k≥0}(dim B_k + 6 + k)`, so expected
  dimension ⟺ `B_0 ≠ ∅` **and** `codim_B B_k ≥ k` — and **`B_0 ≠ ∅` IS
  properness**, the phase target on the tight class. **The route's hypothesis
  contains its conclusion as its weakest clause.** (JC-3): every classical bound
  on heights of ideals of minors is an **upper** bound taking the generic rank as
  **input** (Eagon–Northcott, Bruns, Eisenbud–Huneke–Ulrich — all four citations
  coordinator-verified, no section pointers asserted), evaluating to the
  **graph-independent constant 7** at 8/8 shapes, so §4.6's filter fires too, with
  input-dependence exhibited twice. (JC-4): the criterion is **identically blind**
  to the pure-condition half (84/84 fibre-quadratic partials vanish on the zero
  section) — tautologous where it applies, vacuous where the arc needs help, **no
  third region**. (JC-5): the re-encoding reproduces §(K-tight) *Steps 2.1/2.4*
  verbatim, with `line(ab)` chart-illegal by `Motive.lean:110`'s conjunct 4.
  (JC-6): a **conservation law** — the determinantal package converts expected
  codimension *into* structure and has no theorem *producing* it over a
  non-generic base; the ambient-Tay repair dies to §(K-pure) (PC6). **Explicitly
  NOT a provenance failure:** granting the source's Theorem 4.2 in full changes
  nothing, since a carrier analogue would *be* the phase target. **Shelf effect:**
  (ZH-4) **STRUCK**, (ZH-3) struck-by-absorption with a mechanism, so §9 retains
  **only (ZH-2) stratified** — two-for-two, still off §8's board. **No gap-map row
  moves; not a PENCIL event.** Detail: §(K-jac) *Steps JC1–JC5*; landing record
  `notes/Pencil-fanout.md` §"ZJACOB".

- **Direction ZSHEAR (ordinal 41, 2026-08-26, opus, docs+scripts only, the
  session's SIDE LINE and the §9 shelf's first direction ever) — (ZH-1) REFUTED
  by GAUGE-TRIVIALITY, a HIT of the negative kind.** (SH-1)/(SH-2), symbolic
  identities in `ℚ[…]` with no sampling: `Φ_S = Λ²(T_{−s})`, so the Witt shear
  group **is** the translation subgroup of `PGL(4)` on line coordinates;
  `Q(w) = 2·dir(w)·mom(w)`, upgrading strategy §9.1's *"same form"* to an
  identity in our own Plücker convention; and `Φ_Sᵀ★Φ_S = ★`, so **`Q` is the
  shear group's own defining invariant**. The shear's pointwise-fixed 3-space is
  a **β-plane of the Klein quadric**, already in §7's in-use list — so the
  spec's *"is it already implicitly available?"* is answered **yes, trivially**.
  (SH-3)/(SH-4): on §(K-flank) *Step F5(d)*'s bed, re-derived and asserted
  before use, the criterion matrix is **equal entry-for-entry** in the pushed
  basis (150/150), rank equal (222/222), `dim R_a` moved at **0 of 45** — so the
  bad-`S` set is `so₃` or `∅`, never a proper nonempty affine subspace, and
  (ZH-1)'s mechanism is **vacuous**. (SH-5): the coordinator's offered per-body
  repair is decided negative in **both** readings — the product action is not
  form-preserving off the diagonal (defect exhibited), and the maximal
  carrier-preserving translation family (dim **49 of 63** at `P21`), though it
  *does* pass §4.6's filter, acts simply transitively on the fixed-normal slice
  and so **is** §(K-slide) *Step 1(e)*'s chart re-labelled, moving `dim R_a`
  (6/6). (SH-6): the general **dichotomy** — a group under which the criterion
  is equivariant cannot turn a failure into an escape, and a family that moves a
  failure propagates nothing. **Durable residue:** `Q(r̃) ≠ 0` is
  `PGL(4)`-invariant, so **no gauge-fixing or frame normalization can ever supply
  it** (consistent with `m2/lambda1.m2` (M4), whose landed status is
  computational feasibility — a scope statement on top, orphaning nothing).
  **Shelf effect:** (ZH-1) **STRUCK**, (ZH-3) re-labelled **circular as posed**,
  (ZH-2) surviving §2.5 **only stratified**, the owed filter note **DISCHARGED**,
  §9.3's order advanced to (ZH-4) — and the shelf **stays off §8's board**. **No
  gap-map row moves; `hbareSplit`/(BE-14) untouched; not a PENCIL event.**
  Detail: §(K-shear) *Steps SH1–SH5*; landing record
  `notes/Pencil-fanout.md` §"ZSHEAR".

- **Direction BZAVOID (ordinal 40, 2026-08-26, opus, docs+scripts only) — the
  commissioned falsification arm is EMPTY BY AN ARGUMENT at EVERY graph, the
  pencil stratum is IDENTIFIED as the planar-atom molecular stratum, and two
  routes CLOSE.** (BE-15): the forced-degeneration T2 criterion generalizes to
  one universal cap per forced class partition, and then dies in the general
  form — forcing confines each class to a local cone, which forces
  `Σ_i def₂(G[V_i]) = 0`, leaving cap deficiency exactly `partitionDef₃(π(G))`,
  a value `def₃`'s own maximand already takes; exact, **cap-free**, enumerated at
  375 719 + 27 474 graphs with zero exceptions. So BATTAIN's triangle-free
  `hnoRigid` premise is a **special case, not the load-bearing step**. (BE-16),
  off the Lean bodies: the rank is a function of the hinge lines alone, the
  pencil hinge is the **join `p_u ∨ p_v`**, so the framework **is**
  `molecularOfCentres` at atom positions `p` and the pencil condition is *every
  closed star of points coplanar* — the all-trigonal-planar molecule; (BE-14) is
  therefore **existential, not generic**. (BE-17): the landed Phases-24–26 `G²`
  apparatus is **dead** — `IsGeneralPositionPlacement` is the literal negation of
  the pencil condition, and its sufficient condition is measured FALSE in exact ℚ
  at three shapes (dictionary gaps 5/4/1) while the molecular rank attains
  114/90/72. (BE-16)(iv): the coordinator's offered transversality count is
  **structurally incapable** of settling `Y° ⊄ Z(G)`, though the same reading's
  "deform off the canonical point" half **survives, priced at `def₂ − def₃`** —
  a SPLIT, on the YLOC precedent. (BE-18): `def₃` is 1-cut additive and the rank
  is `GL₄`-invariant, so **(BE-14) reduces to 2-connected graphs**. Free
  corollary: (BE-14) holds in closed form wherever the triangle-edge subgraph is
  spanning and connected — a **subclass** of the declined `def₂ = def₃` slice, so
  **the declined partial is still unclaimed**. **(BE-14) OPEN, `hbareSplit`
  untouched, nothing refuted, not a PENCIL event.** Detail: §(K-bare-ext)
  *Steps BE14–BE18*; landing record `notes/Pencil-fanout.md` §"BZAVOID".

- **Direction GXESC (ordinal 35, 2026-08-26, fable, docs+scripts only) —
  (GR-108) and existential escape REFUTED BY WITNESS; the price form
  survives everywhere.** Four verified single-cycle `O ⊆ M` witnesses from
  `n = 16` (three independent exact models each; mut16 one transposition
  from GBLAW's strand witness) have pure pos+neg maximum families —
  `d_adm = d_par + 2`, no balanced optimum — killing both of GBLAW's live
  shapes at once; **(GR-104)(i) holds at all four (prices exactly +2)** and
  is proven ⟺ the gap-2 law ((GR-117)(i)), proven at every bal-or-
  half-resident pair ((GR-117)(ii)); the reversal-label ledger (GR-115)
  proven (M-closed ⟹ balance-valid, every `2k`); reshaped residual the
  **half-witness clause** ((GR-117)(iii), 0 counterexamples at 248 pairs).
  Canonical home §(K-grid) *Steps G135–G139*; driver `w4/gxesc.py`.
  **(GR-15) OPEN; E1/E2 not fired (successor named); E3 ARMED, not fired.**
- **Direction GBLAW (ordinal 34, 2026-08-25 → 08-26, fable, docs+scripts only)
  — (GR-108) attacked by its pinned exchange shape, an honest OPEN reshape.**
  The arc-transversal normal form ((GR-110): maximum families are
  independent-transversal families, `|R| = 2|K|`), the recombination theorem
  ((GR-111): glued-difference exchange, maximum-family connectivity, the
  `2k = 2` refutation shape sharpened to universal linkage) and the escape
  lemma ((GR-112): no fine move crosses the balance layer) reduce (GR-108) to
  **existential escape** — 0 failures at 1 099 swept pairs ((GR-113), stratum
  strengthened exhaustively: no forcing maximum at `n ≤ 6`); universal escape
  REFUTED at the `n = 16` strand witness, where separation also fails 0/48
  exhaustively. Canonical home §(K-grid) *Steps G130–G134*; driver
  `w4/gblaw.py`. **(GR-15) OPEN; E3 ARMED, not fired.**
- **Direction GPRICE (ordinal 33, 2026-08-25, fable, docs+scripts only) —
  (GR-104)(i) settled under a restricted quantifier, a graded outcome of the
  third kind.** The colour-swap identity ((GR-105)), the reversal-set normal
  form ((GR-106): `dist = n − |R|` exact at `O ⊆ M`, `f` in `2^n`, reaching
  `n = 18`) and the reachability theorem ((GR-107)) prove **(GR-104)(i) at
  `2k = 2`, every `n`, modulo the minted balance law (GR-108) alone** (outright
  when some odd branch is off `M`; every failure a gap-4 (GR-108) failure);
  (GR-108) measured 1 431/1 431 (`n ≤ 6` sub-cell EXHAUSTIVE, hunt EMPTY to
  `n = 18`, strong form failing from exactly `n = 12` — a proof must exchange
  between maximum reversal sets). Canonical home §(K-grid) *Steps G125–G129*;
  driver `w4/gprice.py`. **(GR-15) OPEN; E3 ARMED, not fired.**
- **Direction OQRANK (ordinal 32, 2026-08-25, fable, docs+scripts only) — input (a)
  DELIVERED at all 174 certified classes, a graded HIT of the first kind.** The
  ⋆-eigen-block route of *Step O29* completed as a mechanism: forced (1,2) split
  profile ((OC-40)), the per-block criterion + Veronese dictionary ((OC-41)), and a
  combinatorial **WALL** ((OC-42): a single-class `b`–`c` `X`-path forces
  `rank(Q|_D) = 2` at every draw) — the naive first-colouring route REFUTED as a
  class statement (27/174: 7 wall, 20 by a second uncharacterized confinement); the
  hunted form GREEN at 174/174 in exact ℚ(i), per-class/per-colouring-generic by
  openness ((OC-43)/(OC-44)); zero rulings — the (K-tight)-event branch never fired.
  New residuals: (OC-44)(iii) wall-avoiding-colouring existence; the second
  confinement. Canonical home §(K-out) *Steps O37–O41*; driver `w4/oqrank.py`.
  **Input (a) class-uniform OPEN; (GR-15) OPEN; E3 ARMED, not fired.**
- **Direction GCHEAP (ordinal 31, 2026-08-25, fable, docs+scripts only) — (GR-C2)
  settled per-configuration in both directions, a graded double outcome.** The
  every-step form is PROVEN for `n_hub < 6|δ|` (lone-dart capacity (GR-100) +
  selection corollary (GR-101)), so **(b′) at the constant 2 is a THEOREM on the
  whole `n_hub ≤ 6` stratum** (modulo (GR-C1) alone at `n = 8, 10`); the
  per-configuration form is REFUTED from `n_hub = 12` by an explicit witness
  ((GR-103)), boundary exact both ways; the as-posed existential survives at every
  audited pair (stalled flips price 0), residual reshaped to **(GR-104)(i)**, the
  price form. One landed inference corrected in place (*Step G108*(v)'s marker: the
  spec-inherited "(iii) proves (GR-C2)" conflated hypotheses). Canonical home
  §(K-grid) *Steps G120–G124*; driver `w4/gcheap.py`. **(GR-15) OPEN; E3 ARMED, not
  fired.**
- **Direction GFLIP (ordinal 30, 2026-08-25, fable, docs+scripts only) — (GR-R1) is
  PROVEN, a HIT of the first kind.** The flip-availability clause holds strengthened —
  `≥ |δ|` feasible majority flips at every unbalanced admissible configuration, no
  habitat/`2k`/connectivity hypothesis — via the demand form (GR-97), the cubic counting
  lemma (GR-98) and the selection theorem (GR-99), so **(GR-89)(ii)'s `n`-free `≤ 12`
  bound is a THEOREM** and (GR-90)'s constant-4 row is *modulo (GR-C1) alone*. One landed
  gloss corrected in place (*Step G109*: the flip can also create a B-monochromatic
  **triple** — the dominant mechanism). Canonical home §(K-grid) *Steps G116–G119*;
  driver `w4/gflip.py`. **(GR-C2) untouched (bar honoured); (GR-15) OPEN; E3 ARMED, not
  fired.**
- **Probe C3-AVOID (2026-08-24, opus, docs+scripts only) — C3's gate PRICED, and the
  price kills it as a crux-avoidance route.** The *"reduce avoiding `S`"* question is
  decided against the landed generation theorem: the **local** gate never fails
  ((AV-1)), but a **conservation law** — every reduction tree has `#leaves = μ(G)` and
  each leaf holds 2 vertices — caps avoidance at `2 μ(G)` ((AV-2)/(AV-4)), giving the
  **universal threshold `|S| ≤ 2`** ((AV-3)), failing from `|S| = 3` at the cycles
  `C_3 … C_6` ((AV-6)), with **no structural hypothesis on `S`** able to lift it
  ((AV-5)). The gate is also only **necessary, not sufficient** ((AV-7)) — the live
  successor. Canonical home `notes/Pencil-strategy.md` §4.7; driver
  `notes/scripts/w4/avoidgen.py`. **§(K-avoid) never opened; no gap-map status moved.**
- **Probe KBARE-FALSIFY (2026-08-20, opus, docs+scripts only) — a T1 HIT.**
  (K-bare-ext), route A's arbitrary-seed insertion lemma, is **refuted as stated** by
  a legal target-rank `G′` seed with cap-free uniform failure; `hbareSplit` **untouched**
  (its consequent is an `∃`; both gadgets attain). Enabling results: the §(K-tight)
  boundary-load calculus **transports** (192/192, `def = 0` scope measured); the
  dependent stratum is **complete** at `corank(G′) ≤ 3`; option-C C1/C3 corrected.
  `notes/Pencil-informal.md` §(K-bare-ext); driver `notes/scripts/kbare/breakhunt.py`.

Reverse-chronological, one line per landing; full derivations live in git,
`notes/Phase39-design.md`, and (for the (K) arc) the workbook section named in each entry, which
is the canonical home a successor reads.

- **Second structural round, slice 2 — the harness MOVE-DOWN ROUND — LANDED
  2026-08-20**: all five *Harness debt* items paid in one pass — `ocon.meet` →
  `lambda`, six `zneq` §(K-out) devices → `ocon`, `aglu.py`'s seven
  `n_hub`-stratum devices → `gridcol`, `gridwit.tree_triple` → `grid`, and the
  adjudicated `closure.Gauss` → `exactcore` — each re-exported from its old home,
  so no consumer changed. Gate was figure invariance, not imports: 18 driver
  modes re-run in the foreground, 12 byte-identical against pre-edit baselines,
  6 against §3's figures. Record: `notes/scripts/README.md` *Harness debt*.
- **Second structural round, slice 1 — the phase-note doc split — LANDED
  2026-08-19** (`f2862531`): the ordinals-1–19 adjudication bullets moved
  **verbatim** to `notes/Pencil-adjudications.md` (relocation verified
  byte-identical), one thin pointer left, and two pre-existing stale hand-off
  sentences fixed in passing — one of them an eighth-fan-out banner still
  claiming "four remaining returns" four landings after it stopped being true.
  Full record: `notes/Pencil-structure.md` §"Slice 4".
- **Doc-split + discipline-distillation rounds COMPLETE (2026-08-19, all three
  slices)** — §(K-grid) → `Pencil-informal-grid.md`; `Pencil-fanout.md`'s
  ordinals 1–19 → `Pencil-fanout-archive.md`; this phase's research-arc
  discipline promoted to the new root manual `RESEARCH-ARC.md`. Verbatim
  relocations, repointed, `check-gapmap-cells.py` clean; detail
  `notes/Pencil-structure.md`.
- **The EIGHTH FAN-OUT — COMPLETE, all five LANDED 2026-08-19** (ordinals 25–29; drivers
  `w4/{gtmpl,gflow,gcoll,oschu,sigz}.py`). **Per-direction verdicts, bars and adjudications
  are NOT restated here** — canonical home `notes/Pencil-fanout.md` §"Eighth fan-out" and its
  five per-direction sections. The five results: **GTMPL** settles attack (c)'s AA-glue case
  at an **exact `n_hub` boundary** (impossible `≤ 14` by an `n`-free proof, REALIZED at 16
  where the (GR-38) kill FAILS; (GR-76)(iii) superseded, not refuted); **GFLOW** gives (b′)
  its **first proven `n`-free constant** (`≤ 12`, modulo (GR-R1)), Clause A′'s sub-clause 1
  PROVEN and sub-clause 2 REFUTED as posed, the residual becoming a *selection* clause (GR-C2)
  — **(b′) at 2 stays OPEN**; **SIGZ**, the authorized disproof hunt, returns **NO HIT** with
  the pivot rule never triggering, and kills the **counting route to a disproof** as a
  theorem ((OC-37)), locating `P21`'s mechanism as one unit short *and* on the `plane_basis`
  degeneracy locus — which corrected (OC-28)(iv)'s quantitative reading at six sites;
  **OSCHU** leaves **(a₁) half-proven and half-reduced to one 3×3 determinant**, its (a₂) leg
  correcting an arc-wide figure (907 labelled shapes = 75 classes, covering 19 of 174; the
  other 155 certified directly, so the `s₀` half is free **without** (GR-10)); **GCOLL**
  **REFUTES (GR-64)(R2)** by 180 Petersen witnesses and **DELIVERS (GR-64)(R1)** at 81 482 shapes —
  the wave's **only** gap-map status move. **Four of the five corrected a defective spec
  clause** (five in all, three inherited verbatim from landed hand-offs) — `notes/dispatch-
  log.md` **F22**. E1/E2/E3 NO at every one; **E3 stays ARMED by GBAL, never fired**;
  **(GR-15) OPEN, class uniformity untouched.**

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
