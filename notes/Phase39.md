# Phase 39 — PENCIL: the hinge-pencil molecular conjecture (work log)

**Status:** in progress — phase stays OPEN (standing user adjudications of 2026-07-24 /
2026-07-30 / 2026-08-02, quoted verbatim in *Current state*). W0–W3 and the whole W5 arc
(L0–L7) are COMPLETE — `hsplit` CLOSED IN FULL and `hfresh`'s counting discharge landed
(2026-07-30). Only three items remain, all carried by the landed successor
`pencil_conjecture_of_hcontract_hK_hbareSplit_of_card` (`Molecule/Pencil/Escape.lean`):
`hcontract` (W4), kernel `hK`, and kernel `hbareSplit` — see *Hand-off*. **Forty-five
kernel-(K) directions are now COMPLETE** (2026-08-05 → 08-26, ordinals 1–35; roster and
per-direction theorem chain in *Decisions made*). **The SIXTH, SEVENTH and EIGHTH FAN-OUTS
ARE ALL COMPLETE** (all fifteen directions LANDED 2026-08-19). **The arc's HITs:**
route-ledger **entry 5 PROVEN in both halves** (GBAL, discharging input (X)); **chart
irreducibility PROVEN** (CIRR); the **AA-glue configuration NOT realizable at `n_hub = 8`**
(AGLU); **(GR-R1) PROVEN** (GFLIP, 2026-08-25 — so (b′)'s `n`-free `≤ 12` bound (GR-89)(ii)
is a THEOREM, the arc's first unconditional bound of (b′)'s shape); **(GR-C2) settled
per-configuration in both directions** (GCHEAP, 2026-08-25 — **(b′) at the constant 2
a THEOREM on the whole `n_hub ≤ 6` stratum**, the per-configuration form refuted from
`n_hub = 12`, residual reshaped to (GR-104)(i)); **input (a) delivered at all 174
certified classes** (OQRANK, 2026-08-25 — the ⋆-eigen-block mechanism completed with
a combinatorial WALL found, the naive form refuted as a class statement,
per-class-generic quantifier, zero (K-tight)-event rulings).
Everything else an honest MISS or an OPEN reshape; verdicts in *Decisions made* and
`notes/Pencil-fanout{,-archive}.md`, **not restated here**. **(GR-15) stays OPEN
throughout; class uniformity untouched; no g-flank at any of the forty-five directions.
E3 is ARMED (by GBAL) and has NOT fired.** Direction codes are **multi-letter and
topic-tagged from the fifth fan-out on** (`notes/Pencil-labels.md` (L5)); grandfathered
single letters are re-used across dates, **always date those**.
**The doc-split AND discipline-distillation rounds are BOTH COMPLETE**
(all three slices, `notes/Pencil-structure.md`; the new `RESEARCH-ARC.md`
promotes this phase's dispatch discipline).
**THE EIGHTH FAN-OUT IS COMPLETE — all five LANDED 2026-08-19** — five
concurrent opus directions, ordinals 25–29; specs, roster, tier split, label
reservations and the losers' ranking all in `notes/Pencil-fanout.md` §"Eighth
fan-out", not restated here (the arc's
thirty-third through thirty-seventh directions: GTMPL / GFLOW / GCOLL / OSCHU /
SIGZ). One gap-map status move in the wave (GCOLL's), the pivot rule never
triggering; **verdicts one-lined in *Decisions made*, per-direction detail in
`notes/Pencil-fanout.md` §"Eighth fan-out" — not restated here**, and the
wave-closing exception-log commit is DONE (`notes/dispatch-log.md`, five rows,
**F22–F24**). **Both queued structural items are LANDED** — the phase-note doc
split (2026-08-19) and the **harness move-down round (2026-08-20)**, which paid
all five *Harness debt* move-downs with **no recorded figure moved**.
**BOTH ARCHITECTURE-TESTING PROBES ARE NOW LANDED, and each returned a verdict.**
**KBARE-FALSIFY (2026-08-20) — a T1 HIT:** (K-bare-ext), route A's arbitrary-seed
insertion lemma, is **REFUTED as stated**, exactly and **cap-free**; **`hbareSplit`
itself is UNTOUCHED and still carried as pinned** (its consequent is an `∃` over
frameworks and every probed gadget attains), so this is a **route** finding, not a
kernel refutation and not a PENCIL event. Detail, the three enabling results and every
figure: `notes/Pencil-informal.md` §(K-bare-ext) *Steps BE1–BE8* — not restated here.
**C3-AVOID (2026-08-24) — the gate DECIDED at threshold `|S| ≤ 2`**, so board option
**C3 is NO-GO as a crux-avoidance route**: the local gate never fails, but a
conservation law caps avoidance at `2 μ(G)`, `μ = |E| − |V| + 1`, `|S| = 3` fails at the
cycles `C_3 … C_6`, and no structural hypothesis on `S` lifts it. Mathematics, proofs
and caps: `notes/Pencil-strategy.md` §4.7 ((AV-1)–(AV-8), driver `w4/avoidgen.py`) —
**§(K-avoid) never opened, no gap-map status moved**, `hK`/`hbareSplit`/(GR-15)/class
uniformity untouched.
**DIRECTION GFLIP (ordinal 30) IS LANDED — dispatched and landed 2026-08-25, a HIT of
the first kind.** The shape was adjudicated at the 2026-08-25 check-in (*Current state*,
the 2026-08-25 bullet): single direction, cheapest first → **(GR-R1)**. The direction
**PROVED it**, strengthened (`≥ |δ|` feasible majority flips, no habitat/`2k`/
connectivity hypothesis), via the demand form (GR-97) + counting lemma (GR-98) +
selection theorem (GR-99) — canonical home §(K-grid) *Steps G116–G119*
(`notes/Pencil-informal-grid.md`), landing record `notes/Pencil-fanout.md` §"GFLIP",
driver `w4/gflip.py`. (GR-C2) stays the whole constant-2 residual, with a sharpened
hypothesis reported. Both probe verdicts were surfaced to the user at the same
check-in — that flag is discharged.
**DIRECTION GCHEAP (ordinal 31) IS LANDED — dispatched and landed 2026-08-25, a graded
double outcome.** The shape was re-elected at the second 2026-08-25 check-in (single
direction, cheapest first → **(GR-C2)**). The direction **settled (GR-C2)
per-configuration in both directions**: the every-step form is **PROVEN for
`n_hub < 6|δ|`** via the lone-dart capacity (GR-100)/(GR-101) — so **(b′) at the
constant 2 is a THEOREM on the whole `n_hub ≤ 6` stratum** (modulo (GR-C1) alone at
`n = 8, 10`) — and the per-configuration form is **REFUTED from `n_hub = 12`** by an
explicit witness (GR-103), the boundary `6|δ|` exact both ways; the as-posed
existential survives at every audited pair (stalled flips price 0) and the residual
is reshaped to **(GR-104)(i), the price form**. Canonical home §(K-grid) *Steps
G120–G124* (`notes/Pencil-informal-grid.md`), landing record `notes/Pencil-fanout.md`
§"GCHEAP", driver `w4/gcheap.py`. GFLIP's harness-debt item is **PAID** (2026-08-25,
the `gridbal_common` move-down); GCHEAP's own residual sibling imports were a recorded
*Harness debt* item, now **PAID** together with GPRICE's (below). **DIRECTION OQRANK (ordinal 32) IS LANDED — dispatched and landed 2026-08-25, a graded
HIT of the first kind.** Picked at the third 2026-08-25 check-in (recon-first → the
eighth strategy-only pass's board re-rank `f72cbb35` → its rank-1 front-runner). The
⋆-eigen-block route of *Step O29* is **completed as a mechanism** ((OC-40)/(OC-41));
its naive single-colouring form is **REFUTED as a class statement** (27/174 — 7 by the
new combinatorial **WALL** (OC-42), 20 by a second uncharacterized confinement); the
hunted form is **GREEN at 174/174**: **input (a) holds at every certified class**, at
an exhibited exact ℚ(i) σ-fixed grid point and every sufficiently generic draw of the
exhibited colouring ((OC-43)/(OC-44)) — NOT class-uniform, which stays OPEN. Zero
rulings: **the (K-tight)-event branch never fired.** New named residuals:
wall-avoiding-colouring existence ((OC-44)(iii)) and the second confinement's
mechanism. Canonical home §(K-out) *Steps O37–O41* (`notes/Pencil-informal.md`),
landing record `notes/Pencil-fanout.md` §"OQRANK", driver `w4/oqrank.py`.
**DIRECTION GPRICE (ordinal 33) IS LANDED — dispatched and landed 2026-08-25
(the fourth check-in's front-runner pick), a graded outcome of the third
kind: (GR-104)(i) is a THEOREM at `2k = 2`, every `n`, modulo the minted
balance law (GR-108) alone** — the reversal-set normal form (GR-106) makes
`f` computable in `2^n`, the refutation hunt is EMPTY to `n = 18`, and
(GR-108)'s strong form fails from exactly `n = 12`, so a proof must exchange
between maximum reversal sets. Canonical home §(K-grid) *Steps G125–G129*
(`notes/Pencil-informal-grid.md`), landing record `notes/Pencil-fanout.md`
§"GPRICE", driver `w4/gprice.py`. **DIRECTION GBLAW (ordinal 34) IS LANDED —
dispatched 2026-08-25 (the fifth check-in's front-runner pick, (GR-108) the
balance law; the same check-in had the GCHEAP/GPRICE harness debt paid
first, `782e8bcd`), landed 2026-08-26: an honest OPEN reshape.** (GR-108)
is neither proven nor refuted; the exchange calculus its pinned proof shape
called for is **PROVEN** ((GR-110)–(GR-112): arc-transversal normal form,
recombination connectivity, the escape lemma), the law REDUCES to
**existential escape** (the new named open kernel, 0 failures at 1 099
swept pairs), and universal escape is **REFUTED at an explicit `n = 16`
witness** defeating both new mechanisms — so any proof must produce the
balance-reaching maximum globally. Canonical home §(K-grid) *Steps
G130–G134* (`notes/Pencil-informal-grid.md`), landing record
`notes/Pencil-fanout.md` §"GBLAW", driver `w4/gblaw.py`. **DIRECTION GXESC
(ordinal 35) IS LANDED — dispatched and landed 2026-08-26 (the sixth
check-in's front-runner pick), a REFUTATION BY WITNESS, the spec's strong
form: (GR-108), the balance law, is FALSE from `n = 16`** (four verified
witnesses, each re-derived through three independent exact models, the
first ONE transposition from GBLAW's strand witness) **and existential
escape falls with it — while (GR-104)(i) SURVIVES at every witness**: it
is ⟺ the **gap-2 law** (GR-117)(i), proven wherever some maximum is
balance-valid or half-resident (GR-117)(ii), and the reshaped residual is
the **half-witness clause** (GR-117)(iii) (counterexample-free at 248
hunted pairs), which would close (GR-104)(i) at `2k = 2` unconditionally.
New proven instrument: the reversal-label ledger (GR-115), M-closed ⟹
balance-valid at every `2k`. Canonical home §(K-grid) *Steps G135–G139*
(`notes/Pencil-informal-grid.md`), landing record `notes/Pencil-fanout.md`
§"GXESC", driver `w4/gxesc.py`. **DIRECTION GHWIT (ordinal 36) IS LANDED —
dispatched and landed 2026-08-26 at `recon-opus` (the first single
direction to run below the top rung, fable conserved), a REFUTATION BY
WITNESS that reaches one clause past its own target: the half-witness
clause (GR-117)(iii), the gap-2 law (GR-117)(i) AND (GR-104)(i) at
`2k = 2` ITSELF are all FALSE** at an explicit habitat-gated
`n_hub = 20` pair whose entire 64-member maximum family is all-(2,2)
with gap 4 ((GR-122), four independent exact models) — so
**per-matching (b′) at the constant 2 is FALSE** and (GR-86)'s gap-4
cap is TIGHT. A second, independent finding **corrects a landed
figure**: (GR-108) is false from **`n = 12`**, exactly, not `n = 16`
((GR-123), superseding (GR-116)(iv) in place). New proven instruments:
the (2,2) budget (GR-120) — which makes the price form a THEOREM at
every `n ≤ 10` and wherever `d_par(M) ≤ 2` — and the slide gate
(GR-121), refuted as a route. **`hK`, (GR-15) and class uniformity are
untouched; E3 stays ARMED and does not fire.** Canonical home
§(K-grid) *Steps G140–G144* (`notes/Pencil-informal-grid.md`), landing
record `notes/Pencil-fanout.md` §"GHWIT", driver `w4/ghwit.py`.
**DIRECTION GMINM (ordinal 37) IS LANDED — 2026-08-26, `recon-opus`,
the first pick under the widened delegation, and it re-prices the
arc's last four directions.** (b′) has **three pairwise-inequivalent
readings** ((GR-127)): **(P)** `∀M`, **(m)** `min_M (d_adm − d_par)`,
**(L)** `min_M d_adm − min_M d_par`. **The ledger consumes (L)** — a
difference of minima, which is what `gdev.min_dev` computes. **(P) is
what GPRICE/GBLAW/GXESC/GHWIT attacked and GHWIT refuted; (m) is now
PROVEN** at every habitat ((GR-126)), so the stronger kill GMINM was
told to hunt **cannot exist**; **(L) is untouched by either**, and the
landed W3 figures already separate it — ledger gap **1**, which
(GR-67)'s parity law forbids any per-matching gap from being — while
at (GR-122)'s own witness shape the ledger gap is **0**. So
**GHWIT refuted a statement the ledger never used**; the four
directions' mechanism theorems stand, their target's relevance does
not. Canonical home §(K-grid) *Steps G145–G148*, landing record
`notes/Pencil-fanout.md` §"GMINM", driver `w4/gminm.py`. **No status
word moves on (GR-104)(i) or per-matching (b′) — both stay REFUTED;
`hK`, (GR-15) and class uniformity untouched; E3 ARMED, not fired.**
**NEXT CONCRETE TASK: the next research direction, coordinator-picked
— and it goes OFF §(K-grid)** (the GMINM prep recorded that in
writing). The new live grid-side statement, for whoever returns: **is
the ledger gap ever `≥ 3`?** (spectrum `{0,1,2}` at 4 935 shapes; by
(GR-127) no proof may fix its anchor matching). The §9 shelf **(ZH-1)–(ZH-6)** stays unpriced and
ineligible. Nothing else structural queued, nothing awaiting user
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

**Kernel-(K) research arc — sixty-two docs+scripts-only dispatches landed, plus eight
strategy-only passes** (2026-08-02 → 08-26) — and, **outside** that count because they test
the architecture rather than the (K) crux, the **two probes**: **KBARE-FALSIFY**
(2026-08-20) and **C3-AVOID** (2026-08-24), both landed. Which pass was which is one-lined in *Decisions
made*; the rule is that the **dispatch** count moves only on a landing (GBAL/GLAW/FRES/OCON/
LTWO are the fortieth through forty-fourth; CIRR the forty-fifth; YLOC the forty-sixth; BALB
the forty-seventh; ZNEQ the forty-eighth; AGLU the forty-ninth; the eighth fan-out's five
the **fiftieth through fifty-fourth**, all landed 2026-08-19; **GFLIP the fifty-fifth**,
**GCHEAP the fifty-sixth**, **OQRANK the fifty-seventh**, **GPRICE the fifty-eighth**,
all 2026-08-25, and **GBLAW the fifty-ninth**, **GXESC the sixtieth**, **GHWIT the sixty-first** and **GMINM the sixty-second**, all 2026-08-26), and a **user call on
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

- **Doc debt, dated 2026-08-20 — this note is 6xx lines against the ~500 tripwire, and the
  relief is a NAMED slice, not a vague "compress later".** The note is genuinely
  *forward*-weighted (CLAUDE.md's actual test): *Hand-off* 186 lines + *Current state* 163
  are live forward state, while the finished part (*Decisions made*) is only 88 — so the
  overage is not bloat and one-lining settled entries will not fix it. The concrete relief
  is a **third doc-split slice** on the precedent of slice 1 (2026-08-19): move *Current
  state*'s three now-SPENT dated wave bullets — the seventh-fan-out dispatch, the post-wave
  adjudication (both calls DISCHARGED) and the eighth-fan-out dispatch (its `σ > 0`
  authorization spent on SIGZ) — **verbatim** to `notes/Pencil-adjudications.md`, leaving
  thin pointers. Deliberately **not** done piecemeal by a coordinator commit: *Hand-off*
  cites the eighth-fan-out bullet by name for the authorization's accepted terms, and slice
  2's own experience was that repointing is where this doc set breaks (68 cross-references in
  one slice), so it wants a scoped dispatch that greps the tree. Until then the overage is
  **acknowledged, not silent**; full relief remains phase close.
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

**THE NEXT CONCRETE TASK — the next research direction, coordinator-picked
under the 2026-08-26 widened delegation, and it goes OFF §(K-grid).** GMINM
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

**Nothing is awaiting user adjudication as of 2026-08-19.** The one item that was —
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

**THE STANDING RESEARCH-PICK DELEGATION — exercised, and NOT live until
GHWIT lands.** The seventh check-in (2026-08-26) elected single direction
front-runner-first → the half-witness clause, dispatched as **GHWIT** at
`recon-opus` (see the top `**Status:**` block and *Current state*'s
2026-08-26 seventh-check-in bullet). The delegation covers the pick
*after* GHWIT; its shape is again a user call.

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
