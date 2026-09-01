# Phase 39 — PENCIL: the hinge-pencil molecular conjecture (work log)

**Status:** in progress — the phase stays OPEN (2026-07-24 adjudication). The target is
**`PencilPair K 3 G`**, and the landed successor
`pencil_conjecture_of_hcontract_hK_hbareSplit_of_card` (`Molecule/Pencil/Escape.lean`)
derives it from exactly **three carried items**: **`hcontract`** (W4 — build parked by the
**2026-08-05 Lean hold**, four informal costs NOT parked), **`hK`** (kernel (K)),
**`hbareSplit`** (kernel (K-bare)). Everything else is closed: W0–W3 and the whole W5 arc
(L0–L7), with **`hsplit` CLOSED IN FULL** and `hfresh`'s counting discharge landed
(2026-07-30).

**The kernel-(K) research arc: 61 directions COMPLETE** (2026-08-05 → 09-01, ordinals
1–53), plus eight strategy-only passes and two architecture probes; **none in flight**.
**Per-direction verdicts, specs and landing write-ups are NOT restated here** —
each direction has one at `notes/Pencil-fanout.md` §"<CODE>" (ordinals 1–19:
`notes/Pencil-fanout-archive.md`) and a canonical mathematical home in the workbooks.
**The arc's standing result, unchanged by all 61: `hK` is not closer.** **(GR-15)** — the
single open gap the whole §(K-grid) chain reduces to — is **untouched**; **class uniformity
of the escape is untouched**; no g-flank was found by any direction; **E3 is ARMED (by
GBAL) and has never fired**.

**WHERE THE (BE-14) THREAD STANDS** — the 2-cut composition lemma (S-mark) is (BE-14)'s
only open step, and it has two sides (details in §(K-bare-ext), the `(K-bare)` gap-map row
and the fan-out write-ups, **not restated here**). **THE EAR SIDE:** (α) **CLOSED**; (β)
**PROVED AT THE WINDOW BY A CLASS THEOREM** (BWIN, with BSHARP's (b1)/(b2) and BRULE's
(b3)) on the reduction's 87-of-91 domain — **MODULO the two side conditions (S1)/(S2)**
((BE-57)(iv)), hypotheses on the middle, vacuous at every drawn piece, **not theorems**;
residue per-shape outside the window plus the `π_u = π_v` corner. **THE GENERAL-PIECE
SIDE:** the internal R-node is **DESCRIBED** (BRNODE, (BE-59)/(BE-60)) and its
achievable decorations are now **REDUCED TO EARS** — at fixed hub flags the legal
configurations of ANY piece are a **product** of ear chains, one per topological branch,
**modulo the cross-branch proviso `G`** (disclosed, never shown nonempty in general)
((BE-64)), so no per-child set past ears is ever needed and the theta child is a
corollary ((BE-66)); half (B) holds at 28/28 measured peels as **per-piece theorems**,
and its **class** quantifier plus the **flag base** off the no-adjacent-hubs class are
the residue ((BE-67)/(BE-68)). Cross-pair welding ((BE-28)(i)) is the third residue,
untouched. **The phase-boundary consequence is reported, NOT acted on** (next block).

**On a future HIT: the phase-boundary consequences are the USER's call** —
whether Phase 39 closes and a successor opens for the Lean is a
`PHASE-BOUNDARIES.md` event against the standing 2026-07-24 no-split
adjudication, surfaced with a commit-count estimate, never taken unilaterally;
the 2026-08-05 Lean hold binds regardless of how good the news is.

**SEVEN reference blocks — RELOCATED 2026-08-27 → 09-01**, verbatim, to
`notes/Pencil-structure.md`, which indexes them; **read them once per session**. The one
line that must stay here: the **State of (K)** gap map in `notes/Pencil-informal.md` is the
phase's status object, **authoritative for every status word** — read it with
`python3 notes/gapmap.py`, never `sed`/`grep`.

## Current state

**The phase stays OPEN.** Standing user adjudications, verbatim (these are the live GO/NO-GO
constraints; the **dated dispatch/selection narrative for every ordinal, 1–44, is
`notes/Pencil-adjudications.md`**, quoting the user byte-for-byte, and git):

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
- **2026-08-05 → 08-26, the selection history for ordinals 1–44, ARCHIVED IN FULL.**
  Every dated adjudication/delegation bullet that picked a direction is in
  `notes/Pencil-adjudications.md` **verbatim** (1–19 moved 2026-08-19, 20–44 moved
  2026-08-26). **None changes a standing constraint** beyond what the next three
  bullets summarize. Read there for the exact quotes — including the 2026-08-19 SIGZ
  authorization terms and the 2026-08-20 `(GR-R1)`/`(GR-C1)`/`(GR-C2)` rename call
  (collision record: `notes/Pencil-labels.md`).

- **THE STANDING RESEARCH-PICK DELEGATION — WIDENED, and re-elected for the current
  session** (2026-08-07, widened at the 2026-08-26 seventh check-in's second call,
  re-elected at the ninth). The coordinator picks **both the shape and the
  direction**; the per-pick check-in has lapsed. The one exception so far is
  **BZAVOID**, which the *user* picked between coordinator-authored options. **Three
  criteria bind on top of it:** **max impact on proving or disproving
  `PencilPair K 3 G`** (the tenth check-in, sharpening the eighth's *distance to the
  phase target*, which superseded cheapest-decisive-first); **falsification /
  architecture-testing as a positive criterion** (seventh check-in, promoting
  strategy §8.5 from a board row to a standing preference); and
  **diversification** — the arc's §(K-grid) concentration is what is being
  corrected. The **Zheng line (strategy §9) is a standing second lane** by the
  tenth check-in, not a one-off side quest.

- **THE DIRECTION-A PIVOT RULE — its stop clause is PRE-ADJUDICATED** (2026-08-26,
  seventh check-in's third call). On a **confirmed** half-2 disproof the loop does
  **not** halt for a user decision — the coordinator works the disproof up to a
  formalization-ready informal statement **inside this phase**, under the standing
  Lean hold (workbook + drivers + a corrected statement, **no `.lean`**), and the
  Lean lands in a successor phase. **What still comes to the user:** (i) the
  **classification** — half 1 (the `hK` *pin* fails: a re-pin, explicitly *"not a
  disproof of the conjecture"*) vs half 2 (the conjecture fails) vs a T1-style
  *route* refutation; (ii) **"confirmed"** — a first return is not confirmed, the bar
  is the (GR-83)/(GR-113) one, and `RESEARCH-ARC.md` item 4 binds (the corrective
  mechanism is the **next pass**), so a confirming pass is priced into the work-up;
  (iii) the **phase boundary** (top `**Status:**` block). This supersedes the
  2026-08-19 SIGZ authorization's adjudicate-at-the-return terms *as to the stop
  clause only*.

- **2026-08-29, THE TARGET AFTER BWIN, and the session boundary** (twelfth check-in).
  Offered the internal R-node (the coordinator's pick), the spread step, discharging
  (S1)/(S2), or the (K-res) wave, the user chose **the internal R-node**; asked whether to
  keep running, the user chose **"recompute only, then hold"**. So the R-node is the next
  concrete task (*Hand-off*), the other three stay **ranked, not dropped**, and the (K-res)
  wave remains the standing user call it already was.

- **Session-headroom calibration — MEASURED 2026-08-26, not argued** (eleventh
  check-in). `weekly_scoped` tracks **fable only** (92 % for a whole session, unmoved
  across four opus recons), so `.claude/commands/coordinate-phase.md`'s *"above ~80 %
  on **either** limit, stagger"* reads as *"above ~80 % on the limit the dispatched
  rung actually consumes"*; `weekly_all` moves **1–2 points per pair-round**. Nothing
  else in the playbook moves.

**Kernel-(K) research arc — seventy-eight docs+scripts-only dispatches landed across 61
directions (ordinals 1–53), plus eight strategy-only passes** (2026-08-02 → 09-01) — and,
**outside** that count because they test the architecture rather than the (K) crux, the
**two probes**, **KBARE-FALSIFY** (2026-08-20) and **C3-AVOID** (2026-08-24), both landed.
The roll call, ordinals, dates and rungs are `notes/Pencil-fanout.md`'s header and its
per-direction sections — **not restated here**; the **dispatch** count moves only on a
landing, and a user call on dispatch *shape* contributes **no** strategy pass; the canonical
homes are `notes/Pencil-structure.md` §"Conventions and canonical homes"'s, not restated
here either. Net effect: **disproof risk removed**, every refuted route/gap has a successor
in the gap map, several structural positives proven, **route-ledger entry 5 PROVEN** (the
arc's first HIT) — and **class uniformity of the escape remains untouched**. **Doc-debt
round CLOSED** (`notes/Pencil-cleanup.md`, 2026-08-13, category D only).

**The other candidate continuations, unselected — RELOCATED 2026-08-29** (verbatim) to
`notes/Pencil-structure.md` §"The unselected candidate continuations": items (a)/(g) **DONE**,
(b)–(f) each with a canonical home carrying the detail. Stable reference, not status by its
own last sentence — **the current ranking of what a wave did not pick is
`notes/Pencil-fanout.md`'s own losers sections, not that list.**

**Read `notes/Pencil-strategy.md` before choosing anything else** — the strategic record (why
class uniformity resists, the candidate stronger invariants with **C1 run and struck**, §5's
symbolic assessment); its own header is its contents table and **its §4.6** is the entry point
for any attack on the crux. **Any (K)- or W4-side numerics dispatch starts from
`notes/scripts/README.md`**; detail in *Blockers*.

**The question, and opening recon verdicts R1–R3 — RELOCATED 2026-08-28** (verbatim) to
`notes/Pencil-structure.md` §"The question and the opening recon": the `ROADMAP.md` §39
pointer plus the two clauses that section does not carry, and R1/R2/R3's three clauses that
still constrain statements. Stable reference, not status — unmoved since 2026-07-23.

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
  owed here** — route 3, packaging (b) was adjudicated 2026-08-02.

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
  eight consecutive direction specs; its *"pin it when the tight side closes"* deferral is
  **RETIRED** by the 2026-08-26 adjudication, which selected the cheap scoping slice now
  queued in *Hand-off*. **(T)/(V)/(E-loc) are slice-sized and need no adjudication; the
  (K-res) WAVE is still a user call.**

- **Doc debt — relief slice LANDED 2026-08-26** (1 500 → 554), and **relocation, not
  compression, every time since** — now **SEVEN** blocks, all stable **reference, not status**,
  sitting verbatim in `notes/Pencil-structure.md` with their own reasons recorded there
  (§"Slice 6" onward): *Conventions* / *Canonical homes* (08-27), *Gates for any
  continuation* (08-28), *The question and the opening recon* + *Durable negatives and
  deliberate non-goals* (08-28), and *What the recent landings closed* + *The unselected
  candidate continuations* (08-29), and *Citations — the phase's verified bibliography*
  (09-01, the BDECOR prep; **a direction that verifies a new source adds it THERE** — BDECOR
  verified none, citing only arc-internal results). Caps **not** bumped, nothing deleted. **The gate is
  MECHANICAL** — `notes/check-phase-note.py` caps this note at **580 lines / 525
  status-header words** and fails if *Decisions made* outgrows the forward sections. **Live
  watch, re-measured 2026-09-01 at the BDECOR landing: 540/580 lines, 474/525 words** —
  the BDECOR prep's *Citations* relocation (the SEVENTH block) bought the room back, so
  the gate is not near binding; ask "what here is reference rather than status?" when it is. **When
  the next landing binds, the question is again "what here is reference rather than
  status?"** — not another fold; the measured diagnosis (three folds recovered 2–5 lines
  each, because the note is forward-weighted and the forward part is what grew) is recorded
  at `notes/Pencil-structure.md`, not restated here. A landing's entry stays **one line**;
  the (BE-14) thread's prose entries are the standing exception, and the oldest demotes when
  the thread's next direction lands.
- The full biconditional transport (design doc's W0 pin) is landed only as its two forward
  implications; the reverse arms need a `complementIso` involution lemma, not in tree —
  deferred, **off every critical path** (§(K-σ) *Step σ6*).
- **Harness debt — four rounds PAID, FOUR ITEMS OUTSTANDING.** Canonical home
  `notes/scripts/README.md` *Harness debt* — **read it before any numerics dispatch**: its
  own header enumerates all four outstanding items, the two deliberately-unfixed *Recorded
  observations*, and the rule for a dispatch that trips §2 rule 2 again. **Not restated
  here** (thinned 2026-08-29; the home was checked first and carries every one).

## Hand-off / next phase

**The phase stays OPEN** (the 2026-07-24 adjudication — no phase-close; see *Current state*).

**BWIN (ordinal 51) LANDED 2026-08-29** and **CLOSED THE WINDOW as a class**
((BE-54)–(BE-58); the machine and its caveats are the `(K-bare)` gap-map row's and the
write-up `notes/Pencil-fanout.md` §"BWIN"'s, not restated here). With BRULE ((b3),
disjoint) and BSHARP ((b1)/(b2) outside the window), **(β) is proved at every window piece
on the 87-of-91 domain, MODULO (S1)/(S2)**; the remaining (β) residue is per-shape outside
the window ((BE-58)(iv)'s ledger) plus the `π_u = π_v` corner ((BE-32)(+), forced). The
strengthened 2-cut lemma **is** (BE-14) (decomposition exhaustive; base `{3-connected}` ∪
`{max deg ≤ 2}` ∪ `{def₂ = def₃}` free, 1-cuts (BE-18), statement **PINNED** as **S-mark**,
simultaneity **VACUOUS** (BE-25)(i)). BIMAGE bounded and classified the ear's residual
geometric sentence; BEARCASE **PROVED (α)** for `m ≥ 3`; BEARFULL, BSHARP and BRULE cut
(β) down to the window BWIN closed.

**BRNODE (52) and BDECOR (53) BOTH LANDED 2026-09-01** — write-ups
`notes/Pencil-fanout.md` §"BRNODE"/§"BDECOR", mathematics §(K-bare-ext) *Steps BE58–BE67*,
drivers `notes/scripts/w4/{brnode,bdecor}.py`. BRNODE closed (BE-31)(ii)'s residue **as a
computation** (the decorated-skeleton law) and located the R-node's content in the
**achievable-decorations class statement**; BDECOR then **reduced that statement to ears**
((BE-64)) and settled its per-child half. The details are the write-ups' and the
`(K-bare)` gap-map row's, **not restated here**.

**THE NEXT CONCRETE TASK — the next research pick, under the standing delegation.** The
coordinator picks the direction; **F26 binds: re-run the consumer trace rather than
inheriting BDECOR's own successor order.** BDECOR's ranking, offered not decided, is
candidate 0 below; the rest stay **ranked, not dropped**:

0. **HALF (B)'s CLASS QUANTIFIER** ((BE-67)(iii)) — *does every internal R-node piece have
   a configuration at which both peel sides attain and `ρ̄₁, ρ̄₂` are in general position?*
   Now **one statement per piece about one irreducible variety** ((BE-65)(ii), citing
   (CH-1)), with both failure modes named and both currently unwitnessed: the welded half
   is **free at theta children**, and the general-position half's only located enemy is a
   flag coincidence **no landed mechanism can force at a virtual edge's terminals**
   ((BE-66)(iv)). Two smaller siblings from the same landing: **the flag base off the
   no-adjacent-hubs class** ((BE-65)(i), a pencil-realization problem for the hub
   subgraph) and **the forced-empty hunt for the cross-branch proviso `G`**, which would
   be BDECOR's own first refutation.

1. **The ONE-END-SERIES case by BWIN's machine** — one peel instead of two
   (`ρ̄₁ = ⟨ℓ_u⟩ + ρ̄(rest)`), budget `δ₁ ≤ 3` by the same excess accounting, or a
   second functional from the clean end. Would retire the (BE-46)/(BE-52)
   per-shape witnesses behind the *sharpened-at-one-end* route — (β)'s largest
   remaining per-shape component ((BE-58)(iv)).
2. **The SPREAD STEP** — *every aggressively-forced pair lies in one `≤6`-cycle
   class*, the last **3.8 %** of (BE-32)(+) (55 known instances). Pure graph
   theory; the merge inequality is **known** not to reach it (a 7-cycle of `Q`
   has slack `−1`). BRULE's job 2: (BE-32)(+) sits **under** three clauses of
   (β) at the `π_u = π_v` corner — the **forced** branch only.
3. **(S1)/(S2), the two side conditions of (BE-57)** — hypotheses on the middle,
   **vacuous at every drawn piece but NOT theorems** ((BE-57)(iv)); the window's
   class theorem carries them until one is discharged. **Open and ranked, not
   dropped.**
4. BTWOCUT's successor (2), the **bundle-construction proof** — (BE-29)(ii) from
   rung to theorem, reaching `DZ` / `spider(5,5,5)+c`. Skipped four times.

Also ranked, unchanged: BTWOCUT's cross-pair closure ((BE-28)(i), motive economy only — S-mark
closes), the point-side flat law (**priced NOT cheap**), BINDUC's **(BE-23)(ii)** (*forced flat
⇒ `def₂ = def₃`*, the disproof side's highest-value single search), and — unclaimed, from
BZAVOID's own successor ranking — a **flat-star dictionary**, re-proving
`molecular_finrank_motions_eq_square_ker`'s surjectivity under a hypothesis admitting coplanar
stars, which would revive route 2 (§(K-bare-ext)). **Superseded, do not re-derive:**
(BE-27)(ii) refuted the reading that the residual gauge group supplies general position — *the
gauge group was never the right place to look*.

**THE (K-res) SCOPING SLICE LANDED 2026-08-28** (RESGRID, ordinal 48; §(K-res),
`notes/Pencil-informal-grid.md`, own gap-map row), discharging the user's 2026-08-26
adjudication and retiring the *"pin it when the tight side closes"* deferral. **The
(K-res) wave remains a user call** — neither started nor pre-empted (price, *Step
RS9*). **The 2026-08-29 user call is discharged (BRNODE landed); this stays ranked.**

**THE CANDIDATE LIST lives in `notes/Pencil-strategy.md` §8 — the option board** (new
2026-08-20): every live route priced in one place, with the two filters that kill most
candidates on sight (growing-ground-set; counting saturation, now closed in **both**
directions by (OC-3)/(OC-37)). **Not restated here** — and the board, not this section,
carries the current ranking. **Not eligible:** route σ's **obligation 1** and the W4
**build** — those, and only those, are held by the hold. **The §9 Zheng shelf** (unpriced,
deliberately off §8's board, an **idea source and never a citation**) is down to **one
dispatchable candidate, (ZH-2) stratified**; the per-item provenance, caveats and order are
strategy §9's, not restated here.

**DO NOT RE-OPEN — what the recent landings closed: RELOCATED 2026-08-29** (verbatim) to
`notes/Pencil-structure.md` §"What the recent landings closed" — BZAVOID's three ((BE-15)
cap-free for the **triangle** mechanism only, the `G²` apparatus, the transversality count),
ZJACOB's conservation law, ZSHEAR's gauge-triviality, GHWIT/GMINM's pair. Stable reference,
not status; every item's own gap-map row carries the same close.

**THE THREE CARRIED ITEMS, RANKED BY DISTANCE TO THE PHASE TARGET** (the 2026-08-26
directive; *Current state*'s delegation bullet; the superseded successor-order convention and
its cost are `notes/dispatch-log.md`'s and `notes/Pencil-fanout.md`'s). **The target is
`PencilPair K 3 G`; exactly these three stand between it and the landed theorem. Rank accordingly.**

1. **`hbareSplit`** (kernel (K-bare), research) **via (BE-14), direct attainment** — *the
   pencil stratum attains `6(|V|−1) − def₃(G)`*, hard step isolated to **`Y° ⊄ Z(G)`**
   (§(K-bare-ext) *Step BE13*, BATTAIN). **The most target-moving statement the arc
   currently owns:** seed-free, induction-free, never uses `¬PencilNondegFeasible`, and it
   discharges `hbareSplit` **and** `PencilPair`'s unconditional conjunct at once, as a
   **standalone theorem** (the phase's own 2026-08-05 bar). Dearer in absolute terms,
   cheaper in structure. Carried as pinned ("C: cheap numerics extensions + A",
   2026-07-30; option B NOT commissioned), extension route recon'd **NO-GO on landed
   machinery**; minimal open statement **(K-bare-ext)**, the arbitrary-seed insertion
   lemma; status row in the gap map, full record in the design doc §"(K-bare)
   extension-route recon", numerics `notes/scripts/kbare/{danger,optc}.py`. **Why it is
   *carried*:** the NO-GO is **definitional** — `PencilNondegFeasible` *is* "a
   nondegenerate realization exists", so at `¬PencilNondegFeasible` the
   chart/reseed/engine apparatus has **nothing to consume** on either side of the split,
   and the one identified calculus is unlanded, needs the owed **KT pp. 684–691 re-pin**,
   and was built for chart-*generic* seeds (**that research is option B, declined
   2026-07-30**). Versus `hK`: easier on uniformity, **harder on the seed side**, habitat
   reaching **corank 2** (DZ). Evidence **strong but sample-scoped** — KBARE-FALSIFY's
   constructed off-line failure at DZ (rank 113) corrected option-C C3's "failure set is
   exactly the line": the sample record stands, the locus claim does not (gap-map row
   (K-bare)). **Still unclaimed:** BATTAIN's `def₂ = def₃` proof-of-concept slice, now
   known to cover the whole of BINDUC's base; it does not discharge `hbareSplit`
   (DZ has `def₂ = 11`).
2. **`hcontract`** (W4) **via route 3's informal costs — dispatchable TODAY, and the hold
   is an argument FOR them, not against.** The **build** is fully decomposed, buildable and
   PARKED by the hold; the other four costs are **not** parked — **(T)**/**(V)**/**(E-loc)**
   are slice-sized and need no adjudication, **(K-res)** is wave-sized and a **USER CALL**
   that route 3 cannot close without. All four are stated once in *Blockers*, "What the
   Lean hold parks, and what it does NOT" — the canonical scope statement, **not restated
   here.** Route **ADJUDICATED 2026-08-02: route 3, packaging (b)**, with (K-res) a
   byte-identical sibling of `hK`; residual carry narrows to **`hnoGood'`**, whose vacuity
   conjecture is **REFUTED** (`|V| = 19`), so branch 4 needs content. When commissioned the
   next commit is **W4-L4b** (`exists_degree_two_of_co1_rigid`, pinned +
   spike-elaborated), then order-flexibly W4-L1/L2/L3′/L5; gates N8/N9/N10/N10b all
   PASSED. Canonical homes: `notes/Phase39-design.md` §§"W4 decomposition recon"/"W4-L4
   identification recon" and `notes/Pencil-W4-informal.md`.
3. **`hK`** (kernel (K), research) **via (GR-15)** — the escape `≢ 0` uniformity kernel,
   the phase's hardest open item and what the whole research arc attacks: **untouched by
   all 61 directions**, and the only one of the three with **no named next slice**.
   Everything in §(K-grid)/§(K-out) is *support* for this, not progress on it. **Standing
   adjudication ("C: literature hunt + A", 2026-07-30): carry `hK` pinned; option B NOT
   authorized**; both literature hunts are MISSes, and since 2026-08-02 it also carries
   **(K-res)**. **The mathematics is NOT restated here** — canonical home is
   `notes/Pencil-informal.md`'s **State of (K)** gap map (per gap: status, what would close
   it, uncovered shapes, a *settled, do not re-derive* block). Read that map, not this
   item, before any (K) work.

**Below the carried items — support work, explicitly ranked lower now.** OGEOM's successors
(the unsearched `n(F°) ≥ 6` frontier; the Kirchhoff-injectivity sentence) are **disproof-risk
reduction**, which by (OC-24) *"can never be the binding obstruction"*; the grid-side residual
(*is the ledger gap ever `≥ 3`?*) is ledger bookkeeping; OQRANK's residuals and the
`2k ∈ {4,6}` corner likewise.

**`hsplit` is CLOSED IN FULL** and **`hfresh`'s mechanical discharge (residue (iv))** with it
(W5-L7c-1…6, 2026-07-30); `pencil_conjecture_of_hcontract_hK_hbareSplit_of_card`
(`Molecule/Pencil/Escape.lean`) wraps `pencil_conjecture_of_hcontract_hK_hbareSplit` and
carries exactly the three items above.

> **Route σ — the one live candidate, and it is NOT settled.** Route A at the dual seed
> `σu`; it would close (K-tight) on the hard stratum, *length-free*. **Offered for
> adjudication**, **not field-blocked**, **not in flight**; it moves no gap-map status and
> changes no standing constraint. It rests on **four obligations, only the first of which is
> Lean** — that one genuinely the hold's, the other three dispatchable and two of them
> decision-relevant *before* any Lean is commissioned. **The four, their `--hunt` findings,
> the validation scope, the *Field scope* caveat, the smallest opening commit and the
> not-the-bridge warning are THIRD-COPIED here no longer** (thinned 2026-08-28): canonical
> homes are §(K-σ) *Step σ5* (`notes/Pencil-informal.md`), the **(K-σ)** and **(K-tight)**
> gap-map rows, and `notes/Pencil-strategy.md` §8.4 — each of which carries all of it,
> checked before thinning. The one clause that is *status* and stays here: **route σ is not
> a route to (K-res)** (obligation 2), so it does not substitute for the (K-res) wave.
>
> **The durable negatives and the deliberate non-goals — RELOCATED 2026-08-28** (verbatim)
> to `notes/Pencil-structure.md` §"Durable negatives and deliberate non-goals": the two
> 2026-08-07 do-not-re-run items, the *not re-litigated per wave* list, and the
> do-not-re-derive/re-sweep/re-open batch. Stable reference, not status.

**Gates for any continuation — RELOCATED 2026-08-28** (verbatim) to
`notes/Pencil-structure.md` §"Gates for any continuation": which gate fires on which file
type, and the figure-invariance discharge. Stable reference, not status; read it once per
session alongside the *Conventions* block relocated there 2026-08-27.

## Adjacent directions (orientation only, not this phase)

The queue is `ROADMAP.md`'s *Queued post-program phases*: ORIGAMI (`notes/Origami.md`), the
bar-joint-side analog, is next; the unqueued survey, incl. IDENT-PANEL, is `notes/IdeaBacklog.md`.

## Decisions made during this phase

**One-line verdicts, reverse-chronological** (`notes/CLAUDE.md` *Forward-weighted note*:
a settled decision keeps full prose only while upcoming work might lean on it — the four
newest (BE-14) entries do, the rest do not). Each direction's *mathematics* is in the workbook
section named; its *spec and landing write-up* in `notes/Pencil-fanout.md` §"<CODE>"
(`notes/Pencil-fanout-archive.md` for ordinals 1–19); the *user call that picked it* in
`notes/Pencil-adjudications.md`; the derivation in git. **Do not grow these back into
paragraphs.**

- **BDECOR** (53, 2026-09-01, opus) — **THE ACHIEVABLE DECORATIONS ARE A PRODUCT OF EAR
  CHAINS** ((BE-64)): the pencil condition is a **per-vertex conjunction**, so at fixed hub
  flags ANY piece's legal configurations are a **product** of ear chains, one per
  **topological branch**, **modulo the cross-branch proviso `G`** — per-child sets past ears **never needed**, theta a corollary
  (generic `dim ρ̄ = max(0, Σ min(a_j,6) − 12)`, welded attainment **FREE**, (BE-66)). Job 2
  CONFIRMED+widened; (b) harmless, (a) **propagates THROUGH the P-node** (7/30 rows off
  general position, all 7 **non-attaining** — a quantifier correction to (BE-62)(iii)).
  Flag base = §(K-chart)'s tower ((BE-65)); half (B) 28/28 **per-piece** ((BE-67)).
- **BRNODE** (52, 2026-09-01, fable) — **THE INTERNAL R-NODE DESCRIBED** ((BE-59)/(BE-60)):
  a child's boundary trace is `Δ ⊕ (0 ⊕ ρ̄_e)` — a function of its `ρ̄` ALONE — so the SP
  recursion extends to the whole SPQR tree (leaf line, `S` sums, `P` intersects, `R` the
  **decorated kernel**), exact at every configuration; job 1's sharp question **YES**.
  (BE-22)(vi)'s collapse = `δ_{xy}(B − uv − e) = 0`, exhaustive `n ≤ 6`, **prism fails at
  two rungs** ((BE-61)); drawn (α)/(β) content **EMPTY** (24/24 peels), residue = the
  **achievable-decorations class statement** ((BE-62)); chord step priced strictly harder
  ((BE-63)). §(K-bare-ext) *BE58–BE62*.
- **BWIN** (51, 2026-08-29, fable) — **THE WINDOW CLOSED BY A CLASS THEOREM** ((BE-57)):
  `ρ̄₁ ∩ Z = ⟨ℓ_u, ℓ_v⟩` at every both-ends-series piece with `δ₁ ≤ 4`. Machine: double
  peel + **modular law** (target ⟺ `W ∩ Z ⊆ ⟨ℓ_u,ℓ_v⟩`, `W` the middle's screw space,
  **arbitrary** — no enumeration, no middle induction, job 2 REFRAMED), the **end-choice
  lemma** (one functional, survivors exactly `⟨ℓ_u,ℓ_v⟩`), the **excess law**
  `excess ≤ max(0, δ₁−3)`. **(b1)+(b2)+(b3) at every window piece ⟹ (β) proved there on
  87-of-91**; window ⊋ barbells (R-node middles in it); two side conditions named,
  vacuous at every drawn middle; 160/160 end draws. §(K-bare-ext) *BE53–BE57*.
- **BRULE** (50, 2026-08-28, opus) — **(b3) DECIDED, the CHEAPEST clause**, by a
  **separation theorem** ((BE-50)): `Π_u`, `Π_v` lie in the very ruling `y ∧ L` lives in
  and same-ruling members meet in `0`, so a failure refutes (b1) or forces the sharpening
  at **both** ends — free wherever a BSHARP mechanism fires, **window included**, so
  **(β)'s two residues are DISJOINT** and (β) is at **the window alone**. Domain named and
  (b3) **struck** at `π_u = π_v` ((BE-49)); (BE-37)(ii)'s *inference* corrected, (Z)
  dominating (R), **no measurement moved** ((BE-51)); one witness per shape ((BE-52)); 0
  failures at 637 draws ((BE-53)). Job 2: (BE-32)(+) is **under** three clauses, forced branch only.
- **BSHARP** (49, 2026-08-28, opus) — the (b1) sharpening is **FALSE** at a dichotomy
  (series end / path saturation), correcting (BE-38)(iii) with no measurement change, and
  it cuts (b2) down to the both-ends-series window. §(K-bare-ext) *BE43–BE47*.
- **RESGRID** (48, 2026-08-28, fable) — the (K-res) scoping slice: §(K-grid)'s **geometry
  transports verbatim** and the (K-res) grid residual is **(RS-5)** ((GR-15)'s criterion,
  quantifier widened; proven per-shape at `W19`/`S29`/`NT21c3`); the tight bookkeeping and
  the (GR-21)+ program do **not** transport; the deficient fringe refuted ((RS-6), θ(2,3,7)
  capped at 58 < 59, retiring §(K-clos) *Z6*'s miss as a theorem). *"One uniform gap serves
  both"* **corrected**; §(K-res) opened with its own gap-map row; wave stays a user call.

The (BE-14) thread the hand-off's candidate (0) sits on — two entries kept at prose length:

- **BEARFULL** (47, 2026-08-27, opus) — the merge inequality's real theorem is a **SHORT-CYCLE
  LAW**: `girth(Q) ≥ 6`, so **every cycle of length `≤ 6` forces `δ = 0`** and
  `δ ≤ max(0, L−6)` — **containing** (BE-32)(ii)/(iii) and **weakening** the latter to `≥ 2`
  common neighbours; **`δ = 0` is an EQUIVALENCE RELATION** (supermodularity + join).
  **(BE-32)(+) PROVED at 196 043/203 723** forced pairs, residue geometry-free with an
  **exact** boundary. **(b2) a COROLLARY of (b1)**. The coordinator's **ear-decomposition
  route REFUTED by a theorem** — min-degree-`≥ 3` forces a chord — so **S-mark's pin STANDS**
  and the internal R-node is **confirmed** on the critical path. §(K-bare-ext) *BE38–BE42*.
- **BEARCASE** (46, 2026-08-27, opus) — **(α) CLOSED**: the greedy's last step is a complete
  criterion (**the 2-step lemma**), its bad case a **scheduling** artifact, and a
  **reordering + slide** removes it ⟹ **the reach formula is PROVED for `m ≥ 3`**
  (constructed, 1 432/1 432); no fourth mechanism at `m ≤ 2`. **(β) as stated REFUTED**
  (unsatisfiable at `δ₁ ≥ 5`; a **propagated prose defect**, no measurement changed), its
  quantifier **COLLAPSED** on the attaining locus, and the (β) side reduced to the single
  residue **(BE-32)(+)**. §(K-bare-ext) *BE34–BE37*.
Settled, one line each:

- **BIMAGE** (45, 2026-08-27, opus) — the ear's `ρ̄₂` is a **chain on the Klein quadric**
  (bijection + three confinement laws); the **series/parallel recursion** minted, residue
  the internal R-node — **now landed by BRNODE**. §(K-bare-ext) *BE29–BE33*.

- **BTWOCUT** (44, 2026-08-26, opus) — strengthened statement **PINNED** (S-mark), simultaneity
  **VACUOUS**, leaf base free; **(BE-14) NOT proved**. §(K-bare-ext) *BE24–BE28*.

- **BINDUC** (42, 2026-08-26, opus) — **3-connected ⇒ `def₂ = 0`**, so the induction's **base
  is FREE**; BZAVOID's 2-cut `− 6` **REFUTED** for an exact `max`-law; **(BE-15)(ii)
  scope-corrected** to the triangle mechanism. §(K-bare-ext) *BE19–BE23*.

- **BZAVOID** (40, 2026-08-26, opus) — falsification arm **EMPTY BY AN ARGUMENT** ((BE-15));
  the pencil stratum **IS** the planar-atom molecular stratum, so (BE-14) is **existential**
  ((BE-16)); two routes CLOSED. §(K-bare-ext) *BE14–BE18*.

- **BATTAIN** (39, 2026-08-26, opus, the arc's first direction ever at `hbareSplit`) — motive
  characterized off the Lean bodies, **bare realizability UNCONDITIONAL**, the first universal
  rank cap by an argument ((BE-11)/(BE-13)). §(K-bare-ext) *Step BE13*.

- **ZJACOB** (43, 2026-08-26, opus, Zheng line) — **(ZH-4) REFUTED by an EQUIVALENCE**
  (`B_0 ≠ ∅` **is** properness); **absorbs (ZH-3)**. §(K-jac) *JC1–JC5*.
- **ZSHEAR** (41, 2026-08-26, opus, the §9 shelf's first direction ever) — **(ZH-1)
  REFUTED by GAUGE-TRIVIALITY**; owed §2.5 filter check **DISCHARGED**. §(K-shear) *SH1–SH5*.
- **GHWIT / GMINM / OGEOM (36–38), 2026-08-26, opus, one-lined** — per-matching (b′) at the
  constant 2 is **FALSE** by witness with (GR-86)'s gap-4 cap TIGHT (GHWIT); that refutation
  **does not reach the ledger**, which consumes the **difference of minima**, `min_M` **PROVEN**
  (GMINM); **no disproof witness**, the geometric route free by an argument on everything
  searched, §8.5's row narrows but does not close (OGEOM). §(K-grid) *G140–G148*, §(K-out)
  *O42–O46*.
- **The 2026-08-25 fable run (30–35), one-lined** — **GFLIP** (GR-R1) PROVEN so (GR-89)(ii)'s
  `n`-free `≤ 12` bound is a THEOREM; **GCHEAP** (b′) at 2 a THEOREM on the whole `n_hub ≤ 6`
  stratum, per-configuration form REFUTED; **OQRANK** a graded HIT, input (a) GREEN at all 174
  certified classes, class-uniform (a) still OPEN; **GPRICE** (GR-104)(i) a theorem at `2k = 2`
  modulo (GR-108); **GBLAW** an honest OPEN reshape, (GR-108) reduced to existential escape;
  **GXESC** (GR-108) and existential escape REFUTED BY WITNESS. §(K-grid) *G116–G139*,
  §(K-out) *O37–O41*.
- **The two architecture probes, one-lined** — **C3-AVOID** (2026-08-24): board option **C3
  NO-GO** as a crux-avoidance route, universal threshold **`|S| ≤ 2`** (strategy §4.7).
  **KBARE-FALSIFY** (2026-08-20): a **T1 HIT**, (K-bare-ext) **refuted as stated**,
  `hbareSplit` **untouched** (§(K-bare-ext) *BE1–BE8*).
- **Structural rounds 1–2 + the slice-6 compression round: COMPLETE** (2026-08-19 → 08-26;
  record `notes/Pencil-structure.md`). **ROADMAP §39 was split by volatility** and no longer
  carries the arc's running state — **do not re-add a direction count or fan-out roll-call
  there**; the count is the ROADMAP Status row's.
- **The EIGHTH FAN-OUT — all five LANDED 2026-08-19** (ordinals 25–29): GTMPL, GFLOW, SIGZ
  ((OC-37) killing the counting route to a disproof), OSCHU, GCOLL (**(GR-64)(R2) REFUTED**).
  Four of five corrected a defective spec clause (`notes/dispatch-log.md` **F22**).
- **Directions 1–24 — ALL LANDED 2026-08-05…08-19** (thirteen across the first five
  fan-outs, one per ordinal from the sixth on). **Net: three HITs** — entry 5 PROVEN both
  halves (GBAL, discharging (X)); chart irreducibility PROVEN (CIRR); AA-glue NOT
  realizable at `n_hub = 8` (AGLU) — the rest honest MISSes or OPEN reshapes, each with a
  named successor. **(GR-15) OPEN throughout; E1/E2 never fired; E3 ARMED by GBAL, not
  fired.** Canonical homes `notes/Pencil-fanout{,-archive}.md` + `notes/Pencil-labels.md`.
- **The 2026-08-05 research cluster, one-lined** (all same day; full detail
  `Phase39-design.md` + git, workbook sections named): notes reorganization
  (`Pencil-labels.md`; design doc **FROZEN**) + class-uniformity recon (5 REFUTED, 3
  ranked, strategy **§4.6**); route σ a **CANDIDATE** (obligation 1 DONE); (K-ind) and the
  Δ-matroid lead **BOTH REFUTED**; the §(K-Λ) triad settled ((Λ0)/(Λ1) PROVEN via M2); the
  sixth–ninth dispatches found the conjecture HOLDS at every uncovered flank, the pure
  condition WRONG INVARIANT, dominance HOLDS but NOT a route; **(K-slide-comb) REFUTED**.

- **Pre-fan-out arc, one-lined (2026-07-24 → 08-04; full detail `Phase39-design.md` + git)**:
  W0–W3/W5 CLOSED `hsplit` IN FULL and isolated kernel **(K)**; corank fixed to **(K-tight)**,
  W4 decomposed, (K-bare-ext) NO-GO'd, the standing adjudications set; **(K-res)** priced and
  **(SAFE-RES)**/`hnoGood'` vacuity REFUTED; (K-slide) (S1) proved, (K-pitch) closed.

- **Promoted out of this phase** (pointers only): TACTICS-GOLF §11/§22/§23; TACTICS-QUIRKS
  §46/§96/§99–§104; FRICTION `exists_injOn_mapsTo_of_ncard_le` + `extensor_pair_smul`
  [mirror-candidate] and the omega/`Set.ncard`-atom idiom.
## Citations (transcribed, project-canonical sources)

**RELOCATED 2026-09-01** (verbatim) to `notes/Pencil-structure.md` §"Citations —
the phase's verified bibliography": the per-source venue data, the verification
dates and the two pointers to the fuller bibliographies it does not duplicate
(`notes/Phase39-design.md` §"(K) literature hunt", `notes/Pencil-informal.md`
§(K-Δ) *Sources*). **Stable reference, not status** — it changes only when a
direction verifies a new source, which is the same disposition as the six blocks
relocated 2026-08-27/29, and it is what this note's *Doc debt* watch item
prescribes instead of a fifth compression fold. Nothing deleted, no cap bumped.
**A direction that verifies a new source adds it THERE, in its landing commit.**
