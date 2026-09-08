# Phase 39 — PENCIL: the hinge-pencil molecular conjecture (work log)

**Status:** in progress — the phase stays OPEN (2026-07-24 adjudication). The target is
**`PencilPair K 3 G`**, and the landed successor
`pencil_conjecture_of_hcontract_hK_hbareSplit_of_card` (`Molecule/Pencil/Escape.lean`)
derives it from exactly **three carried items**: **`hcontract`** (W4 — build parked by the
**2026-08-05 Lean hold**; informal side CLOSED as an argument), **`hK`** (kernel (K)),
**`hbareSplit`** (kernel (K-bare)). Everything else is closed — W0–W3, all of W5
(L0–L7), `hsplit` and `hfresh` (2026-07-30, unchanged since).

**The research arc: 88 directions COMPLETE** (2026-08-05 → 09-03, ordinals 1–80 — 83 on
kernel (K), **WTRI/WELOC/WPAIR/WGROW (58–61) on W4**, **RPOOL (75) on (K-res)**; direction
= ordinal + 8), plus nine strategy passes, two probes, a scoping recon. **GPACK (66) opened
the `hK` lane** (GLIST 68, GGLOB 71, GLEAF 80); the ninth pass's **ranks 1–4 SPENT**
(BSCOND 76, BARCH 77, GLEAF 80, BINSERT 82); its round of four COMPLETE (OBAR 78, DSAT 79). Per-direction verdicts, specs and write-ups live at
`notes/Pencil-fanout.md` §"<CODE>" (1–19: the archive) plus a workbook home — **not
restated here**. **The arc's standing result, unchanged: `hK` is not closer.**
**(GR-15)** — the single open gap the §(K-grid) chain reduces to — is **untouched**; **class
uniformity untouched**; no g-flank found; **E3 is ARMED (by GBAL), has NEVER fired, and is
NOT one landing away** — why: **block 14**.

**`hK` LANE (66, 68, 71, 80): (GR-18)(iii)'s split half is a THEOREM, its residual
CSP-FREE and IS (GR-10) at `D = 0`; successor 4 SPENT — reached, and *necessary* (GLEAF).
ESCAPE (OWALL 70): (OC-44)(iii) REDUCED to (OW)**; **U3 (OBAR), C2 (DSAT) STRUCK**.
**(GR-10)/(GR-15)/(OC-8) unchanged**. Detail: **blocks 11–13**.

**W4's INFORMAL SIDE IS CLOSED** (58–61): **(T)/(E-pair)/(V) THEOREMS**, **(E) open, TIGHT,
off every W4 path**, list **EMPTY** — leaving the USER call **(K-res)**, now DEARER (**RPOOL
75 REFUTED (RS-5)**), and the held build. Detail: **block 9**.

**WHERE THE (BE-14) THREAD STANDS** — S-mark is its **only open step**; detail: **block 8**.
Status only: (β) at the window is **UNCONDITIONAL** ((BE-142)–(BE-148)); OUTSIDE it the
residue is **TWO items + a corner, not four**, its one-end half class-level
**CONDITIONAL on (PENCIL-SATURATES) at `deg ≥ 2`**, so (β) is **not independent of half
(B)** ((BE-164)–(BE-171)); cross-cut forcing **empty**; flag base **DISCHARGED**; the
per-side residue (14) is **REDUNDANT** at both 2-blocks under that clause — **REFUTED**,
`-GEN` too, leaving **-CHART**, a **THEOREM at `deg 1`** ((BE-127)), so **14 → 12** stands
generically. At `deg ≥ 2` the **METHOD** ((BE-139)) is **SCOPED to `Λ²K⁴`**, the FIXED
graph `Γ` carrying the clause EXACTLY ((BE-149)/(BE-150)), and **14 → 12 reduces to the
two-sided (E4), UNPROVED** ((BE-152)/(BE-153)), **OPEN** at 0/772; class uniformity
**untouched**. The 12 are **unwitnessed, NOT excluded** ((BE-97)(iv)) except `⟨M⟩`, empty at 93; cross-pair welding **untouched**.

**On a future HIT: the phase-boundary consequences are the USER's call** — whether Phase 39
closes and a successor opens for the Lean is a `PHASE-BOUNDARIES.md` event against the
standing 2026-07-24 no-split adjudication, surfaced with a commit-count estimate, never
unilateral; the 2026-08-05 Lean hold binds regardless.

**FOURTEEN reference blocks sit in `notes/Pencil-structure.md`**, indexed there — **read
them once per session**. The line that stays here: the **State of (K)** gap map
(`notes/Pencil-informal.md`) is this phase's status object, **authoritative for every
status word**; read it with `python3 notes/gapmap.py`, never `sed`/`grep`.

## Current state

**The phase stays OPEN.** Standing user adjudications, verbatim (these are the live GO/NO-GO
constraints; the **dated dispatch/selection narrative for every ordinal, 1–44, is
`notes/Pencil-adjudications.md`**, quoting the user byte-for-byte, and git):

- **2026-07-24:** *"Let's leave the phase open and continue the work on the conjecture in this
  phase. Unless there's a good reason to split here."*
- **2026-07-30 (both kernels) / 2026-08-02 (W4) — RELOCATED VERBATIM 2026-09-03** to
  `notes/Pencil-adjudications.md`: the same day's *declines are not locks* directive demotes
  them to **history**. `hK`/`hbareSplit` stay **pinned** (a claim about the proof, not a bar);
  W4's build is parked **by the Lean hold**, not by the 2026-08-02 call.
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

- **2026-09-03, DECLINES ARE NOT PERMANENT LOCKS** (verbatim): *"I wouldn't overemphasize
  user decisions or make them too binding: we should ultimately be driven by the math. So if
  there are still some promising directions that happened to be declined once in the past, we
  shouldn't lock them out forever."* An adjudication is **a past priority call, not a
  prohibition**; re-opening needs **a mathematical reason, not permission** — cite what
  changed, never a fresh opinion. **Re-opened:** both option Bs (option B's first step is a
  **design pass**, unparked by the hold) and **(K-res)**'s cheap slice + flank. **NOT
  loosened** (barred by *mathematics*, not priority): the (a′)/(b′) do-not-do, §2.5 counting
  saturation, the §(K-ind) gate, the Zheng unrefereed caveat. **The Lean hold is untouched
  and remains the user's.**

- **2026-09-03, THE REPRIORITIZE DIRECTIVE** (verbatim): *"we should try to tackle the most
  promising directions (either for proving or disproving the headline result); if the current
  approach seems to be getting in a rut then it's time to reprioritize."* Sharpens the
  delegation's first criterion; adds an explicit licence to move off a ranked list.

- **2026-08-29, the target after BWIN** (twelfth check-in) — **SPENT**: the user picked the
  internal R-node (long since landed) over the spread step, (S1)/(S2) and the (K-res) wave;
  those three stay **ranked, not dropped**, and the (K-res) wave is still a user call.

- **Session-headroom calibration — MEASURED 2026-08-26** (eleventh check-in).
  `weekly_scoped` tracks **fable only**, so the playbook's *"above ~80 % on **either**
  limit, stagger"* reads as *"on the limit the dispatched rung actually consumes"*;
  `weekly_all` moves **1–2 points per pair-round**.

**The arc's cumulative tally** — roll call, ordinals, dates and rungs live in
`notes/Pencil-fanout.md`'s header and per-direction sections, **the only place they are
maintained** (this note's copy has gone stale before). Counting rules: the count moves only
on a **landing**; a user call on dispatch *shape* is **no** strategy pass; the two probes
(KBARE-FALSIFY, C3-AVOID) sit outside it. Net effect: **disproof risk removed**, every
refuted route/gap has a gap-map successor, **entry 5 PROVEN**, **class uniformity
untouched**. **Doc-debt round CLOSED** (`notes/Pencil-cleanup.md`, 2026-08-13).

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

- **Open: kernels (K) and (K-bare); W4's remaining item is a USER call** — the per-item
  route is in *Hand-off*'s three carried items and **not duplicated here** (the two W4
  bullets that stood here were **merged at the BBASE landing**, having converged on the
  same sentence once (GROW-6) landed). **Route 3's informal cost list is EMPTY**
  (2026-09-02): **(T)** a theorem (WTRI, §(SAFE-RES) *Step TF5*), **(E-loc)** refuted and
  shown unnecessary (WELOC, (EL-5)/(EL-6)), **(E-pair)** a theorem (WPAIR + WGROW,
  §widened kernels *PR1–PR6* + *GW1–GW6*) and **(V)** with it ((PAIR-6)). **(E)** itself
  stays open and **tight**, now off every W4 path. Two facts that still constrain future
  statements: **`hnoGood'` is NON-vacuous** (2026-08-02), so branch 4 needs content, and
  **(SAFE-RES) is REFUTED** the same day. **No adjudication is owed** — route 3, packaging
  (b) was adjudicated 2026-08-02.

- **What the Lean hold parks, and what it does NOT — corrected 2026-08-20, because this
  bullet read as though it parked all of W4.** The hold parks **Lean**: the W4 build
  (W4-L4b onward), the `noRigid`-free Lean leaf, and route σ's steering commit. It never
  parked route 3's informal costs, and every one of those is now discharged (bullet above).
  What is left is **(K-res)**, a kernel of `hK`'s difficulty class on the complementary
  habitat whose proof route is *strictly harder* (its habitat sits wholesale in the
  `dim R_a = 1` stratum where the (K) recon found no landed-brick route). **Its SCOPING
  LANDED** (RESGRID, 48) and its two **cheap items are now SPENT** (RPOOL, 75): the pool
  sweep ran and the flank hunt **HIT** — **(RS-5) is REFUTED**, so the wave is **dearer**,
  not closer. **The WAVE itself has still never been attacked** and stays a **user call**
  (offered and declined 2026-09-02; not re-litigated at RPOOL). What it now costs: prove the
  **repaired** statement uniformly **and** route the `index < 2·g_forced` members, which have
  **no named home** — the `§(K-res)/(RS-5)` row carries both, and *Step RS9*'s pricing gains
  a fourth line. The *"pin it when the tight side closes"* deferral stays **RETIRED**.

- **Doc debt — the gate is MECHANICAL** (`notes/check-phase-note.py`: **580 lines / 525
  status-header words**, plus a fail if *Decisions made* outgrows the forward sections),
  and the standing remedy is **relocation or merger, never a fold** — **FOURTEEN** reference
  blocks now sit verbatim in `notes/Pencil-structure.md`, indexed by its own table, with no
  cap ever bumped and nothing deleted; **which relocation bought what is that file's record,
  not this one's**. **The rule that keeps working:** ask *"what here is reference rather than
  status?"* — six landings running have paid for themselves that way. **LINES bind, not
  words**, so the next landing MUST merge or rotate rather than append. **Do NOT relocate the
  *"On a future HIT"* block** — standing safety policy, read first by a fresh session. A
  landing's entry stays **one line**; the (BE-14) thread's prose entries are the standing
  exception, the oldest demoting at 580/580.
- The full biconditional transport (design doc's W0 pin) is landed only as its two forward
  implications; the reverse arms need a `complementIso` involution lemma, not in tree —
  deferred, **off every critical path** (§(K-σ) *Step σ6*).
- **Harness debt — four rounds PAID; the count is the HOME's, never restated here** (it read
  SIX from GLIST to 2026-09-03 while the home said TEN). Canonical home
  `notes/scripts/README.md` *Harness debt* — **read it before any numerics dispatch**: its
  own header enumerates every outstanding item, the two deliberately-unfixed *Recorded
  observations*, and the rule for a dispatch that trips §2 rule 2 again. One is a **silent**
  correctness hazard, not a tidy-up: `bimage.pt_in` truncates a `Λ²K⁴` input to `K⁴` with no
  assert firing — **no `Λ²`-side draw may go through `pt_in`**.

## Hand-off / next phase

**The phase stays OPEN** (the 2026-07-24 adjudication — no phase-close; see *Current state*).

**THE (BE-14) THREAD, settled frame + its last landings — RELOCATED 2026-09-02** to
`notes/Pencil-structure.md` §"The (BE-14) thread — per-landing detail" (**block 8**); the
write-ups and the `(K-bare)` gap-map row stay authoritative. **Reference, not status.** The
status that stays here: **S-mark is (BE-14)'s only open step**, (β) is proved at the window
**modulo (BE-57)(iv)'s (S1)/(S2)**, half (B)'s residue is **item 1 of the workbook's four**
((BE-121)(i); 2–4 are item 0's (b)/(c)/(d)) — item 1 being **(PENCIL-SATURATES-CHART)**, a
**THEOREM at every side-degree-`1` terminal** ((BE-127)) and **OPEN** at side-degree `≥ 2`,
where BLINE killed the `(∗)` route ((BE-130)) — and cross-pair welding is **untouched**.

**THE W4 DEVIATION'S PER-LANDING DETAIL — RELOCATED 2026-09-02** to
`notes/Pencil-structure.md` **block 9**: the thread is untouched since WGROW (61) and its
informal argument is **closed**. Status is in the header, not repeated here.

**BBASE (62) → BSATUR (65) — RELOCATED 2026-09-08** to **block 8**, which already owned the detail; the one *status* clause, **(CH-1) does not apply to the flag base** ((BE-89)), is in the header.

**THE 2026-09-02 ROUND'S PER-LANDING CLAUSES (66–72) — RELOCATED 2026-09-02** to
`notes/Pencil-structure.md` **block 13**; blocks 8/11/12 already own the detail. **Reference,
not status.** The two clauses that stay: **no gap-map status word moved at any of the six,
and BOPEN (72) closes half (B)'s item 1 at side-degree `1`** (block 8), and **the `hK` lane's ranking is
`notes/Pencil-strategy.md` §8's board, NOT this list** (re-ranked `70c06abe`/`5583a919`; it
carries the standing **do-not-do** — no more (a′)/(b′) ledger directions), whose ranks 1 and
3 are spent.

**THE RE-RANK ON THE REPAIRED LISTS IS LANDED** — the **ninth strategy-only pass**,
coordinator-authored 2026-09-03 at `notes/Pencil-strategy.md` **§8**, which is where the
ranking lives and is **not restated here**; it supersedes the 2026-08-25 list and the
2026-09-02 `hK` table *as rankings* (both back-linked in that commit). **Its rank 1 is
SPENT: BSCOND (76) DECIDED (S1)/(S2)**, so (β) at the window is **UNCONDITIONAL**
((BE-142)–(BE-148)); **its rank 2 is SPENT TOO: BARCH (77)** answered both halves — the
method class is **NOT** dead, it **changes ambient**, and 14 → 12 **reduces to the
two-sided (E4), UNPROVED** ((BE-149)–(BE-155)) — and **§8's bar LIFTED NARROWLY** there:
`A_sharp` properness as posed **stays barred**, `Γ`-properness and (E4) are **lifted**
((BE-154)(iii); recorded in §8, as §8's own rule requires). **THE ROUND OF FOUR IS COMPLETE — OBAR (78), DSAT (79), GLEAF (80) all LANDED**: DSAT struck C2 as a *uniform* carry (the (K-res) half PROVED, the class half measured at five shapes, so NOT as a class-only conjunct); **GLEAF SPENT §8's rank 3** — the reach question SPLIT, the machinery **does** reach the branch-side demand by a theorem and the residual **implies** it, so no proof there moves (GR-10) ((GR-145)–(GR-152)). All four verdicts have had the coordinator's verification tier.**
**THE NEXT CONCRETE TASK is
(BE-154)(iv)**: one new `barch.py` mode running the `Γ_Π` and `(e₁, e₂)` tests at
`bdegtwo.sweep_points`' 411 **chart** points at **both** sides of the peel — it reaches the
three fibre shapes `cert` cannot, and it **falsifies (E4) if (E4) is false**. Neither rank's
closure closes S-mark: (BE-14) needs both halves. (GR-144)'s successor **1 is DEMOTED** (it **IS** (GR-10) here, (GR-140)(v)),
**2** is engineering (150/150 decided, 2 473 of 2 623 left), **3** is a search (does *path*
consistency decide where arc does not), and **4 is SPENT** (GLEAF 80: reached, and
*necessary*, so it moves nothing) — **the list is one step from exhausted and no member of
it reaches (GR-10)**. The (K-res) **cheap
slice is SPENT** (RPOOL). **The three replacement picks that failed are RELOCATED** to
`notes/Pencil-structure.md` **block 14**, with the sub-item re-lettering hazard. Two things
stay the USER's call, both OFFERED 2026-09-02 and DECLINED IN FAVOUR OF CONTINUING RESEARCH:
the **(K-res) wave** (its *scoping slice* LANDED 2026-08-28, below — it is **not** queued) and
whether W4's now-closed informal side changes anything about the **2026-08-05 Lean hold** —
the user's to lift, never a coordinator's.

The ranked list:

0. **HALF (B)'s CLASS QUANTIFIER, now (PENCIL-SATURATES-CHART) — A THEOREM AT EVERY
   SIDE-DEGREE-`1` TERMINAL** ((BE-127)(i)), so (BE-101)(i)/(ii) hold with the clause
   **proved** and **14 → 12 stands generically**. **(BE-69) is the WRONG warrant, and not
   needed** ((BE-122)/(BE-123)); BPROPER's two measured inputs are **PROVED** ((BE-124)/(BE-126)). Sub-items:
   **(a) the side-degree-`≥ 2` instances — the OBSTRUCTION is the METHOD, CLAUSE OPEN.**
   `(∗)` is exact ((BE-129)), **FALSE from `dim A = 5`** ((BE-130)), generic at 14 of 27
   shapes ((BE-133)), one obstruction with (BE-119)'s ((BE-132)); BDEGTWO settled **both**
   (BE-134) gaps — sweep PROVED, *keep `xc₂…xc_k`* MOOT, `(∗)` too strong, fibre-properness
   closed-form — leaving **no `p_x`-free subspace** ((BE-136)–(BE-139)). Successors:
   `A_sharp` properness; a chart hunt for (BE-138)'s three. *Kill: by the `(K-bare)` row;*
   **(b) [MARGIN]** a row with `margin > 0` at `Π_x`, `Π_y` or `⟨M⟩` — the arc's first
   **shortfall** if it exists, unexhibited at 54 rows ((BE-128)(i)), none new at BLINE or
   BDEGTWO ((BE-135)(i)/(BE-140)(iv)); **(c) [BLOCKS]** the **11** live blocks, `⟨M⟩` empty at 93 rows
   ((BE-121)(i), 72 + 21 — **not** (BE-108), whose figure is 72); **(d) [NON-ATTAIN]** the
   non-attaining case, **INHABITED, NOT ACTIVATED** ((BE-120)/(BE-121)(i)). **Cite the TAG,
   never the letter** — why: block 14. **Three siblings, all closed — do not re-hunt**:
   cross-cut forcing (BGENUINE), the flag base (item 1), the forced-empty `G` hunt ((BE-72)).

1. **THE FLAG BASE — DISCHARGED by BBASE** (verdict in *Decisions made*); its three cheap
   leftovers (is `B_real` a forest on the class; cyclomatic `≥ 2`; is a triangle necessary)
   are **RELOCATED** to `notes/Pencil-structure.md` **block 8**.
2.–4. **THE LANE'S STANDING MENU — RELOCATED 2026-09-02** to
`notes/Pencil-structure.md` §"The (BE-14) lane's standing candidate list" (**block 10**):
~~one-end-series~~ (**entry 2 SPENT at BSERIES, 83** — fired on ONE habitat, **conditionally**,
and re-scoped onto (BE-45)(iv) on the other), ~~**(S1)/(S2)**~~ (**entry 3 KILLED by BSCOND,
76**), BTWOCUT's bundle, and the *also ranked* tail (cross-pair closure, the
point-side flat law, BINDUC's **(BE-23)(ii)**, the flat-star dictionary), with its
*superseded, do not re-derive* note. **Reference, not status**: the rest unmoved since
BSIGMA (ordinal 67); the live items are 0 and 1 above.

**THE (K-res) ROW's TWO CHEAP ITEMS ARE SPENT** (RPOOL, 75, 2026-09-03; §(K-res)
*RS11–RS16*): the pool sweep ran over all **102** `def = 0` members of the recorded 255 and
the flank hunt **HIT** — **(RS-5) is REFUTED** by `R20`, `W19` with a longer core. The
scoping slice landed 2026-08-28 (RESGRID, 48). **The wave remains a user call**, neither
started nor pre-empted, and is now **dearer**: see *Blockers*. **Kill condition for the
successor: the repaired statement settled, or a flank at `g_forced ≥ 2` — decided by the
`§(K-res)/(RS-5)` row.**

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
`notes/Pencil-structure.md` §"What the recent landings closed" — BZAVOID's three (incl. the
**`G²` apparatus**), ZJACOB, ZSHEAR, GHWIT/GMINM. Stable reference, not status; every item's
own gap-map row carries the same close.

**THE THREE CARRIED ITEMS, RANKED BY DISTANCE TO THE PHASE TARGET** (the 2026-08-26
directive; *Current state*'s delegation bullet; the superseded successor-order convention and
its cost are `notes/dispatch-log.md`'s and `notes/Pencil-fanout.md`'s). **The target is
`PencilPair K 3 G`; exactly these three stand between it and the landed theorem. Rank accordingly.**

1. **`hbareSplit`** (kernel (K-bare), research) **via (BE-14), direct attainment** — *the
   pencil stratum attains `6(|V|−1) − def₃(G)`*, hard step now the **strengthened 2-cut
   composition lemma, PINNED as S-mark** ((BE-23)(e)); BATTAIN's `Y° ⊄ Z(G)` (*Step BE12*,
   not BE13) is that same target one framing up. **The most target-moving statement the arc
   currently owns:** seed-free, induction-free, never uses `¬PencilNondegFeasible`, and it
   discharges `hbareSplit` **and** `PencilPair`'s unconditional conjunct at once, as a
   **standalone theorem** (the phase's own 2026-08-05 bar). Dearer in absolute terms,
   cheaper in structure. Carried as pinned; **OPTION B IS SPENT, NOT DECLINED** (BINSERT, 82)
   — **(K-bare-ext) REFUTED on BOTH KT routes** by a panel collapse, only the un-analyzed
   joint sweep left, which re-opens the calculus link (§(K-ins)). **WHY IT IS
   *CARRIED* — RELOCATED 2026-09-03** to `notes/Pencil-structure.md` **block 14**: the
   definitional NO-GO, the KT pp. 684–691 re-pin (LANDED 2026-08-02), the `hK` comparison, and
   KBARE-FALSIFY's sample-scoped evidence. **Reference, not status**; the `(K-bare)`
   gap-map row stays authoritative.
   **DEAD, not unclaimed** (repaired 2026-09-03): BATTAIN's `def₂ = def₃` slice
   is DISCHARGED — (BE-23)(c) attains it by (BE-20)(ii), leaving (BE-14) equivalent to the
   2-cut lemma alone (BINDUC, ordinal 42, 2026-08-26). What is left is (BE-20)(ii)'s
   inherited (BE-13) ingredient: the **point-side flat law**, priced **NOT cheap**, already
   ranked in block 10's tail — one residual, one name.
2. **`hcontract`** (W4) **via route 3's informal costs — dispatchable TODAY, and the hold
   is an argument FOR them, not against.** The **build** is fully decomposed, buildable and
   PARKED by the hold; the other costs are **not** parked — **(T) is a THEOREM** ((TF-5),
   WTRI), **(E-loc) is REFUTED** ((EL-5), WELOC) and **(V) is a theorem given (E-pair)**
   ((PAIR-6), WPAIR). **(PAIR-5) is SETTLED BOTH WAYS** ((GROW-4)/(GROW-5), WGROW), so
   **(E-pair) is a theorem** ((GROW-6)) and W4's non-user-call list is **EMPTY** — only
   **(K-res)** is open, wave-sized and a **USER CALL** route 3 cannot close without.
   *(This item read "leaving the seed condition (PAIR-5), slice-sized" until 2026-09-02 —
   stale since WGROW, against this note's own header and Step GW6.)* Stated once in *Blockers*, "What the Lean hold parks" — **not restated here.** Route **ADJUDICATED 2026-08-02: route 3, packaging (b)**, with (K-res) a
   byte-identical sibling of `hK`; residual carry narrows to **`hnoGood'`**, whose vacuity
   conjecture is **REFUTED** (`|V| = 19`), so branch 4 needs content. When commissioned the
   next commit is **W4-L4b** (`exists_degree_two_of_co1_rigid`, pinned +
   spike-elaborated), then order-flexibly W4-L1/L2/L3′/L5; gates N8/N9/N10/N10b all
   PASSED. Canonical homes: `notes/Phase39-design.md` §§"W4 decomposition recon"/"W4-L4
   identification recon" and `notes/Pencil-W4-informal.md`.
3. **`hK`** (kernel (K), research) **via (GR-15)** — the escape `≢ 0` uniformity kernel,
   the phase's hardest open item and what the arc attacks: **untouched by every kernel-(K)
   direction through BSCOND (ordinal 76)** — name the last ordinal, never a count (SWEEP C;
   this line carried two mutually inconsistent tallies until 2026-09-03) — but GPACK (66),
   GLIST (68) and GGLOB (71) reshaped its named next slice.
   **THE LANE'S PER-LANDING DETAIL IS RELOCATED 2026-09-02** to
   `notes/Pencil-structure.md` §"The `hK` lane — per-landing detail" (**block 11**), the
   disposition blocks 8 and 9 got; it also carries (GR-133)'s **price** and the standing
   *do not quote §2.5 as supplying freeness* warning. **Reference, not status.** The status:
   **(GR-18)(iii)'s packing-and-split half is a THEOREM** ((GR-130)); its residual is a
   **binary** 9-valued hub CSP, clause (a) **free**, local criterion exact
   ((GR-134)/(GR-135)/(GR-139)) — and GGLOB made it **CSP-FREE**: the packing is a *function*
   of the solution, so what is left is an orientation-plus-two-colourings criterion on `H`
   that **is (GR-10)** here ((GR-140)). Both handles are **dead** — counting by saturation
   ((GR-141)), matroid union by an exhibited exchange failure ((GR-142)) — and the obstruction
   splits **three ways** ((GR-143)): hub-local, propagation-visible (all of the 82 %),
   propagation-invisible from `n_hub = 6`, which that population cannot present. Four
   successors at (GR-144), **successor 1 DEMOTED 2026-09-03** (it *is* (GR-10) here — the
   gap-map `(K-grid)` close-it has not caught up); three live. **(GR-10)/(GR-15) unchanged
   in status.** Everything in §(K-grid)/§(K-out) is *support*, not progress on it. **THE
   2026-07-30 STANDING ADJUDICATION and the two literature-hunt MISSes are RELOCATED
   2026-09-03** to **block 14**; its live consequence stays: carry `hK` pinned, option B NOT
   authorized, and since 2026-08-02 it also carries **(K-res)**. **The mathematics is NOT
   restated here** — canonical home is `notes/Pencil-informal.md`'s **State of (K)** gap map.
   Read that map, not this item, before any (K) work.

**Below the carried items — support work, explicitly ranked lower now.** OGEOM's successors
(the unsearched `n(F°) ≥ 6` frontier; the Kirchhoff-injectivity sentence) are **disproof-risk
reduction**, which by (OC-24) *"can never be the binding obstruction"*; the grid-side residual
(*is the ledger gap ever `≥ 3`?*), OQRANK's residuals and the `2k ∈ {4,6}` corner are ledger
bookkeeping.

**`hsplit` is CLOSED IN FULL** and **`hfresh`'s mechanical discharge (residue (iv))** with it
(W5-L7c-1…6, 2026-07-30); `pencil_conjecture_of_hcontract_hK_hbareSplit_of_card`
(`Molecule/Pencil/Escape.lean`) wraps `..._of_hcontract_hK_hbareSplit`, carrying exactly the
three items above.

> **Route σ — a live candidate on THIS section's list; ranking is §8's, not this
> section's.** Route A at the dual seed `σu`; it would close (K-tight) on the hard stratum,
> *length-free*. **Offered for adjudication**, **not field-blocked**, **not in flight**
> (`notes/Pencil-adjudications.md`: never selected); it moves no gap-map status. It rests on
> **four obligations, only the first of which is Lean** — that one genuinely the hold's, the
> other three dispatchable and two decision-relevant *before* any Lean is commissioned. **The
> four, their `--hunt` findings, the validation scope, the smallest opening commit and the
> not-the-bridge warning are THIRD-COPIED here no longer** (thinned 2026-08-28; the *Field
> scope* caveat left the list 2026-09-03 — **DISCHARGED**, §(K-clos) (AC-1), source-level):
> canonical homes are §(K-σ) *Step σ5*, the **(K-σ)**/**(K-tight)** rows, and
> `notes/Pencil-strategy.md` §8.4. The one clause that is *status* and stays here: **route σ
> is not a route to (K-res)** (obligation 2), so it does not substitute for the wave.
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

- **THE NINTH STRATEGY PASS — THE RE-RANK** (2026-09-03, coordinator, no dispatch) — **ranks
  1–4 ALL SPENT** (BSCOND 76, BARCH 77, GLEAF 80, BINSERT 82); **the list is EXHAUSTED**,
  option B SPENT save its joint sweep. Home: strategy §8.
- **THE LIVENESS DOC ROUND** (2026-09-03; `c89c7adb`…`e5c2f03e`) — **~52 of ~108
  forward-looking entries carried a defect**; rule in `RESEARCH-ARC.md` **§8**, record in
  **block 14**. **The status objects were clean** — the rot was in the recommendation layer.
- **Coordinator round reconciliations** (2026-09-02) — §7's tally **stale by six**; cited,
  never incremented per direction. Three concurrency hazards, two gate blind spots: block 14.

- **BSCOND** (76, opus) — **(BE-57)(iv)'s TWO WINDOW CONDITIONS DECIDED AND THEY WERE ONE
  GAP**: (S1) REMOVABLE, (S2) half theorem / half REFUTED-then-CLOSED. `w4/bscond.py`.
- **BINSERT** (82, recon-opus, **rank 4**) — **OPTION B SPENT: BOTH KT ROUTES REFUTED** at
  `corank(G′)=3`, a **panel collapse**; only its joint sweep left. `w4/binsert.py`.
- **BSERIES** (83, recon-opus, block 10's **entry 2**) — *sharpened-at-one-end* **SPLITS**:
  at ONE clean end **(b2) ⟸ (b1)** class-level by a two-kill law, **CONDITIONAL on
  (PENCIL-SATURATES) at `deg ≥ 2`** (half (B)'s OPEN 0(a)); at BOTH, **no peel** — which **IS
  (BE-45)(iv)**. So **(BE-58)(iv): TWO items + a corner, not four**. `w4/bseries.py`.
- **RPOOL** (75, opus) — **(RS-5) IS REFUTED** by `R20 = family_g(5,(0,0,2),(4,4,4))`,
  `widened.W19` with a longer core, in the recorded pool since 2026-08-02; 30 of 102
  `def = 0` members refute, split by the **per-block** floor. §(K-res) *RS11–RS16*.
- **GLEAF** (80, recon-opus, the ninth pass's **rank 3**, the round of four's last) — **THE
  REACH QUESTION SPLITS: the machinery DOES reach leaf-covering on the branches — an Edmonds
  partition over six `M(G°)/K_j`, criterion `Σ_j ν_j(F) ≤ σ(F)` — and the residual IMPLIES
  it**, so a proof there cannot move (GR-10); only pure hubs can fail and `σ(F) ≥ 1` at every
  proper `F` ((GR-145)–(GR-152), §(K-grid) *G165–G172*). `w4/gleaf.py`.
- **DSAT** (79, recon-opus, the ninth pass's **C2 trace**) — **C2's OWN KILL CONDITION FIRED:
  the motive is UNSAT off the class (PROVED), SAT on it (five shapes)** — struck as a
  *uniform* carry, **not** as a class-only one ((DM-5)–(DM-11), §(K-dom) *D8–D14*). `w4/dsat.py`.
- **OBAR** (78, recon-opus, the ninth pass's **U3 gate**) — **§8.2's U3 GATE IS NEGATIVE
  THREE WAYS, SO U3 IS STRUCK AND U1 IS ALONE**; the unrun ledger had nothing to compute,
  the object being **(T3) restated pointwise** ((OC-56)–(OC-61), §(K-out) *O52–O57*). `w4/obar.py`.
- **BARCH** (77, recon-opus, the ninth pass's **rank 2**) — **THE METHOD CLASS IS NOT DEAD;
  IT CHANGES AMBIENT**; **14 → 12 reduces to the two-sided (E4), UNPROVED** ((BE-149)–(BE-155)). `w4/barch.py`.
- **BDEGTWO** (74, opus, block 8) — **(BE-134)'s TWO GAPS SETTLED; the obstruction the
  ARCHITECTURE** ((BE-136)–(BE-141)) — inside `Λ²K⁴` only, scoped at BARCH. `w4/bdegtwo.py`.
- **BLINE** (73, opus, block 8) — **`(∗)` IS DECIDED: a theorem below `dim A = 3`, FALSE
  from `dim A = 5`, (BE-127)(ii)'s route dying with it**; the clause **OPEN**, 0/270
  ((BE-129)–(BE-135), *BE128–BE134*). `w4/bline.py`.
- **BOPEN** (72, opus, block 8) — **(PENCIL-SATURATES-CHART) IS A THEOREM at every
  side-degree-`1` terminal**, (BE-69) retired as its warrant ((BE-122)–(BE-128)).
- **GGLOB** (71, opus, block 11) — **THE GLOBAL CSP IS CSP-FREE, both handles DEAD, the
  82 % RE-LOCATED**; on this stratum the residual **IS (GR-10)** ((GR-139)–(GR-144),
  *G159–G164*). **E1 does not fire.** `w4/gglob.py`.
- **OWALL** (70, opus, block 12) — **(OC-44)(iii) REDUCED to (OW)**, geometry-free, *Step
  O41*'s attack refuted by LOGIC ((OC-50)–(OC-55), §(K-out) *O47–O51*). `w4/owall.py`.
- **GLIST** (68, opus, block 11) — **(GR-132)'s RESIDUAL: NORMAL FORM, LOCAL HALF EXACT,
  OBSTRUCTION GLOBAL**, 82 % hub-locally feasible ((GR-134)–(GR-138), *G154–G158*).
- **BPROPER** (69, opus, block 8) — **PROPERNESS HALF SETTLED AT EVERY SIDE**
  ((BE-114)–(BE-121)), residues **discharged at BOPEN**. `w4/bproper.py`.
- **BSIGMA** (67, opus, block 8) — **(PENCIL-SATURATES-GEN) FALSE TOO**, its floor a
  **THEOREM** at a path side ((BE-109)–(BE-113)). `w4/bsigma.py`.
- **GPACK** (66, opus, block 11) — **(GR-18)(iii) SPLITS, the split half a THEOREM** off
  `def(G) = 0` ((GR-129)–(GR-133)); exchange freedom **load-bearing**. `w4/gpack.py`.
- **BSATUR** (65, opus, block 8) — **(PENCIL-SATURATES) IS FALSE, THE REPAIR IS FREE**
  ((BE-104)–(BE-108)): a bad plane exists **iff `ρ_i ≥ 5`**, the defect a **quantifier** no
  sampler could see; **SLACK**, repair **-GEN** (itself refuted at BSIGMA).
- **BDOUBLE** (64, 2026-09-02, opus, **one-lined at the GLIST landing**) —
  **(NO-DOUBLE-PENCIL) IS REFUTED and the tight block is REDUNDANT** ((BE-99)–(BE-103),
  *BE98–BE102*), so **14 → 12** blocks — under (PENCIL-SATURATES), itself REFUTED at BSATUR
  and again at BSIGMA; read `-CHART`. `w4/bdouble.py`.
- **BUNIF** (63, 2026-09-02, opus, **one-lined at the GLIST landing**) — **`reach` IS
  PER-SIDE DATA, both directions PROVED**: (BE-67)(iii) ⟺ 14 per-side inequalities,
  (BE-71)(ii) answered generically ((BE-94)–(BE-98), *BE93–BE97*). `w4/bunif.py`.
- **BBASE** (62, 2026-09-02, opus, **one-lined at the GLIST landing**) — **THE FLAG BASE IS
  FREE and is NOT (CH-1)'s object** ((BE-89)–(BE-93), *BE88–BE92*); cyclomatic `≥ 2` open.
- **THE FOUR W4-SIDE LANDINGS (58–61), 2026-09-02 — entries in block 9**, which owns the
  detail. Once: **(T), (E-pair), (V) THEOREMS**, **(E-loc) REFUTED** (`T32`), **(E) TIGHT**,
  **W4's non-user-call list EMPTY** — leaving (K-res) and the held build. `w4/w{tri,eloc,pair,grow}.py`.

**DEMOTED 2026-09-02, EXTENDED 2026-09-03** per this note's oldest-demotes rule; the newest
landing above it is RPOOL (ordinal 75). Settled, one line each:
- **BGENUINE** (57) / **BONEONE** (56) / **BSPREAD** (55) / **BPEEL** (54) / **BDECOR** (53),
  2026-09-01, opus, **all one-lined 2026-09-03 to pay for the ninth strategy pass's entry**
  (the rotation *Doc debt* prescribes at 580/580, not a fold) — cross-cut forcing **GENUINE
  and it does not bite** (392/392); `δ_i` and the R-node test **per-side**; **(BE-32)(+) a
  THEOREM**, star-2/SPREAD retired; half (B)'s class quantifier **one number per peel**,
  exhaustiveness retired; the decorations **a product of ear chains** modulo the cross-branch
  proviso `G`. §(K-bare-ext) *BE63–BE87*; detail in **block 8**.
- **BRNODE** (52) / **BWIN** (51) / **BRULE** (50) / **BSHARP** (49), 2026-08-28…09-01,
  **one-lined 2026-09-03, stale clause corrected 2026-09-08** — the R-node's
  decorated-skeleton law ((BE-59)–(BE-63)); the window closed by a class theorem, **(β)
  proved there — UNCONDITIONALLY since BSCOND, not "modulo (S1)/(S2)"** ((BE-54)–(BE-58));
  **(b3) DECIDED** ((BE-49)–(BE-53)); the (b1) sharpening **FALSE** at a dichotomy.
  §(K-bare-ext) *BE43–BE62*; detail in **block 8**.
- **RESGRID** (48, 2026-08-28, fable) — the (K-res) scoping slice: §(K-grid)'s geometry
  **transports verbatim**, the bookkeeping does not, the deficient fringe **refuted**
  ((RS-6)); residual **(RS-5) since REFUTED** (RPOOL), (RS-1)–(RS-4) stand.
- **BEARFULL** (47) / **BEARCASE** (46) / **BIMAGE** (45), 2026-08-27, opus, **one-lined at
  the DSAT landing** — **SHORT-CYCLE LAW** `girth(Q) ≥ 6`, (b2) a corollary of (b1),
  ear-decomposition **REFUTED**; **(α) CLOSED**, **(β) as stated REFUTED** to (BE-32)(+),
  **since PROVED** ((BE-74)); `ρ̄₂` a **Klein chain** + **series/parallel**. *BE29–BE42*.
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
  record `notes/Pencil-structure.md`). **ROADMAP §39 was split by volatility** — **do not
  re-add a direction count or fan-out roll-call there**; the count is the Status row's.
- **The EIGHTH FAN-OUT — all five LANDED 2026-08-19** (ordinals 25–29): GTMPL, GFLOW, SIGZ
  ((OC-37) killing the counting route to a disproof), OSCHU, GCOLL (**(GR-64)(R2) REFUTED**).
  Four of five corrected a defective spec clause (`notes/dispatch-log.md` **F22**).
- **Directions 1–24 — ALL LANDED 2026-08-05…08-19** (thirteen across the first five
  fan-outs, one per ordinal from the sixth on). **Net: three HITs** — entry 5 PROVEN both
  halves (GBAL, discharging (X)); chart irreducibility PROVEN (CIRR); AA-glue NOT
  realizable at `n_hub = 8` (AGLU) — the rest honest MISSes or OPEN reshapes, each with a
  named successor. **(GR-15) OPEN throughout; E1/E2 never fired; E3 ARMED by GBAL, not
  fired.** Canonical homes `notes/Pencil-fanout{,-archive}.md` + `notes/Pencil-labels.md`.
- **The 2026-08-05 research cluster — RELOCATED 2026-09-03** to `Pencil-structure.md`
  **block 14** (settled history; `Phase39-design.md` + git carry the detail).
- **Pre-fan-out arc (2026-07-24 → 08-04) and the *Promoted out of this phase* pointer list
  — RELOCATED 2026-09-03** to `Pencil-structure.md` **block 14** (settled history + pointers).
## Citations (transcribed, project-canonical sources)

**RELOCATED 2026-09-01** (verbatim) to `notes/Pencil-structure.md` §"Citations — the
phase's verified bibliography (block 7), which carries the per-source venue data and
the verification dates. **Stable reference, not status.** **A direction that verifies a
new source adds it THERE, in its landing commit.**