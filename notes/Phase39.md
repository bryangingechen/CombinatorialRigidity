# Phase 39 — PENCIL: the hinge-pencil molecular conjecture (work log)

**Status:** in progress — the phase stays OPEN (2026-07-24 adjudication). The target is
**`PencilPair K 3 G`**, and the landed successor
`pencil_conjecture_of_hcontract_hK_hbareSplit_of_card` (`Molecule/Pencil/Escape.lean`)
derives it from exactly **three carried items**: **`hcontract`** (W4 — build parked by the
**2026-08-05 Lean hold**; informal side CLOSED as an argument), **`hK`** (kernel (K)),
**`hbareSplit`** (kernel (K-bare)). Everything else is closed — W0–W3, all of W5
(L0–L7), `hsplit` and `hfresh` (2026-07-30, unchanged since).

**The research arc: 121 directions COMPLETE** (2026-08-05 → 09-12, ordinals **1–113** —
116 on kernel (K), **WTRI/WELOC/WPAIR/WGROW (58–61) on W4**, **RPOOL (75) on (K-res)**; direction
= ordinal + 8), **none in flight**, plus **seventeen** strategy passes (the seventeenth,
2026-09-12, the first to RE-ROUTE a lane rather than re-order it; board at
§8's head), two probes, a scoping recon. **GPACK (66) opened the
`hK` lane**; roll calls are §8's, per-direction verdicts `fanout.md`'s. **Standing result,
unchanged: `hK` is not closer.** **(GR-15)** and **class uniformity untouched**; no g-flank;
**E3 ARMED (GBAL), NEVER fired** — **block 14**.

**`hK` LANE (66, 68, 71, 80):** (GR-18)(iii)'s split half a THEOREM, residual CSP-FREE and **IS**
(GR-10) at `D = 0`; ESCAPE (OWALL 70) REDUCED to (OW), **U3/C2 STRUCK**. **THE `G°` INDUCTION
UNDER A LOCAL MOVE FAMILY IS STRUCK** (GBASE 108, (GR-233)–(GR-240)): its base contains `CL_m`
past `m > (c+1)/2`, where (GR-34) proves no uncorrelated charging can close — **a BASE lemma is
(GR-15) with its easy half deleted** — and the base share rises to a **constant**
(`0 → 20.5 → 27.7 → 30.3 %`, isomorphism-class unit), so the induction reduces **≈ 70 %**.
Transport's second obstruction is **named and avoidable** ((GR-241)–(GR-248)) and the lift's
draw cap runs **both ways** ((GR-244)). **THE ROUTING CONSEQUENCE IS THE USER'S CALL.**
**(GR-10)/(GR-15)/(OC-8) unchanged**. Blocks **11–13**.

**W4's INFORMAL SIDE IS CLOSED** (58–61): (T)/(E-pair)/(V) **THEOREMS**, (E) **open and off every
path**, list **EMPTY** — leaving the USER call **(K-res)** and the held build. Block **9**.

**THE (BE-14) THREAD** — S-mark its **only open step**; detail **block 8**, settled history
`fanout.md`'s. **Live:** (β) **UNCONDITIONAL** at the window, outside it **TWO items + a corner**
((BE-142)–(BE-171)); at `deg ≥ 2` the item is **OPEN** — (E4), `(BE-E4′)`, `Γ`-properness and the
whole **ARC class** REFUTED or EXHAUSTED ((BE-156)–(BE-224)); the `Π_x` obligation is
**DECOMPOSED, top rung free**, residue **30** tuples, its four successors **REFUTED as
universals** and **intact at (Q-gen)**, the obligation itself **UNTOUCHED and OPEN**
((BE-225)–(BE-270)). **BOTH halves hang on it**; **OPEN** at 0/772 + 0/411. **`⟨M⟩` is CLOSED BY
PROOF** ((BE-272)/(BE-277)) — the path lemma, **stronger** than (BE-259)(i)'s shape — so **three
of three routes to a rung-3 `Good = ∅` piece are closed**, the remaining **12** blocks stay
**unwitnessed, NOT excluded**, and the residue **is** (BE-259)(ii)'s question one dimension down:
**one lemma discharges both**.

**On a future HIT the phase-boundary consequences are the USER's call** — a `PHASE-BOUNDARIES.md` event against the 2026-07-24 no-split adjudication, surfaced with an estimate, never unilateral; the 2026-08-05 Lean hold binds regardless.

**FIFTEEN reference blocks in `notes/pencil/structure.md`** — read once per session. The **State
of (K)** gap map is this phase's status object, **authoritative for every status word**; read it
with `python3 notes/gapmap.py`, never `sed`/`grep`.

## Current state

**The phase stays OPEN.** Standing user adjudications, verbatim (these are the live GO/NO-GO
constraints; the **dated dispatch/selection narrative for every ordinal, 1–44, is
`notes/pencil/adjudications.md`**, quoting the user byte-for-byte, and git):

- **2026-07-24:** *"Let's leave the phase open and continue the work on the conjecture in this
  phase. Unless there's a good reason to split here."*
- **2026-07-30 (both kernels) / 2026-08-02 (W4) — RELOCATED VERBATIM 2026-09-03** to
  `notes/pencil/adjudications.md`: the same day's *declines are not locks* directive demotes
  them to **history**. `hK`/`hbareSplit` stay **pinned** (a claim about the proof, not a bar);
  W4's build is parked **by the Lean hold**, not by the 2026-08-02 call.
- **2026-08-05, the standing reproducibility requirement:** *"in general, I would like all of
  the scripts we run to be committed for reproducibility"* — now a hard rule of the harness
  (`notes/scripts/README.md`); every script the project runs is tracked, probes included.
- **2026-08-05 → 08-26, the selection history for ordinals 1–44, ARCHIVED IN FULL.**
  Every dated adjudication/delegation bullet that picked a direction is in
  `notes/pencil/adjudications.md` **verbatim** (1–19 moved 2026-08-19, 20–44 moved
  2026-08-26). **None changes a standing constraint** beyond what the next three
  bullets summarize. Read there for the exact quotes — including the 2026-08-19 SIGZ
  authorization terms and the 2026-08-20 `(GR-R1)`/`(GR-C1)`/`(GR-C2)` rename call
  (collision record: `notes/pencil/labels.md`).

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
  **design pass**, unparked by the hold; the `hbareSplit` one is now **SPENT OUTRIGHT**,
  INSJOINT 90) and **(K-res)**'s cheap slice + flank. **NOT
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
`notes/pencil/fanout.md`'s header and per-direction sections, **the only place they are
maintained** (this note's copy has gone stale before). Counting rules: the count moves only
on a **landing**; a user call on dispatch *shape* is **no** strategy pass; the two probes
(KBARE-FALSIFY, C3-AVOID) sit outside it. Net effect: **disproof risk removed**, every
refuted route/gap has a gap-map successor, **entry 5 PROVEN**, **class uniformity
untouched**. **Doc-debt round CLOSED** (`notes/pencil/cleanup.md`, 2026-08-13).

**The other candidate continuations, unselected — RELOCATED 2026-08-29** (verbatim) to
`notes/pencil/structure.md` §"The unselected candidate continuations": items (a)/(g) **DONE**,
(b)–(f) each with a canonical home carrying the detail. Stable reference, not status by its
own last sentence — **the current ranking of what a wave did not pick is
`notes/pencil/fanout.md`'s own losers sections, not that list.**

**Read `notes/pencil/strategy.md` before choosing anything else** — the strategic record (why
class uniformity resists, the candidate stronger invariants with **C1 run and struck**, §5's
symbolic assessment); its own header is its contents table and **its §4.6** is the entry point
for any attack on the crux. **Any (K)- or W4-side numerics dispatch starts from
`notes/scripts/README.md`**; detail in *Blockers*.

**The question, and opening recon verdicts R1–R3 — RELOCATED 2026-08-28** (verbatim) to
`notes/pencil/structure.md` §"The question and the opening recon": the `ROADMAP.md` §39
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
  and the standing remedy is **relocation or merger, never a fold** — **FIFTEEN** reference
  blocks now sit verbatim in `notes/pencil/structure.md`, indexed by its own table, with no
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

**PARALLEL HARNESS TRACK, not blocking this one** — `notes/Harness-structure.md`
(slices 8–14 + the review/tagging/taxonomy passes LANDED; **§D6 + §D7 = the NEXT round's diagnosis**, D7 instrumented post-hoc; kill conditions on each). Use **`/coordinate-research`**, not
`/coordinate-phase`. `python3 notes/ledger.py --label '(BE-216)' | --brief | --round |
--frontier | --delta | --lint` answers "what is proved" in one call (`--stats` for the live claim census — never quoted here, D6.8; `--backlog` ranks the tagging worklist, `--label` flags CONTESTED
claims where a later row supersedes an earlier); the corpus is now one file per section under `notes/pencil/` with its own
CLAUDE.md (gap map: `notes/pencil/workbook/gapmap.md`).

**THE (BE-14) THREAD, settled frame + its last landings — RELOCATED 2026-09-02** to
`notes/pencil/structure.md` §"The (BE-14) thread — per-landing detail" (**block 8**); the
write-ups and the `(K-bare)` gap-map row stay authoritative. **Reference, not status.** The
status that stays here: **S-mark is (BE-14)'s only open step**, (β) is proved at the window
**modulo (BE-57)(iv)'s (S1)/(S2)**, half (B)'s residue is **item 1 of the workbook's four**
((BE-121)(i); 2–4 are item 0's (b)/(c)/(d)) — item 1 being **(PENCIL-SATURATES-CHART)**, a
**THEOREM at every side-degree-`1` terminal** ((BE-127)) and **OPEN** at side-degree `≥ 2`,
where BLINE killed the `(∗)` route ((BE-130)) — and cross-pair welding is **untouched**.

**THE W4 DEVIATION'S PER-LANDING DETAIL — RELOCATED 2026-09-02** to
`notes/pencil/structure.md` **block 9**: the thread is untouched since WGROW (61) and its
informal argument is **closed**. Status is in the header, not repeated here.

**BBASE (62) → BSATUR (65) — RELOCATED 2026-09-08** to **block 8**, which already owned the detail; the one *status* clause, **(CH-1) does not apply to the flag base** ((BE-89)), is in the header.

**THE 2026-09-02 ROUND'S PER-LANDING CLAUSES (66–72) — RELOCATED 2026-09-02** to
`notes/pencil/structure.md` **block 13**; blocks 8/11/12 already own the detail. **Reference,
not status.** The two clauses that stay: **no gap-map status word moved at any of the six,
and BOPEN (72) closes half (B)'s item 1 at side-degree `1`** (block 8), and **the `hK` lane's ranking is
`notes/pencil/strategy.md` §8's board, NOT this list** (re-ranked `70c06abe`/`5583a919`; it
carries the standing **do-not-do** — no more (a′)/(b′) ledger directions), whose ranks 1 and
3 are spent.

**THE NEXT CONCRETE TASK is the EIGHTEENTH §8 pass and a round off it.** The seventeenth pass's round of three is **COMPLETE and LANDED** (BSIXTEEN 111, GODDRUNG 112, BPROPCL 113), **spending ranks 1, 2 and 3 together for the FOURTH consecutive round**. **BPROPCL (113) closed rank 3: the shared residue is NOT A LEMMA — it is a ONE-DRAW CERTIFICATE.** Properness is a property of **one peel**, and one draw with `a_i = 0`, `ρ_i = δ_i ≤ 5`, `c_i(U) < dim U` **proves** it there, composing rows 2, 3 and 4 of (BE-255)(i) in three different semicontinuity directions — **certified at 375/375 eligible rows and 15/15 in the `dist ≥ 6` regime**. What is **not** supplied is the **class** statement the two clauses intend, and the two are different objects. **The mechanism both clauses name is FALSE** (general position against `Λ²K⁴`, exceeded at 102 of 1 281 at `Π_x`, by a proved saturation mechanism). **THE CROSS-RETURN REVERSAL:** BPROPCL's headline through six steps was *"the two residues are NOT one question"*; **BSIXTEEN landed mid-run** proposing the `⟨P₀⟩`-relative repair, BPROPCL **tested** it at **1 281/1 281**, and so **(BE-277)(iii) is REFUTED in its own frame and CONFIRMED in BSIXTEEN's** — two directions fenced off each other's lemma converging on one. **The corner stays LIVE at 248/248** with `max δ = 4`, so `ρ_i ≤ 5` is **not tight** ((BE-291)–(BE-298)). **The eighteenth pass's open successors, in the round's own words:** the **class** statement over all internal R-node peels; **(BLOCK-GP)** at `dim ⟨P₀⟩ ∈ {4,5}`; **uniform `dim Z = 0`** for GODDRUNG's repaired colouring; and one axis a coordinator must route — **whether `Chart(H) → Chart(side_i)` is dominant**, which conditions every side-row figure on the `hbareSplit` lane. **GODDRUNG (112) LANDED**, closing rank 2: **the parity obstruction is NOT essential and the criterion was never parity** — (GR-37)(ii) already gives it as **cut-space membership**, `k = 2a` with `a` the number of cyclic arcs of the odd-rung set. **Decisive witness `m = 6`:** all six rungs odd, `k = 0`, `τ = 0`, **no obstruction**, and the landed rule still fails — on the **mono-hub** conjunct. **The REPAIRED rule is admissible, NC1-clear and FULLY-GOOD at every even `m` from 6 to 40** (`n_hub = 12…80`, **18/18**, exact-ℚ, cap-free). **Two landed sentences fall:** (GR-239)(ii)'s *even-rung-length slice* is **SCOPED** (measurement stands, criterion does not) and **(GR-34)(ii)'s *"one deviating hub"* is REFUTED — it is TWO**. **But F26 lowers the payoff:** a uniform **rule** is not a uniform **(GR-15) argument**, and nothing landed consumes (GR-15) on a subfamily — so §8's stated payoff is refuted and the successor is **uniform `dim Z = 0` for the repaired colouring over all `m`**, the only thing left between the repair and uniform (GR-15) on `CL_m` ((GR-249)–(GR-256)).** **BSIXTEEN (111) LANDED**, closing rank 1: **the eleven are NOT eleven problems.** (BE-30)(iv) names **no block**, so `c_i(U) ≤ dim(⟨P₀⟩ ∩ U)` holds pointwise at **all sixteen** and the right-hand side is a closed-form table `B(m, U) = max(|U ∩ {Π_x, Π_y}|, m + dim U − 6)` (4 480 cells asserted, **13 664/13 664** on `Chart(H)`, reproducing (BE-258)(iii)'s and (BE-272)(ii)'s columns unfitted). **Two more blocks close cap-free** (`⟨L⟩`, `⟨M⟩⊕⟨L⟩`) and **the other nine reduce to ONE named candidate, (BLOCK-GP)** — so `Good ≠ ∅` at rung 3 follows from **one lemma, not eleven**. **Three by-products:** the hoped-for block-sum **inheritance lemma is FALSE** (`c_i` is superadditive, exact-ℚ witness, strict at 7 120/10 000); **(BE-259)(i)'s threshold extends to `dist_i ≤ 5`**; and **`Σδ ≤ dim U + 5`** is proved, so *"higher rungs are free"* is **false in general**. **AND THE SCOPE LIMIT THAT CORRECTS §8's OWN FRAMING:** `π_u = π_v` is **FORCED at 392 of 928** internal R-node peels ((BE-81)), all rung-3, where the four blocks do not decompose the screw space — so closing all sixteen proves `Good ≠ ∅` at rung 3 **in the generic flag regime only**, the coincident-flag arm staying a per-piece theorem and **class-level OPEN** ((BE-278)–(BE-285)). **The round as dispatched was:** **`BSIXTEEN`** (`(BE-278)`–`(BE-290)` / *Steps BE277–BE289*), **`GODDRUNG`** (**the correlated colouring rule at ODD rung lengths** — the only shape (GR-34) leaves open, attacked at the parity failure GBASE located; `(GR-249)`–`(GR-256)` / *Steps G269–G276*) and **`BPROPCL`** (**the shared residue** — one properness lemma making (BE-259) and (BE-274) unconditional at once, 248 of 2 946 in-region peels; `(BE-291)`–`(BE-298)` / *Steps BE290–BE297*); then the EIGHTEENTH pass off what they return. **THE SEVENTEENTH PASS LANDED 2026-09-12** (coordinator-authored, no dispatch spent, no label minted) and is the **first to RE-ROUTE a lane rather than re-order it**: with the `G°` induction struck ((GR-238)), weight moves to the `(BE-14)`/`hbareSplit` lane and the `hK` lane keeps **one** entry — the correlated rule, because (GR-34) proves that is the only shape a proof of (GR-15) can have. **Three inherited successors are DEMOTED, not retracted** (GSECOND's `T↑∃∃` successors, GBASE's `n_hub = 10` residual, the transport gate generally): a positive on any of them closes nothing while the base stands. New bar **(o)**: no entry may be ranked on advancing the `G°` induction under a local move family. **PROVENANCE OF THE RE-ROUTE:** the sixteenth pass put the routing question to the user with four options; the answer was *"per your best judgment"* — **a DELEGATION, not a ruling**, so a future pass may revisit it freely on evidence, and it does NOT carry the force of the 2026-07-24 no-split adjudication or the 2026-09-12 local-move ruling. **The round as dispatched off the sixteenth pass was:**

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
   **(b) [MARGIN] — EXHIBITED 2026-09-12** after five directions reported it unexhibited:
   BWHOLEH's certificate gives `margin = 2+1−2−0 = **+1** > 0` at `Π_x`, confirmed at the `H`
   layer by (BE-250)(i) (`dim M(H) = 7` vs `6`). **The item is EXISTENTIAL, so the steering
   that bounds BWHOLEH's headline verdict is sufficient here, not a weakness** ((BE-267)); **(c) [BLOCKS]** the **11** live blocks, `⟨M⟩` empty at 93 rows
   ((BE-121)(i), 72 + 21 — **not** (BE-108), whose figure is 72); **(d) [NON-ATTAIN]** the
   non-attaining case, **INHABITED, NOT ACTIVATED** ((BE-120)/(BE-121)(i)). **Cite the TAG,
   never the letter** — why: block 14. **Three siblings, all closed — do not re-hunt**:
   cross-cut forcing (BGENUINE), the flag base (item 1), the forced-empty `G` hunt ((BE-72)).

1. **THE FLAG BASE — DISCHARGED by BBASE** (verdict in *Decisions made*); its three cheap
   leftovers (is `B_real` a forest on the class; cyclomatic `≥ 2`; is a triangle necessary)
   are **RELOCATED** to `notes/pencil/structure.md` **block 8**.
2.–4. **THE LANE'S STANDING MENU — RELOCATED 2026-09-02** to
`notes/pencil/structure.md` §"The (BE-14) lane's standing candidate list" (**block 10**):
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

**THE CANDIDATE LIST lives in `notes/pencil/strategy.md` §8 — the option board** (new
2026-08-20): every live route priced in one place, with the two filters that kill most
candidates on sight (growing-ground-set; counting saturation, now closed in **both**
directions by (OC-3)/(OC-37)). **Not restated here** — and the board, not this section,
carries the current ranking. **Not eligible:** route σ's **obligation 1** and the W4
**build** — those, and only those, are held by the hold. **The §9 Zheng shelf** (unpriced,
deliberately off §8's board, an **idea source and never a citation**) is down to **one
dispatchable candidate, (ZH-2) stratified**; the per-item provenance, caveats and order are
strategy §9's, not restated here.

**DO NOT RE-OPEN — what the recent landings closed: RELOCATED 2026-08-29** (verbatim) to
`notes/pencil/structure.md` §"What the recent landings closed" — BZAVOID's three (incl. the
**`G²` apparatus**), ZJACOB, ZSHEAR, GHWIT/GMINM. Stable reference, not status; every item's
own gap-map row carries the same close.

**THE THREE CARRIED ITEMS, RANKED BY DISTANCE TO THE PHASE TARGET** (the 2026-08-26
directive; *Current state*'s delegation bullet; the superseded successor-order convention and
its cost are `notes/dispatch-log.md`'s and `notes/pencil/fanout.md`'s). **The target is
`PencilPair K 3 G`; exactly these three stand between it and the landed theorem. Rank accordingly.**

1. **`hbareSplit`** (kernel (K-bare), research) **via (BE-14), direct attainment** — *the
   pencil stratum attains `6(|V|−1) − def₃(G)`*, hard step now the **strengthened 2-cut
   composition lemma, PINNED as S-mark** ((BE-23)(e)); BATTAIN's `Y° ⊄ Z(G)` (*Step BE12*,
   not BE13) is that same target one framing up. **The most target-moving statement the arc
   currently owns:** seed-free, induction-free, never uses `¬PencilNondegFeasible`, and it
   discharges `hbareSplit` **and** `PencilPair`'s unconditional conjunct at once, as a
   **standalone theorem** (the phase's own 2026-08-05 bar). Dearer in absolute terms,
   cheaper in structure. Carried as pinned; **OPTION B IS SPENT OUTRIGHT** (BINSERT 82,
   INSJOINT 90) — **(K-bare-ext) REFUTED on BOTH KT routes** by a panel collapse, and its last
   endpoint (the joint sweep) **EXCLUDED**; link 2 stays discharged (§(K-ins)). **WHY IT IS
   *CARRIED* — RELOCATED 2026-09-03** to `notes/pencil/structure.md` **block 14**: the
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
   identification recon" and `notes/pencil/workbook/W4.md`.
3. **`hK`** (kernel (K), research) **via (GR-15)** — the escape `≢ 0` uniformity kernel,
   the phase's hardest open item and what the arc attacks: **untouched by every kernel-(K)
   direction through BSCOND (ordinal 76)** — name the last ordinal, never a count (SWEEP C;
   this line carried two mutually inconsistent tallies until 2026-09-03) — but GPACK (66),
   GLIST (68) and GGLOB (71) reshaped its named next slice.
   **THE LANE'S PER-LANDING DETAIL IS RELOCATED 2026-09-02** to
   `notes/pencil/structure.md` §"The `hK` lane — per-landing detail" (**block 11**), the
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
   restated here** — canonical home is `notes/pencil/workbook/gapmap.md`'s **State of (K)** gap map.
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
> (`notes/pencil/adjudications.md`: never selected); it moves no gap-map status. It rests on
> **four obligations, only the first of which is Lean** — that one genuinely the hold's, the
> other three dispatchable and two decision-relevant *before* any Lean is commissioned. **The
> four, their `--hunt` findings, the validation scope, the smallest opening commit and the
> not-the-bridge warning are THIRD-COPIED here no longer** (thinned 2026-08-28; the *Field
> scope* caveat left the list 2026-09-03 — **DISCHARGED**, §(K-clos) (AC-1), source-level):
> canonical homes are §(K-σ) *Step σ5*, the **(K-σ)**/**(K-tight)** rows, and
> `notes/pencil/strategy.md` §8.4. The one clause that is *status* and stays here: **route σ
> is not a route to (K-res)** (obligation 2), so it does not substitute for the wave.
>
> **The durable negatives and the deliberate non-goals — RELOCATED 2026-08-28** (verbatim)
> to `notes/pencil/structure.md` §"Durable negatives and deliberate non-goals": the two
> 2026-08-07 do-not-re-run items, the *not re-litigated per wave* list, and the
> do-not-re-derive/re-sweep/re-open batch. Stable reference, not status.

**Gates for any continuation — RELOCATED 2026-08-28** (verbatim) to
`notes/pencil/structure.md` §"Gates for any continuation": which gate fires on which file
type, and the figure-invariance discharge. Stable reference, not status; read it once per
session alongside the *Conventions* block relocated there 2026-08-27.

## Adjacent directions (orientation only, not this phase)

The queue is `ROADMAP.md`'s *Queued post-program phases*: ORIGAMI (`notes/Origami.md`), the
bar-joint-side analog, is next; the unqueued survey, incl. IDENT-PANEL, is `notes/IdeaBacklog.md`.

## Decisions made during this phase

**One-line verdicts, reverse-chronological** (`notes/CLAUDE.md` *Forward-weighted note*:
a settled decision keeps full prose only while upcoming work might lean on it — the four
newest (BE-14) entries do, the rest do not). Each direction's *mathematics* is in the workbook
section named; its *spec and landing write-up* in `notes/pencil/fanout.md` §"<CODE>"
(`notes/pencil/fanout-archive.md` for ordinals 1–19); the *user call that picked it* in
`notes/pencil/adjudications.md`; the derivation in git. **Do not grow these back into
paragraphs.**

- **THE NINTH STRATEGY PASS — THE RE-RANK** (2026-09-03, coordinator, no dispatch) — **ranks 1–4 ALL SPENT**, the list **EXHAUSTED**; ordinals in the header. Home: strategy §8.
- **THE LIVENESS DOC ROUND** (2026-09-03; `c89c7adb`…`e5c2f03e`) — **~52 of ~108 forward-looking entries carried a defect**; rule in `RESEARCH-ARC.md` **§8**, record in **block 14**. **The status objects were clean** — the rot was in the recommendation layer.
- **Coordinator round reconciliations** (2026-09-02) — §7's tally **stale by six**; cited, never incremented per direction. Three concurrency hazards, two gate blind spots: block 14.

- **BSCOND** (76, opus) — **(BE-57)(iv)'s TWO WINDOW CONDITIONS DECIDED AND THEY WERE ONE GAP**: (S1) REMOVABLE, (S2) half theorem / half REFUTED-then-CLOSED. `w4/bscond.py`.
- **BINSERT** (82) + **INSJOINT** (90), recon-opus, **rank 4** — **OPTION B SPENT OUTRIGHT**:
  both KT routes REFUTED at `corank(G′)=3` by a **panel collapse**, last endpoint EXCLUDED
  (`need′ − need = dim U′ − dim U` preserves the deficit; `≥ 2` was route A's `need`, (INS-15)). `w4/{binsert,insjoint}.py`.
- **BSERIES** (83, recon-opus, block 10 **entry 2**) — *sharpened-at-one-end* **SPLITS**: at
  ONE clean end **(b2) ⟸ (b1)**, **CONDITIONAL on (PENCIL-SATURATES) at `deg ≥ 2`**; at BOTH
  **no peel**, which **IS (BE-45)(iv)**. **(BE-58)(iv): TWO items + a corner.** `w4/bseries.py`.
- **RPOOL** (75, opus) — **(RS-5) IS REFUTED** by `R20 = family_g(5,(0,0,2),(4,4,4))`, `widened.W19` one generator parameter along and in the pool since 2026-08-02; 30 of 102 `def = 0` members refute. §(K-res) *RS11–RS16*.
- **GLEAF** (80, recon-opus, ninth pass **rank 3**) — **THE REACH QUESTION SPLITS**: an
  Edmonds partition over six `M(G°)/K_j` DOES reach leaf-covering and the residual **IMPLIES**
  it, so no proof there moves (GR-10) ((GR-145)–(GR-152), *G165–G172*). `w4/gleaf.py`.
- **DSAT** (79, recon-opus, ninth pass **C2 trace**) — **C2's KILL CONDITION FIRED: UNSAT off
  the class (PROVED), SAT on it** — struck as a *uniform* carry ((DM-5)–(DM-11), *D8–D14*). `w4/dsat.py`.
- **OBAR** (78, recon-opus, ninth pass **U3 gate**) — **U3 NEGATIVE THREE WAYS, STRUCK, U1 ALONE**; the unrun ledger was **(T3) pointwise** ((OC-56)–(OC-61), *O52–O57*). `w4/obar.py`.
- **GEXPAND** (96, §8's rank 1) — **NO ADDITIVE EXPANSION MOVE EXISTS AT `D = 0`, BY A PROOF**: (GR-25)(i) at the complement of the new hubs is an excess-boundary cap, refuted by (SD-6) for every `|E_ss|` ((GR-170)/(GR-171)); zero-net-excess is an **identity**, so the entry's mechanism was a tautology ((GR-169)); `CL_m` in-habitat for all `m ≥ 6` makes the stratum **infinite** ((GR-175)). §(K-ind) (I4) strengthened ((GR-176)). `w4/gexpand.py`.
- **GSIMUL** (98, §8's rank 4) — **SPLIT**: the simultaneous island repair is settled by ONE **shared** pair (predicted disjoint mechanism a theorem firing 0/26), instrument **2 492/2 492** once searched, (GR-153)(d) extends to `n_hub = 8` by (GR-25)'s cut criterion, open from 10 ((GR-185)–(GR-192)). Four corrections to one-day-old prose; all GISLAND verdicts survive. `w4/gsimul.py`.
- **GFORCE** (97, §8's rank 2) — **THE HANDLES CLOSE AND THE ENTRY IS STILL REFUTED**: a monotone parameter-free closure, sound at 0/7 224, certifies **4 of 18** separators and is **INCOMPARABLE** with (GR-9) ((GR-177)–(GR-181)); a **third** handle, unpredicted and a theorem, takes it to **14/18** with a 567+41 residual dichotomy ((GR-183)/(GR-184)). **Struck §8's rank 3 in passing** — the unconstrained tree-triple is not sufficient for `κ < ∞` ((GR-182)). `w4/gforce.py`.
- **GISLAND** (94, §8's rank 1) — **THE `Λ ≠ ∅` STRATUM IS SWEPT COMPLETE**: `lamcap` fence removed, **166 088** shapes, **0** NC1 and **0** rank misses, orbit control 40/40 — *Step G28* residual 4 CLOSED, **E1 does not fire** ((GR-157)); the island owns a **proven** repair instrument on a parity law ((GR-153)–(GR-156)); (GR-26)(iii) REFUTED ((GR-158)). **(GR-15) untouched.** `w4/gisland.py`.
- **GCOIND** (95, §8's rank 2) — **SPLIT: the `r = 4` collapse criterion IS COMBINATORIAL, the class it was hunted in IS NOT.** `C(H₊) = ⊕_j C(H₊ − E_j)` is parameter-free and poly-time over the complete 3 128-partition population, so value-independence at `r = 4` is a **THEOREM** and a negative becomes a proof ((GR-163)/(GR-164)); the counting/closure class is **REFUTED** at 4 of 9 blocks ((GR-167)); any certificate forces an **unconstrained** tree-triple ((GR-165)). **(GR-15) untouched.** `w4/gcoind.py`.
- **BCORNER** (93, research-direction-opus, §8's rank-1 successor) — **`(BE-OBL)` IS REFUTED AND THE OBLIGATION IS UNTOUCHED**: 62 certificates on BSIGMA's **landed** `degenerate_peel` (`ρ=(5,5)`, `c=(2,1)`, `a=(0,0)`, in-regime), all at `Σδ ∈ {10,11}` — **rung 1**, where (BE-225)(i) already made the obligation free — so the kill is wholly over-strength and the obligation **holds 62/62**; the added hypothesis is **GRASSMANN-FREE** at `ρ_j ≥ 5` (62/62), refuting (BE-228)(iii)'s *"exactly"* and (BE-227)(i)'s *"equivalent"*; successor **`(BE-OBL7)` ∧ `(BE-OBLK)`**, 4 tuples ((BE-231)–(BE-238)). `w4/bcorner.py`.
- **BOBLIG** (92, recon-opus, §8's rank-1 successor) — **THE NAKED OBLIGATION IS *DECOMPOSED*,
  TOP RUNG FREE**: a three-rung `Σδ` ladder (`≥ 8` TRUE hypothesis-free, `= 7` *not both fire*, `≤ 6` **IS** (NO-DOUBLE-PENCIL)), residue EXACTLY **30** `a = 0` tuples at `max ρ ≤ 5`, the modular-law route **CIRCULAR**, successor **`(BE-OBL)`** = item 0(a) ∧ `c_j(Π_x) ≥ 1`; and the **UN-FENCED `deg₁(x) = 2` population is the FIRST to reach the quantifier** — 0 violations at 135/135, residue reached 0 ((BE-225)–(BE-230)). `w4/boblig.py`.
- **BNONUNI** (91, recon-opus, §8's rank-2 successor) — **`(BE-E4′)` IS DECIDED, DEAD BOTH
  WAYS, and rank 2 has NO SUCCESSOR**: FALSE below `ρ₁+ρ₂ = 6` (REFUTED at 14 gated in-regime peels on a **non-uniform** profile), **IS** the `Π_x` obligation above it at `a = 0`, relaxation zone **NON-ATTAINABLE** ((BE-219)–(BE-221)). Successor: the **naked obligation** ((BE-223)). `w4/bnonuni.py`.
- **BGTWOA** (89, recon-opus, §8's rank 2) — **THE BSTEER LIFT FAILS AND THE FRONTIER IS EXHAUSTED**: `e_j ≥ ρ_j − 2` is free, so `(BE-G_2)`'s content is only `ρ_j ∈ {2,3}`, DISJOINT from BSTEER's `ρ_j = 1`, and it is FALSE at 4/4 fully-gated IN-REGIME peels by **(BE-175)(i) ITSELF** on the non-firing side — both added hypotheses index **side 2** — so all five members die; **`(BE-F_4)` IS `ρ_i ≥ 4`** ((BE-210)–(BE-216)). Its *"(BE-E4′) UNREFUTED"* verdict is **SUPERSEDED at BNONUNI**. `w4/bgtwoa.py`.
- **BEFOURP** (88, recon-opus, **frontier since EXHAUSTED at BGTWOA**) — **(BE-E4′) DECOMPOSED**: coverage a **SUM** ((BE-204)); the 245 die exactly on `f+g ≥ 6` ((BE-205)); **`α_x` IS `Σ_x`** ((BE-206)); `(BE-F_5)` REFUTED, **FLAG REGIME LOAD-BEARING** ((BE-207)–(BE-209)). `w4/befourp.py`.
- **BLONGARC** (87, recon-opus) — **THE SPEC'S QUESTION IS NO, THE LADDER EXTENDS ANYWAY**: one **α-space** count closes item 0(a) at arc `≤ 5` (**48/99**) and the **path-bound CLASS is SPENT** at (BE-189)(iii)'s own threshold ((BE-196)–(BE-203)). `w4/blongarc.py`.
- **BRANKV** (86, recon-opus) — **THE POINTWISE CLAUSE IS FALSE** at 24/24 gated arc-3 points;
  the same radical closed item 0(a) at arc `≤ 3`, **15/99**, subsumed by BLONGARC ((BE-188)–(BE-195)). `w4/brankv.py`.
- **BGPROP** (85, recon-opus, the tenth pass's **rank 1**) — **BRIDGE TRANSPORTS, LEMMA FALSE**
  at 10/99 by a codim-6 floor; 53/99 class-uniformly proper ((BE-180)–(BE-187)). `w4/bgprop.py`.
- **BSTEER** (84, recon-opus, (BE-162)(iii)) — **NO: `ρ̄₂` cannot be steered into `Π_x`**; `(BE-E4′)` SURVIVED its `δ₂ = 1` boundary by a **degree count at `x`** ((BE-172)–(BE-177)), since SUPERSEDED at BNONUNI. `w4/bsteer.py`.
- **BFOUR** (81, recon-opus, (BE-154)(iv)) — **(E4) IS FALSE** at `K4(5,2,2,2,2,2)` reflagged,
  ATTAINING, every gate green; the named population could not have found it ((BE-156)–(BE-163)). Detail: **block 8**. `w4/bfour.py`.
- **BARCH** (77, recon-opus, rank 2) — **THE METHOD CLASS CHANGES AMBIENT**; 14 → 12 reduced to (E4) ((BE-149)–(BE-155)). Detail: **block 8**. `w4/barch.py`.
- **BDEGTWO** (74, opus, block 8) — **(BE-134)'s TWO GAPS SETTLED; the obstruction the ARCHITECTURE, inside `Λ²K⁴` only** ((BE-136)–(BE-141)). `w4/bdegtwo.py`.
- **BLINE** (73, opus, block 8) — **`(∗)` IS DECIDED: a theorem below `dim A = 3`, FALSE from
  `dim A = 5`**; the clause **OPEN**, 0/270 ((BE-129)–(BE-135), *BE128–BE134*). `w4/bline.py`.
- **BOPEN** (72, opus, block 8) — **(PENCIL-SATURATES-CHART) A THEOREM at every side-degree-`1` terminal**, (BE-69) retired ((BE-122)–(BE-128)).
- **GGLOB** (71, opus, block 11) — **THE GLOBAL CSP IS CSP-FREE, both handles DEAD**; on this
  stratum the residual **IS (GR-10)** ((GR-139)–(GR-144), *G159–G164*); E1 does not fire. `w4/gglob.py`.
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
- **BDOUBLE** (64, 2026-09-02, opus) — **(NO-DOUBLE-PENCIL) IS REFUTED and the tight block
  REDUNDANT** ((BE-99)–(BE-103), *BE98–BE102*), so **14 → 12** under (PENCIL-SATURATES),
  itself refuted at BSATUR and BSIGMA; read `-CHART`. `w4/bdouble.py`.
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
  record `notes/pencil/structure.md`). **ROADMAP §39 was split by volatility** — **do not
  re-add a direction count or fan-out roll-call there**; the count is the Status row's.
- **The EIGHTH FAN-OUT — all five LANDED 2026-08-19** (ordinals 25–29): GTMPL, GFLOW, SIGZ
  ((OC-37) killing the counting route to a disproof), OSCHU, GCOLL (**(GR-64)(R2) REFUTED**).
  Four of five corrected a defective spec clause (`notes/dispatch-log.md` **F22**).
- **Directions 1–24 — ALL LANDED 2026-08-05…08-19** (thirteen across the first five
  fan-outs, one per ordinal from the sixth on). **Net: three HITs** — entry 5 PROVEN both
  halves (GBAL, discharging (X)); chart irreducibility PROVEN (CIRR); AA-glue NOT
  realizable at `n_hub = 8` (AGLU) — the rest honest MISSes or OPEN reshapes, each with a
  named successor. **(GR-15) OPEN throughout; E1/E2 never fired; E3 ARMED by GBAL, not
  fired.** Canonical homes `notes/Pencil-fanout{,-archive}.md` + `notes/pencil/labels.md`.
- **The 2026-08-05 research cluster — RELOCATED 2026-09-03** to `pencil/structure.md`
  **block 14** (settled history; `Phase39-design.md` + git carry the detail).
- **Pre-fan-out arc (2026-07-24 → 08-04) and the *Promoted out of this phase* pointer list
  — RELOCATED 2026-09-03** to `pencil/structure.md` **block 14** (settled history + pointers).
## Citations (transcribed, project-canonical sources)

**RELOCATED 2026-09-01** (verbatim) to `notes/pencil/structure.md` §"Citations — the
phase's verified bibliography (block 7), which carries the per-source venue data and
the verification dates. **Stable reference, not status.** **A direction that verifies a
new source adds it THERE, in its landing commit.**