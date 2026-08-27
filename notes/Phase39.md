# Phase 39 — PENCIL: the hinge-pencil molecular conjecture (work log)

**Status:** in progress — the phase stays OPEN (2026-07-24 adjudication). The target is
**`PencilPair K 3 G`**, and the landed successor
`pencil_conjecture_of_hcontract_hK_hbareSplit_of_card` (`Molecule/Pencil/Escape.lean`)
derives it from exactly **three carried items**: **`hcontract`** (W4 — build parked by the
**2026-08-05 Lean hold**, four informal costs NOT parked), **`hK`** (kernel (K)),
**`hbareSplit`** (kernel (K-bare)). Everything else is closed: W0–W3 and the whole W5 arc
(L0–L7), with **`hsplit` CLOSED IN FULL** and `hfresh`'s counting discharge landed
(2026-07-30).

**The kernel-(K) research arc: 54 directions COMPLETE** (2026-08-05 → 08-27, ordinals
1–46), plus eight strategy-only passes and two architecture probes; **nothing is in flight**.
**Per-direction verdicts, specs and landing write-ups are NOT restated here** —
each direction has one at `notes/Pencil-fanout.md` §"<CODE>" (ordinals 1–19:
`notes/Pencil-fanout-archive.md`) and a canonical mathematical home in the workbooks.
**The arc's standing result, unchanged by all 54: `hK` is not closer.** **(GR-15)** — the
single open gap the whole §(K-grid) chain reduces to — is **untouched**; **class uniformity
of the escape is untouched**; no g-flank was found by any direction; **E3 is ARMED (by
GBAL) and has never fired**.

**NEXT CONCRETE TASK — (BE-32)(+) AS A THEOREM**, the **single named residue** the ear case's
(β) side is now down to: *a graph that forces `π_u = π_v` has `δ_{uv} = 0`*, still **MEASURED**
(208 418 instances, aggressive closure, no argument) — and **two of its mechanisms are already
proved**, (BE-32)(ii)/(iii). BEARCASE **closed (α)**: the reach formula is **PROVED for
`m ≥ 3`** by a reordering-plus-slide, discharging BIMAGE's headline cap. It also **refuted (β)
as stated** (unsatisfiable at `δ₁ ≥ 5`; the correct target is what the landed driver already
tests — no measurement changed) and **collapsed its quantifier** on the attaining locus. Rest
of the ranking: *Hand-off*, **not restated here**. **This is the SEVENTH consecutive direction
in §(K-bare-ext)**, overriding diversification by the max-impact criterion; the **(K-res)
scoping slice** stands deferred a **THIRD** round — a deferral, not a drop — alongside
**(ZH-2)** and **(BE-23)(ii)**.

**On a future HIT: the phase-boundary consequences are the USER's call** —
whether Phase 39 closes and a successor opens for the Lean is a
`PHASE-BOUNDARIES.md` event against the standing 2026-07-24 no-split
adjudication, surfaced with a commit-count estimate, never taken unilaterally;
the 2026-08-05 Lean hold binds regardless of how good the news is.

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

- **Session-headroom calibration — MEASURED 2026-08-26, not argued** (eleventh
  check-in). `weekly_scoped` tracks **fable only** (92 % for a whole session, unmoved
  across four opus recons), so `.claude/commands/coordinate-phase.md`'s *"above ~80 %
  on **either** limit, stagger"* reads as *"above ~80 % on the limit the dispatched
  rung actually consumes"*; `weekly_all` moves **1–2 points per pair-round**. Nothing
  else in the playbook moves.

**Kernel-(K) research arc — sixty-nine docs+scripts-only dispatches landed across 52
directions (ordinals 1–44), plus eight strategy-only passes** (2026-08-02 → 08-26) — and,
**outside** that count because they test the architecture rather than the (K) crux, the
**two probes**, **KBARE-FALSIFY** (2026-08-20) and **C3-AVOID** (2026-08-24), both landed.
The roll call, ordinals, dates and rungs are `notes/Pencil-fanout.md`'s header and its
per-direction sections — **not restated here**; the **dispatch** count moves only on a
landing, and a user call on dispatch *shape* contributes **no** strategy pass. Canonical
homes: `notes/Pencil-informal.md` (**State of (K)** map = entry point),
`notes/Pencil-W4-informal.md` (W4-residual), `notes/Pencil-strategy.md` (strategy). Net
effect: **disproof risk removed**, every refuted route/gap has a successor in the gap map,
several structural positives proven, **route-ledger entry 5 PROVEN** (the arc's first HIT)
— and **class uniformity of the escape remains untouched**. **Doc-debt round CLOSED**
(`notes/Pencil-cleanup.md`, 2026-08-13, category D only; the D-2 fix's regression history
is in `notes/check-gapmap-cells.py`'s docstring).

The other candidate continuations, unselected — items (a)/(g) **DONE** (second-fan-out
directions M and R), each with a canonical home carrying the detail: **(b)** **(K-wit)**, the
pitch route's single live form at companion splits (§(K-Λ)) — its (OC-8) residue now reduces
to chart irreducibility (**DONE**, CIRR) plus input (a), which itself **FACTORS** (**DONE**,
ZNEQ) into a dominated half and the target-rank half (OSCHU, landed 2026-08-19; OQRANK,
landed 2026-08-25); **(c)** the **W4 build**, decomposed and buildable, **PARKED** by the
Lean hold; **(d)** the companion-length dichotomy frame (§(K-dom) *D7*) + the unprobed
`k ≥ 4` parallel-edge item (§(K-pure) *P4*); **(e)** §(K-Λ) item (vii)'s residual, since
LTWO a named, non-empty, floor-classified family; **(f)** strategy §4.6's shortlist,
**partially superseded** for the tight stratum, U3 still unrun. **The current ranking of
what a wave did not pick is `notes/Pencil-fanout.md`'s own losers sections, not this list.**

**Read `notes/Pencil-strategy.md` before choosing anything else** — the strategic record (why
class uniformity resists, the candidate stronger invariants with **C1 run and struck**, §5's
symbolic assessment); its header is its own contents table, and **its §4.6** is the entry
point for any attack on the crux. **Any (K)- or W4-side numerics dispatch starts from
`notes/scripts/README.md`** (a symbolic one also from `notes/scripts/m2/README.md`); detail
in *Blockers*.

## The question and the opening recon

**The question is stated once, in `ROADMAP.md` §39** (the intersection stratum:
each body's hinges both concurrent *and* coplanar, i.e. a pencil of lines through
a point in a plane; in the `G²` molecular reading, every atom's bond-star
coplanar — sp²/planar-bonded atoms; the trivial direction is pencil ⇒ panel per
body, so the content is the **lower bound**, and the all-bodies form implies every
mixed version by rank lower-semicontinuity) — **not restated here**. Two clauses
that section does not carry: the condition only bites at bodies of degree `≥ 3`,
and the two literature hunts after the opening one (2026-07-30 rigidity-side,
2026-08-05 Δ-matroid-side) are both MISSes for **complementary** reasons
(§(K-Δ)) — **this is new mathematics**.

**Opening recon verdicts R1–R3** (landed 2026-07-23) are one-lined in
`ROADMAP.md` §39; the full record, grounding and the W0–W5 decomposition are
`notes/Phase39-design.md`. Three clauses still constrain statements: **R1** pins
the statement in the Phase-35 containment model + `ExtensorThroughPoint` (dual of
`ExtensorInPanel`), satisfiable for every graph and self-dual on-stratum via
`screwComplementIso` (§(K-clos) (AC-1)); **R2**'s queued-warmup claim is
*bar-joint-side* and **false** for body-hinge on dense graphs; **R3**'s three open
cores (outer Thm-5.6 strip-extend, Case-I glue Claim 6.4, Case III Claim 6.12
span break) are what W3–W5 were built against.

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
  eight consecutive direction specs; its *"pin it when the tight side closes"* deferral is
  **RETIRED** by the 2026-08-26 adjudication, which selected the cheap scoping slice now
  queued in *Hand-off*. **(T)/(V)/(E-loc) are slice-sized and need no adjudication; the
  (K-res) WAVE is still a user call.**

- **Doc debt — relief slice LANDED 2026-08-26** (1 500 → 554; record
  `notes/Pencil-structure.md` §"Slice 6"). **The gate is MECHANICAL** —
  `notes/check-phase-note.py` caps this note at **580 lines / 525 status-header words** and
  fails if *Decisions made* outgrows the forward sections. **Live watch, measured at the
  BEARCASE landing: 572/580 lines, 492/525 words.** That landing compressed *Decisions made*
  before it wrote — the 2026-08-25 fable run, GHWIT/GMINM/OGEOM, and the two probes each
  folded into one grouped entry — and the **same move is the next landing's first step**;
  their canonical homes are `notes/Pencil-fanout.md` + the workbooks. A landing's entry is
  **one line**; the (BE-14) thread's five prose entries are the standing exception, and the
  oldest of them demotes when the thread's next direction lands.
- The full biconditional transport (design doc's W0 pin) is landed only as its two forward
  implications; the reverse arms need a `complementIso` involution lemma, not in tree —
  deferred, **off every critical path** (§(K-σ) *Step σ6*).
- **Harness debt — four rounds PAID, FOUR ITEMS OUTSTANDING.** Canonical home
  `notes/scripts/README.md` *Harness debt* (its own header carries the current
  paid/outstanding split) — **read it before any numerics dispatch**: it also carries the
  two deliberately-unfixed *Recorded observations* and the rule for a dispatch that trips
  §2 rule 2 again (record the item naming every consumer; do **not** modify the landed
  file). The open items are `zneq.ledger` (deferred on purpose — it needs a commit that can
  re-run `oschu --gtarget` / `--census1` / `--census2`, figure invariance being discharged
  by re-running, not by inspection), the `kbare/` sibling imports, OQRANK's two arrivals,
  and the reversal-model sibling imports on `gprice.py`/`gblaw.py`/`gxesc.py`.

## Hand-off / next phase

**The phase stays OPEN** (the 2026-07-24 adjudication — no phase-close; see *Current state*).

**THE NEXT CONCRETE TASK — (BE-32)(+), the EAR CASE'S SINGLE NAMED RESIDUE.** The
strengthened 2-cut lemma **is** (BE-14) (decomposition exhaustive; base
`{3-connected}` ∪ `{max deg ≤ 2}` ∪ `{def₂ = def₃}` free, 1-cuts (BE-18),
statement **PINNED** as **S-mark**, simultaneity **VACUOUS** (BE-25)(i)). BIMAGE
bounded and classified its residual geometric sentence for the **ear**; BEARCASE
then **PROVED (α)** — the reach formula holds for `m ≥ 3` — **refuted (β) as
stated** and **collapsed its quantifier**, leaving one residue.
**BEARCASE's ranked successors, which supersede BIMAGE's:**

1. **(BE-32)(+) as a theorem** — *a graph that forces `π_u = π_v` has
   `δ_{uv} = 0`*. The **single named residue** of the ear case on the (β) side:
   everything else reduces to generic-position statements about one piece, and
   **two of its three mechanisms are already proved** ((BE-32)(ii)/(iii), a common
   triangle and `≥ 3` common neighbours). Still MEASURED only — 208 418 instances
   under the **aggressive** closure, which over-claims forcing, so an empty sweep
   is the stronger statement but not an argument.
2. **(b2) for a general piece** — the middle clause of (BE-37)(ii)'s reduction.
3. **The internal R-node** ((BE-31)(ii)) — the step from ear to general piece;
   (BE-25)(iii) closes the **leaf** R-node only, and BEARCASE's independent
   sampler now reaches R-node pieces.
4. BTWOCUT's successor (2), the **bundle-construction proof** — (BE-29)(ii) from
   rung to theorem, reaching `DZ` / `spider(5,5,5)+c`. Skipped twice.

Also ranked, unchanged: BTWOCUT's cross-pair closure ((BE-28)(i), motive economy
only — S-mark closes) and the point-side flat law (**priced NOT cheap**); and from
BINDUC **(BE-23)(ii)** (*forced flat ⇒ `def₂ = def₃`*), the disproof side's
highest-value single search. **Superseded, do not re-derive:** (BE-27)(ii) refuted
the reading that the residual gauge group supplies general position — *the gauge
group was never the right place to look*.

Also unclaimed, from BZAVOID's own successor ranking: a **flat-star dictionary** —
re-prove `molecular_finrank_motions_eq_square_ker`'s surjectivity under a hypothesis
admitting coplanar stars, which would revive route 2 (§(K-bare-ext)).

**THEN — the (K-res) SCOPING SLICE**, deferred a **SECOND** round by the
max-impact directive (2026-08-27) and NOT dropped. One direction: *does (GR-15)/§(K-grid) transport to
the `W19`-type (K-res) habitat?* This is the
user's 2026-08-26 adjudication (offered the full wave, the cheap scoping slice,
or a re-deferral, they chose the **scoping slice**), and it retires the stale
*"pin it when the tight side closes"* deferral — the coordinator hand-off note
that had sat unresolved in this section since the arc opened — **without**
commissioning a wave at an `hK`-class kernel. After it, pick the next off the
target-ordered list below.

**THE CANDIDATE LIST lives in `notes/Pencil-strategy.md` §8 — the option board** (new
2026-08-20): every live route priced in one place, with the two filters that kill most
candidates on sight (growing-ground-set; counting saturation, now closed in **both**
directions by (OC-3)/(OC-37)). **Not restated here** — and the board, not this section,
carries the current ranking. **Not eligible:** route σ's **obligation 1** and the W4
**build** — those, and only those, are held by the hold. **The §9 Zheng shelf** (unpriced,
deliberately off §8's board, an **idea source and never a citation**) is down to **one
dispatchable candidate, (ZH-2) stratified**: (ZH-1)/(ZH-4) STRUCK, (ZH-3)
struck-by-absorption, (ZH-5) a design note, (ZH-6) write-up material — provenance, caveats
and order in strategy §9.

**DO NOT RE-OPEN — what the recent landings closed.** From **BZAVOID**: the
forced-degeneration cap as a refutation route for **any** graph ((BE-15); cap-free for the
**triangle** mechanism, the general one MEASURED only — a proof of **(BE-23)(ii)** would
restore it in full and is the disproof side's highest-value single search); the landed
Phases-24–26 `G²` apparatus, whose general-position gate is the **literal negation** of the
pencil condition ((BE-17)); and the **transversality/dimension count** ((BE-16)(iv)). From
**ZJACOB**: the determinantal / scheme-theoretic package is a **conservation law** — it
converts expected codimension *into* structure with **no theorem producing it** over a
non-generic base, so any route getting properness from a codimension count, a Jacobian
criterion or Cohen–Macaulayness is answered by §(K-jac) before it starts. From **ZSHEAR**:
`Q(r̃) ≠ 0` is `PGL(4)`-invariant, so **no gauge-fixing can ever supply it**. From
**GHWIT/GMINM**: per-matching (b′) at the constant 2 is FALSE and the `min_M` reading is
PROVEN — **do not re-open either**.

**THE THREE CARRIED ITEMS, RANKED BY DISTANCE TO THE PHASE TARGET** (the 2026-08-26
directive; *Current state*'s delegation bullet), replacing the
previous-direction's-successor-order convention that produced five consecutive directions
on a ledger residual the ledger does not consume. **The target is `PencilPair K 3 G`, and
exactly these three stand between the landed theorem and it. Rank accordingly.**

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
   all 52 directions**, and the only one of the three with **no named next slice**.
   Everything in §(K-grid)/§(K-out) is *support* for this, not progress on it. **Standing
   adjudication ("C: literature hunt + A", 2026-07-30): carry `hK` pinned; option B NOT
   authorized**; both literature hunts are MISSes, and since 2026-08-02 it also carries
   **(K-res)**. **The mathematics is NOT restated here** — canonical home is
   `notes/Pencil-informal.md`'s **State of (K)** gap map (per gap: status, what would close
   it, uncovered shapes, a *settled, do not re-derive* block). Read that map, not this
   item, before any (K) work.

**Below the carried items — support work, explicitly ranked lower now.**
OGEOM's successors (the unsearched `n(F°) ≥ 6` frontier; the Kirchhoff-
injectivity sentence) are **disproof-risk reduction**, which by (OC-24) *"can
never be the binding obstruction"*; the grid-side residual (*is the ledger gap
ever `≥ 3`?*) is ledger bookkeeping; OQRANK's residuals and the `2k ∈ {4,6}`
corner likewise.

**`hsplit` is CLOSED IN FULL** (W5-L7c-1…6, landed 2026-07-30) and **`hfresh`'s mechanical
discharge (residue (iv)) is CLOSED too**. The landed successor
`pencil_conjecture_of_hcontract_hK_hbareSplit_of_card` (`Molecule/Pencil/Escape.lean`) wraps
`pencil_conjecture_of_hcontract_hK_hbareSplit` and carries exactly the three items above.

> **Route σ — the one live candidate, and it is NOT settled.** Route σ = route A at the dual
> seed `σu`; it would close (K-tight) on the hard stratum, *length-free*, via
> `Λ²Π̂(b) + Λ²Π̂(c) + α_{pt(b)} = K⁶`. **Offered for adjudication**, **no longer
> field-blocked** (§(K-clos): the polarity generalizes, `ℝ` the *narrowest* choice); it moves
> no gap-map status and changes no standing constraint. **It rests on FOUR obligations, and
> only the first is Lean.** Canonical home for all four, the `--hunt` findings, the validation
> scope and the *Field scope* caveat: §(K-σ) *Step σ5* (`notes/Pencil-informal.md`); priced in
> `notes/Pencil-strategy.md` §8.4. **Obligation 1 is
> genuinely the hold's** — §(K-σ)'s own verdict is *"Lean engineering against a landed
> pattern, **not new mathematics**"*; smallest commit when opened:
> `exists_common_seed_pencilRow_and_polynomials` (`Engine.lean:476`, chart **total**);
> **`exists_pencilSeed_of_nondeg` (`Reseed.lean:65`) is NOT the bridge** (circular).
> **Obligations 2–4 are NOT Lean, NOT blocked, and NOT in flight**, two of them
> decision-relevant *before* any Lean is commissioned: **(2)** scope — the `dim R_a = 0`
> stratum untouched and the **(K-res)** habitat unsampled, so **route σ is not a route to
> (K-res)** even fully built; **(3)** (σ6)'s failure direction **unwitnessed**
> (`predAfalse = 0/47`); **(4)** the branch it closes has **never been observed nonempty**,
> so its value is **insurance, not repair**.
>
> **Two durable negatives from the 2026-08-07 adjudication — do not re-run:** §4.6's
> shortlist is **partially superseded** for the tight stratum (U2 delivered by (GR-16)'s
> reduction; U3's negative-form insight already exploited); the symbolic meta-option
> ("upgrade §(K-Λ) via M2") is **landed, not pending** (`m2/lambda0.m2`) — only §5.3 item
> (i) remains, ruled out by §5.3's own local-frame feasibility boundary.
> **Not open, and not re-litigated per wave:** the **(FR-6) follow-ons** ((ii)/(iv)
> un-commissioned; **(iii)** struck by (OC-17)), the unselected leads (b)–(f) in *Current
> state*, and route σ / W4. **Deliberate non-goals — do not re-derive, re-sweep, or
> re-open:** (Λ0), (Λ1), the `g₁₄` clause, §(K-ind), §(K-Δ), §(K-clos)'s field question,
> §(K-ann)'s settled batch ((ANH-1)–(ANH-6), (SD-6)) and §(K-out)'s settled batch
> ((OC-1)–(OC-7); pinned, disjoint pools) — including "does the polarity generalize?",
> (D2)'s far block, POOL-G/POOL-S, a counting/matroid route to (OUT)'s hypothesis ((OC-3)
> refutes the whole class), or `lambda.py`'s figures (slice **S3**'s carve-out is spent).

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

**One-line verdicts, reverse-chronological** (`notes/CLAUDE.md` *Forward-weighted note*:
a settled decision keeps full prose only while upcoming work might lean on it — the four
(BE-14) entries do, the rest do not). Each direction's *mathematics* is in the workbook
section named; its *spec and landing write-up* in `notes/Pencil-fanout.md` §"<CODE>"
(`notes/Pencil-fanout-archive.md` for ordinals 1–19); the *user call that picked it* in
`notes/Pencil-adjudications.md`; the derivation in git. **Do not grow these back into
paragraphs.**

The (BE-14) thread the next task sits on — five entries, kept at prose length:

- **BEARCASE** (46, 2026-08-27, opus) — **(α) CLOSED**: the greedy's last step is a complete
  criterion (**the 2-step lemma**), its bad case a **scheduling** artifact, and a
  **reordering + slide** removes it ⟹ **the reach formula is PROVED for `m ≥ 3`**
  (constructed, 1 432/1 432); no fourth mechanism at `m ≤ 2`. **(β) as stated REFUTED**
  (unsatisfiable at `δ₁ ≥ 5`; a **propagated prose defect**, no measurement changed), its
  quantifier **COLLAPSED** on the attaining locus, and the (β) side reduced to the single
  residue **(BE-32)(+)**. §(K-bare-ext) *BE34–BE37*.
- **BIMAGE** (45, 2026-08-27, opus) — BTWOCUT's *"nothing bounds that image"* **REFUTED**:
  the ear's `ρ̄₂` is the span of a **chain on the Klein quadric** (a bijection; the
  coordinator's hypothesis CONFIRMED, plus three confinement laws it missed), its bad locus
  is **three mechanisms**, exactness MEASURED 358/358, every trap a **configuration
  artifact** (607/607). Off the ear an exact **series/parallel recursion** replaces the
  refuted path-intersection bound, residue the **internal R-node**; three merge-inequality
  theorems + `δ ≤ dist` empty at 542 893. **Ear case REDUCED, not proved.** §(K-bare-ext)
  *BE29–BE33*.
- **BTWOCUT** (44, 2026-08-26, opus) — strengthened statement **PINNED** (S-mark closes,
  S-all does not), simultaneity worry **VACUOUS**, leaf base free, BINDUC's 56 ear misses
  cleared as a constructor artifact, general-position half **dissolved on everything
  swept**; **(BE-14) NOT proved**, reduced to one geometric sentence. §(K-bare-ext)
  *Steps BE24–BE28*.
- **BINDUC** (42, 2026-08-26, opus) — **3-connected ⇒ `def₂ = 0`**, so the induction's
  **base is FREE**; BZAVOID's 2-cut `− 6` **REFUTED**, replaced by an exact `max`-law;
  (BE-14) proved at 5 824 further graphs; the general new-cap mechanism fires empty,
  **scope-correcting (BE-15)(ii)** to the triangle mechanism only. §(K-bare-ext) *BE19–BE23*.

Settled, one line each:

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
