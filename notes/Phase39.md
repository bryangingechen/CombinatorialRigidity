# Phase 39 — PENCIL: the hinge-pencil molecular conjecture (work log)

**Status:** in progress — phase stays OPEN (standing user adjudications of 2026-07-24 /
2026-07-30 / 2026-08-02, quoted verbatim in *Current state*). W0–W3 and the whole W5 arc
(L0–L7) are COMPLETE — `hsplit` CLOSED IN FULL and `hfresh`'s counting discharge landed
(2026-07-30). Only three items remain, all carried by the landed successor
`pencil_conjecture_of_hcontract_hK_hbareSplit_of_card` (`Molecule/Pencil/Escape.lean`):
`hcontract` (W4), kernel `hK`, and kernel `hbareSplit` — see *Hand-off*. **Sixteen
kernel-(K) fan-out directions plus CFLANK, GCAP, GUNIF, GEXIST, GORIENT, GDEV, GADM, GPSA,
GDESC, GBAL and GLAW are now COMPLETE** (2026-08-05 → 08-19; per-direction theorem chain in
*Decisions made*). Headline positives **(FR-R1) PROVEN** and the (GR-16)–(GR-60) theorem
chain; GUNIF refuted both its targets; GEXIST/GORIENT/GDEV/GADM (honest MISSes /
form-refutations) re-anchored the target on the growth-law form, shift-metric layer proven
UNBOUNDED; **GPSA** proved entry 5's parity half; **GDESC** reshaped the balance half into
a matching-flexibility statement without closing it; **GBAL** (the FIFTEENTH direction,
LANDED 2026-08-19) **PROVED (GR-54), the balance theorem: route-ledger entry 5 is PROVEN in
both halves, a HIT** — discharging input (X) and re-deriving GPSA's parity half without
Petersen. **GLAW** (the SIXTEENTH direction, LANDED 2026-08-19, one of five concurrent
sixth-fan-out directions, `notes/Pencil-fanout.md` §"Sixth fan-out") is an **honest MISS
carrying four theorems and one refutation on (a′)**: (GR-55)–(GR-58) give (a′) coordinates
and verify it EXHAUSTIVELY on the whole `n_hub ≤ 6` stratum at no cap; (GR-59) REFUTES the
stronger per-matching variant (`min_M` load-bearing); (GR-60) names the residual **input
(Y)** — GBAL's input (X)'s whole-graph/proper-chunk counterpart by (GR-56)(iv), though
GBAL's proof does **not** transfer to it. **E3 stays ARMED (by GBAL's HIT) but does NOT
fire**: entry 1's **(a′)** stays open, no bar. **(GR-15) stays OPEN throughout; class
uniformity untouched by every round; no g-flank at any of the sixteen.** **Next concrete
task: land the remaining three sixth-fan-out drafts, in order — FRES, then OCON, then
LTWO** (OCON's landing depends on FRES's section existing; each already returned as its
own untracked `notes/Pencil-draft-<CODE>.md`) — see *Hand-off*. Direction codes are
**multi-letter and topic-tagged from the fifth fan-out on** (`notes/Pencil-labels.md`
(L5)); grandfathered single letters are re-used across dates — **always date those**.

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
  them; cap lifted, rescue §1 pre-authorized (`notes/Pencil-fanout.md` §§"Second"–"Fifth").
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
  LANDED 2026-08-13 (`notes/Pencil-fanout.md` §"Seventh direction"). Same check-in: top rung
  = fable (opus only if the weekly limit runs out); cap **lifted**; rescue §1 mechanical
  fixups **pre-authorized** — all still binding.
- **2026-08-13, phase-shape adjudication (changes no standing constraint).** Offered the four
  options GUNIF's refutation raised, the user answered, verbatim: *"I think we should continue
  with the research here, but perhaps not in this session. Are we ready for handoff to a fresh
  session?"* — **RESOLVED: the research arc CONTINUES** (not packaging-and-stopping); nothing
  else moved, selection falling back to the standing 2026-08-07 delegation.
- **2026-08-13/14, ninth- through eleventh-direction selections (changed no standing
  constraint).** All three picks **re-delegated to a top-rung fable recon** (second through
  fourth uses of the 2026-08-12 shape); verdicts **GEXIST**/**GORIENT**/**GDEV** verified
  and **ACCEPTED** (`notes/Pencil-fanout.md` §§"Ninth"–"Eleventh"), landed 08-13/13/15.
- **2026-08-17, twelfth-direction selection (BROKE the fable-recon streak; changed no
  standing constraint).** Offered three shapes, the user chose **coordinator-authored prep
  from GDEV's routing clause** — *"Cheaper, but no independent ranking of the losers."* — so
  GADM's spec and ranking record are the coordinator's (a future top-rung recon may overturn
  its bars freely). GADM **PREPPED and LANDED 2026-08-17**.
- **2026-08-18, thirteenth-direction selection (returned to the fable-recon shape; changed
  no standing constraint).** The user elected **"Delegate the pick to a fable recon"** — the
  **fifth** use of the 2026-08-12 shape, because the coordinator-authored twelfth prep had no
  independent ranking of the losers. Verdict **GPSA** (entry 5, BOTH halves; (b′) secondary)
  **verified and ACCEPTED, including its OVERRIDE of GADM's shift-metric routing clause**;
  every GADM bar upheld, the override targeting the routing clause only
  (`notes/Pencil-fanout.md` §"Thirteenth direction"). Same check-in: **all four rungs
  dispatchable**, cap **lifted**, rescue §1 fixups **pre-authorized** (standing). GPSA
  **LANDED** the same day.
- **2026-08-18, fourteenth-direction prep — NO selection, and a recorded rung
  down-substitution (changes no standing constraint).** GPSA's landed otherwise-clause
  routed the fourteenth deterministically (*"entry 5 stuck with a named blocking
  configuration → that configuration"*), its stuck branch instantiated by GPSA's own
  landing — the routing rests on landed mathematics, unlike the GADM clause it overrode, so
  **no selection pass was run**. The user adjudicated the *prep* to the **opus** rung against
  a top-rung-mapped task (weekly_scoped at 83%; **fable conserved for the research
  dispatch**) — a deviation logged in `notes/dispatch-log.md`; cost disclosed as the
  twelfth's was (no independent top-rung reader of the *ranking*), the *primary* being fixed.
  **GDESC dispatched at fable and LANDED 2026-08-18** (`notes/Pencil-fanout.md` §"Fourteenth
  direction"); the **FIFTEENTH is NOT dispatched** — its routing is a coordinator/user call
  between input (X) and (a′).
- **2026-08-19, sixth-fan-out dispatch — a NEW shape (user-adjudicated multidispatch;
  changes no standing constraint).** Asked how to proceed with the unrouted fifteenth, the
  user elected a **multidispatch of five concurrent opus directions**, verbatim: *"I'd like
  to try a multidispatch of opus agents here. Keep an eye on the 5h session limits and
  let's dispatch as many agents as we can on independent directions so that we can
  maximize the number of ideas we make progress on at once without getting interrupted."*
  Five directions dispatched concurrently — **GBAL**/**GLAW** (compute-licensed tier),
  **OCON**/**LTWO**/**FRES** (derivation-first tier), tier split and label reservations
  coordinator-set (`notes/Pencil-fanout.md` §"Sixth fan-out"). **GBAL LANDED 2026-08-19** —
  route-ledger entry 5 PROVEN in both halves, a HIT, discharging input (X); E3 ARMED, not
  fired. **GLAW LANDED 2026-08-19** — an honest MISS: (a′) gets coordinates, an exhaustive
  verification and a proven constraint on any proof (`min_M` load-bearing); residual named
  input (Y); E3 still not fired. OCON/LTWO/FRES: draft returned, landing pending.

**Kernel-(K) research arc — forty-one docs+scripts-only dispatches, plus seven
strategy-only passes** (2026-08-02 → 08-19; the second the 2026-08-12 fable recon, the third
through fifth the 2026-08-13/08-14 ninth-, tenth- and eleventh-direction selection recons, the
sixth the 2026-08-18 thirteenth-direction selection recon, the seventh the 2026-08-18
**fourteenth-direction prep** — an opus design pass that made **no** selection, the routing
being fixed; **the twelfth's pick was coordinator-authored at the user's 2026-08-17 election,
so it contributed no pass**; the sixth fan-out's multidispatch election is a user call on
dispatch *shape*, not a selection recon, so it contributes no pass either). The count moves
only on a landing; GBAL's is the fortieth, GLAW's the forty-first. Canonical homes: workbook
`notes/Pencil-informal.md` (**State of (K)** map = entry point), `notes/Pencil-W4-informal.md`
(W4-residual), `notes/Pencil-strategy.md` (strategy); one line per landing in *Decisions
made*, canonical with git — **not restated here**. Net effect: **disproof risk removed**,
every refuted route/gap has a successor in the gap map, several structural positives
proven, and **route-ledger entry 5 is PROVEN, the arc's first HIT**; **class uniformity of
the escape remains untouched by all forty-one dispatches.**

**Doc-debt round CLOSED — `notes/Pencil-cleanup.md`** (2026-08-13, category D only; D-5 a
watch item; the D-2 fix regressed at GORIENT's landing, re-repaired `07f6f9b6`).

> **The one live candidate, and it is NOT settled — `notes/Pencil-informal.md` §(K-σ)** (the
> canonical home for the four obligations, the `--hunt` findings, the validation scope and the
> *Field scope* caveat; the *Hand-off* blockquote below carries the forward half — neither is
> restated here). **Route σ** = route A run at the dual seed `σu` (the polarity replaces every
> body's point by its own panel normal); it would close (K-tight) on the hard stratum,
> *length-free*, via `Λ²Π̂(b) + Λ²Π̂(c) + α_{pt(b)} = K⁶`. A **candidate offered for
> adjudication**, resting on four obligations (the first shrunk to two conditions, 2026-08-05)
> and **no longer field-blocked** (2026-08-06, §(K-clos): the polarity generalizes, `ℝ` the
> *narrowest* field choice). Standing consequences: no gap-map status moves on account of
> route σ; `hK`/`hbareSplit` stay carried as pinned; **W4 stays PARKED**; the phase does
> **not** close.

The other candidate continuations, unselected (items (a)/(g) are **DONE** as second-fan-out
directions M and R); each has a canonical home carrying the detail, not restated here: **(b)**
**(K-wit)**, the pitch route's single live form at companion splits (§(K-Λ); the (OC-8) residue is
a **containment** question, §(K-out) *Steps O9–O12*); **(c)** the **W4 build** — decomposed,
buildable, **PARKED** by the 2026-08-05 Lean hold; **(d)** the companion-length dichotomy frame
(§(K-dom) *D7*) + the unprobed `k ≥ 4` parallel-edge item (§(K-pure) *P4*); **(e)** §(K-Λ) item
(vii)'s residual (no swept family realizes one); **(f)** strategy §4.6's ranked shortlist,
**partially superseded** for the tight stratum (durable negatives in *Hand-off*); U3 still unrun.

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

**Next concrete task: LAND the remaining three sixth-fan-out drafts, in order — FRES, then
OCON, then LTWO** (OCON's landing depends on FRES's section existing). All five directions
of the sixth fan-out (dispatched 2026-08-19 by explicit user multidispatch adjudication,
`notes/Pencil-fanout.md` §"Sixth fan-out") have returned; **GBAL and GLAW landed the same
day** — full verdicts in this note's top `**Status:**` paragraph and in *Decisions made*,
**not restated here** (in one clause: entry 5 PROVEN both halves, a HIT, input (X)
discharged; (a′) an honest MISS with input (Y) named, `min_M`'s per-matching variant
REFUTED; E3 ARMED, not fired). The remaining three (OCON/LTWO/FRES targets recorded at
their own landings) are draft-complete, awaiting coordinator verification and serial
landing per the standard checklist (`notes/Pencil-fanout.md` §"Landing checklist"). Labels
claimed: GBAL **(GR-49)–(GR-54) / Steps G68–G73**, GLAW **(GR-55)–(GR-60) / Steps
G74–G79**; the next unclaimed tail is **(GR-61)+ / Steps G80+** (`notes/Pencil-labels.md`).
No standing constraint moves: phase OPEN, Lean hold STANDS, W4 PARKED, `hK`/`hbareSplit`
pinned, option B un-commissioned.

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
> **The FIRST through SIXTEENTH directions are ALL COMPLETE** — roll call (with commit
> hashes for the first five) is one-lined with dates in *Decisions made*; the delegations
> that picked the SIXTH through FIFTEENTH under them are in *Current state*'s dated
> bullets; not repeated here. **No g-flank found by any of them; (GR-15) stays OPEN, unchanged, modulo (GR-4′); no
> gap-map status moves.**
> **Two durable negatives from the same adjudication — do not re-run:** (i) §4.6's shortlist
> is **partially superseded** for the tight stratum (U2 delivered by (GR-16)'s hub-multigraph
> reduction; U3's negative-form insight already exploited by the cap/budget style); (ii) the
> symbolic meta-option ("upgrade §(K-Λ) via M2") is **landed, not pending** (`m2/lambda0.m2`) —
> only §5.3 item (i) (whole-graph elimination) remains, ruled out by §5.3's own local-frame
> feasibility boundary.
> **The NINTH through SIXTEENTH directions — GEXIST, GORIENT (both 2026-08-13, honest
> MISSes), GDEV (2026-08-15, a REFUTATION-with-successors), GADM (2026-08-17, an honest
> MISS carrying a theorem and a refutation), GPSA (2026-08-18: entry 5's parity half
> PROVEN), GDESC (2026-08-18: entry 5's balance half RESHAPED, a route dissolved), GBAL
> (2026-08-19: entry 5 PROVEN in BOTH halves, a HIT) and GLAW (2026-08-19: an honest MISS
> giving (a′) coordinates, an exhaustive stratum verification and a proven per-matching
> refutation) — landed the theorem block (GR-32)–(GR-60).** Per-direction records are
> canonical in `notes/Pencil-fanout.md` §§"Ninth"–"Sixteenth direction"; the mathematics
> itself — including the bounded-deviation form-refutation ((GR-42)/(GR-43)), the
> binding-capable obstruction family ((GR-36)/(GR-40)), the W3 stick split and the (a′)
> support figures — lives in workbook §(K-grid) *Steps G38–G79* **and its *State of (K)*
> gap-map row, the canonical home for (K) status — not restated here.** What binds forward,
> beyond what the gap map already carries:
> - **The cross-entry finding (GLAW, by (GR-56)(iv)):** GDESC's **input (X)** (the
>   whole-graph balance instance) and GLAW's **input (Y)** (the proper-chunk full-goodness
>   instance) are the two instances of ONE inequality. **(X) is now PROVEN** by GBAL's
>   (GR-54) — but the proof does **not** transfer to (Y): GBAL's argument is a whole-graph
>   instrument, (Y) is quantified over every proper chunk, a genuinely different question,
>   and no step of GBAL's argument was localized to a chunk. **(Y) stays open, sharpened by
>   (X)'s proof, not discharged by it.**
> - **Ledger entry 5 PROVEN in BOTH halves — a HIT** ((GR-54)): an entry-5 HIT alone still
>   does NOT close the `Λ = ∅` `D = 0` existence target and does NOT itself fire E3 — it
>   **ARMS** E3, and **(a′)** (now also carrying input (Y)) is the *only* thing left.
> - **Every direction's TERMINATION check fired nothing except arming E3** (E1/E2 NO
>   throughout — GBAL's (GR-54) proves `d_adm = ∞` can **never** fire at `Λ = ∅`, `D = 0`;
>   GLAW's (GR-59) refutes only the per-matching variant, never (a′) itself). The **sixth
>   fan-out's remaining three drafts** are the next-task slot at the top of this section, not
>   a routing call.
> **Coordinator hand-off note, still not loaded onto any direction:** whether (GR-15) as
> quantified ("every tight class shape") also covers the `W19`-type **(K-res)** sibling
> habitat is unresolved — pin it when the tight side closes, not before.
> **Not selected at the 2026-08-07 adjudication**, and so not open: the **(FR-6) follow-ons**
> (§(K-frame) *What would change this* (ii)–(iv) — the `ℓ_min = 5` battery beyond θ(3,4,5), the
> (FR-7) irreducibility foothold, the (AC-9) anti-correlation's structurality), the unselected
> leads (b)–(f) above, and the parked Lean half of route σ / the W4 build.
> Deliberate non-goals: (Λ0), (Λ1), the `g₁₄` clause, §(K-ind), §(K-Δ), **§(K-clos)'s field
> question**, **§(K-ann)'s settled batch** ((ANH-1)–(ANH-6), (SD-6)) and **§(K-out)'s settled
> batch** ((OC-1)–(OC-7); the two pools are pinned and **disjoint**) are **done** — do not
> re-derive, re-sweep, re-run their literature hunt, re-open "does the polarity generalize?",
> re-measure (D2)'s far block, re-sample POOL-G or POOL-S, **propose a counting / matroid route
> to (OUT)'s hypothesis** ((OC-3) refutes the whole class), or touch `lambda.py`'s figures — the
> one carve-out, the re-baselining round's slice **S3**, is **spent** (it coded the landed (Λ0f′)
> in place of (Λ0f) and moved the one figure it was licensed to, `outer.py --geom`'s).
> Standing constraints — W4 PARKED (fully decomposed and buildable, no build without a fresh
> adjudication), `hK`/`hbareSplit` pinned, option B un-commissioned in both kernel cases — all
> unchanged; see *Current state*.

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
**`notes/check-gapmap-cells.py` before any gap-map edit — §(K-grid)'s status cap was
bumped to 2035 at the 2026-08-19 GLAW landing (closeit cap unchanged at 873; reasons for
both 2026-08-19 bumps recorded in the script); append past that and the NEXT landing must
RECOMPUTE the cell instead.**

## Adjacent directions (orientation only, not this phase)

ORIGAMI (`notes/Origami.md`, next queued) is the bar-joint-side analog; the wider unqueued
survey — incl. IDENT-PANEL, the nearest neighbour — is `notes/IdeaBacklog.md`.

## Decisions made during this phase

Reverse-chronological, one line per landing; full derivations live in git,
`notes/Phase39-design.md`, and (for the (K) arc) the workbook section named in each entry, which
is the canonical home a successor reads.

- **The FIFTEENTH and SIXTEENTH directions — GBAL and GLAW, both LANDED 2026-08-19**
  (`w4/{gbal,glaw}.py`; canonical home §(K-grid) Steps G68–G79). Two of five concurrent
  directions of a user-adjudicated **sixth fan-out** (GBAL/GLAW/OCON/LTWO/FRES,
  `notes/Pencil-fanout.md` §"Sixth fan-out"). **GBAL is a HIT — the arc's first**: a z-form
  change of coordinates chains ((GR-49)–(GR-53)) to **(GR-54), the balance theorem** —
  route-ledger **entry 5 PROVEN in both halves**, discharging input (X), re-deriving GPSA's
  parity half without Petersen; (GR-45)–(GR-48) subsumed, not contradicted. **GLAW is an
  honest MISS** carrying four theorems and one refutation on **(a′)**: (GR-55)–(GR-58) give
  (a′) coordinates and verify it EXHAUSTIVELY on the whole `n_hub ≤ 6` stratum at no cap;
  (GR-59) REFUTES the per-matching variant (`min_M` load-bearing, no proof may fix its
  anchor matching); (GR-60) names the residual **input (Y)** — by (GR-56)(iv) the
  whole-graph/proper-chunk instances of one inequality together with GDESC's input (X),
  though GBAL's proof does **not** transfer to (Y) (a different quantifier). **E3 ARMED,
  not fired** — entry 1's (a′) stays open, no bar. (GR-15) OPEN, unchanged; no g-flank.

- **The FIRST through FOURTEENTH fan-outs/directions — all LANDED 2026-08-05…08-18**
  (canonical homes the workbook sections named; commits `d5ae55aa`…, `cdd23d30`, `12edc305`,
  `b32c1c2c`, `cd0af9e1` for the first five; CFLANK/GCAP/GUNIF/GEXIST/GORIENT/GDEV/GADM/
  GPSA/GDESC (`w4/{cflank,gcap,gunif,gexist,gorient,gdev,gadm,gpsa,gdesc}.py`, §(K-grid)
  Steps G24–G67) the sixth–fourteenth). Twenty-two directions total (thirteen in the first
  five fan-outs, one per ordinal from the sixth on): (GR-21)–(GR-28) closed
  TCOL's two flank sites AS ROUTES; GCAP's `g ≤ 1` cap at `k ≥ 3` since REFUTED by GUNIF
  (both of GUNIF's own targets refuted too, route DEAD); GEXIST/GORIENT honest MISSes
  ((GR-32)–(GR-39)) re-anchoring the target on bounded-deviation selection; GDEV a
  REFUTATION-with-successors ((GR-40)–(GR-42)); GADM an honest MISS carrying (GR-43)
  (shift-metric UNBOUNDED), routing overridden by GPSA; GPSA proves entry 5's parity half
  ((GR-44)); GDESC RESHAPES the balance half ((GR-45)–(GR-48)) into input (X), later
  discharged by GBAL. (b′) supported; headline positives (GR-9)/(FR-R1) PROVEN, (GR-15)
  OPEN throughout; uniformity untouched; E1/E2/E3 never fired. Coordinator corrective pass
  same day as GUNIF (docs only) — landing-checklist item 6 (`notes/Pencil-fanout.md`).

- **The 2026-08-05 research cluster, one-lined** (all same day; full detail
  `Phase39-design.md` + git, workbook sections named): docs/strategy pair — notes
  reorganization (registry `notes/Pencil-labels.md`; `Phase39-design.md` **FROZEN**) + the
  class-uniformity recon (5 REFUTED, 3 ranked, strategy **§4.6**); the route-σ arc (three
  landings, `sigma.py`, §(K-σ)) — route σ a **CANDIDATE**, σ-intertwining refuted
  literally/confirmed covariantly, σ-equivariant recipes **DEAD**, obligation 1 DONE
  ((σ7) proven), field scope superseded by §(K-clos); (K-ind) and the Δ-matroid lead **BOTH
  REFUTED as routes** (§(K-ind), §(K-Δ): no induction move relates two class members —
  pencil side runs `Graph.pencil_reduction`, not KT Thm 4.9 — and (K-Δ)'s literature hunt
  fails on two hypotheses); §(K-Λ) triad — `g₁₄` clause NOT forced, Λ-completeness stands
  (`outer.py` *Step 3a*), (Λ0) PROVEN class-uniform (widened to (Λ0f′), `m2/lambda0.m2`),
  (Λ1) an IDENTITY over the function field (`m2/lambda1.m2`); the sixth–ninth dispatches
  (§(K-flank)/§(K-pure)/§(K-Λ)/§(K-dom)) — conjecture HOLDS at every uncovered flank (851
  shapes), pure condition WRONG INVARIANT, (K-Λ) ⟺ (K-wit) at `ℓ = 4`, dominance HOLDS but
  NOT a route; harness + workbook prep (two commits, no math, 67/67 drivers re-run 0 changed
  figures — `notes/scripts/README.md`; `Pencil-W4-informal.md`; *State of (K)* map);
  **(K-slide-comb) REFUTED class-wide**, packing half uniform ((C6)), (C7) corrected
  (`kslidecomb.py`, §(K-slide-comb)).

- **Pre-fan-out arc, one-lined (2026-07-24 → 08-04; full detail `Phase39-design.md` + git)**:
  W0–W3 layers, W5-L4 `exists_pencilSeed_of_nondeg`, `Pencil/` split, W5-L5 cut arm +
  `PencilPair` restatement, L6a bare-pin **FALSE**, L6b triangle-free re-pin; the 2026-07-30
  W5-L7 build day CLOSED `hsplit` IN FULL and isolated kernel **(K)**; (K) route-1 gate
  FIRED (locality REFUTED, `localtest*.py`), reducing (K) to *stress non-constancy* graded by
  (D2); the 2026-07-30 recon day fixed the corank stratification to **(K-tight)**, decomposed
  W4 (W4-L4b pinned buildable, gates N8–N10b PASSED), NO-GO'd the (K-bare) extension
  (**(K-bare-ext)**), and set this phase's standing (K)/(K-bare)/W4 adjudications (quoted in
  *Current state*); the 2026-08-02 W4 residual arc priced the kernel-widening (only `hK`
  widens, to **(K-res)**) and REFUTED **(SAFE-RES)** and `hnoGood'` vacuity (`W19`); (K-tight)
  itself re-pinned against KT pp. 684–691 (`repin.py`), narrowing the kernel to
  (K-move)/(K-pitch); the 2026-08-04 pair proved (K-slide) (S1), reduced (K-slide-cl) to
  combinatorics, and developed (K-pitch) (θ(3,3,6) CLOSED).

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
