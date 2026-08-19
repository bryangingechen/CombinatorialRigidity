# Phase 39 — PENCIL: the hinge-pencil molecular conjecture (work log)

**Status:** in progress — phase stays OPEN (standing user adjudications of 2026-07-24 /
2026-07-30 / 2026-08-02, quoted verbatim in *Current state*). W0–W3 and the whole W5 arc
(L0–L7) are COMPLETE — `hsplit` CLOSED IN FULL and `hfresh`'s counting discharge landed
(2026-07-30). Only three items remain, all carried by the landed successor
`pencil_conjecture_of_hcontract_hK_hbareSplit_of_card` (`Molecule/Pencil/Escape.lean`):
`hcontract` (W4), kernel `hK`, and kernel `hbareSplit` — see *Hand-off*. **Twenty-nine
kernel-(K) directions are now COMPLETE** (2026-08-05 → 08-19: thirteen across the first
five fan-outs, fourteen more one per ordinal from the sixth through the nineteenth, plus
**CIRR** (ordinal twenty-four) and **YLOC** (ordinal twenty) — roster and per-direction
theorem chain in *Decisions made*). **The SIXTH FAN-OUT IS COMPLETE — all five directions
(GBAL/GLAW/OCON/LTWO/FRES) LANDED 2026-08-19.** Headline positives **(FR-R1) PROVEN**, the
(GR-16)–(GR-60) theorem chain, and **route-ledger entry 5 PROVEN in both halves, a HIT**
(GBAL, discharging input (X)); **E3 ARMED but does NOT fire** — entry 1's **(a′)** stays
open (GLAW, residual **input (Y)**); §(K-frame) (FR-4)'s named gap **CLOSED with no
rider** (FRES); §(K-out) (OC-8)'s hard-stratum qualifier now **FREE**, its residue reduced
to two named inputs **ADDED, not removed** (OCON, an honest MISS); §(K-Λ) item (vii)
**REALIZED at a proven size floor**, an honest MISS on the "class forbids it" branch,
`(K-wit)`'s residual recomputed not re-graded (LTWO). **(GR-15) stays OPEN throughout;
class uniformity untouched; no g-flank at any of the twenty-nine.** **The SEVENTH FAN-OUT
is IN PROGRESS — two of five landed 2026-08-19: CIRR** (chart irreducibility, a HIT)
**and YLOC** (input (Y) localized, an honest MISS with substantial positive content —
GBAL's chunk-level instrument DEMOTED BY WITNESS, GLAW's routing override SPLIT by rung;
full verdicts in *Decisions made*). Three directions remain in flight — **BALB** (b′) /
**AGLU** AA-glue at `n_hub ≥ 8` / **ZNEQ** `Z ≠ ∅` — ordinals twenty-first–twenty-third,
coordinator-specced (`notes/Pencil-fanout.md` §"Seventh fan-out"). **Next concrete task:
land BALB (returned, verified), then ZNEQ and AGLU as they return** — see *Hand-off*.
Direction codes are **multi-letter and topic-tagged from the fifth fan-out on**
(`notes/Pencil-labels.md` (L5)); grandfathered single letters are re-used across
dates — **always date those**.

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
  coordinator-set (`notes/Pencil-fanout.md` §"Sixth fan-out"). **All five directions —
  GBAL, GLAW, FRES, OCON and LTWO — LANDED 2026-08-19; the fan-out is COMPLETE** — full
  verdicts in the header above and *Decisions made*, not restated here.

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
  instrument at the chunk level** instead.

**Kernel-(K) research arc — forty-six docs+scripts-only dispatches, plus seven
strategy-only passes** (2026-08-02 → 08-19). Which pass was which is one-lined in *Decisions
made*; the rule is that the **dispatch** count moves only on a landing (GBAL/GLAW/FRES/OCON/
LTWO are the fortieth through forty-fourth; CIRR the forty-fifth; YLOC the forty-sixth), and
a **user call on dispatch *shape*** — either multidispatch election, or a coordinator-authored
pick like the twelfth's — contributes **no** strategy pass. Canonical homes: workbook
`notes/Pencil-informal.md` (**State of (K)** map = entry point), `notes/Pencil-W4-informal.md`
(W4-residual), `notes/Pencil-strategy.md` (strategy). Net effect: **disproof risk removed**,
every refuted route/gap has a successor in the gap map, several structural positives proven,
and **route-ledger entry 5 is PROVEN, the arc's first HIT**; **class uniformity of the escape
remains untouched by all forty-six.**
**Doc-debt round CLOSED — `notes/Pencil-cleanup.md`** (2026-08-13, category D only; D-5 a
watch item; the D-2 fix regressed at GORIENT's landing, re-repaired `07f6f9b6`).

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
point — `Z ≠ ∅` is **ZNEQ**'s target, still in flight); **(c)** the **W4 build**,
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

**The sixth fan-out is COMPLETE — all five directions LANDED 2026-08-19**; verdicts in the
top `**Status:**` paragraph, per-direction detail in `notes/Pencil-fanout.md` §"Sixth
fan-out", labels claimed in `notes/Pencil-labels.md` — **none of it restated here.** No
standing constraint moved: phase OPEN, Lean hold STANDS, W4 PARKED, `hK`/`hbareSplit`
pinned, option B un-commissioned.

**CIRR (twenty-fourth, chart irreducibility) and YLOC (twentieth, input (Y) localized) both
LANDED 2026-08-19** — CIRR a HIT, YLOC an honest MISS with substantial positive content;
canonical homes new §(K-chart) and §(K-grid) *Steps G80–G85* (`notes/Pencil-informal.md`),
verdicts in `notes/Pencil-fanout.md` §§"Twenty-fourth direction"/"Twentieth direction" —
**not restated here**. **Next concrete task: land BALB (returned, verified,
next in line), then ZNEQ and AGLU as they return — one coordinator commit per
direction**, each merging that direction's untracked draft
(`notes/Pencil-draft-<CODE>.md`) into the workbook, committing its driver, moving its
reservation row into the `notes/Pencil-labels.md` registry, and recomputing the owning
section's *State of (K)* gap-map row (**the §(K-grid) row is near its cap** — 1927/2035
status words, 863/873 close-it words after YLOC's landing; BALB's landing may need a
recompute + a dated cap bump, `notes/check-gapmap-cells.py`). Dispatched concurrently at
**opus** 2026-08-19; specs, bars, riders and the **not-selected ranking** are in
`notes/Pencil-fanout.md` §"Seventh fan-out", **not restated here**:

| direction | ordinal | target, in one clause | labels reserved |
|---|---|---|---|
| **BALB** | twenty-first | **(b′)**, `d_adm − d_par ≤ 2` — never a primary before; (GR-50) is the first instrument that could **bound** it | (GR-67)–(GR-72) / G86–G91 |
| **AGLU** | twenty-second | ledger attack **(c)** — is the (GR-38) AA-glue configuration **realizable** at `n_hub ≥ 8`? | (GR-73)–(GR-78) / G92–G97 |
| **ZNEQ** | twenty-third | **(OC-19) input (a)**, `Z ≠ ∅` at every class (shape, split) — a whole-(K-tight) input, not (OUT)'s | (OC-23)–(OC-28) / O19–O24 |

**E3 is ARMED** (GBAL's entry-5 HIT) but **YLOC did NOT fire it** (a′ not hit, only its
pinned route demoted; firing is the coordinator's action). **"Chart irreducibility,
un-owned" is now CLOSED** (CIRR, a HIT, §(K-chart)). **Not selected this wave, still
queued** (ranking in the fan-out doc): (OC-19) input (c) class-uniformly — OCON's #1 by
value but **(GR-15)-flavoured**, natural next primary once a chunk-level instrument for
(Y) exists (YLOC's own attempt was DEMOTED BY WITNESS, not a success — its two-rung
successor routing is in *Decisions made*); §(K-out) items 3/4; **(d′)**. **Not eligible:**
route σ's Lean half and the W4 build, **BLOCKED by the standing 2026-08-05 Lean hold**.

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
> **Not selected at the 2026-08-07 adjudication**, and so not open: the **(FR-6) follow-ons**
> (§(K-frame) *What would change this* (ii) the `ℓ_min = 5` battery beyond θ(3,4,5) and (iv)
> the (AC-9) anti-correlation's structurality stay open and un-commissioned; **(iii)**, the
> (FR-7) irreducibility foothold, is **struck as unnecessary** by (OC-17) — the opposite of
> entering it, no bar crossed), the unselected leads (b)–(f) above, and route σ / W4.
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

- **The seventh fan-out, two of five LANDED 2026-08-19** (`notes/Pencil-fanout.md`
  §"Seventh fan-out"; BALB next, AGLU/ZNEQ still in flight). **CIRR** (twenty-fourth,
  canonical home new §(K-chart) `notes/Pencil-informal.md`, `w4/cirr.py`) — **a HIT**:
  chart irreducibility proven once ((CH-1), a tower of affine-linear fibres whose
  constant-fibre-dimension clause **is** `IsNondegPencilRealization` conjunct 3), all four
  consumers audit clean ((CH-7)), (CH-8) a pointer to the landed, strictly stronger
  `not_pencilNondegFeasible_of_triangle_two_hubs` (`Motive.lean:563`). **YLOC** (twentieth,
  canonical home §(K-grid) *Steps G80–G85*, `w4/yloc.py`) — **an honest MISS with
  substantial positive content**: GBAL's chunk-level instrument for input (Y) is
  **DEMOTED BY WITNESS** ((GR-62): full goodness is not a function of the (GR-50) degree
  data), the coordinator's predicted obstruction **REFUTED as stated** and located two
  links earlier ((GR-63)); the positive residue is a colouring-free collision bound on
  `d_fg` ((GR-64)) and a coordinate-free fit identity unifying `dist(m, M)`/`z_mono(S)`
  ((GR-65)), with GBAL's own certificate measured missing both of (Y)'s constraints
  ((GR-66)). GLAW's routing override **SPLIT**, not upheld: GBAL's z-form serves the
  chunk/balance rung, GLAW's coset coordinates reinstated for the distance rung. Both:
  no gap-map status moves; class uniformity, (GR-15), (OC-8), (ANH-R1), entry 5
  untouched; TERMINATION fires nothing, E3 stays ARMED (by GBAL), not fired.

- **The FIRST through NINETEENTH fan-outs/directions — all LANDED 2026-08-05…08-19**
  (canonical homes the workbook sections named; commits `d5ae55aa`…, `cdd23d30`, `12edc305`,
  `b32c1c2c`, `cd0af9e1` for the first five; CFLANK/GCAP/GUNIF/GEXIST/GORIENT/GDEV/GADM/
  GPSA/GDESC/GBAL/GLAW/OCON/LTWO/FRES (`w4/{cflank,gcap,gunif,gexist,gorient,gdev,gadm,gpsa,
  gdesc,gbal,glaw,ocon,ltwo}.py`; FRES no driver) the sixth–nineteenth). Twenty-seven
  directions total (thirteen in the first five fan-outs, one per ordinal from the sixth on):
  (GR-21)–(GR-28) closed TCOL's two flank sites AS ROUTES; GCAP's `g ≤ 1` cap at `k ≥ 3` since
  REFUTED by GUNIF (both of GUNIF's own targets refuted too, route DEAD); GEXIST/GORIENT
  honest MISSes ((GR-32)–(GR-39)) re-anchoring the target on bounded-deviation selection;
  GDEV a REFUTATION-with-successors ((GR-40)–(GR-42)); GADM an honest MISS carrying (GR-43)
  (shift-metric UNBOUNDED), routing overridden by GPSA; GPSA proves entry 5's parity half
  ((GR-44)); GDESC RESHAPES the balance half ((GR-45)–(GR-48)) into input (X); **GBAL PROVES
  it** ((GR-49)–(GR-54), the balance theorem — route-ledger entry 5 in BOTH halves, the arc's
  first HIT, discharging (X), re-deriving GPSA's parity half without Petersen); **GLAW** an
  honest MISS on **(a′)** ((GR-55)–(GR-58) coordinates + exhaustive `n_hub ≤ 6` verification;
  (GR-59) REFUTES the per-matching variant; (GR-60) names residual input (Y) — GBAL's proof
  does **not** transfer to it); **OCON** an honest MISS freeing (OC-8)'s hard-stratum
  qualifier ((OC-17)–(OC-22): `Z` Zariski-open not a stratum, (OC-8) reduced to `Z ≠ ∅` +
  chart irreducibility + one rigid chart point, two inputs ADDED not removed); **LTWO** an
  honest MISS on the "class forbids it" branch, §(K-Λ) item (vii) REALIZED at a proven size
  floor ((Λ4)–(Λ8): `|V| ≥ 21`/`26`, witnesses `LT21a`/`LT21b`/`LT26`, Λ-completeness stands);
  **FRES** closes §(K-frame) (FR-4)'s named gap with no rider ((FR-15)–(FR-17): the
  chart-MAP-vs-chart-VARIETY clause, the (ANH-R1) β-clause at every bare-cycle site). (b′)
  supported; headline positives (GR-9)/(FR-R1) PROVEN, (GR-15) OPEN throughout; uniformity
  untouched; E1/E2 never fired, **E3 ARMED by GBAL, not fired**.

- **The 2026-08-05 research cluster, one-lined** (all same day; full detail
  `Phase39-design.md` + git, workbook sections named): notes reorganization
  (`notes/Pencil-labels.md`; `Phase39-design.md` **FROZEN**) + the class-uniformity recon (5
  REFUTED, 3 ranked, strategy **§4.6**); route σ became a **CANDIDATE** (§(K-σ), obligation 1
  DONE, field scope superseded by §(K-clos)); (K-ind) and the Δ-matroid lead **BOTH REFUTED
  as routes**; the §(K-Λ) triad settled ((Λ0)/(Λ1) PROVEN via the M2 layer, Λ-completeness
  stands); the sixth–ninth dispatches (§(K-flank)/§(K-pure)/§(K-Λ)/§(K-dom)) found the
  conjecture HOLDS at every uncovered flank, the pure condition WRONG INVARIANT, dominance
  HOLDS but NOT a route; **(K-slide-comb) REFUTED class-wide** (`kslidecomb.py`).

- **Pre-fan-out arc, one-lined (2026-07-24 → 08-04; full detail `Phase39-design.md` + git)**:
  the W0–W3/W5 build CLOSED `hsplit` IN FULL and isolated kernel **(K)** (route-1 locality
  REFUTED, reducing it to stress non-constancy); the corank stratification was fixed to
  **(K-tight)**, W4 decomposed (W4-L4b buildable) and (K-bare-ext) NO-GO'd, setting this
  phase's standing (K)/(K-bare)/W4 adjudications (quoted in *Current state*); the 2026-08-02
  residual arc priced the kernel-widening to **(K-res)** and REFUTED **(SAFE-RES)**/
  `hnoGood'` vacuity; (K-tight) re-pinned against KT pp. 684–691, narrowing to
  (K-move)/(K-pitch); the 2026-08-04 pair proved (K-slide) (S1) and closed (K-pitch) at
  θ(3,3,6).

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
