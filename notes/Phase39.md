# Phase 39 — PENCIL: the hinge-pencil molecular conjecture (work log)

**Status:** in progress — phase stays OPEN (standing user adjudications of 2026-07-24 /
2026-07-30 / 2026-08-02, quoted verbatim in *Current state*). W0–W3 and the whole W5 arc
(L0–L7) are COMPLETE — `hsplit` CLOSED IN FULL and `hfresh`'s counting discharge landed
(2026-07-30). Only three items remain, all carried by the landed successor
`pencil_conjecture_of_hcontract_hK_hbareSplit_of_card` (`Molecule/Pencil/Escape.lean`):
`hcontract` (W4), kernel `hK`, and kernel `hbareSplit` — see *Hand-off*. **All thirteen
fan-out directions plus CFLANK, GCAP, GUNIF, GEXIST, GORIENT, GDEV and GADM are now
COMPLETE** (2026-08-05 → 08-17; roster in *Decisions made*'s FIRST-through-TWELFTH
entries). Headline
positives **(FR-R1) PROVEN** and (GR-16)–(GR-28); GUNIF **REFUTED both of its targets** at
`n_hub ≥ 8`; GEXIST is an honest **MISS** — three new theorems ((GR-32)/(GR-33)/(GR-35))
reduce the uniform existence target to a **minority-dart orientation problem**; GORIENT,
also an honest **MISS**, adds four more ((GR-36)–(GR-39)) and re-anchors the target on a
**bounded-deviation selection principle** (W3 the sticking instance); **GDEV REFUTES that
form as posed** ((GR-40)–(GR-42): a habitat family with an unbounded parity floor whose
every member is still fully-good — a form-refutation, never a flank), re-anchoring it on
the `d_fg = d_adm` law; **GADM** (LANDED 2026-08-17, the arc's first coordinator-authored
prep) proves **(GR-43)** — the odd-cycle-packing shift floor: the **shift-metric layer is
UNBOUNDED** (`d_par = d_adm = d_fg = m` exactly at the necklaces, killing the growth law's
bounded-correction reading) while the **(a′) `d_fg = d_adm` law survives its first
large-`d` test** (rank-certified at the optimum up to `n_hub = 50`) and ledger entry 5
(per-shape admissibility) settles as a **separate OPEN statement** — but **(GR-15) stays
OPEN throughout; class uniformity untouched by every round.** The research arc
**CONTINUES**: the THIRTEENTH direction is **GPSA** — **route-ledger entry 5**, per-shape
admissibility in BOTH halves (the Hall/SDR parity step and the ≤ 6-odd-branch balance
rider), (b′) the secondary — picked by a **top-rung fable recon** (2026-08-18, fifth use
of the 2026-08-12 shape) whose verified verdict **OVERRODE** GADM's shift-metric routing
clause; **PREPPED, not yet dispatched. Dispatching GPSA is the next concrete task**
(see *Hand-off*). Direction codes
are **multi-letter and topic-tagged from the fifth fan-out on** (`notes/Pencil-labels.md`
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
  (`notes/scripts/README.md`). Every script the project runs is tracked, including probes
  whose answers reach a note.
- **2026-08-05…07, second through fifth fan-outs (all COMPLETE; user-adjudicated).**
  T/R/M, G/Q/O, E/J, PEX/TCOL; route σ / W4 / the (FR-6) follow-ons not selected at any of
  them; cap lifted, rescue §1 pre-authorized (`notes/Pencil-fanout.md` §§"Second"–"Fifth").
- **2026-08-07, delegation adjudication (binds from the SIXTH direction on).** Asked at
  the session-start check-in what to do once TCOL lands, the user selected **"Keep going
  on my own judgment"** — *"After landing TCOL I pick the next direction from the
  hand-off's candidate list and continue dispatching without checking in."* This
  delegates **selection only** and changes **no** standing constraint (phase OPEN; Lean
  hold stands; W4 PARKED; `hK`/`hbareSplit` carried as pinned; option B un-commissioned);
  the same check-in's top-rung/cap/rescue calls are otherwise unchanged. The coordinator's
  picks under it (the SIXTH through ELEVENTH directions) are one-lined in *Decisions made*.
- **2026-08-12, seventh-direction delegation (refines the above; changes no standing
  constraint).** The user, verbatim: *"Let's have a fable subagent make the decision /
  do a reprioritization and then follow its guidance."* — the precedent that the pick may
  itself be delegated to a **top-rung fable recon**. Its verdict (GCAP) was verified,
  accepted and LANDED 2026-08-13 (`notes/Pencil-fanout.md` §"Seventh direction"). Same
  check-in: top rung = fable (opus only if the weekly limit runs out); the dispatch cap
  **lifted**; rescue §1 mechanical fixups **pre-authorized** — all still binding.
- **2026-08-13, phase-shape adjudication (changes no standing constraint).** Offered the
  four options GUNIF's refutation raised, the user answered, verbatim: *"I think we
  should continue with the research here, but perhaps not in this session. Are we ready for
  handoff to a fresh session?"* — **RESOLVED: the research arc CONTINUES** (not
  packaging-and-stopping); nothing else moved, and selection fell back to the standing
  2026-08-07 delegation (the 2026-08-12 delegate-the-pick precedent applying too).
- **2026-08-13/14, ninth- through eleventh-direction selections (change no standing
  constraint).** All three picks **re-delegated to a top-rung fable recon** (second through
  fourth uses of the 2026-08-12 shape); verdicts — **GEXIST**, **GORIENT**, **GDEV** — all
  verified and **ACCEPTED** (records in `notes/Pencil-fanout.md` §§"Ninth"–"Eleventh
  direction"); GEXIST/GORIENT **LANDED 2026-08-13** (honest MISSes), GDEV **LANDED
  2026-08-15** (the bounded-deviation form refuted as posed, successors named).
- **2026-08-17, twelfth-direction selection (BREAKS the fable-recon streak; changes no
  standing constraint).** Offered three shapes, the user chose **coordinator-authored prep
  from GDEV's routing clause**, verbatim content *"take (a′) as the primary attack per
  GDEV's measured 133/133 `d_fg = d_adm` finding, (b′) as the secondary, and write the spec
  myself. Cheaper, but no independent ranking of the losers."* — so GADM's spec and ranking
  record are the coordinator's (cost disclosed in the spec's *Status*; a future top-rung
  recon may overturn its bars freely). GADM **PREPPED and LANDED 2026-08-17** (an honest
  MISS on (a′)-as-a-theorem carrying (GR-43); entry 5 settled OPEN; no flank).
- **2026-08-18, thirteenth-direction selection (returns to the fable-recon shape; changes
  no standing constraint).** The user chose, from the multiple-choice options, **"Delegate
  the pick to a fable recon"** — the **fifth** use of the 2026-08-12 shape, elected
  specifically because the coordinator-authored twelfth prep had no independent ranking of
  the losers. The recon's verdict — **GPSA**: route-ledger **entry 5** (per-shape
  admissibility, BOTH halves), **(b′)** secondary — was **verified and ACCEPTED, including
  its OVERRIDE of GADM's shift-metric routing clause** (the recorded closure chain consumes
  no `d_par`; spec, full loser ranking with bars, amended TERMINATION test, and the
  process finding — the clause contradicted GADM's own ranking principle, unread by any
  second reader — all in `notes/Pencil-fanout.md` §"Thirteenth direction"). Every GADM
  ranking bar was upheld; the override targets the routing clause only. Same check-in:
  **all four rungs dispatchable**, cap **lifted**, rescue §1 fixups **pre-authorized**
  (the standing configuration). **PREPPED 2026-08-18, not yet dispatched** — see *Hand-off*.

**Kernel-(K) research arc — thirty-seven docs+scripts-only dispatches, plus six
strategy-only passes** (2026-08-02 → 08-18; the second is the 2026-08-12 fable recon,
the third through fifth the 2026-08-13/08-14 ninth-, tenth- and eleventh-direction
selection recons, the sixth the 2026-08-18 thirteenth-direction selection recon, all
above; **the twelfth's pick was coordinator-authored at the user's 2026-08-17 election,
so it contributed no pass**). Canonical homes: workbook `notes/Pencil-informal.md` (**State of (K)** map =
entry point), `notes/Pencil-W4-informal.md` (W4-residual), `notes/Pencil-strategy.md`
(strategy); one line per landing in *Decisions made*, canonical with git — **not
restated here**. Net effect: **disproof risk removed**, every refuted route/gap has a
successor in the gap map, several structural positives proven; **class uniformity of
the escape remains untouched by all thirty-seven dispatches.**

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
directions M and R); each has a canonical home carrying the detail, not restated here:
**(b)** **(K-wit)**, the pitch route's single live form at companion splits (§(K-Λ); the
(OC-8) residue is a **containment** question, §(K-out) *Steps O9–O12*); **(c)** the **W4
build** — decomposed, buildable, **PARKED** by the 2026-08-05 Lean hold; **(d)** the
companion-length dichotomy frame (§(K-dom) *D7*) + the unprobed `k ≥ 4` parallel-edge item
(§(K-pure) *P4*); **(e)** §(K-Λ) item (vii)'s residual (no swept family realizes one);
**(f)** strategy §4.6's ranked shortlist — **partially superseded** for the tight stratum
(durable negatives in *Hand-off*); U3 still unrun.

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

**Next concrete task: DISPATCH GPSA, the THIRTEENTH kernel-(K) direction** — spec ready
in `notes/Pencil-fanout.md` §"Thirteenth direction" (prepped 2026-08-18; the pick a
top-rung fable recon's, fifth use of the 2026-08-12 shape, which **OVERRODE** GADM's
shift-metric routing clause — override verified and accepted, grounds in the spec).
Target: **route-ledger entry 5 — per-shape admissibility (`d_adm < ∞`) in BOTH halves**:
the Hall/SDR parity step (workbook *Step G53*'s undischarged caveat) and the
≤ 6-odd-branch balance rider; **(b′)** (`d_adm − d_par ≤ 2`) the secondary. Rung: top
(fable); labels **(GR-44)+ / Steps G58+** reserved (`notes/Pencil-labels.md`); driver
`notes/scripts/w4/gpsa.py`. An entry-5 HIT does **NOT** fire E3 — it **arms** it: the
fourteenth is then **(a′)** at its named sticking case (no re-proposal bar — the recon
ranked it second on sequencing only); a `d_adm = ∞` shape is a g-flank and fires E1
(new clause (v)). The shift-metric layer's bar and the full loser ranking are in the
spec's ranking record. No standing constraint moves with this: phase OPEN, Lean hold
STANDS, W4 PARKED, `hK`/`hbareSplit` pinned, option B un-commissioned.

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
> **The FIRST through TWELFTH directions are ALL COMPLETE** — roll call (with commit hashes
> for the first five) is one-lined with dates in *Decisions made*; the delegations that picked
> the SIXTH through ELEVENTH under them are in *Current state*'s dated bullets; not repeated
> here. **No g-flank found by any of them; (GR-15) stays OPEN, unchanged, modulo (GR-4′); no
> gap-map status moves.**
> **Two durable negatives from the same adjudication — do not re-run:** (i) §4.6's shortlist
> is **partially superseded** for the tight stratum (U2 delivered by (GR-16)'s hub-multigraph
> reduction; U3's negative-form insight already exploited by the cap/budget style); (ii) the
> symbolic meta-option ("upgrade §(K-Λ) via M2") is **landed, not pending** (`m2/lambda0.m2`) —
> only §5.3 item (i) (whole-graph elimination) remains, ruled out by §5.3's own local-frame
> feasibility boundary.
> **The NINTH through TWELFTH directions — GEXIST, GORIENT (both 2026-08-13, honest
> MISSes), GDEV (2026-08-15, a REFUTATION-with-successors) and GADM (2026-08-17, an honest
> MISS carrying a theorem and a refutation) — landed the theorem block (GR-32)–(GR-43).**
> Per-direction records are canonical in `notes/Pencil-fanout.md`
> §§"Ninth"–"Twelfth direction", the mathematics in workbook §(K-grid) *Steps G38–G57* —
> **not restated here**. What binds forward:
> - **The bounded-deviation selection form is REFUTED as posed** ((GR-42), the pentagon
>   necklaces `NK(m)`: `d ≥ m/2` unbounded while every member stays rank-certified
>   fully-good) — a form-refutation, never a flank. **Do not re-attack a shape-free `d`**;
>   and GADM split its growth-law successor: the bounded-shift-correction READING is
>   also refuted ((GR-43): the shift-metric layer is unbounded), while the (a′)
>   `d_fg = d_adm` half survives, open.
> - **The obstruction family is binding-capable, NOT capacity-tight** — GEXIST's framing was
>   a strict under-proxy, corrected by (GR-36) — so **every "0 fully-hot" figure carries its
>   family qualifier**: the capable family carries 761 on a 184-shape subsample, and
>   (GR-40)'s corner condition prunes 815 → 573, a prune and not a zero.
> - **The W3 stick SPLITS: 1 shift-metric + 1 balance unit** (`d_par(W3) = 2`, `d_adm = 3`;
>   GADM's correction of GDEV's "the whole stick is the balance layer's" — fixed in place at
>   Step G49 and the gap-map row), and the `d_fg = d_adm` regularity now measures at
>   **133 shapes (all `d ≤ 3`) + GADM's fresh 108-shape census + the four NK members at `d`
>   up to 10, rank-certified at the optimum** — quote it with that provenance; it is attack
>   (a′), still open as a theorem.
> - **Ledger entry 5 (per-shape admissibility) is a SEPARATE OPEN statement** (GADM Step
>   G53): (GR-37)(iii)'s "balance rider alike" clause is statement-beyond-proof (flagged at
>   the statement site; the parity half stands) — so an (a′) HIT alone does NOT close the
>   `Λ = ∅` `D = 0` existence target and would NOT fire E3.
> - **GDEV's and GADM's TERMINATION checks both fired nothing** (E1/E2/E3 all NO); GADM's
>   outcome-3 branch routed the **thirteenth** to the shift-metric layer — **since
>   OVERRIDDEN** by the accepted 2026-08-18 recon verdict (GPSA, §"Thirteenth direction";
>   the next-task slot at the top of this section carries the dispatch).
> **Coordinator hand-off note, still not loaded onto any direction:** whether (GR-15) as
> quantified ("every tight class shape") also covers the `W19`-type **(K-res)** sibling
> habitat is unresolved — pin it when the tight side closes, not before.
> **Not selected at the 2026-08-07 adjudication**, and so not open: the **(FR-6) follow-ons**
> (§(K-frame) *What would change this* items (ii)–(iv) — the `ℓ_min = 5` battery beyond
> θ(3,4,5), the (FR-7) irreducibility foothold, the (AC-9) anti-correlation's structurality),
> the unselected leads (b)–(f) above, and the parked Lean half of route σ / the W4 build.
> Deliberate non-goals: (Λ0), (Λ1), the `g₁₄` clause, §(K-ind), §(K-Δ), **§(K-clos)'s field
> question**, **§(K-ann)'s settled batch** ((ANH-1)–(ANH-6), (SD-6)) and **§(K-out)'s settled
> batch** ((OC-1)–(OC-7); the two pools are pinned and **disjoint**) are **done** — do not
> re-derive, re-sweep, re-run their literature hunt, re-open "does the polarity generalize?",
> re-measure (D2)'s far block, re-sample POOL-G or POOL-S, **propose a counting / matroid route
> to (OUT)'s hypothesis** ((OC-3) refutes the whole class), or touch `lambda.py`'s figures — the
> one carve-out, the re-baselining round's slice **S3**, is **spent**: it edited `lambda.py` on
> purpose (OPENED-block scope (3), coding the landed (Λ0f′) in place of the superseded (Λ0f)) and
> moved exactly the one recorded figure it was licensed to, `outer.py --geom`'s.
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
  commit is **W4-L4b** (`exists_degree_two_of_co1_rigid`, pinned + spike-elaborated, 1 commit),
  then order-flexibly W4-L1/L2/L3′/W4-L5. Gates N8/N9(+rank-29 control)/N10/N10b all PASSED
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
not move*; a **symbolic** dispatch adds `notes/scripts/m2/README.md`.

## Adjacent directions (orientation only, not this phase)

ORIGAMI (`notes/Origami.md`, next queued) is the bar-joint-side analog; the wider unqueued
survey — incl. IDENT-PANEL, the nearest neighbour — is `notes/IdeaBacklog.md`.

## Decisions made during this phase

Reverse-chronological, one line per landing; full derivations live in git,
`notes/Phase39-design.md`, and (for the (K) arc) the workbook section named in each entry, which
is the canonical home a successor reads.

- **The ELEVENTH and TWELFTH directions — GDEV LANDED 2026-08-15, GADM LANDED
  2026-08-17** (`w4/{gdev,gadm}.py`; canonical home §(K-grid) Steps G48–G57, full
  statements in *Current state*/*Hand-off*). GDEV a REFUTATION-with-successors
  ((GR-40)–(GR-42): the bounded-deviation selection form refuted as posed); GADM an
  honest MISS carrying (GR-43) (shift-metric layer UNBOUNDED) and settling ledger
  entry 5 OPEN. (GR-15) stays OPEN throughout; E1/E2/E3 none fired; GADM's
  shift-metric routing of the thirteenth was overridden 2026-08-18 (GPSA).

- **The EIGHTH through TENTH directions — GUNIF/GEXIST/GORIENT, all LANDED
  2026-08-13** (`w4/{gunif,gexist,gorient}.py`; canonical home §(K-grid) Steps
  G34–G47, full statements in *Current state*). GUNIF REFUTED both targets
  ((GR-28)(iv) exact boundary, GR-29–31), route DEAD; GEXIST an honest MISS
  ((GR-32)/(GR-33)/(GR-35) + (GR-34) refuting `CL10`) reducing the target to a
  minority-dart orientation problem; GORIENT an honest MISS ((GR-36)–(GR-39))
  re-anchoring it on a bounded-deviation selection principle sticking at W3, four
  dispatchable attacks named. Per-shape (GR-15) holds throughout, stays OPEN.
  Coordinator corrective pass same day (GUNIF), docs only — gate-invisible defects
  fixed, prophylactic now landing-checklist item 6 (`notes/Pencil-fanout.md`).

- **The SIXTH and SEVENTH directions — CFLANK LANDED 2026-08-07, GCAP LANDED
  2026-08-13** (`w4/cflank.py`, `w4/gcap.py`; canonical homes §(K-grid) Steps G24–G28 /
  G29–G33). Eight proven results (GR-21)–(GR-28) closed TCOL's two flank sites AS
  ROUTES (certificate-3 proven per swept shape); GCAP's `g ≤ 1` cap at `k ≥ 3` since
  REFUTED by GUNIF. (GR-15) stays OPEN; uniformity untouched.

- **The FIRST through FIFTH fan-outs — all LANDED 2026-08-05…08-07** (canonical homes
  the workbook sections named; commits `d5ae55aa`…, `cdd23d30`, `12edc305`, `b32c1c2c`,
  `cd0af9e1`; thirteen directions A/B/C+S1–S4, T/R/M, G/Q/O, E/J, PEX/TCOL). Headline
  positives (GR-9)/(FR-R1) PROVEN, (GR-15) OPEN; uniformity untouched throughout.

- **2026-08-05 docs/strategy pair**: Notes reorganization (label registry
  **`notes/Pencil-labels.md`**; `Phase39-design.md` **FROZEN**, 119 anchors) and the broad
  class-uniformity recon (five directions REFUTED, three successors ranked —
  `notes/Pencil-strategy.md` **§4.6**, incl. (OUT) → §(K-Λ) *Step 5a*, `k=4 ⟺ hnoRigid` tight).

- **The route-σ arc — three landings** (2026-08-05, `sigma.py`; §(K-σ)): route σ a
  **CANDIDATE**; σ-intertwining refuted literally / confirmed covariantly; σ-equivariant
  recipes **DEAD**; obligation 1 DONE ((σ7) proven); field scope superseded by §(K-clos).

- **(K-ind) and the Δ-matroid lead BOTH REFUTED as routes** (2026-08-05; §(K-ind), §(K-Δ)):
  no induction move relates two class members (correction — pencil side runs
  `Graph.pencil_reduction`, not KT Thm 4.9); (K-Δ) (literature only) fails on two
  hypotheses, its missing ingredient the ground set, not the min-max.

- **§(K-Λ) triad** (2026-08-05): `g₁₄` clause NOT forced, Λ-completeness stands
  (`outer.py` *Step 3a*); (Λ0) PROVEN class-uniform, criterion widened to (Λ0f′)
  (`m2/lambda0.m2`); Macaulay2 layer LANDED, (Λ1) an IDENTITY over the function field
  (`m2/lambda1.m2`).

- **The 2026-08-05 research day, sixth–ninth dispatches** (§(K-flank)/§(K-pure)/§(K-Λ)/
  §(K-dom)): conjecture HOLDS at every uncovered flank (851 shapes); pure condition WRONG
  INVARIANT; (K-Λ) ⟺ (K-wit) at `ℓ = 4`; dominance HOLDS but NOT a route.

- **Harness + workbook prep** (2026-08-05, two commits; no math; 67/67 drivers re-run,
  0 changed figures) — `notes/scripts/README.md`; `Pencil-W4-informal.md`; *State of (K)* map.

- **(K-slide-comb) REFUTED class-wide; packing half uniform ((C6)); (C7) corrected**
  (2026-08-05, `kslidecomb.py`; workbook §(K-slide-comb)).

- **The 2026-08-04 pair** — (K-slide) (S1) PROVEN, (K-slide-cl) reduced to combinatorics
  (`kslide.py`/`kslidecl.py`); (K-pitch) developed, naive collinear collapse REFUTED, (T5)
  extends companions to length 4 (`pitch.py`; θ(3,3,6) CLOSED). Workbooks §(K-slide),
  §(K-slide-cl), §(K-pitch).

- **(K-tight) KT pp. 684–691 re-pin DONE — carrier escape criterion proven+validated**
  (2026-08-02, `repin.py`; workbook §(K-tight)); kernel narrowed to (K-move)/(K-pitch).

- **W4 residual arc, three landings** (2026-08-02; `Pencil-W4-informal.md`):
  kernel-widening PRICED (only `hK` widens, to **(K-res)**); **(SAFE-RES) REFUTED**
  (successor (E)+(T)+(V)); **`hnoGood'`** vacuity REFUTED (`W19`), branch 4 needs content.

- **The 2026-07-30 recon day** (`Phase39-design.md` + git): corank stratification leaves
  **(K-tight)**; (K-bare) extension NO-GO (**(K-bare-ext)**); W4 decomposed, W4-L4b pinned
  buildable, gates N8/N9/N10/N10b PASSED. Adjudications: **"C: literature hunt + A"** (K),
  **"C: cheap numerics + A"** (K-bare), **"B: L4 recon first"** (W4); option B NOT commissioned.

- **(K) route-1 gate FIRED — locality REFUTED, NO-GO** (2026-07-30, `localtest*.py`):
  (K) reduced to *stress non-constancy*; graded by (D2) (far-dependence `3(k−3)`, `k=6`).

- **The 2026-07-30 W5-L7 build day** (`hsplit` CLOSED IN FULL; `Phase39-design.md` + git):
  kernel **(K)** isolated; six leaves landed; `escapePoly` refuted by a BLOCKED build.

- **Older W5-L5/L6 / W0–W4 entries** (one-lined; detail `Phase39-design.md` + git):
  L6b triangle-free re-pin; L6a bare-pin **FALSE**; W5-L5 cut arm + `PencilPair`
  restatement; L4 `exists_pencilSeed_of_nondeg`; `Pencil/` split; W0–W3 layers.

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
