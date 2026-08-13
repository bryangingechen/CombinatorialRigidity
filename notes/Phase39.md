# Phase 39 — PENCIL: the hinge-pencil molecular conjecture (work log)

**Status:** in progress — phase stays OPEN (standing user adjudications of 2026-07-24 /
2026-07-30 / 2026-08-02, quoted verbatim in *Current state*). W0–W3 and the whole W5 arc
(L0–L7) are COMPLETE — `hsplit` CLOSED IN FULL and `hfresh`'s counting discharge landed
(2026-07-30). Only three items remain, all carried by the landed successor
`pencil_conjecture_of_hcontract_hK_hbareSplit_of_card` (`Molecule/Pencil/Escape.lean`):
`hcontract` (W4), kernel `hK`, and kernel `hbareSplit` — see *Hand-off*. **ALL FIVE
fan-outs plus the SIXTH, SEVENTH and EIGHTH directions are now COMPLETE** — thirteen
fan-out directions (A/B/C+S1–S4, T/R/M, G/Q/O, E/J, PEX/TCOL) plus CFLANK, GCAP, GUNIF
(2026-08-05 → 08-13); per-direction verdicts one-lined in *Decisions made*. Headline
positives **(FR-R1) PROVEN** and (GR-16)–(GR-28); GUNIF **REFUTED both of its targets**
at `n_hub ≥ 8`, but **(GR-15) stays OPEN throughout; class uniformity untouched by every
round.** The resulting phase-shape escalation was **RESOLVED 2026-08-13 — the research
arc CONTINUES**, a ninth direction next (prep + dispatch belong to a **fresh session**;
see *Current state* + *Hand-off*). Direction codes are **multi-letter and topic-tagged
from the fifth fan-out on** (`notes/Pencil-labels.md` (L5)); grandfathered single
letters are re-used across dates — **always date those**.

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
- **2026-08-05, dispatch ordering (user-adjudicated; RESOLVED 2026-08-06):** `g₁₄` →
  invariant-through-moves → σ-equivariance → **mechanisms pass** → Δ-matroid. The ordering's
  open tail (does route σ or §4.6's shortlist preempt the mechanisms pass?) was resolved by the
  **2026-08-06 second fan-out adjudication**: the mechanisms pass runs as direction **M**, in
  parallel with **T** ((AC-6) tight stratum) and **R** ((ANH-R1)); route σ not selected.
- **2026-08-06, third fan-out (COMPLETE, G/Q/O):** all four live leads selected (NOT route
  σ's Lean half), merged into three directions, serial O→Q→G — `notes/Pencil-fanout.md`
  §"Third fan-out". **2026-08-06, fourth fan-out (COMPLETE, E/J):** selected the (GR-10)
  min-max attack and the shared dominance lemma; serial E→J, top rung —
  `notes/Pencil-fanout.md` §"Fourth fan-out".
- **2026-08-07, fifth fan-out (COMPLETE, PEX/TCOL):** of the post-fourth-fan-out hand-off's
  five candidates the user selected (FR-R1) and the (GR-15)/(GR-4′) attack (not the (FR-6)
  follow-ons, the unselected leads (b)–(f), or route σ / W4). Serial **PEX → TCOL** (order
  load-bearing — both are colouring-existence over the same *Step G12* structure); both
  mapped top rung, **opus substituted** (fable unavailable); 10-dispatch cap **lifted**,
  rescue §1 mechanical fixups **pre-authorized**. Specs + the (L5) direction-code rule:
  `notes/Pencil-fanout.md` §"Fifth fan-out", `notes/Pencil-labels.md`.
- **2026-08-07, delegation adjudication (binds from the SIXTH direction on).** Asked at
  the session-start check-in what to do once TCOL lands, the user selected **"Keep going
  on my own judgment"** — *"After landing TCOL I pick the next direction from the
  hand-off's candidate list and continue dispatching without checking in."* This
  delegates **selection only** and changes **no** standing constraint (phase OPEN; Lean
  hold stands; W4 PARKED; `hK`/`hbareSplit` carried as pinned; option B un-commissioned).
  Supersedes the *Hand-off*'s prior "next direction awaits user adjudication" sentence;
  the same check-in's top-rung/cap/rescue calls are otherwise unchanged. The coordinator's
  picks under it, sixth direction **CFLANK** (2026-08-07), seventh direction **GCAP**
  (2026-08-13, per the 2026-08-12 refinement below) and eighth direction **GUNIF**
  (2026-08-13, **LANDED, both targets REFUTED** — see *Hand-off*), are one-lined in
  *Decisions made*.
- **2026-08-12, seventh-direction delegation (refines the above; changes no standing
  constraint).** Asked whether the standing delegation still held for the seventh
  direction, the user answered, verbatim: *"Let's have a fable subagent make the decision
  / do a reprioritization and then follow its guidance."* Selection was delegated to a
  **top-rung fable recon**, whose verdict — direction **GCAP**, CFLANK's own successor
  recommendation with three recorded corrections — the coordinator verified and
  **accepted**; LANDED 2026-08-13 (`notes/Pencil-fanout.md` §"Seventh direction",
  one-lined in *Decisions made*). Same check-in: top rung = fable (opus substitutes only
  if the weekly scoped limit runs out); the 10-dispatch cap is **lifted**; rescue §1
  mechanical fixups are **pre-authorized** — both still binding for the next dispatch.
- **2026-08-13, phase-shape adjudication (RESOLVES the escalation below; changes no
  standing constraint).** Asked to choose among the four options GUNIF's refutation
  raised — lift the Lean hold; a ninth direction on a surviving handle; package the
  arc and stop; attack strategy §2.3's wall — the user answered, verbatim: *"I think
  we should continue with the research here, but perhaps not in this session. Are we
  ready for handoff to a fresh session?"* **RESOLVED — the research arc CONTINUES**
  (the "ninth direction" option); packaging-and-stopping was **not** chosen. **Not
  lifted, not commissioned, not stopped:** the Lean hold **STANDS**, W4 stays
  **PARKED**, option B stays un-commissioned in both kernel cases, the phase stays
  **OPEN**. Which handle was not specified, so selection falls back to the standing
  2026-08-07 delegation, with the 2026-08-12 precedent that the pick may itself be
  delegated to a top-rung recon. **"Not in this session"** — the ninth direction's
  prep and dispatch are a **fresh session**'s task; see *Hand-off* for the candidate
  set.

**Kernel-(K) research arc — thirty-three docs+scripts-only dispatches, plus two
strategy-only passes** (2026-08-02 → 08-13; the second strategy pass is the 2026-08-12
fable reprioritization recon above). Mathematics: workbook `notes/Pencil-informal.md`
(**State of (K)** map = entry point / canonical per-gap status home); W4-residual
verdicts `notes/Pencil-W4-informal.md`; strategy `notes/Pencil-strategy.md`. One line
per landing in *Decisions made*, canonical with git — **not restated here**. Net
effect: the **disproof risk is removed**, every refuted route/gap carries its
successor in the gap map, and several structural positives are proven (listed per
landing in *Decisions made*); **class uniformity of the escape remains untouched by
every one of the arc's thirty-three dispatches.**

**Doc-debt, not to action now:** (a) §(K-grid)'s *State of (K)* gap-map row has
accumulated seven directions' narrative clauses in one cell, against that map's own
one-row-per-gap discipline; (b) the workbook's *Section index* line ranges were
re-synced for §(K-grid)/§(K-frame)/§(K-mech) on 2026-08-13 (~936 lines stale before),
but every row above §(K-grid) is still ~10 lines stale from older drift. Both are
compression/re-sync slices owed at the next cleanup round or phase close (meanwhile
grep the `## §(…)` heading as the durable anchor).

> **The one live candidate, and it is NOT settled — `notes/Pencil-informal.md` §(K-σ)** (the
> canonical home; the four obligations, the `--hunt` findings, the validation scope and the
> *Field scope* caveat all live there, and the *Hand-off* blockquote below carries the forward
> half — **neither is restated here**). **Route σ** = route A run at the dual seed `σu`, where
> the polarity replaces every body's point by its own panel normal; it would close (K-tight) on
> the hard stratum, *length-free*, via `Λ²Π̂(b) + Λ²Π̂(c) + α_{pt(b)} = K⁶`. It is a **candidate
> offered for adjudication**, resting on four obligations (the first verified in both directions
> and shrunk to two conditions, 2026-08-05). It is **no longer field-blocked** (2026-08-06,
> §(K-clos)): the polarity generalizes, the general-`K` transport is landed, and `ℝ` is the
> *narrowest* field choice. Standing consequences: **no gap-map status moves on account of route σ**;
> `hK` and `hbareSplit` stay carried as pinned; **W4 stays PARKED**; the phase does **not** close.

The other candidate continuations, unselected (items (a)/(g) are **DONE** as second-fan-out
directions M and R); each has a canonical home carrying the detail, not restated here.

- **(b)** **(K-wit)**, the single live form of the pitch route at companion splits (§(K-Λ);
  §(K-out)'s (OC-3) rules out any counting route to its (OUT) shortcut, and since direction O
  the (OC-8) residue is a **containment** question — §(K-out) Steps O9–O12).
- **(c)** the **W4 build** — fully decomposed and buildable, but **PARKED** by the standing
  2026-08-05 Lean-hold adjudication; does not open without a fresh user adjudication.
- **(d)** the **companion-length dichotomy** as an organizing frame (§(K-dom) *D7*); the
  concrete unprobed item is `k ≥ 4` with a **parallel `G°` edge** (`P21`-type, §(K-pure) *P4*).
- **(e)** the residual of §(K-Λ) item (vii): **two or more hubs on a length-4 companion's
  interior** — no swept family realizes one.
- **(f)** `notes/Pencil-strategy.md` §4.6's ranked shortlist — **partially superseded for
  the tight stratum by the 2026-08-12 adjudication** (durable negatives in *Hand-off*);
  U3 (`hK` as a non-existence) still unrun.

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

Full record, grounding, and the W0–W5 decomposition: **`notes/Phase39-design.md`**. One-line
verdicts, kept because each still constrains statements:

- **R1** — statement pinned in the Phase-35 containment model + `ExtensorThroughPoint`
  (dual of `ExtensorInPanel`); satisfiable for every graph; self-dual on-stratum via
  `screwComplementIso` (the polarity **generalizes** — §(K-clos) (AC-1)).
- **R2** — the conjecture survives all exact-rational rank tests; the queued warmup claim
  is *bar-joint-side*, **false** for body-hinge on dense graphs.
- **R3** — KT Lemma 6.2 / Case II survive with pinned choices; three open cores: the outer
  Thm-5.6 strip-extend, the Case-I glue (Claim 6.4), Case III's Claim 6.12 span break.

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
  `notes/scripts/README.md`). Read it before any numerics dispatch; treat any un-repointed
  copy of a lifted prohibition as stale.

## Hand-off / next phase

**The phase stays OPEN** (the 2026-07-24 adjudication — no phase-close; see *Current state*).

**`hsplit` is CLOSED IN FULL** (W5-L7c-1…6, landed 2026-07-30) and **`hfresh`'s mechanical
discharge (residue (iv)) is CLOSED too**. The landed successor
`pencil_conjecture_of_hcontract_hK_hbareSplit_of_card` (`Molecule/Pencil/Escape.lean`) wraps
`pencil_conjecture_of_hcontract_hK_hbareSplit` and carries exactly three open items, below.

> **Route σ's remaining substance is its parked LEAN half** (obligation 1; the numerics half is
> DONE — §(K-σ) *Steps σ3–σ5*, one-lined in *Decisions made*; obligation 1 shrank to two
> conditions and **(σ7)** is proven). When adjudicated open, the smallest concrete commit steers
> to a common seed via the landed `exists_common_seed_pencilRow_and_polynomials`
> (`Engine.lean:476`; the chart is **total**), carrying two design decisions: (a) which maximal
> minor per LI conjunct (the dual conjuncts are unions of basic opens); (b) **which FIELD** —
> settled as mathematics (§(K-clos): the polarity generalizes, `mapSupport` landed, `ℝ` the
> **narrowest** option), still a user call as scope. **`exists_pencilSeed_of_nondeg`
> (`Reseed.lean:65`) is NOT the bridge** (circular). Route σ faces exactly **one** crux (the
> workbook's two kills of M₁ share one stated reason — the `hinge(vb) := q(ab)` pinning).
> **BLOCKED by the standing 2026-08-05 Lean-hold adjudication (general, not W4-scoped)**; does
> not open without a fresh user adjudication.
>
> **The FIRST through EIGHTH directions are ALL COMPLETE** — first (A/B/C), the harness
> re-baselining round (S1–S4), second (T/R/M), third (G/Q/O), fourth (E `cdd23d30` / J
> `12edc305`), fifth (PEX `b32c1c2c` / TCOL `cd0af9e1`), sixth (CFLANK `a46eb5c5`), seventh
> (GCAP `b48cad79`), eighth (GUNIF `77840be4`, corrective pass `0a13c228`); each
> direction one-lined in *Decisions made* (with dates), its workbook section the
> canonical home, every driver coordinator-re-run.
>
> **2026-08-07 delegation (supersedes "next direction awaits user adjudication" above).**
> Asked at check-in what to do once TCOL lands, the user selected **"Keep going on my own
> judgment"** — the coordinator picks the next direction and dispatches without checking
> in (selection only; every standing constraint unchanged — see *Current state*). Its
> picks — **SIXTH CFLANK** (a structural flank against **(GR-15)** at TCOL's item (v)) and
> **SEVENTH GCAP** — both **LANDED**: `notes/Pencil-fanout.md` §§"Sixth"/"Seventh
> direction"; deliveries recorded there and in *Decisions made*, not repeated here. **No
> flank found either time; (GR-15) stays OPEN, unchanged in status.**
>
> **Two durable negatives from the same adjudication — do not re-run:** (i) strategy
> §4.6's shortlist is **partially superseded** for the tight stratum — U2's demand is
> exactly what §(K-grid) (GR-16)'s hub-multigraph reduction **delivered**; U3's
> negative-form insight is already exploited by the cap/budget style; (ii) the symbolic
> meta-option ("upgrade §(K-Λ)'s 38-strata evidence via M2") is **landed, not pending**
> (`m2/lambda0.m2`, 2026-08-05) — only strategy §5.3 item (i) (whole-graph elimination)
> remains, ruled out by §5.3's own local-frame feasibility boundary.
>
> **TERMINATION test for the (GR-15)/grid line — checked on GCAP's return, did NOT
> fire** (a cap and new mechanisms were named), so the coordinator dispatched the
> **EIGHTH direction, GUNIF**, **LANDED 2026-08-13, REFUTING BOTH TARGETS**
> (`notes/Pencil-fanout.md` §"Eighth direction"; workbook §(K-grid) *Steps G34–G37*,
> one-lined in *Decisions made* — the full (GR-29)/(GR-30)/(GR-31) detail not
> repeated here). **Per-shape (GR-15) HOLDS at every new witness; (GR-15) itself
> stays OPEN, unchanged** — the refutation kills the certificate-3 *uniformity
> route*, not the statement.
>
> **The literal TERMINATION test still does not fire on GUNIF's return** (a cap
> *was* proven, (GR-29), and new mechanisms *were* named) — **it is the
> REFUTATION of the line's named positive-termination path that triggered the
> escalation**: "cap + the `Λ ≠ ∅` flip + the `D > 0` lift + (GR-4′) = (GR-15)
> proven = `hK` discharged" is **DEAD AS SPECIFIED**, its first ingredient false
> in general (from `n_hub = 8` on, GR-30).
>
> **The escalation is RESOLVED (2026-08-13, verbatim in *Current state*): the
> research arc CONTINUES.** **The next concrete commit is a fresh session's: prep
> the NINTH direction** — spec it into `notes/Pencil-fanout.md` §"Ninth direction" +
> reserve its namespace in `notes/Pencil-labels.md`, the shape the seventh and
> eighth directions used — then dispatch top rung; selection under the standing
> 2026-08-07 delegation (or its own 2026-08-12-style recon delegation).
>
> **Candidate set, four items — the fourth changes the ranking; none is selected.**
> GUNIF's own named handles (§(K-grid) *Step G37*): **(1)** a repair theorem
> "distance ≤ `g`" (measured equal at all four (GR-30) witnesses); **(2)**
> exact-alignment thinness of binding colourings (measured, not proven); **(3)**
> the (GR-29) ledger itself as a **positive tool**, naming exactly where a
> binding-at-`g ≥ 2` configuration must live. **(4)**, a coordinator finding of
> this session not yet elsewhere in the docs: **build the `n_hub = 8`
> enumerator** — a degree-pruned cubic-multigraph generator with isomorphism
> rejection, opening the ~190 050 **labelled** cubic multigraphs there (CFLANK's
> *What would change this* item (iv), §(K-grid) *Step G28*), dedup the whole
> cost. **The argument, plainly:** GUNIF *proved* the arc's entire `D = 0`
> evidence base — CFLANK's 40 742-shape hunt (GR-26) and GCAP's 549 172-block
> sweep (GR-28) alike — was swept at `n_hub ∈ {2,4,6}` only, a stratum the
> (GR-29) ledger shows *cannot* exhibit the (GR-28)(iv) failure, which appears
> at the first size beyond it. The arc is **systematically blind past
> `n_hub = 6`**, and (4) alone *removes* the blindness rather than working
> inside it — **compute engineering, not mathematics**, but arguably the
> **highest-value** of the four right now. Selection stays the fresh session's,
> under the standing delegation.
>
> **Coordinator hand-off note, still not loaded onto any direction:** whether (GR-15) as
> quantified ("every tight class shape") also covers the `W19`-type **(K-res)** sibling
> habitat is unresolved — pin it when the tight side closes, not before.
>
> **Not selected at the 2026-08-07 adjudication**, and so not open: the **(FR-6) follow-ons**
> (§(K-frame) *What would change this* items (ii)–(iv) — the `ℓ_min = 5` battery beyond
> θ(3,4,5), the (FR-7) irreducibility foothold, the (AC-9) anti-correlation's structurality),
> the unselected leads (b)–(f) above, and the parked Lean half of route σ / the W4 build.
>
> Deliberate non-goals: (Λ0), (Λ1), the `g₁₄` clause, §(K-ind), §(K-Δ), **§(K-clos)'s field
> question**, **§(K-ann)'s settled batch** ((ANH-1)–(ANH-6), (SD-6)) and **§(K-out)'s settled
> batch** ((OC-1)–(OC-7); the two pools are pinned and **disjoint**) are **done** — do not
> re-derive, re-sweep, re-run their literature hunt, re-open "does the polarity generalize?",
> re-measure (D2)'s far block, re-sample POOL-G or POOL-S, **propose a counting / matroid route
> to (OUT)'s hypothesis** ((OC-3) refutes the whole class), or touch `lambda.py`'s figures — the
> one carve-out, the re-baselining round's slice **S3**, is **spent**: it edited `lambda.py` on
> purpose (OPENED-block scope (3), coding the landed (Λ0f′) in place of the superseded (Λ0f)) and
> moved exactly the one recorded figure it was licensed to, `outer.py --geom`'s.
> **W4 stays parked** despite being fully decomposed and buildable (no W4 build without a fresh
> user adjudication), `hK`/`hbareSplit` stay carried as pinned, option B in both kernel cases
> stays un-commissioned.

The three carried items:

- **`hcontract`** (W4) — **fully decomposed, buildable, and PARKED.** Canonical home:
  `notes/Phase39-design.md` §"W4 decomposition recon" + §"W4-L4 identification recon" (the
  canonical leaf list lives THERE), residual mathematics in `notes/Pencil-W4-informal.md`. State:
  the L4 verdict trades minimality for the pencil habitat's `hcard` bound, so the co-1 case closes
  minimality-free and KT's non-simple-contraction trigger provably reduces to it; the residual
  carry narrows to **`hnoGood'`**, whose vacuity conjecture is **REFUTED** (2026-08-02,
  `|V| = 19`), so branch 4 needs content. **Route ADJUDICATED (2026-08-02): route 3, packaging
  (b)** — the structure-theorem-pinned dispatch invariant (W4 workbook §(SAFE-RES)'s (C7)/(C8)
  split; the collision with §(K-slide-comb)'s same-numbered labels is registered in
  `notes/Pencil-labels.md`), with **(K-res)** carried as a sibling of
  the byte-identical `hK`. **Recorded, not built — W4 stays parked**; when commissioned the next
  concrete commit is **W4-L4b** (`exists_degree_two_of_co1_rigid`, pinned + spike-elaborated, all
  bricks landed, 1 commit), then order-flexibly W4-L1/L2/L3′ and the W4-L5 arc. Gates
  N8/N9(+rank-29 control)/N10/N10b all PASSED (`notes/scripts/w4/hybrid_gates.py`).
- **`hK`** (kernel (K), research) — the escape `≢ 0` uniformity kernel, and the phase's hardest
  open item. **Standing adjudication ("C: literature hunt + A", verbatim, 2026-07-30): keep
  carrying `hK` as pinned; option B is NOT authorized.** Both literature hunts are MISSes
  (2026-07-30 rigidity-side; 2026-08-05 Δ-matroid-side, §(K-Δ)). Since the 2026-08-02 W4
  route-3(b) adjudication `hK` also carries the **(K-res)** residual habitat as a
  byte-identical sibling (structural reading: §(K-ind) *I5*).
  **The mathematics is NOT restated here.** Canonical home: `notes/Pencil-informal.md` — its
  **State of (K)** gap map is one row per named gap, each with status, what would close it, and
  what it is conditional on, plus the uncovered-shape list and a *settled, do not re-derive*
  block. Read that map, not this bullet, before any (K) work; update it in place.
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

- **The EIGHTH direction — GUNIF LANDED 2026-08-13** (`w4/gunif.py`; canonical home
  §(K-grid) Steps G34–G37). **REFUTED both targets**: (GR-28)(iv) at `k ≥ 3` refuted
  with an exact boundary — theorem at `n_hub ≤ 6` (GR-29), false from `n_hub = 8`
  (GR-30); repair theorem unprovable as posed (GR-31). Per-shape (GR-15) HOLDS at
  every witness, itself **stays OPEN**; route DEAD (candidate set + the 2026-08-13
  "continue" adjudication: *Hand-off*). **Coordinator corrective pass
  2026-08-13, docs only** (one rung up, gate-invisible defects found in
  verification): the (GR-28)(iv) status move completed inside the canonical
  gap-map cell and two other §(K-grid) sites, GCAP's answered *What would change
  this* leads marked, and **four merged draft-scaffolding blocks stripped** (E /
  TCOL / GCAP / GUNIF) after auditing every action each listed — all verified
  performed, so nothing was buried; prophylactic in `notes/Pencil-fanout.md`'s
  landing checklist (item 6).

- **The SIXTH and SEVENTH directions — CFLANK LANDED 2026-08-07, GCAP LANDED
  2026-08-13** (`w4/cflank.py`, `w4/gcap.py`; canonical homes §(K-grid) Steps
  G24–G28 / G29–G33). Eight proven results (GR-21)–(GR-28): excess law, five sparsity
  caps, flip injection, private-branch repair, cut criterion, a 40 742-shape exhaustive
  hunt, exact computability of the (GR-8) maximum, the closed defect formula — TCOL's
  two flank sites closed **AS ROUTES**, certificate-3 **proven per swept shape**;
  GCAP's `g ≤ 1` cap at `k ≥ 3` **since REFUTED by GUNIF**. **(GR-15) stays OPEN**;
  `§(K-gcap)`/`GC-` unopened; uniformity untouched.

- **The FIRST through FIFTH fan-outs — all LANDED 2026-08-05…08-07** (canonical homes
  the workbook sections named; commits `d5ae55aa`…, `cdd23d30`, `12edc305`, `b32c1c2c`,
  `cd0af9e1`). Thirteen directions (A/B/C+S1–S4, T/R/M, G/Q/O, E/J, PEX/TCOL); headline
  positives **(GR-9)**/**(FR-R1)** PROVEN, (GR-15) OPEN; uniformity untouched throughout.

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
