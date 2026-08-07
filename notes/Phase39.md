# Phase 39 — PENCIL: the hinge-pencil molecular conjecture (work log)

**Status:** in progress — phase stays OPEN (standing user adjudications of 2026-07-24 /
2026-07-30 / 2026-08-02, quoted verbatim in *Current state*). W0–W3 and the whole W5 arc
(L0–L7) are COMPLETE — `hsplit` CLOSED IN FULL and `hfresh`'s counting discharge landed
(2026-07-30). Only three items remain, all carried by the landed successor
`pencil_conjecture_of_hcontract_hK_hbareSplit_of_card` (`Molecule/Pencil/Escape.lean`):
`hcontract` (W4), kernel `hK`, and kernel `hbareSplit` — see *Hand-off*. Kernel-(K) research
is at its thirty-first docs+scripts-only pass (workbook `notes/Pencil-informal.md`; the settled
W4-residual arc is `notes/Pencil-W4-informal.md`). **ALL FIVE rounds are now COMPLETE** —
first fan-out A/B/C, the harness re-baselining round S1–S4, second fan-out T/R/M, third
fan-out G/Q/O (2026-08-06), fourth fan-out E/J (2026-08-07), fifth fan-out PEX/TCOL
(2026-08-07, PEX **(FR-R1) PROVEN**, TCOL four structural results proven but **(GR-15)
stays OPEN — no flank found**; full verdicts in *Decisions made*). **The user has
delegated next-direction selection to the coordinator** ("keep going on my own judgment",
2026-08-07 — see *Hand-off*); the **sixth direction, CFLANK**, is PREPPED (not yet
dispatched) — `notes/Pencil-fanout.md` §"Sixth direction". **Class uniformity remains
untouched by every round.**
Direction codes are **multi-letter and topic-tagged from the fifth fan-out on**
(`notes/Pencil-labels.md` clause **(L5)**); the grandfathered single letters are re-used
across dates — **always date those**.

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
  the session-start check-in "TCOL is the fifth fan-out's last direction. When it lands,
  what should I do?", the user selected **"Keep going on my own judgment"** — *"After
  landing TCOL I pick the next direction from the hand-off's candidate list and continue
  dispatching without checking in."* This delegates **selection only** and changes **no**
  standing constraint: the phase stays OPEN, the 2026-08-05 Lean hold stands, W4 stays
  PARKED, `hK`/`hbareSplit` stay carried as pinned, option B in both kernel cases stays
  un-commissioned. Supersedes the *Hand-off*'s prior "next direction awaits user
  adjudication" sentence — the same check-in's top-rung/cap/rescue calls (above bullet)
  are otherwise unchanged. The coordinator's first pick under this delegation is the
  **sixth direction, CFLANK** — `notes/Pencil-fanout.md` §"Sixth direction".

**Kernel-(K) research arc — thirty docs+scripts-only dispatches, plus one strategy-only
pass** (2026-08-02 → 08-07).
Mathematics: the workbook `notes/Pencil-informal.md`, whose **State of (K)** map is the entry
point, the canonical per-gap status home, and the artifact a pass *updates*; settled
W4-residual verdicts are in `notes/Pencil-W4-informal.md`; strategy in
`notes/Pencil-strategy.md`. One line per landing in *Decisions made*, which with git is the
canonical dispatch record — **neither the landings nor the per-gap statuses are restated
here**. Net effect: the **disproof risk is removed**; every refuted route/gap is recorded in
the gap map with its successor; the arc's structural positives are (Λ1), §(K-ann)'s recipe,
§(K-out)'s **proven combinatorial half** ((OC-10)), §(K-grid)'s **proven tree-triple theorem**
((GR-9)), and §(K-frame)'s **minimal dominance lemma** ((FR-1)–(FR-4)), now discharged in
full on the bare-cycle stratum by PEX ((FR-R1) PROVEN); TCOL added four more proven
structural results on the tight stratum ((GR-16)–(GR-19)) without closing (GR-15); **class
uniformity of the escape remains untouched by every one of the arc's thirty dispatches.**

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

The other candidate continuations, unselected, without preference; each has a canonical home
that carries the detail, so they are **not** restated here. (Former items (a)/(g) — the
mechanisms pass and the (ANH-R1) probe — are **DONE** as second-fan-out directions M and R.)

- **(b)** **(K-wit)**, the single live form of the pitch route at companion splits (§(K-Λ);
  §(K-out)'s (OC-3) rules out any counting route to its (OUT) shortcut, and since direction O
  the (OC-8) residue is a **containment** question — §(K-out) Steps O9–O12).
- **(c)** the **W4 build** — fully decomposed and buildable, but **PARKED** by the standing
  2026-08-05 Lean-hold adjudication; does not open without a fresh user adjudication.
- **(d)** the **companion-length dichotomy** as an organizing frame (§(K-dom) *D7*); the
  concrete unprobed item is `k ≥ 4` with a **parallel `G°` edge** (`P21`-type, §(K-pure) *P4*).
- **(e)** the residual of §(K-Λ) item (vii): **two or more hubs on a length-4 companion's
  interior** — no swept family realizes one.
- **(f)** `notes/Pencil-strategy.md` §4.6's ranked shortlist: U1 **half delivered**, U2's
  ground set survives (its cocircuit/circuit duality corrected), **U3** (`hK` as a
  non-existence) still unrun.

**Read `notes/Pencil-strategy.md` before choosing anything else** — the post-fan-out strategic
record (why class uniformity resists, what the KT formalization yielded, the candidate stronger
invariants with **C1 run and struck**, §5's symbolic assessment); its header is its own table of
contents. **Its §4.6** is the entry point for any attack on the crux: six refutations plus the
ranked `U1`–`U3` shortlist, each with its cheapest decisive experiment.

**Any (K)- or W4-side numerics dispatch starts from `notes/scripts/README.md`**, and a symbolic
one also from `notes/scripts/m2/README.md`. Detail in *Blockers* — not restated here.

File layout: `Molecule/Pencil.lean` split into `Molecule/Pencil/{Statement,Arms,Motive,Chart,
Engine,Reseed,Witness,Steer,Pair,Pair2,Escape,Base}.lean`. Full per-leaf history:
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

- **R1** — statement pinned in the Phase-35 containment model + a per-body homogeneous
  concurrency point (`ExtensorThroughPoint`, dual of `ExtensorInPanel`); satisfiable for every
  graph; self-dual on-stratum via `screwComplementIso` (in tree over `ℝ`; the polarity itself
  **generalizes** — §(K-clos) (AC-1)). Dense `K4`/`K3,3`/θ(2,2,2): the stratum collapses.
- **R2** — the conjecture survives all exact-rational rank tests; the deep all-coplanar locus is
  deficient exactly when `2|E| < 3|V| − 3`, so the queued claim is *bar-joint-side*, **false**
  for body-hinge on dense graphs.
- **R3** — KT Lemma 6.2 / Case II survive with pinned choices; three open cores: the outer
  Thm-5.6 strip-extend, the Case-I glue (Claim 6.4), Case III's Claim 6.12 span break.

## Blockers / open questions

**All W5 blockers are CLOSED** (2026-07-24 → 07-30; verdicts one-lined in *Decisions made*, full
record in `notes/Phase39-design.md` + git). **One residual note from the L5 cut arm still
stands** because it constrains future statements: feasibility propagation *as a proposition* is
refuted for any purely combinatorial (`≤3`-closedHubNbhd) criterion
(`not_pencilNondegFeasible_of_triangle_two_hubs`); it does not touch L6's own habitat claim.

- **Open: kernels (K) and (K-bare), and W4 (`hcontract`)** — the entire remaining work of the
  phase; see *Hand-off* for the per-item route and the `notes/Phase39-design.md` pointers. W4 is
  fully decomposed (recons of 2026-07-30): buildable leaves W4-L4b/L1/L2/L3′/L5 plus the carried
  `hKc`/`hbareContract`/`hnoGood'`; the build sequence awaits commissioning. **`hnoGood'` is
  known NON-vacuous** (2026-08-02) — branch 4 needs content; routes in
  `notes/Pencil-W4-informal.md` §"`hnoGood'` vacuity", adjudication owed. **(SAFE-RES) is
  REFUTED** (same day); routes 1/3 now cost §(SAFE-RES)'s (T) + (V) + the reduced (E), with (T) a
  genuine research gap, plus **one** widened kernel (K-res).
- The full biconditional transport `ExtensorThroughPoint C q ↔ ExtensorInPanel (screwComplementIso
  C) q` (design doc's W0 pin) is landed only as its two forward implications; the reverse arms
  need a `complementIso` involution lemma, not in tree — deferred, **off every critical path**
  (§(K-σ) *Step σ6*: route σ does not need it, and sketches the route to it).
- **Harness debt — CLEARED, round CLOSED** (2026-08-06, S1–S4; canonical home
  `notes/scripts/README.md` *Harness debt* → **CLOSED**). Read it before any numerics dispatch;
  treat any un-repointed copy of a lifted prohibition as stale.

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
> **The FIRST through FIFTH fan-outs are ALL COMPLETE** — first (A/B/C), the harness
> re-baselining round (S1–S4), second (T/R/M), third (G/Q/O), fourth (E `cdd23d30` / J
> `12edc305`), fifth (PEX `b32c1c2c` / TCOL `cd0af9e1`); each direction one-lined in
> *Decisions made* (with dates), its workbook section the canonical home, every driver
> coordinator-re-run.
>
> **2026-08-07 delegation (supersedes "next direction awaits user adjudication" above).**
> Asked at check-in what to do once TCOL lands, the user selected **"Keep going on my own
> judgment"** — the coordinator now picks the next direction and dispatches without
> checking in (selection only; every standing constraint is unchanged — see *Current
> state*). Pick: the **SIXTH direction, CFLANK** — a single direction (not a fan-out)
> targeting a structural flank against **(GR-15)**, TCOL's item (v) — **PREPPED,
> dispatches next**: `notes/Pencil-fanout.md` §"Sixth direction";
> `notes/Pencil-labels.md`.
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
  route-3(b) adjudication `hK` also carries the **(K-res)** residual habitat as a byte-identical
  sibling — and §(K-ind) *I5* now gives that packaging a structural reading: **(K-res) is the
  boundary of the class under the induction's own move.**
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

- **The SIXTH direction — CFLANK adjudicated (delegation) and prepped, 2026-08-07, not yet
  dispatched.** The user delegated next-direction *selection* (no standing constraint) to the
  coordinator ("keep going on my own judgment" — *Current state*); the coordinator picked
  TCOL's own *What would change this* item (v) — a targeted structural flank against
  **(GR-15)** — as **direction CFLANK**, minted under (L5), reserving **§(K-prof)** / `PF-`
  (0-hit verified) as the unclaimed tail of §(K-grid)'s family. Mapped top rung, opus
  substituted. Spec `notes/Pencil-fanout.md` §"Sixth direction"; reservation
  `notes/Pencil-labels.md`.

- **The FIFTH fan-out — both directions LANDED 2026-08-07** (PEX `b32c1c2c`, TCOL
  `cd0af9e1`; canonical homes the workbook sections named). *PEX, §(K-frame) continuation Steps
  FR7–FR11, `patexist.py`*: the bare-cycle stratum PROVEN **finite** (22 iso classes / 76
  sites / 1976 labelled instances) and exhaustively enumerated; **(FR-R1) PROVEN**, (FR-4)'s
  named gap the sole rider. *TCOL, §(K-grid) continuation Steps G19–G23, `gridcol.py`*: four
  structural results PROVEN — the branch-level reduction (GR-16), the circuit run law
  (GR-17), the 6-spanning-tree packing statement (GR-18), collapse order 4 at all 18 habitat
  separators (GR-19) — but **(GR-15) stays OPEN, no flank found**. Uniformity untouched by
  both.

- **The FOURTH fan-out — both directions LANDED 2026-08-07** (E `cdd23d30`, J `12edc305`;
  canonical homes the workbook sections named). *E* (§(K-grid) Steps G14–G18, `packmm.py`):
  the (GR-10) min-max REFUTED as posed (NP-complete at exact balance, (GR-13)); (GR-10)
  itself survives exhaustive enumeration; residual re-aimed at (GR-15). *J* (new section
  §(K-frame), `framedom.py`+`.m2`): the chart-to-frame dominance lemma delivered in minimal
  form ((FR-1)–(FR-3)), transport by `G′`-regridding (FR-4); (ANH-14) discharged 1904/1904
  sites (FR-5); residue (FR-R1) — now PROVEN by PEX. Uniformity untouched by both.

- **The THIRD fan-out — all three directions LANDED 2026-08-06** (canonical homes the
  workbook sections named). *G* (§(K-grid) Steps G8–G13, `gridwit.py`): (GR-4)
  refuted-and-repaired ((GR-4′)), tree-triple theorem (GR-9) PROVEN. *Q* (§(K-ann) Steps
  A14–A17, `anhr1.py`/`anhr1.m2`): the "upgrade" premise refuted; ONE universal irreducible
  degree-12 polynomial governs the bare-cycle stratum (ANH-14). *O* (§(K-out) Steps O9–O12,
  `outerwide.py`/`.m2`): the availability map FORCED (OC-10). All three converged on
  chart-to-frame dominance — delivered by J, discharged by PEX. Uniformity untouched.

- **The SECOND fan-out — all three directions LANDED 2026-08-06** (canonical homes the
  workbook sections named): *T* (§(K-grid)) and *R* (§(K-ann)) both **superseded in detail**
  by later fan-outs (G/E and Q respectively); *M* (§(K-mech), `mech.py`) mechanised both
  §(K-pure) *P8* anomalies in one calculus, rescuing 6v11e ((MX-7)), σ rider NO ((MX-8)).
  Uniformity untouched by all three.

- **The harness re-baselining round — all four debt items CLEARED, round CLOSED** (2026-08-06,
  five commits `d5ae55aa`…S4; trigger dispatch-log **F13**). Canonical home:
  `notes/scripts/README.md` *Harness debt* → **CLOSED**. 260 invocations, 21 figures moved, each
  repointed in its moving commit. Two moves are mathematics: **(AC-9)** (§(K-clos)), **(OC-9)**
  (§(K-out)). **No gap-map row moved.**

- **The 2026-08-06 three-way kernel-(K) fan-out — three landings** (*C* `closure.py` §(K-clos):
  the field question SETTLED, `ℝ` the narrowest choice; *A* `annih.py` §(K-ann): the arc's first
  RECIPE, residual (ANH-R1); *B* `outerline.py` §(K-out): (OUT) MEASURED, headline the negative
  (OC-3)). Same day: §2.3's convergence note — A's and B's residuals are one shape.

- **Notes reorganization: label registry opened; workbook and design doc INDEXED, not split or
  compressed** (2026-08-05, docs only). Canonical home **`notes/Pencil-labels.md`**. Two argued
  skips: no `notes/pencil/` move; **`Phase39-design.md` FROZEN** (119 anchors).

- **Broad class-uniformity recon: five directions REFUTED, three live successors ranked**
  (2026-08-05; canonical home `notes/Pencil-strategy.md` **§4.6**). Refuted: `∀λ`, the `Gr(3,6)`
  cluster structure (a **third** ambient-ground-set MISS), moment-curve/positivity, the
  codimension comparison, definable choice/QE, "choose the split to force `k = 4`". One new
  derivation **(OUT)** → §(K-Λ) *Step 5a*. Calibration: **`k = 4` ⟺ `hnoRigid` is tight**.

- **The route-σ arc — three landings; canonical home workbook §(K-σ)** (2026-08-05, `sigma.py`).
  **Route σ a CANDIDATE** (route A at `σu`, `★r ∥ C(bc)`); σ-intertwining **REFUTED literally,
  CONFIRMED covariantly** (§(K-Λ)'s failure locus is a σ-orbit); **σ-equivariant recipes DEAD**;
  obligation 1's numerics half **DONE** (`--hunt`: dual conjuncts **NOT** implied — 53
  counterexamples, an F11-class correction to *Step σ4*'s 63/63 — shrunk to two conditions,
  steering exact, **(σ7)** proven); field scope **superseded 2026-08-06** by §(K-clos).

- **(K-ind) REFUTED as a route — no move of the induction relates two class members**
  (2026-08-05, workbook §(K-ind), no driver): tight ⟺ `(5c+1, 6c)`, `splitOff` fixes `G°`, the
  class is a finite antichain, and the failure locus is a **divisor** whose only numerical
  invariant *is* `hK` — circular as posed. **Correction: the pencil side does NOT run KT Thm 4.9**
  — it is `Graph.pencil_reduction`, `hK` entering only via `pencilPair_of_splitOff_of_habitat`.

- **(K-Δ): the Δ-matroid / orthogonal-matroid lead is CHECKED AND REFUTED** (2026-08-05, workbook
  §(K-Δ), literature only) — two fatal hypothesis failures (the subject's objects are *totally
  isotropic*, `V_bc` never is; its ground set is `[3]` and never grows), so §7's lead is
  discharged and §2.2 sharpens to **the missing ingredient is the ground set, not the min-max**.

- **The `g₁₄` clause is NOT forced by any class habitat — Λ-completeness stands as written**
  (2026-08-05, `outer.py`; workbook §(K-Λ) *Step 3a*). Residual: ≥ 2 hubs on a companion interior.

- **(Λ0) + the `a`-line spans PROVEN at the generic point, CLASS-UNIFORM; the recorded criterion
  was INCOMPLETE** (2026-08-05, `m2/lambda0.m2`; §(K-Λ)) — **(Λ0f′)**; uniform because (Λ0) is
  far-graph-free and (K-wit) is not.

- **The Macaulay2 layer LANDED; (Λ1) is an IDENTITY over the function field** (2026-08-05,
  `m2/lambda1.m2`; §5.4's conventions bind, ungauged expansion does not finish). Same commit made
  the figure-invariance gate proportionate.

- **The 2026-08-05 research day, sixth–ninth dispatches** (canonical homes §(K-flank), §(K-pure),
  §(K-Λ), §(K-dom)): the conjecture HOLDS at every uncovered flank (851 shapes); the pure
  condition is the WRONG INVARIANT ((PC-Z)/(K-chord) the successors); (K-Λ) REFUTED as an
  independent gap (⟺ (K-wit) at `ℓ = 4`); dominance HOLDS but is NOT a route ((D1)–(D3)).

- **Harness + workbook prep** (2026-08-05, two commits; no mathematics, no verdict changes; 67/67
  drivers re-run, 0 changed figures) — `notes/scripts/README.md`;
  `notes/Pencil-W4-informal.md`; `W19`/`S29` + the *State of (K)* map.

- **(K-slide-comb) REFUTED class-wide; the packing half made uniform ((C6)); (C2)'s length-4
  entry corrected ((C7))** (2026-08-05, `kslidecomb.py`; workbook §(K-slide-comb)) — the
  colouring premise fails inside the class; **(C6)** proven at every class shape (Edmonds), so
  the packing is never the obstruction; **(C7)**: `K4` coverage 439→702/877.

- **(K-slide) (S1) PROVEN; (K-slide-cl) reduced to combinatorics** (2026-08-04,
  `kslide.py`/`kslidecl.py`; workbooks §(K-slide), §(K-slide-cl)) — one exact limit witness
  closes a split (23/23 pitched; parallel `G°`-edges order-0-obstructed, leaving `P21`).

- **(K-pitch) developed; naive collinear collapse REFUTED; (T5) extends companions to length 4**
  (2026-08-04, `pitch.py`; workbook §(K-pitch)) — (T1)–(T4), the sign law, the five-bracket
  monomial (θ(3,3,6) CLOSED; 29/29); weakest exact forms (K-wit)/(K-pitch-∞).

- **(K-tight) KT pp. 684–691 re-pin DONE — carrier escape criterion proven+validated; every
  recorded escape failure was a sampler artifact** (2026-08-02, `repin.py`; workbook
  §(K-tight)); kernel narrowed to (K-move)/(K-pitch).

- **W4 residual arc, three landings (2026-08-02; canonical home `notes/Pencil-W4-informal.md`).**
  Kernel-widening **PRICED** — only `hK` widens, to **(K-res)** (`widened.py`); **(SAFE-RES)
  REFUTED**, successor (SAFE-RES′) = (E) + (T) + (V), with **(T)** not landed-reachable (`S29`,
  `saferes.py`); **`hnoGood'` vacuity REFUTED** via the Ear Lemma (`W19`, `nogood_subdiv.py`), so
  branch 4 needs content and the residual **structure theorem** survives as route 3(b)'s pin.

- **The 2026-07-30 recon day (one-lined; every verdict is carried forward in the matching
  *Hand-off* bullet — full record `notes/Phase39-design.md` + git).** *(K) non-constancy —
  PARTIAL*: corank stratification by `index(G) = 5|E| − 6(|V|−1)`, leaving **(K-tight)** as the
  hard kernel. *(K-bare) extension route — NO-GO on landed machinery*: minimal open statement
  **(K-bare-ext)**. *W4 decomposition + W4-L4 identification*: minimality traded for feasibility,
  W4-L4b pinned buildable, gates N8/N9/N10/N10b PASSED. User adjudications, verbatim:
  **"C: literature hunt + A"** (K), **"C: cheap numerics extensions + A"** (K-bare), **"B: L4
  recon first"** (W4). Option B in both kernel cases: **NOT commissioned.**

- **(K) route-1 gate FIRED — locality REFUTED, NO-GO** (2026-07-30, `escape/localtest*.py`) —
  with identical radius-1 chain data the escape's zero locus moves with the far graph, killing
  route 1 and route 2's pointwise reuse; (K) reduced instead to *stress non-constancy*. (Since
  **graded** by (D2): far-dependence is `3(k−3)`, and the gate was run at the maximal `k = 6`.)

- **The 2026-07-30 W5-L7 build day** (`hsplit` CLOSED IN FULL; canonical record
  `notes/Phase39-design.md` + git): recon isolated kernel **(K)**; L7a–L7c landed six leaves
  ending at `pencil_conjecture_of_hcontract_hK_hbareSplit`, then `hfresh`'s residue (iv) and
  the consumer headline; `escapePoly` refuted by a BLOCKED build (dispatch-log F9 ×2).

- **Older W5-L5/L6 / W0–W4 entries (one-lined; canonical detail in `notes/Phase39-design.md`
  + git).** W5-L6: L6b re-pinned **triangle-free** (the spike refuted the `hcard`-only pin),
  headline `pencilNondegFeasible_of_ncard_closedHubNbhd_le_three_of_triangleFree` (`Steer.lean`);
  L6a's invariant + safe-vertex transfer (the bare pin was **FALSE**, 10-vertex counterexample);
  L6d's triangle-free split-off. W5-L5: the full cut arm (sub-cases i–v, `hcutPendant3` inline),
  the user-adjudicated route-(b′) `PencilPair` restatement, base and loop arms; L4
  `exists_pencilSeed_of_nondeg`; `Pencil.lean`→`Pencil/` split. W3: L7 `pencil_conjecture_of_arms`,
  the L4 cut arm, L1/L2. W2/W1/W0: the extensor-pair layer, the statement layer, self-duality.

- **Promoted out of this phase** (one-line pointers; the cross-references carry the content):
  TACTICS-GOLF §11/§22/§23; TACTICS-QUIRKS §46/§96/§99/§100/§101/§102/§103/§104; FRICTION
  `exists_injOn_mapsTo_of_ncard_le` + `extensor_pair_smul` [mirror-candidate] and the
  omega/`Set.ncard`-atom idiom.

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
