# Phase 39 — PENCIL: the hinge-pencil molecular conjecture (work log)

**Status:** in progress — phase stays OPEN (standing user adjudications of 2026-07-24 /
2026-07-30 / 2026-08-02, quoted verbatim in *Current state*). W0–W3 and the whole W5 arc
(L0–L7) are COMPLETE — `hsplit` CLOSED IN FULL and `hfresh`'s counting discharge landed
(2026-07-30). Only three items remain, all carried by the landed successor
`pencil_conjecture_of_hcontract_hK_hbareSplit_of_card` (`Molecule/Pencil/Escape.lean`):
`hcontract` (W4), kernel `hK`, and kernel `hbareSplit` — see *Hand-off*. Kernel-(K) research
is at its twenty-seventh docs+scripts-only pass (workbook `notes/Pencil-informal.md`; the settled
W4-residual arc is `notes/Pencil-W4-informal.md`). **ALL FOUR earlier 2026-08-06 rounds are
COMPLETE** (first fan-out A/B/C; the harness re-baselining round S1–S4; second fan-out T/R/M;
third fan-out G/Q/O — net shape: the tight stratum hangs on **(GR-10) alone** with the geometry
proven ((GR-9)), and directions O/Q terminated at one shared residue, **chart-to-frame
dominance**). **The FOURTH fan-out — directions E ((GR-10) min-max) / J (the shared dominance
lemma), user-adjudicated 2026-08-06, dispatched SERIALLY E → J at the top rung — is IN FLIGHT**
(specs: `notes/Pencil-fanout.md` §"Fourth fan-out"; see *Hand-off*).
Fan-out direction letters are re-used across dates — **always date them**.

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
- **2026-08-06, third fan-out:** of the post-second-fan-out hand-off's five live leads the user
  selected **all four research leads** (T/R convergence target; per-shape M2 identity; (K-wit)
  via (OC-8); widen `outerline.py --comb`) and NOT route σ's parked Lean half; a same-session
  follow-up: **dispatch serially, not in parallel** (token budget), O and Q at opus, G at the
  top rung. Coordinator merged leads 3+4 into direction **O** (one section's continuations).
  Specs + rationale: `notes/Pencil-fanout.md` §"Third fan-out".
- **2026-08-06, fourth fan-out:** of the post-third-fan-out hand-off's four candidate
  directions the user selected **(1) the (GR-10) min-max attack** and **(2) the shared
  chart-to-frame dominance lemma**, and NOT the unselected leads (b)–(f) or the parked Lean
  half (route σ / W4) — the Lean hold stands. Serial dispatch (the session default), order
  E → J; both at the top rung (coordinator playbook application, recorded in the specs:
  `notes/Pencil-fanout.md` §"Fourth fan-out"; reservations: `notes/Pencil-labels.md`).

**Kernel-(K) research arc — twenty-six docs+scripts-only dispatches, plus one strategy-only
pass** (2026-08-02 → 08-06).
Mathematics: the workbook `notes/Pencil-informal.md`, whose **State of (K)** map is the entry
point, the canonical per-gap status home, and the artifact a pass *updates*; settled
W4-residual verdicts are in `notes/Pencil-W4-informal.md`; strategy in
`notes/Pencil-strategy.md`. One line per landing in *Decisions made*, which with git is the
canonical dispatch record — **neither the landings nor the per-gap statuses are restated
here**. Net effect: the **disproof risk is removed**; every refuted route/gap is recorded in
the gap map with its successor; the arc's structural positives are (Λ1), §(K-ann)'s recipe,
§(K-out)'s **proven combinatorial half** ((OC-10)), and §(K-grid)'s **proven tree-triple
theorem** ((GR-9)); the **tight stratum now hangs on the single geometry-free (GR-10)**; the
third fan-out's three directions **converged on one missing technology — chart-to-frame
dominance / uniform constructed witnesses** (§(K-out) (OC-16), §(K-ann) (ANH-14), §(K-grid)
Step G13); and **class uniformity of the escape remains untouched by every one of them**.

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
that carries the detail, so they are **not** restated here. (The former items (a)/(g) of this
list — the mechanisms pass and the (ANH-R1) probe — are **DONE**, landed as second-fan-out
directions M and R; their letters survive only in cross-references.)

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
> **The FIRST fan-out (A/B/C of 2026-08-05/06), the harness re-baselining round (S1–S4), the
> SECOND fan-out (T/R/M) and the THIRD fan-out (G/Q/O) are ALL COMPLETE** — each direction
> one-lined in *Decisions made*, its workbook section the canonical home, every driver
> coordinator-re-run.
>
> **The FOURTH fan-out (directions E / J, user-adjudicated 2026-08-06 — the (GR-10) min-max
> attack and the shared chart-to-frame dominance lemma; leads (b)–(f) and the parked Lean
> half NOT selected) is IN FLIGHT, dispatched SERIALLY E → J, both at the top rung** — specs,
> grounding and cautions: `notes/Pencil-fanout.md` §"Fourth fan-out"; label reservations:
> `notes/Pencil-labels.md`. Direction **E** attacks **(GR-10)** (both-block tree-triple
> colouring existence; 907/907 measured; the grouped-exchange failure the named obstruction —
> a partition-constrained base packing one constraint from Phases-12–15 machinery), whose
> discharge with the proven (GR-9), (GR-5) and §(K-clos) (AC-7) closes `hK` on the tight
> stratum. Direction **J** attacks the residue directions O and Q both terminated at,
> **chart-to-frame dominance** (§(K-out) (OC-16); §(K-ann) (ANH-14)), via §(K-grid) *Step
> G13*'s candidate lemma shape ("explicit constructed point off the explicit bad divisor +
> irreducibility ⟹ dominance") — the transport to the contracted objects is the unattempted
> step. Landing per the fan-out doc's checklist; the coordinator lands E before dispatching J.
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

- **Third fan-out, direction G LANDED — §(K-grid) Steps G8–G13: (GR-4) REFUTED as stated and
  repaired, the tree-triple certificate theorem (GR-9) PROVEN, the tight-stratum residual
  merged into (GR-10) alone** (2026-08-06, `gridwit.py`; canonical home workbook **§(K-grid)**).
  Cheap kill (ii) fired — 185/4200 widened-pool overshoots, every one exact against the proven
  unified family (GR-8) (sub-multigraph cycle spaces; rank-1 members = ≤-2-class cycles);
  (GR-4′) the repair, off the critical path; (GR-9) three-group collapse + Vandermonde + no
  bond-in-a-group ⟹ Tay target with no generic-arrangement input; (GR-10) measured 907/907,
  min-max obstruction named exactly (grouped co-independence fails exchange). §2.3's
  prediction landed on its informative branch; uniformity untouched pending (GR-10).

- **Third fan-out, direction Q LANDED — §(K-ann) Steps A14–A17: no shape refuted, the
  dispatch's "upgrade" premise itself REFUTED, and the bare-cycle stratum reduced to
  chart-to-frame dominance** (2026-08-06, `anhr1.py`/`anhr1.m2`; canonical home workbook
  **§(K-ann)**). (ANH-16) the per-shape M2 identity is the *pointwise restatement* of (ANH-R1)
  ((ANH-9)(iii) already makes census rows proofs) — *Step A13* item 4 struck as an upgrade
  route; (ANH-13) branch-core normal form, `deg C = 12(c(G)−2)`; (ANH-14) ONE universal
  irreducible degree-12 polynomial governs the whole bare-cycle stratum (1904/6426 sites), so
  no (ANH-7)-style recipe exists for (ANH-R1)'s certificate; (ANH-15) the bad locus strictly
  contains (ANH-11)'s. Third independent arrival at the dominance residue; uniformity untouched.

- **Third fan-out, direction O LANDED — §(K-out) Steps O9–O12: the combinatorial half PROVEN,
  (OC-7)'s necessity clause REFUTED, (OC-8) reduced to one explicit line** (2026-08-06,
  `outerwide.py`/`outerwide.m2`; canonical home workbook **§(K-out)**). (OC-10) the availability
  map is forced (items 1–2 struck; θ(3,4,5) the unique theta member; an F11 self-caught proof
  repair — `hnoRigid` load-bearing); (OC-12) at degree-3 hubs `λ₁ = 0 ⟺` coincident hinge off
  `{p = pt(b)}`; (OC-13)/(OC-14) the bad locus is one panel line `C₀`, inhabited by 38/38
  constructed nondegenerate points; (OC-16) `Δ = [a,u,b]·C₀(pt b) ≢ 0` at the `ℓ_min = 5`
  frame's generic point. (OC-8) stays OPEN as a containment question; uniformity untouched.

- **Second fan-out, direction R LANDED — §(K-ann) Steps A10–A13: (ANH-R1) one-point-decidable,
  discharged at every probed triple, and REFUTED pointwise** (2026-08-06, `shrink.py`; canonical
  home workbook **§(K-ann)** continuation). (ANH-9) the weak-map formulation — one exact rank
  computation at one rational point decides (ANH-R1) per triple; (ANH-10) the pinned census
  probe: clean negative at 26/26 guarded generic seeds, 58/58 sites `τ_β ≠ 0`; (ANH-11)/(ANH-12)
  the bad locus **inhabited** by exact rational guard-accepted points (`supp` 11 → 6 at six
  (ANH-R1)-exact witnesses) — no counting/matroid/placement-blind route exists (the τ-side
  (OC-3) analogue); "easier or merely smaller" settled: **merely smaller**, T and R converging
  on uniform constructed witnesses. (ANH-R1) stays OPEN; uniformity untouched.

- **Second fan-out, direction M LANDED — §(K-mech): both *P8* anomalies mechanised, 6v11e
  RESCUED** (2026-08-06, `mech.py`; canonical home workbook **§(K-mech)**). One calculus (the
  realizable-load space `Ω`, α-confinement (MX-2)): the 6v11e drop = a forced welded flex
  ((MX-6)); the `K222`/`K4` incidence = a forced pole-cluster load ((MX-4)/(MX-5), bounds
  2/2/3 met with equality, controls ≤ 1); **the slide device closes 6v11e** at a
  mechanism-guided support ((MX-7), 9/9 prediction table) — §(K-pure) *P7*'s "device does not
  reach this shape" withdrawn; σ rider NO ((MX-8)); `|V°| ≤ 6` predictor measured
  complete-and-sound, one new (W4)-failing shape ((MX-9)). Uniformity untouched.

- **Second fan-out, direction T LANDED — §(K-grid): the tight stratum reduced, with proven
  reductions, to two geometry-free gaps** (2026-08-06, `grid.py`; canonical home workbook
  **§(K-grid)**). Each `⋆`-eigen-block is a conic direction network = **generalized-spline
  system** ((GR-1), rank identity 688/688); the gap map's close-route sentence REFUTED as worded
  ((GR-2), the mono-hub bond); corrected to two proven counting families ((GR-3)), exact at
  generic labels ((GR-4), true-modulo-named-gap); chart-image membership PROVEN + machine-verified
  ((GR-5), 5/5) — a target-rank grid IS `hK`'s conclusion object; census 15/15 → **907/907**, no
  kill. Residual: **(GR-4) + (GR-6)**. Uniformity untouched.

- **The harness re-baselining round — all four debt items CLEARED, round CLOSED** (2026-08-06,
  five commits `d5ae55aa`…S4; trigger dispatch-log **F13**). Canonical home:
  `notes/scripts/README.md` *Harness debt* → **CLOSED**. 260 invocations, 21 figures moved, each
  repointed in its moving commit. Two moves are mathematics: **(AC-9)** (§(K-clos)), **(OC-9)**
  (§(K-out)). **No gap-map row moved.**

- **The 2026-08-06 three-way kernel-(K) fan-out — three landings; each one's canonical home is
  its named workbook section, none restated here.** *C* (`closure.py`, **§(K-clos)**): §(K-σ)'s
  **field question SETTLED** (`ℝ` the **narrowest** choice), the σ-fixed **grid recipe REFUTED**
  class-wide. *A* (`annih.py`, **§(K-ann)**): the arc's first **RECIPE** (`λ` a self-stress of
  `H/P`); residual **(ANH-R1)**, relocation #4. *B* (`outerline.py`, **§(K-out)**): (OUT)
  **MEASURED**, headline the **negative (OC-3)** — no counting argument can ever deliver it —
  plus **(OC-7)**, the defect that opened the round above. **No status moves; uniformity
  untouched.** Same day: §2.3's **convergence note** — A's and B's residuals are one shape.

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

- **The 2026-08-05 research day, sixth–ninth dispatches (one line each; the named workbook
  section is the canonical home).** *A* (`flanks.py`, §(K-flank)): the conjecture **HOLDS at every
  uncovered flank** (exact `∃`-witnesses, 851 shapes, 0 failures); `hK` needs **no re-pin**. *C*
  (`pure.py`, §(K-pure)): the pure condition is the **WRONG INVARIANT**; **(K-slide-cl) REFUTED as
  stated**; **(PC-Z)** the reformulation, **(K-chord)** the successor. *B* (`lambda.py`, §(K-Λ)):
  **(K-Λ) REFUTED as an independent gap** — at `ℓ = 4` *equivalent* to **(K-wit)** (Witt); (Λ1),
  (Λ0d)/(Λ0f) named there. *C1* (`dominance.py`, §(K-dom)): **dominance HOLDS (rank 9), not a
  route** — **(D1)**–**(D3)** grade it by `k`. **Uniformity untouched by all four.**

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
