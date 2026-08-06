# Phase 39 — PENCIL: the hinge-pencil molecular conjecture (work log)

**Status:** in progress — phase stays OPEN (standing user adjudications of 2026-07-24 /
2026-07-30 / 2026-08-02, quoted verbatim in *Current state*). W0–W3 and the whole W5 arc
(L0–L7) are COMPLETE — `hsplit` CLOSED IN FULL and `hfresh`'s counting discharge landed
(2026-07-30). Only three items remain, all carried by the landed successor
`pencil_conjecture_of_hcontract_hK_hbareSplit_of_card` (`Molecule/Pencil/Escape.lean`):
`hcontract` (W4), kernel `hK`, and kernel `hbareSplit` — see *Hand-off*. Kernel-(K) research
is at its twenty-first docs+scripts-only pass (workbook `notes/Pencil-informal.md`; the settled
W4-residual arc split out to `notes/Pencil-W4-informal.md` on 2026-08-05; the twenty-first is
the **2026-08-06** fan-out's direction B — workbook §(K-out), `outerline.py` — and that fan-out
is now **COMPLETE**. Its direction letters are re-used from the 2026-08-05 one, whose direction
B was §(K-Λ); always date them).

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
- **2026-08-05, dispatch ordering (user-adjudicated, partly executed):** `g₁₄` →
  invariant-through-moves → σ-equivariance → **mechanisms pass** → Δ-matroid. The first three
  are DONE and Δ-matroid was run early in the same parallel round, so **only the mechanisms
  pass is unstarted**. **OPEN and explicitly left to the user:** whether verifying **route σ**
  (below) preempts it, and — since 2026-08-05 — whether §4.6's uniformity shortlist ((f) below)
  does. Not decided here.

**Kernel-(K) research arc — twenty docs+scripts-only dispatches, plus one strategy-only
pass** (2026-08-02 → 08-06).
Mathematics: the workbook `notes/Pencil-informal.md`, whose **State of (K)** map is the entry
point and the artifact a pass *updates*; settled W4-residual verdicts are in
`notes/Pencil-W4-informal.md`; strategy in `notes/Pencil-strategy.md`. One line per landing in
*Decisions made*, which with git is the canonical dispatch record — **not restated here**. Net
effect: the **disproof risk is removed**; seven named gaps, routes or constructions moved from
open to refuted-or-superseded ((K-slide-comb), (K-slide-cl) as stated, (K-Λ) as independent,
C1/(K-dom) as a route, **(K-ind)**, **(K-Δ)**, and §(K-clos)'s grid recipe as a class
statement), with **(K-chord)**/**(K-wit)** the successors; the arc gained its first
**class-uniform positive** ((Λ1)) and, 2026-08-06, its first **recipe** — a formula, not a
search — in §(K-ann), whose two inputs are *not* uniform; §(K-σ)'s **field scope is settled**;
§(K-out) measured (OUT)'s hypothesis and **proved it can never be delivered by a count**
((OC-3)); and **class uniformity of the escape remains untouched by every one of them**.

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
that carries the detail, so they are **not** restated here:

- **(a)** the **mechanisms pass** — the two unexplained mechanisms of §(K-pure) *P8*/*P9*
  (6v11e's `dim V_bc = 2` drop and the `V_bc ∩ Λ²π̂ ≠ 0` incidence at `K222` /
  `K4 (1,1,3,5,4,4)`), with the widened slide-support menu and the `|V°| ≤ 6` sweep; *P9*
  item 5 says to start at 6v11e. This is the **last unstarted item of the adjudicated
  ordering**; §(K-σ) *Step σ6* adds one probe to it (`V_bc ∩ Λ²π̂ ≠ 0` is the σ-image of
  `V_bc ∩ α(·) ≠ 0` at the dual seed).
- **(b)** **(K-wit)**, the single live form of the pitch route at companion splits: §(K-Λ)
  supplies its necessary-and-sufficient companion form, the two-point failure locus (now known
  to be a σ-orbit) and the side conditions (Λ0d)/(Λ0f′). *(2026-08-06, §(K-out)):* its `k = 4`
  sufficient route **(OUT)** is now measured — *available* pointwise but **never automatic**,
  and **(OC-3) rules out any counting route to it**; the residue is (OC-8).
- **(c)** the **W4 build** — fully decomposed and buildable, but **PARKED** by the standing
  2026-08-05 adjudication holding the Lean back until the research yields *"an informal proof or
  disproof or any results that would be significant as standalone pieces of math"*. It does not
  open without a fresh user adjudication.
- **(d)** the **companion-length dichotomy** as an organizing frame (§(K-dom) *D7*): `k = 3`
  closed by §(K-pitch)'s bracket monomial, `k ≥ 4` by dominance at every shape probed — an
  *observation*, not a proof. The concrete unprobed item is `k ≥ 4` with a **parallel `G°`
  edge** (`P21`-type), where §(K-pure) *P4* locates a separate obstruction.
- **(e)** the residual of §(K-Λ) item (vii): whether a class shape can carry **two or more hubs
  on a length-4 companion's interior**. No swept family realizes one.
- **(f)** *(2026-08-05; U1 + U2 RUN 2026-08-06 as direction A, §(K-ann))* the **three ranked live
  entries of `notes/Pencil-strategy.md` §4.6**: U1 **half delivered** (the named move and the
  bracket formula, not their inputs), U2's `E(H)` ground set survives with its cocircuit/circuit
  duality corrected, **U3** (`hK` as a non-existence) still unrun.
- **(g)** *(new, 2026-08-06)* **(ANH-R1)** — `H/P − β` pencil-rigid, i.e. `τ_β ≠ 0` at the
  pencil placement (workbook §(K-ann) *Step A8*: **relocation #4**, on the mixed stratum and a
  strictly smaller graph, and whether it is *easier* than its parent is **open**). Discharging
  it closes the whole length-4-companion stratum via Λ-completeness. Smallest concrete commit:
  an `annih.py --shrink` census hunting a class seed with `supp_pen ⊊ supp_gen` at `k = 4`.

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
- **Harness debt — FOUR parked items, now a named list** (`notes/scripts/README.md` *Harness
  debt*, the canonical home — not restated here): `localtest.meet_line`, `lambda.omega_curves`'
  coded (Λ0f) equivalence at the newly-reachable `g₁₄ = 0` points, `flanks.star_span_ranks`
  at **four** consumers, and — **new 2026-08-06, an escalation** — `place_pencil_general`'s
  in-plane sampler degenerating at ≈ 9 % of habitat frames in a way that **forces `λᵢ = 0`** and
  that `star_span_ranks`, *the documented guard against exactly it*, does not catch (§(K-out)
  **(OC-7)**; second `plane_basis` contamination, first with the guard failing). No item
  corrupts a recorded figure — 1–3 fail loudly, 4 is one-directional — but 4 carries a
  **standing rule that binds now**: no `place_pencil_general` battery may be quoted as a *rate*
  or as evidence about a generic chart point. The recorded option is still **one deliberate
  re-baselining commit clearing all four**, a coordinator decision, not a side errand. Same
  block:
  `outer.py --patterns` and `--sweep` run over different denominators (7002 vs 4280 pairs), so
  their companion counts are **not comparable**.

## Hand-off / next phase

**The phase stays OPEN** (the 2026-07-24 adjudication — no phase-close; see *Current state*).

**`hsplit` is CLOSED IN FULL** (W5-L7c-1…6, landed 2026-07-30) and **`hfresh`'s mechanical
discharge (residue (iv)) is CLOSED too**. The landed successor
`pencil_conjecture_of_hcontract_hK_hbareSplit_of_card` (`Molecule/Pencil/Escape.lean`) wraps
`pencil_conjecture_of_hcontract_hK_hbareSplit` and carries exactly three open items, below.

> **The numerics half of the σ-NONDEGENERACY VERIFICATION is DONE** (2026-08-05,
> `sigma.py --hunt`; canonical home, **not restated here**: workbook §(K-σ) *Step σ3* / *Step
> σ4b* / *Step σ5*, one-lined in *Decisions made*). Net: the dual conjuncts CAN fail on the
> hard stratum, the steering WORKS exactly, obligation 1 shrinks to two conditions, and
> **(σ7)** is proven.
>
> **Smallest concrete commit if work continues on this thread: the LEAN half of obligation 1**
> — steer to a common seed via the landed `exists_common_seed_pencilRow_and_polynomials`
> (`Engine.lean:476`). Its docstring already names this consumer shape, and the chart is a
> **total** parameterization (no chart-image side condition). It carries **two** design
> decisions. (a) **Which maximal minor to fix per LI conjunct** — the dual conjuncts are unions
> of basic opens, not single hypersurface complements, so the repair needs sufficiency,
> graph-dependently. (b) **WHICH FIELD — SETTLED as mathematics, still a user call as scope**
> (2026-08-06, workbook §(K-clos); canonical home, not restated here): the polarity **does**
> generalize, its general-`K` transport is landed (`mapSupport`), so `ProjectiveInvariance.lean`
> needs nothing — and `ℝ` is the **narrowest** option, not a safe default, since `hK` over `ℂ̄`
> implies it over every infinite characteristic-0 field and not conversely. **`exists_pencilSeed_of_nondeg`
> (`Reseed.lean:65`) is NOT the bridge** and is circular if used as one.
> **BUT THAT COMMIT IS BLOCKED**: the standing 2026-08-05 adjudication holding the Lean back
> pending *"an informal proof or disproof or any results that would be significant as standalone
> pieces of math"* is **general, not W4-scoped**, so it holds back this repair too. It does not
> open without a fresh user adjudication.
>
> **Route σ faces exactly ONE crux, not two.** The workbook kills M₁ twice — §(K-tight)
> *Step 1* as "the nondegeneracy-forbidden locus", *Step 2.6* as "M₁'s span is
> carrier-unrealizable" — but the second's stated reason is the **same** `hinge(vb) := q(ab)`
> pinning. That materially bounds what verifying route σ costs.
>
> **The three-way fan-out is COMPLETE** (2026-08-06: C §(K-clos) `890ec4a6`, A §(K-ann)
> `c9cf5792`, B §(K-out) — this commit). No gap-map *status* moves, so the adjudication below is
> unchanged in shape; two option prices changed. **(OUT) is now measured**, and its cheapest
> continuation (§(K-out) *What would change this*) is **widening `outerline.py --comb` past
> `outer.sweep_shapes()`'s `|V°| ≤ 5` cap** (14 s at the present scope) to hunt `dim R = 6`
> (which makes (OUT) *dead* there) or `dim R ≤ 4` / `μ ≥ 2` (which closes it there). Second, and
> coordinator-owned: the deliberate re-baselining commit clearing all **four** *Harness debt*
> items — item 4 is the first defect that changes how existing output may be *read*.
>
> **THE NEXT COMMIT IS DECIDED — the harness re-baselining round** (user-adjudicated 2026-08-06:
> *"let's fix the harness and clear any debt there while you're at it."*). It clears **all four**
> harness-debt items in one sequence and re-baselines every recorded figure; scope, order and the
> moved-figure rule are in `notes/scripts/README.md` *Harness debt*, **OPENED** block. Trigger:
> dispatch-log **F13** — a mitigation for a recorded defect found ineffective. **It precedes all
> research below.**
>
> **QUEUED, still an open user adjudication** — three contenders, none pre-selected: the remaining
> route-σ work; the **mechanisms pass** (*Current state* (a)); and `Pencil-strategy.md` §4.6's
> ranked shortlist (*Current state* (f)), the only one aimed at **class uniformity itself**. The
> live crux is **(ANH-R1)**: is `H/P − β` pencil-rigid, and is that *easier* than its parent or
> merely smaller? §2.3's new convergence note — two independent routes, one residual shape —
> argues the wall is structural, so attack it directly if a third route lands there too.
>
> Deliberate non-goals: (Λ0), (Λ1), the `g₁₄` clause, §(K-ind), §(K-Δ), **§(K-clos)'s field
> question**, **§(K-ann)'s settled batch** ((ANH-1)–(ANH-6), (SD-6)) and **§(K-out)'s settled
> batch** ((OC-1)–(OC-7); the two pools are pinned and **disjoint**) are **done** — do not
> re-derive, re-sweep, re-run their literature hunt, re-open "does the polarity generalize?",
> re-measure (D2)'s far block, re-sample POOL-G or POOL-S, **propose a counting / matroid route
> to (OUT)'s hypothesis** ((OC-3) refutes the whole class), or touch `lambda.py`'s figures.
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
is touched. **When `notes/scripts/` is touched**, the gate is figure invariance, **triggered by
what the commit modifies**: if `git diff --name-only -- '*.py' '*.m2'` shows **no tracked driver
modified** (a pure addition, or prose only), that check *is* the discharge and goes in the commit
message; if a driver **is** modified, the full baseline / re-run / byte-identical obligation
stands for it and its import closure. Both halves, plus the invocations exceeding a 600 s
foreground budget (`flanks.py --limit`, `lambda.py --adv`, and `outerline.py --pool`/`--shapes`
which do not fit *together*), are in `notes/scripts/README.md` *Hard rule — figures do not move*,
with the primitive index, layering map, invocation table and conventions; a **symbolic** dispatch
adds `notes/scripts/m2/README.md`.

## Adjacent directions (orientation only, not this phase)

ORIGAMI (`notes/Origami.md`, next queued) is the bar-joint-side analog; the wider unqueued
survey — incl. IDENT-PANEL, the nearest neighbour — is `notes/IdeaBacklog.md`.

## Decisions made during this phase

Reverse-chronological, one line per landing; full derivations live in git,
`notes/Phase39-design.md`, and (for the (K) arc) the workbook section named in each entry, which
is the canonical home a successor reads.

- **The 2026-08-06 three-way kernel-(K) fan-out — three landings, one line each; the named
  workbook section is the canonical home and none is restated here.** *C* (`closure.py`, ℚ(i),
  **§(K-clos)**): §(K-σ)'s **field question SETTLED** — the polarity generalizes, transport
  landed, `ℝ` the **narrowest** choice — and the σ-fixed **grid recipe REFUTED** class-wide by
  `C11`. *A* (`annih.py`, **§(K-ann)**): the arc's first **RECIPE** — `λ` is a self-stress of the
  contracted `H/P`, one Klein pairing at a named far move, `E(H/P)` a Tay **circuit** at `k = 4`,
  one 4-point bracket on 89 % of triples; residual **(ANH-R1)** = relocation #4. *B*
  (`outerline.py`, **§(K-out)**): (OUT)'s hypothesis **MEASURED**, headline the **negative
  (OC-3)** — the bad locus is nonempty on *every* class shape's chart, so **no counting argument
  can ever deliver it**; availability only pointwise (356/357, 270/270, two disjoint pinned
  pools) with an (OUT)-silent *nondegenerate* constructed point; **(OC-7) a HARNESS DEFECT**
  (≈ 9 % of habitat frames forced `λᵢ = 0`, uncaught by the documented guard, *Harness debt* 4).
  **No gap-map status moves; class uniformity untouched by all three.** *Coordinator capture,
  same day:* the **harness re-baselining round OPENED** (user-adjudicated; scope in
  `notes/scripts/README.md` *Harness debt*), dispatch-log rows + **F13**/**F14**, and
  `Pencil-strategy.md` §2.3's **convergence note** — A's and B's residuals are both
  *pencil-rigidity of a contraction of `H`*, so §2.3's wall is structural, not route-specific.

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
  section is the canonical home).** *A* (`flanks.py`, §(K-flank)): the conjecture **HOLDS at
  every uncovered flank** — half 2 per shape by exact `∃`-witnesses (8 named + 843 stratum
  shapes, 0 failures); `hK` needs **no re-pin**; a **∀-realization** escape form REFUTED at
  `P21`. *C* (`pure.py`, §(K-pure)): the pure condition is the **WRONG INVARIANT**;
  **(K-slide-cl) REFUTED as stated**; **(PC-Z)** the exact reformulation; **(K-chord)** the
  successor. *B* (`lambda.py`, §(K-Λ)): **(K-Λ) REFUTED as an independent gap** — at `ℓ = 4`
  *equivalent* to **(K-wit)** (Witt); `Φ_loc` always rank 2 ((Λ1)); `ℓ = 5,6` refuted *through
  the (T5) frame*; (Λ0d)/(Λ0f) named. *C1* (`dominance.py`, §(K-dom)): **dominance HOLDS at every
  class habitat probed (rank 9) but is not a route to uniformity**; the **companion length** `k`
  governs — **(D1)** `rank dV ≤ min(9, 6k−14)`, **(D2)** far block `≤ 3(k−3)` attained, **(D3)**
  `hnoRigid ⟹ k ≥ 4`. **Class uniformity untouched by all four.**

- **Harness + workbook prep** (2026-08-05, two commits; no mathematics, no verdict changes; 67/67
  drivers re-run, 0 changed figures) — `notes/scripts/README.md`;
  `notes/Pencil-W4-informal.md`; `W19`/`S29` + the *State of (K)* map.

- **(K-slide-comb) REFUTED class-wide; the packing half made uniform ((C6)); (C2)'s length-4
  entry corrected ((C7))** (2026-08-05, `kslidecomb.py`; workbook §(K-slide-comb)) — the
  colouring premise fails inside the class; **(C6)** proven at every class shape (Edmonds), so
  the packing is never the obstruction; **(C7)**: `K4` coverage 439→702/877.

- **(K-slide) (S1) PROVEN, and (K-slide-cl) reduced to combinatorics** (2026-08-04,
  `kslide.py` / `kslidecl.py`; workbooks §(K-slide), §(K-slide-cl)) — the slide is a chart
  automorphism at `ε ≠ 0` with the row family polynomial through `ε = 0`, so **one exact limit
  witness closes a split** (23/23 pitched; `K4`/`W4` controls closed at every split; parallel
  `G°`-edges order-0-obstructed, leaving `P21`).

- **(K-pitch) developed; the naive collinear collapse REFUTED; Λ-compression (T5) extends
  companions to length 4** (2026-08-04, two dispatches, `pitch.py`; workbook §(K-pitch)) —
  motion-side transfer (T1)–(T4), the sign law, the `pt(a)`-sweep quartic, and the five-bracket
  monomial at companion-chain splits (θ(3,3,6) CLOSED; 29/29). Far data enters `Q(z)` only
  through the annihilator covector. Weakest exact forms (K-wit)/(K-pitch-∞).

- **(K-tight) KT pp. 684–691 re-pin DONE — carrier escape criterion proven+validated; every
  recorded escape failure was a sampler artifact** (2026-08-02, `repin.py`; workbook §(K-tight))
  — attainment ⟺ two functionals independent on `U`; failure locus `line(ab) ∪ P′`; seed 442 and
  the 94/96 non-escapes were `plane_basis` degeneracies (**the first of two** — see §(K-out)
  (OC-7)). Kernel narrowed to (K-move)/(K-pitch).

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

- **The 2026-07-30 W5-L7 build day (one-lined; `hsplit` is CLOSED IN FULL, so nothing upcoming
  leans on the detail — canonical record: `notes/Phase39-design.md` + git).** Recon isolated
  kernel **(K)** (route (b), the (6.44) identity, REFUTED); user adjudicated "route 3: build
  now". L7a landed with the rigid `k=0` half closed minimality-free (KT Lemma 3.4); L7b re-pinned
  split-data-free after `escapePoly` was refuted by a BLOCKED build (dispatch-log F9 ×2); L7c
  decomposed into six leaves ending at `pencil_conjecture_of_hcontract_hK_hbareSplit`; then
  `hfresh`'s residue (iv), the consumer headline, and the blueprint node restatement.

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
