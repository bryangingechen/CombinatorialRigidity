# Phase 39 — PENCIL: the hinge-pencil molecular conjecture (work log)

**Status:** in progress — phase stays OPEN (standing user adjudications of 2026-07-24 /
2026-07-30 / 2026-08-02, quoted verbatim in *Current state*). W0–W3 and the whole W5 arc
(L0–L7) are COMPLETE — `hsplit` CLOSED IN FULL and `hfresh`'s counting discharge landed
(2026-07-30). Only three items remain, all carried by the landed successor
`pencil_conjecture_of_hcontract_hK_hbareSplit_of_card` (`Molecule/Pencil/Escape.lean`):
`hcontract` (W4), kernel `hK`, and kernel `hbareSplit` — see *Hand-off*. Kernel-(K) research
is at its sixth docs-only pass (workbook `notes/Pencil-informal.md`; the settled W4-residual
arc split out to `notes/Pencil-W4-informal.md` on 2026-08-05).

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
- **2026-08-05, phase direction (first):** *"**C1 dominance Jacobian spike**"* — chosen from four
  surfaced options (C1 / the Macaulay2 symbolic upgrade / un-park W4 / close the phase). Ran and
  landed the same day; verdict mixed, and it is **not** recommended as a continuation.
- **2026-08-05, phase direction (second — the live one):** the **Macaulay2 symbolic upgrade**,
  quoted verbatim in the *Direction ADJUDICATED* block below, together with the standing
  requirement that **every script the project runs is committed** for reproducibility. Its
  harness half landed the same day. **W4 stays parked**, `hK`/`hbareSplit` stay carried as
  pinned, option B in both kernel cases stays **NOT** commissioned, the phase does **not** close.

W0–W3 and W5-L0–L7 are COMPLETE (`hsplit` closed in full; `hfresh`'s counting discharge landed).
The landed headline `pencil_conjecture_of_hcontract_hK_hbareSplit_of_card`
(`Molecule/Pencil/Escape.lean`) carries exactly three open items — `hcontract` (W4), `hK`,
`hbareSplit` — each detailed in *Hand-off*.

**Kernel-(K) research arc — ten docs+scripts-only research dispatches** (2026-08-02 → 08-05).
Mathematics: the kernel-(K) workbook `notes/Pencil-informal.md`, whose **State of (K)** map is
the entry point and the artifact a pass *updates*; the settled W4-residual verdicts are in
`notes/Pencil-W4-informal.md`. One line per landing in *Decisions made*, which with git is the
canonical dispatch record — **not restated here**. Net effect of the whole arc: the **disproof
risk is removed** (the conjecture holds at every uncovered flank by exact witnesses, and the
pivot rule does not fire); four named gaps moved from open to refuted-or-superseded
((K-slide-comb), (K-slide-cl) as stated, (K-Λ) as independent, and C1/(K-dom) as a route), with
**(K-chord)** and **(K-wit)** as the successors; the arc gained its first **class-uniform
positive** statement — (Λ1) as a symbolic identity, about `Φ_loc`'s shape, not about the escape;
and **class uniformity of the escape is untouched by every one of them** — no uniform gap has
closed.

**The three-way fan-out is COMPLETE** (A `0ee85777`, C `e38eb6b5`, B `7b4422dd`, all 2026-08-05;
workbook §(K-flank), §(K-pure), §(K-Λ); scoping record `notes/Pencil-fanout.md`).

Remaining uniform (K) gaps: **(K-wit)** (the pitch route's single live form), the
**`∃Σ`-repaired (K-slide-cl)** with its successor residue **(K-chord)**, and `P21`-type
parallel-`G°`-edge (K-res) shapes — none closed by the fan-out, which is per-shape. Canonical
status home for all of them: the workbook's **State of (K)** gap map.

**The C1 dominance spike (2026-08-05, ninth dispatch) is spent and NOT recommended** — dominance
HOLDS at every class habitat probed, but C1 is not an inductive route and does not reach
uniformity. Canonical home: workbook **§(K-dom)** + its gap-map row. Its one lasting addition to
the arc's vocabulary is the **companion length** `k` (the shortest `b`–`c` path of
`H = G − v − a`) as the governing *local* invariant.

**Direction ADJUDICATED 2026-08-05 (second adjudication of the day), verbatim:**

> *"Ah, I was hoping subagents would start using Macualay2 immediately but I guess we need to do
> some more harness setup first. Let's do that after confirming these results. Also, in general,
> I would like all of the scripts we run to be committed for reproducibility: is that being
> done?"*

C1's results were confirmed independently before acting on this, and the answer to the second
question is **yes** — every driver is tracked (`git ls-files notes/scripts/`); that is now a
standing hard rule of the harness rather than luck. The direction is the **Macaulay2 symbolic
upgrade** (`notes/Pencil-strategy.md` §5.3/§5.4), and it is **DELIVERED IN FULL** (two dispatches,
both 2026-08-05): `notes/scripts/m2/` with its README and all four §5.4 conventions, then
`lambda1.m2` ((Λ1) as an identity over the function field) and `lambda0.m2` ((Λ0) + the `a`-line
spans at the generic point — **class-uniform**, and it exposed a hypothesis the recorded (Λ0f)
omits). Workbook §(K-Λ). Unchanged by this adjudication: **W4 stays parked**, `hK` and
`hbareSplit` stay carried as pinned, option B in both kernel cases is still **NOT** commissioned,
and the phase does **not** close.

> **Read `notes/Pencil-strategy.md` before choosing anything else.** It is the post-fan-out
> strategic record: *why* class uniformity resists (the three-ingredient diagnosis, the
> uniform-negatives/per-shape-positives asymmetry, the `Gr(3,6)` framing, and the
> counting-saturation argument that rules out every count-expressible invariant), what the KT
> formalization did and did not yield, the **candidate stronger inductive invariants** — **C1 run
> and struck**, leaving C2 (carry `V_bc` general position as a motive conjunct) and C3 (the mixed
> stratum) — and §5's symbolic-computation assessment, now with the M2 layer landed, its
> conventions binding, and its **measured feasibility boundary** recorded (local frame viable,
> whole graph not).

The other candidate continuations, unselected, without preference; each has a canonical home that
carries the detail, so they are **not** restated here:

- **(a)** the two **unexplained mechanisms** of §(K-pure) *P8*/*P9* — 6v11e's `dim V_bc = 2` drop
  and the `V_bc ∩ Λ²π̂ ≠ 0` incidence at `K222` / `K4 (1,1,3,5,4,4)` — with the widened
  slide-support menu and the `|V°| ≤ 6` sweep; *P9* item 5 says to start at 6v11e.
- **(b)** **(K-wit)**, the single live form of the pitch route at companion splits: §(K-Λ)
  supplies its necessary-and-sufficient companion form, the two-point failure locus, and
  (Λ0d)/(Λ0f).
- **(c)** the **W4 build** — fully decomposed and buildable, but **PARKED** by the standing
  2026-08-05 adjudication holding the Lean back until the research yields *"an informal proof or
  disproof or any results that would be significant as standalone pieces of math"*. It does not
  open without a fresh user adjudication.
- **(d)** the **companion-length dichotomy** as an organizing frame (§(K-dom) *D7*): `k = 3`
  closed by §(K-pitch)'s bracket monomial, `k ≥ 4` by dominance at every shape probed — an
  *observation*, not a proof (*D6* explains why the dominance half will not become
  combinatorial). The concrete unprobed item is `k ≥ 4` with a **parallel `G°` edge**
  (`P21`-type), where §(K-pure) *P4* locates a separate obstruction.

**Any (K)- or W4-side numerics dispatch starts from `notes/scripts/README.md`** — the harness
entry point (primitive index, layering map + import rule, invocation table, mandatory
conventions, the *Divergences* rows that must **not** be merged), landed by the 2026-08-05 prep
commits together with the workbook split and the *State of (K)* map (*Decisions made*). **A
symbolic dispatch also reads `notes/scripts/m2/README.md`** — the Macaulay2 island's four extra
conventions, the first of which is that its output is *evidence*, never a substitute for Lean.
**Every script the project runs is tracked** (standing user requirement, 2026-08-05); a dispatch
that produces a driver commits it.

File layout: `Molecule/Pencil.lean` split into
`Molecule/Pencil/{Statement,Arms,Motive,Chart,Engine,Reseed,Witness,Steer,Pair,Pair2,Escape,
Base}.lean`. Full per-leaf history: `notes/Phase39-design.md` §"W5 leaf decomposition" +
§"W5-L7 research recon"; this section stays a pointer, not a second copy. The opening recon ran
2026-07-23; verdicts (R1–R3) below in *Opening recon verdicts*.

## The question

KT's theorem (formalized: `molecular_conjecture`, Phases 17–26; the
multigraph/coplanar-model strengthening, Phase 35) says the generic
body-hinge rank in `ℝ³` is already achieved on the *panel* stratum —
each body's hinges coplanar — and, by projective duality (Phase 25),
on the *molecular* stratum — each body's hinges concurrent. PENCIL
asks about the **intersection stratum**: each body's hinges both
concurrent *and* coplanar, i.e. a **pencil** of lines through a point
in a plane. Does a pencil realization generic in that stratum still
achieve the generic body-hinge rank (Tay's tree-packing count;
`5G` ⊇ 6 edge-disjoint spanning trees at `d = 3` via KT Cor. 5.7)?

In the `G²` molecular reading (Phase 25/26 modelling), the hinges at
the body of atom `v` are the bond lines through `p(v)` — concurrency
is automatic — so the pencil condition says **`v`'s bond-star is
coplanar** (its neighbors lie in a plane through `p(v)`). Chemically:
sp²/planar-bonded atoms. So PENCIL reads: *does the molecular count
stay valid for molecules with planar-bonded atoms?* The condition
only bites at bodies of degree ≥ 3 (two coplanar lines are
automatically projectively concurrent).

Trivial direction: pencil ⇒ panel per body, so pencil rank ≤ generic
(KT). The content is the lower bound. The all-bodies statement is the
strongest form: any mixed version (pencil on a subset of bodies,
generic elsewhere) follows by rank lower-semicontinuity, since the
all-pencil stratum sits inside every mixed stratum.

The queue entry hoped for a warmup (no new carrier material); the
opening recon **refuted the warmup premise** — the carrier material is
indeed all in-tree, but three KT proof steps consume panel-only
freedom the pencil pin removes (see *Opening recon verdicts*). As of
2026-07-23 no literature result on this stratum was found (searched;
Jordán 2016 and the KT paper are silent) — **this is new mathematics**.

## Opening recon verdicts (R1–R3, landed 2026-07-23)

Full record, grounding, and the W0–W5 decomposition: **`notes/Phase39-design.md`**. One-line
verdicts, kept because each still constrains statements:

- **R1** — statement pinned in the Phase-35 containment model + a per-body homogeneous
  concurrency point (`ExtensorThroughPoint`, dual of `ExtensorInPanel`); satisfiable for every
  graph; self-dual on-stratum via `screwComplementIso`. For dense graphs (`K4`, `K3,3`,
  θ(2,2,2)) the stratum *collapses* to the all-coplanar locus.
- **R2** — the conjecture survives all exact-rational rank tests; the deep all-coplanar locus is
  deficient exactly when `2|E| < 3|V| − 3`, so the queued "all-coplanar is rank-deficient" claim
  is a *bar-joint-side* fact, **false** for body-hinge on dense graphs.
- **R3** — KT Lemma 6.2 / Case II survive with pinned choices; three open cores: the outer
  Thm-5.6 strip-extend, the Case-I glue (Claim 6.4), and Case III's Claim 6.12 span break.

## Blockers / open questions

**All W5 blockers are CLOSED** (2026-07-24 → 07-30; verdicts one-lined in *Decisions made*, full
record in `notes/Phase39-design.md` + git): the L5 cut arm and its `hcutPendant3` residual, the
L5 base-arm parallel-class blocker (user-adjudicated route (b′)), the L4 WF-conjunct /
shared-`fill` pair, L6's split-arm safe-vertex existence (proven minimality-free; the L6/L7
coupling is benign), and `hfresh`'s mechanical discharge. **One residual note from the L5 cut arm
still stands** because it constrains future statements: feasibility propagation *as a
proposition* is refuted for any purely combinatorial (`≤3`-closedHubNbhd) criterion
(`not_pencilNondegFeasible_of_triangle_two_hubs`) — it does not touch L6's own habitat claim.

- **Open: kernels (K) and (K-bare), and W4 (`hcontract`)** — the entire remaining work of the
  phase; see *Hand-off* for the per-item route and the `notes/Phase39-design.md` pointers. W4
  is now fully decomposed (recons of 2026-07-30): buildable leaves W4-L4b/L1/L2/L3′/L5 plus
  the carried `hKc`/`hbareContract`/`hnoGood'`; the W4 build sequence awaits commissioning
  (the "B: L4 recon first" adjudication deferred it until the L4 recon — now complete).
  **`hnoGood'` is now known NON-vacuous** (2026-08-02) — branch 4 needs content; routes in
  the W4 workbook `notes/Pencil-W4-informal.md` §"`hnoGood'` vacuity", adjudication owed.
  **(SAFE-RES) is REFUTED** (same day); routes 1/3 now cost §(SAFE-RES)'s (T) + (V) + the
  reduced (E), with (T) a genuine research gap (no landed lemma can decide it, and no
  certified search can see it), plus **one** widened kernel (K-res) — `hbareSplit` is
  untouched (same file, §"widened kernels (routes 1/3)").
- The full biconditional transport `ExtensorThroughPoint C q ↔ ExtensorInPanel (screwComplementIso
  C) q` (design doc's W0 pin) is landed only as its two forward implications; the reverse arms
  need a `complementIso` involution lemma, not in tree — deferred, not on any critical path.

## Hand-off / next phase

**The phase stays OPEN** (the 2026-07-24 adjudications — no phase-close; see *Current state*).

**`hsplit` is CLOSED IN FULL** (W5-L7c-1…6, all landed 2026-07-30 — one-line verdicts in
*Decisions made*; full detail `notes/Phase39-design.md` §"W5-L7 research recon" "L7c
decomposition"), and **`hfresh`'s mechanical discharge (residue (iv)) is CLOSED too** (same day).
The landed successor `pencil_conjecture_of_hcontract_hK_hbareSplit_of_card`
(`Molecule/Pencil/Escape.lean`) wraps `pencil_conjecture_of_hcontract_hK_hbareSplit` and carries
exactly three remaining open items, detailed below.

> **The adjudicated direction is COMPLETE, so the phase direction is again a USER DECISION.**
> The Macaulay2 symbolic upgrade delivered both halves it named (`lambda1.m2`, `lambda0.m2`) and
> its **boundary is now measured, not guessed**: generic-point computation makes a *far-graph-free*
> statement class-uniform, and (K-wit) — the escape's uniformity — is not one. Nothing is
> pre-selected here; no phase close, pivot or re-scope is proposed. Read
> `notes/Pencil-strategy.md` first: its §5.3 now records what the route bought and where it stops,
> and its §6 lists the standing alternatives (C2, C3, un-parking W4, closing the phase).
>
> **Smallest concrete commit if work continues on this thread** — the cheap follow-up this pass
> itself generates (workbook §(K-Λ) *What would change this* (vi)): **search the class for a
> habitat forcing `g₁₄ = [b,x₁,x₃,c] = 0`** on its whole pencil chart, i.e. whose outer companion
> lines `C(bx₁)`, `C(x₃c)` necessarily meet. The clause is generic on the frame variety, so a hit
> would mean a habitat chart that fails to dominate it — and would put a third branch into (Λ2)
> and force restating the Λ-completeness theorem. This is a `w4/`-side exact-ℚ search (new driver
> beside `flanks`/`pure`/`lambda`, per §2's layering rule), not an M2 job.
>
> Deliberate non-goals: (Λ0) and (Λ1) are **done** — do not re-derive or re-sample them, and do
> not touch `lambda.py`'s figures (its `--span`/`--witt` runs are unchanged and were re-verified
> this pass). Everything else is unchanged: **W4 stays parked** despite being fully decomposed and
> buildable (do **not** open a W4 build without a fresh user adjudication), `hK`/`hbareSplit` stay
> carried as pinned, option B in both kernel cases stays un-commissioned.

The three carried items:

- **`hcontract`** (W4) — **fully decomposed, buildable, and PARKED.** Canonical home:
  `notes/Phase39-design.md` §"W4 decomposition recon" + §"W4-L4 identification recon" (the
  canonical leaf list lives THERE), with the residual mathematics in the W4 workbook
  `notes/Pencil-W4-informal.md`. State: the L4 verdict trades minimality for the pencil
  habitat's `hcard` bound, so the co-1 case closes minimality-free and KT's
  non-simple-contraction trigger provably reduces to it; the residual carry narrows to
  **`hnoGood'`**, whose vacuity conjecture is **REFUTED** (2026-08-02, `|V| = 19`,
  `nogood_subdiv.py`), so branch 4 needs content. **Route ADJUDICATED (2026-08-02): route 3,
  packaging (b)** — the structure-theorem-pinned dispatch invariant (W4 workbook §(SAFE-RES)'s
  (C7)/(C8) split — *not* `notes/Pencil-informal.md` §(K-slide-comb)'s same-numbered labels),
  with **(K-res)** carried as a sibling of the byte-identical `hK`; bundle and numerics in that
  file's §"widened kernels (routes 1/3)". **Recorded, not built — W4 stays parked** (see
  *Current state*); when commissioned the next concrete commit is **W4-L4b**
  (`exists_degree_two_of_co1_rigid`, pinned + spike-elaborated, all bricks landed, 1 commit),
  then order-flexibly W4-L1/L2/L3′ (spike-COMPILED) and the W4-L5 arc, carrying `hKc`/
  `hbareContract`/`hnoGood'`/`hremove`. Gates N8/N9(+rank-29 control)/N10/N10b all PASSED
  (`notes/scripts/w4/hybrid_gates.py`).
- **`hK`** (kernel (K), research) — the escape `≢ 0` uniformity kernel, and the phase's hardest
  open item. **Standing adjudication ("C: literature hunt + A", verbatim, 2026-07-30): keep
  carrying `hK` as pinned (zero effort now); commissioning the stress-as-chart-rational-function
  infrastructure (option B) is NOT authorized.** The literature hunt ran the same day — **NO
  HIT**, the crux confirmed novel (nearest work: the White–Whiteley 1983/1987 pure-condition
  papers, the right exemplars if option B is ever commissioned; see *Citations* + design doc
  §"(K) literature hunt"). Since the 2026-08-02 W4 route-3(b) adjudication `hK` also carries the
  **(K-res)** residual habitat as a byte-identical sibling (same difficulty class, same stratum,
  one uniform gap serves both).
  **The mathematics is NOT restated here.** Canonical home: `notes/Pencil-informal.md` — its
  **State of (K)** gap map is one row per named gap ((K-tight), (K-move), (K-pitch), (K-wit),
  (K-pitch-∞), (K-Λ), (S1)/(K-slide), (K-slide-cl), (K-slide-comb), (C6), (C7), `P21`,
  (K-flank), (K-chord), (K-dom)), each
  with status, what would close it, and what it is conditional on, plus the uncovered-shape list
  and a *settled, do not re-derive* block. Read that map, not this bullet, before any (K) work;
  update it in place rather than writing a fresh summary. Route history: design doc §"W5-L7
  research recon" "(K) route-1 gate" + "(K) non-constancy recon".
- **`hbareSplit`** (kernel (K-bare), research) — the bare-half-off-feasibility kernel, **carried
  as pinned** (the standing GO, "C: cheap numerics extensions + A", verbatim 2026-07-30; option B,
  the insertion-calculus research, NOT commissioned), with its **extension route recon'd NO-GO on
  landed machinery** the same day: the devices are definitionally dead at infeasible `G`, and the
  count dichotomy's stressed stratum is NONEMPTY, so `¬Feasible` buys no corank control. Minimal
  open statement: **(K-bare-ext)**; the mathematics is not restated here — status row in the
  workbook's *State of (K)* map, full record in the design doc §"(K-bare) extension-route recon"
  (options block ADJUDICATED, option-C results appended), numerics
  `notes/scripts/kbare/{danger,optc}.py`.

Gates for any continuation: `lake build` (warning-clean) + `lake lint` when `.lean` is touched;
`blueprint/verify.sh` + `blueprint/lint.sh` (vocabulary gate bans "stratum"/"strata") when `.tex`
is touched. **When `notes/scripts/` is touched**, the gate is figure invariance — and since
2026-08-05 it is **triggered by what the commit modifies**, not unconditional: if
`git diff --name-only -- '*.py' '*.m2'` shows **no tracked driver modified** (a pure addition, or
prose only), that check *is* the discharge and goes in the commit message; if a driver **is**
modified, the full baseline / re-run / byte-identical obligation stands for it and its import
closure. Both halves, plus the two invocations that exceed a 600 s foreground budget
(`flanks.py --limit`, `lambda.py --adv`), are in `notes/scripts/README.md` *Hard rule — figures
do not move*.

**Any (K)- or W4-side numerics dispatch starts from `notes/scripts/README.md`** — primitive index,
layering map, invocation table, conventions (degeneracy guards + a rank/dimension assert on every
sampled object are mandatory; the `plane_basis` precedent is cited there). Do not reimplement a
primitive it lists, and do not merge a *Divergences* row. A **symbolic** dispatch adds
`notes/scripts/m2/README.md` (M2 version pinned + printed; deterministic, no seed; re-derived
primitives pinned in-driver; additive only — never a port of an existing driver).

## Adjacent directions (orientation only, not this phase)

ORIGAMI (`notes/Origami.md`, next queued) is the bar-joint-side
analog; the wider unqueued survey — incl. IDENT-PANEL, the nearest
neighbor — is `notes/IdeaBacklog.md`.

## Decisions made during this phase

Reverse-chronological, one line per landing; full derivations live in git and
`notes/Phase39-design.md` (per-decision pointer where the design doc has a named section).

- **(Λ0) + the `a`-line spans PROVEN at the generic point — CLASS-UNIFORM, and the recorded
  criterion was INCOMPLETE** (2026-08-05 eleventh dispatch, docs+scripts-only,
  `notes/scripts/m2/lambda0.m2`, 0.1 s) — §5.3's first item, the payoff the M2 layer was built
  for. Every (Λ0) clause is now a nonzero polynomial on **one irreducible variety**, the
  containments and `t`-degrees are identities, and the **38 strata are irrelevant** at the generic
  point (each maps *onto* a dense subset of that variety — the bridge, block (P6)). The exact span
  criterion **(Λ0f′)** is `p⁺₂p⁺₃·g₁₃g₁₄g₂₄ ≠ 0`: the recorded (Λ0f) omits the three Gram
  factors, and **`g₁₄ = [b,x₁,x₃,c] ≠ 0` is asserted nowhere** — non-vacuous by a degeneration
  keeping every other clause. Cost avoided: `t` never becomes an indeterminate (`ω±(t)` are
  structurally cubic/quadratic, so coefficients come from finite differences).
  **Methodological verdict: the upgrade is uniform because (Λ0) is far-graph-free, and (K-wit)
  is not — this confirms `Pencil-strategy.md` §2.3 rather than circumventing it. No gap-map
  status moves.** Workbook §(K-Λ).

- **The Macaulay2 layer LANDED, and (Λ1) is now an IDENTITY over the function field**
  (2026-08-05 tenth dispatch) — `notes/scripts/m2/` with its README carrying §5.4's four
  conventions in binding form (output is *evidence*, never a substitute for Lean; M2 **1.26.06**
  pinned + printed, deterministic; re-derived primitives pinned in-driver; additive only), plus
  `lambda1.m2`: a **gauge-free proof** ((M1) universal cofactor identity + (M2) universal
  quadratic expansion + (M3) α/β isotropy) and an end-to-end check on a slice meeting every
  GL(4)-orbit once. (Λ1) needs **none** of (Λ0); `rank Φ_loc = 2` becomes generic. Boundary
  measured: the ungauged 28-coordinate expansion does **not** finish (600 s). Same commit made
  the **figure-invariance gate proportionate** — it now fires on
  `git diff --name-only -- '*.py' '*.m2'` (no tracked driver modified ⟹ that check discharges it;
  a modified driver ⟹ the full obligation for it and its import closure), after the old
  unconditional reading cost ~62 baseline+re-run pairs on `673cfbf3` while provably vacuous and
  not even completable (`flanks.py --limit` 762 s, `lambda.py --adv` 536 s).

- **The 2026-08-05 research day, sixth–ninth dispatches (one line each; the named workbook
  section is the canonical home and is what a successor reads).**
  *A* (`flanks.py`, §(K-flank)): the conjecture **HOLDS at every uncovered flank** — half 2 per
  shape by exact `∃`-witnesses (8 named + 843 stratum shapes, 0 failures); `hK` needs **no
  re-pin**; a **∀-realization** escape form REFUTED at `P21`.
  *C* (`pure.py`, §(K-pure)): the pure condition is the **WRONG INVARIANT** (a *rank* certificate,
  blind to (W4)); **(K-slide-cl) REFUTED as stated**; **(PC-Z)** the exact reformulation and
  **(PC1)–(PC3)/(PC-OBS)** the arc's first identically-vanishing-pitch theorem; **(K-chord)** the
  successor.
  *B* (`lambda.py`, §(K-Λ)): **(K-Λ) REFUTED as an independent gap** — at `ℓ = 4` *equivalent* to
  **(K-wit)** (Witt); `Φ_loc` always rank 2 ((Λ1)), so the bad far covectors are two structurally
  meaningful points; `ℓ = 5,6` refuted *through the (T5) frame*; (Λ0d)/(Λ0f) named.
  *C1* (`dominance.py`, §(K-dom)): **dominance HOLDS at every class habitat probed (rank 9) but
  is not a route to uniformity**; the **companion length** `k` enters as the governing local
  invariant — **(D1)** `rank d(H ↦ V_bc) ≤ min(9, 6k−14)`, **(D2)** far block `≤ 3(k−3)` attained,
  **(D3)** `hnoRigid ⟹ k ≥ 4`, so the cap bites only on (K-res).
  **Class uniformity of the escape is untouched by all four.**

- **Harness + workbook prep** (2026-08-05, two commits; no mathematics, no verdict changes; 67/67
  drivers re-run, 0 changed figures) — `notes/scripts/README.md` as the harness entry point;
  `notes/Pencil-W4-informal.md` opened; `W19`/`S29` + the *State of (K)* map — *Current state*.

- **(K-slide-comb) REFUTED class-wide; the packing half made uniform ((C6)); (C2)'s length-4
  entry corrected ((C7))** (2026-08-05 fifth dispatch, docs+scripts-only, exact
  `notes/scripts/w4/kslidecomb.py`) — the colouring premise fails inside the class: `χ(K5) = 5`
  with all-`{3,4}` tight+hnoRigid lengths (properness forced at every `ℓ`), and 4-colourable
  hub graphs with no *acyclic* 4-colouring (forced by `L_{φu φw}` ∈ every menu) — so
  (K-slide-cl) is back to **open** on a named sub-class. **(C6)** proven: the unrestricted
  6-fold base packing exists at every class shape (Edmonds matroid partition; its min-max
  hypothesis *is* 5/6-sparsity), so the packing is never the obstruction. **(C7)**: the ℓ=4
  entry is not forced (12/12 exact witnesses), `K4` coverage 439→702/877. Workbook
  §(K-slide-comb).

- **(K-slide) (S1) PROVEN, and (K-slide-cl) reduced to combinatorics** (2026-08-04, third and
  fourth dispatches, exact-ℚ `kslide.py` / `kslidecl.py`; workbooks §(K-slide), §(K-slide-cl)) —
  the slide is a chart automorphism at `ε ≠ 0` with the row family polynomial through `ε = 0`, so
  **one exact limit witness closes a split** (23/23 pitched; `K4`/`W4` controls closed at every
  split; parallel `G°`-edges order-0-obstructed, leaving `P21`). The tetrahedral collapse is a
  WW87 Thm-2.18 specialization inside the decoration variety, reducing the class statement to the
  combinatorial (K-slide-comb) — refuted the next day (entry above); length dictionary proven
  complete, 7/7 members witnessed.

- **(K-pitch) uniform-gap attack — naive collinear collapse REFUTED, slide-in named and
  validated; Λ-compression (T5) extends companions to length 4** (2026-08-04 second dispatch,
  `pitch.py --companion4 | --slide`) — far data enters `Q(z)` only through the annihilator
  covector of `V_bc` in the companion span (the fact (K-dom) (D2) later turns into the
  `3(k−3)` far-dependence bound); the slide-in limit is rank-persistent, pitched on simple
  `G°` / null on parallel-edge `G°`. Workbook §(K-pitch) Steps 5b/6. *(Its named gap (K-Λ) is
  since refuted as independent — the B entry above.)*

- **(K-pitch) developed — motion-side transfer (T1)–(T4) proven; bracket-monomial closed form at
  companion-chain splits; θ(3,3,6) CLOSED** (2026-08-04, exact-ℚ `notes/scripts/w4/pitch.py`) —
  transmitted load spans the perp of `V_bc ⊕ ⟨C_ab, C_ac⟩`, sign law `Q(r)·Q(z) < 0`, escape ⟺
  some `H`-motion pairs non-trivially with the meet line, `pt(a)`-sweep quartic with `a`-free
  leading term, `Q(z) = 2[x,y,a,b][b,x,a,c][y,c,a,b][x,y,a,c][b,x,y,c]`; pitch nonzero 29/29.
  Weakest exact forms (K-wit)/(K-pitch-∞). Workbook §(K-pitch).

- **(K-tight) KT pp. 684–691 re-pin DONE — carrier escape criterion proven+validated; every
  recorded escape failure was a sampler artifact** (2026-08-02, docs+scripts-only, exact-ℚ
  `notes/scripts/w4/repin.py`) — attainment ⟺ two functionals independent on `U`
  (`dim U = dim R_a + 1` forced; 80/80); (K-tight) failure ⟺ `★r ∥ C(Π(b)∩Π(c))`, failure locus
  `line(ab) ∪ P′`. Seed 442 and the 94/96 non-escapes were `plane_basis` degeneracies; corrected
  record: every target-rank seed escapes. Kernel narrowed to (K-move)/(K-pitch). Workbook
  §(K-tight); the design doc's (K)-sections carry dated pointers.

- **W4 routes 1/3 kernel-widening PRICED — one kernel, not two; no counterexample**
  (2026-08-02) — only `hK` widens, to **(K-res)**, carried as a sibling of the byte-identical
  `hK`; `hbareSplit` is unreachable at a residual. The `s₀ = 0` step breaks while the escape
  holds; **(E)** reduces to a cheap `noRigid`-free leaf + **(E-loc)**. W4 workbook
  `notes/Pencil-W4-informal.md` §"widened kernels (routes 1/3)"; `widened.py`.
- **(SAFE-RES) REFUTED; successor (SAFE-RES′) open** (2026-08-02) — `S29` (`|V| = 29`, every
  branch `≤ 2` interiors, all ear length in hub chains) refutes it; **(SAFE-RES′)** = (E) +
  (T) + (V), 255/255 inhabitants, with **(T)** not landed-reachable and invisible to a
  certified search. W4 workbook §(SAFE-RES); `saferes.py`.
- **`hnoGood'` vacuity REFUTED; the PENCIL workbooks opened** (2026-08-02) — `W19`
  (`|V| = 19`), both feasibility verdicts landed-lemma-certified, reached via the **Ear
  Lemma**; branch 4 needs content, and the residual **structure theorem** at a maximal cluster
  survives as route 3(b)'s pin. W4 workbook §"`hnoGood'` vacuity"; `nogood_subdiv.py`.
- **The 2026-07-30 recon day (one-lined; every verdict is carried forward in the matching
  *Hand-off* bullet, which is the canonical home — full record `notes/Phase39-design.md` + git).**
  *(K) non-constancy — PARTIAL*: corank stratification by `index(G) = 5|E| − 6(|V|−1)` (correcting
  N7's "nullity 1"), leaving **(K-tight)** as the hard kernel (`escape/n9.py`). *(K-bare)
  extension route — NO-GO on landed machinery*: minimal open statement **(K-bare-ext)**. *W4
  decomposition + W4-L4 identification*: minimality traded for feasibility, W4-L4b pinned
  buildable, residual narrowed to `hnoGood'`, gates N8/N9/N10/N10b PASSED. User adjudications,
  verbatim: **"C: literature hunt + A"** (K), **"C: cheap numerics extensions + A"** (K-bare),
  **"B: L4 recon first"** (W4). Option B in both kernel cases: **NOT commissioned.**
- **(K) route-1 gate FIRED — locality REFUTED, NO-GO** (2026-07-30, docs-only; exact-ℚ
  `notes/scripts/escape/localtest*.py`) — with identical radius-1 chain data the escape's zero
  locus moves with the far graph (stress supported on every edge; sensitivity to a single
  distance-4 vertex move), killing route 1 and route 2's pointwise reuse; (K) reduced instead to
  *stress non-constancy* via the local 1-dim `S^⊥` lever. Design doc §"W5-L7 research recon".
- **The 2026-07-30 W5-L7 build day (one-lined; `hsplit` is CLOSED IN FULL, so nothing upcoming
  leans on the detail — canonical record: `notes/Phase39-design.md` §"W5-L7 research recon" +
  git).** Recon isolated kernel **(K)** (route (b), the (6.44) identity, REFUTED); user
  adjudicated "route 3: build now". L7a landed with the rigid `k=0` half closed minimality-free
  (KT Lemma 3.4); L7b re-pinned split-data-free as
  `hasGenericPencilRealization_of_independent_pencilRow_target` after `escapePoly` was refuted by
  a BLOCKED build (dispatch-log F9 ×2); L7c decomposed into six leaves ending at
  `pencil_conjecture_of_hcontract_hK_hbareSplit`, its L7c-3/4 numerics gate making route (a) —
  carry `hbareSplit` — GO. Then `hfresh`'s residue (iv) and the consumer headline
  `pencil_conjecture_of_hcontract_hK_hbareSplit_of_card`; blueprint node
  `thm:pencil-conditional-realization-pair` restated + `\lean{...}` extended.
- **Older W5-L5/L6 / W0–W4 entries (one-lined; canonical detail in `notes/Phase39-design.md`
  + git).** W5-L6: L6b re-pinned **triangle-free** (the spike refuted the `hcard`-only pin),
  headline `pencilNondegFeasible_of_ncard_closedHubNbhd_le_three_of_triangleFree` (`Steer.lean`);
  L6a's invariant + safe-vertex transfer (the bare pin was **FALSE**, 10-vertex counterexample);
  L6d's triangle-free split-off. W5-L5: the full cut arm (sub-cases i–v, `hcutPendant3` inline),
  the user-adjudicated route-(b′) `PencilPair` restatement, base and loop arms; L4
  `exists_pencilSeed_of_nondeg`; `Pencil.lean`→`Pencil/` split. W3: L7
  `pencil_conjecture_of_arms`, the L4 cut arm, L1/L2. W2/W1/W0: the extensor-pair layer, the
  statement layer + self-duality, opening recon (R1–R3).

- **Promoted out of this phase** (one-line pointers; the cross-references carry the content):
  TACTICS-GOLF §11/§22/§23; TACTICS-QUIRKS §46/§96/§99/§100/§101/§102/§103/§104; FRICTION
  `exists_injOn_mapsTo_of_ncard_le` + `extensor_pair_smul` [mirror-candidate] and the
  omega/`Set.ncard`-atom idiom.

## Citations (transcribed, project-canonical sources)

- Katoh–Tanigawa, *A proof of the molecular conjecture*, Discrete
  Comput. Geom. **45** (2011) — the KT pointers in this note
  (Cor. 5.7, Thm 4.9, Thm 5.5, Lemma 6.13, the Case I/II/III split)
  are transcribed from `notes/Pencil.md`'s 2026-07-23 survey against
  the project-canonical source (ROADMAP *References*); KT pointer
  verification history: `notes/Phase35.md` *Citations*,
  `notes/Phase23-cleanup.md`. The (K-tight) re-pin (2026-08-02)
  verified pp. 681–691 (Lemma 6.10's proof: Claims 6.11/6.12, the
  `p₁/p₂/p₃` constructions, (6.44), the Lemma 2.1 four-point span)
  directly against the `.refs` copy — workbook §(K-tight) Step 0.
- Jordán 2016 (MSJ Memoirs 34) — checked silent on the pencil stratum
  in the 2026-07-23 survey (the no-literature-result finding), re-confirmed
  by the 2026-07-30 (K) literature hunt (0 pages match pencil/coplanar/
  concurrent/molecular/special-position).
- The 2026-07-30 (K) literature hunt (option C, `Phase39-design.md` §"(K)
  literature hunt") verified these project-new sources against the `.refs`
  copies / primary metadata, all MISSes on the (K-tight) crux: White–Whiteley,
  *The algebraic geometry of motions of bar-and-body frameworks*, SIAM J.
  Alg. Disc. Meth. **8** (1987) 1–32; White–Whiteley, *The Algebraic Geometry
  of Stresses in Frameworks*, SIAM J. Alg. Disc. Meth. **4** (1983) 481–511
  (DOI 10.1137/0604049); Whiteley, *Rigidity of molecular structures: generic
  and geometric analysis*, in Rigidity Theory and Applications (Thorpe &
  Duxbury, eds.), Kluwer/Plenum 1999, 21–46; Whiteley, *Union of matroids and
  rigidity of frameworks*, SIAM J. Discrete Math. **1** (1988) 237–255;
  Schulze–Tanigawa, *Linking rigid bodies symmetrically* (arXiv:1402.0039);
  Garamvölgyi, *Stress-linked pairs of vertices and the generic stress
  matroid* (arXiv:2308.16851).
- White–Whiteley 1987 (op. cit. above) §2 — verified against the `.refs` copy
  (2026-08-04, the (K-slide-cl) development): Proposition 2.6 (the pure condition
  `C(G) = det M(G,T)`, a bracket polynomial of degree `|V|−1`, linear per edge),
  Corollary 2.7 (`C(G(p)) ≠ 0` ⟺ `G(p)` k-isostatic), Theorem 2.18 (nonzero pure
  k-condition ⟺ k edge-disjoint spanning trees ⟺ matroid union of k cycle matroids;
  proof by the shared-indeterminates-per-tree specialization — the technique the
  tetrahedral collapse instantiates), Corollary 2.19 (Tay's count).
- Whiteley, *Some matroids from discrete applied geometry*, in Matroid Theory
  (Bonin–Oxley–Servatius, eds.), Contemp. Math. **197**, AMS 1996, 171–311 —
  §12.2's screw-center description of body-hinge motions
  (`Sᵢ − Sⱼ = α_{ij} h_{ij}`) verified against the `.refs` copy (2026-08-04,
  the (K-pitch) development); volume/pages verified against AMS metadata.
- The 2026-08-05 (K-slide-comb) pass reuses the project-canonical
  **Edmonds 1965**, *Minimum partition of a matroid into independent subsets*
  (matroid partition / union; verified in Phase 12 — `notes/Phase12.md`
  *References*, `.refs/edmonds-1965-minimum-partition-matroid.pdf`) and the
  **Tutte 1961 / Nash-Williams 1961** tree-packing pair (Phase 13). One
  project-new source, verified against publisher metadata (DOI landing page):
  **Grünbaum**, *Acyclic colorings of planar graphs*, Israel J. Math. **14**
  (1973) 390–408, DOI 10.1007/BF02764716 — the origin of *acyclic colouring*,
  the invariant the collapse's colouring premise actually needs. Brooks'
  theorem is cited by name only (classical; no bibliographic pointer claimed).
