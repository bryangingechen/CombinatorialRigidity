# Phase 39 — PENCIL: the hinge-pencil molecular conjecture (work log)

**Status:** in progress — phase stays OPEN (standing user adjudications of 2026-07-24 /
2026-07-30 / 2026-08-02, quoted verbatim in *Current state*). W0–W3 and the whole W5 arc
(L0–L7) are COMPLETE — `hsplit` CLOSED IN FULL and `hfresh`'s counting discharge landed
(2026-07-30). Only three items remain, all carried by the landed successor
`pencil_conjecture_of_hcontract_hK_hbareSplit_of_card` (`Molecule/Pencil/Escape.lean`):
`hcontract` (W4), kernel `hK`, and kernel `hbareSplit` — see *Hand-off*. Kernel-(K) research
is at its fifth docs-only pass (workbook `notes/Pencil-informal.md`; the settled W4-residual
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

W0–W3 and W5-L0–L7 are COMPLETE (`hsplit` closed in full; `hfresh`'s counting discharge landed).
The landed headline `pencil_conjecture_of_hcontract_hK_hbareSplit_of_card`
(`Molecule/Pencil/Escape.lean`) carries exactly three open items — `hcontract` (W4), `hK`,
`hbareSplit` — each detailed in *Hand-off*.

**Kernel-(K) research arc — five docs+scripts-only dispatch days** (mathematics in the
kernel-(K) workbook `notes/Pencil-informal.md` — whose *State of (K)* map is the entry point —
and, for the 2026-08-02 W4-residual verdicts, in `notes/Pencil-W4-informal.md`; one-line
records in *Decisions made*): **2026-08-02** — `hnoGood'`
vacuity REFUTED, (SAFE-RES) REFUTED, the routes-1/3 kernel widening PRICED ((K-res)), the
(K-tight) carrier re-pin DONE. **2026-08-04** — (K-pitch)'s motion-side transfer + bracket
monomial; the slide-in degeneration (naive collinear collapse REFUTED); the slide-transfer
theorem (S1), closing the `K4`/`W4` control habitats at **every** split (23/23 witnesses), with
parallel `G°`-edges proven order-0-obstructed; then the tetrahedral collapse, reducing
(K-slide-cl) to the combinatorial (K-slide-comb). **2026-08-05 — (K-slide-comb) is REFUTED
class-wide** (workbook §(K-slide-comb); `notes/scripts/w4/kslidecomb.py`): 5-chromatic (`K5`)
and acyclicity-obstructed hub graphs both sit in the class, so the tetrahedral collapse is a
*sub-class* device and **(K-slide-cl) is back to open** — but its packing half is now uniform
and proven ((C6), Edmonds matroid partition from 5/6-sparsity alone), (C2)'s length-4 entry is
corrected, and **(C7)** (the repaired dictionary) is the named continuation.

Remaining uniform (K) gaps: **(K-Λ)**, **(K-slide-cl)** (routes: (C7), or a decoration with more
than four hub positions), and `P21`-type parallel-`G°`-edge shapes. Canonical status home for all
of them: the workbook's **State of (K)** gap map.

**Next concrete work: the three-way research fan-out, prepared and not yet dispatched —
`notes/Pencil-fanout.md`.** The 2026-08-05 user adjudication (verbatim there) holds the Lean
back until the research yields *"an informal proof or disproof or any results that would be
significant as standalone pieces of math"*, so **W4 stays parked even though it is fully
decomposed and buildable**. The three directions are A (adversarial test at the shapes no
mechanism covers — a disproof of the conjecture is the headline outcome), B ((K-Λ)'s
quadric-avoidance), C (the White–Whiteley pure condition un-specialized). That file carries the
exact questions, the verified grounding, the non-collision dispatch mechanics (read-only,
commits nothing, coordinator lands serially), and the pivot rule if A refutes the conjecture.

**Numerics harness prepped (2026-08-05, prep commit — no mathematics, no `.lean`).** The
`notes/scripts/` harness is now layered: one canonical `sys.path` bootstrap
(`notes/scripts/scriptpath.py`), one home for the reimplemented exact-ℚ / Plücker primitives
(`notes/scripts/exactcore.py`), and **`notes/scripts/README.md`** as the entry point (primitive
index, layering map + import rule, full driver invocation table, mandatory conventions, and the
*Divergences* rows that must **not** be merged). Gated figure-invariant against a pristine
pre-change tree: **67/67 documented driver invocations, 0 changed figures.**

**Workbook split by arc (2026-08-05, second prep commit — no mathematics, no `.lean`, no
figures).** The settled W4-residual arc (three closed sections; W4 itself parked) moved out of
`notes/Pencil-informal.md` into **`notes/Pencil-W4-informal.md`** at full detail, so a (K)
research dispatch reads only live material. The (K) workbook gained the canonical `W19`/`S29`
definitions in its *Shared dictionary* and a one-screen **State of (K)** gap map — the artifact
a future pass **updates** instead of re-deriving five section verdicts in sequence (where the
fourth pass's acyclic-vs-proper colouring conflation hid). No verdict moved.

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

Full record, grounding, and the W0–W5 decomposition:
**`notes/Phase39-design.md`**. One-line verdicts:

- **R1** — panel-side statement pinned in the Phase-35 containment
  model + per-body homogeneous concurrency point (`ExtensorThroughPoint`
  dual of `ExtensorInPanel`); satisfiable for every graph; self-dual
  on-stratum via the landed `screwComplementIso`. Surprise: for dense
  graphs (K4, K3,3, theta(2,2,2)) the stratum *collapses* to the
  all-coplanar locus.
- **R2** — conjecture survives all exact-rational rank tests; the deep
  all-coplanar locus is deficient exactly when `2|E| < 3|V| − 3` — the
  queued "all-coplanar is rank-deficient" claim is a *bar-joint-side*
  fact, false for body-hinge on dense graphs.
- **R3** — KT Lemma 6.2 / Case II survive with pinned choices; the
  outer Thm-5.6 strip-extend, the Case-I glue (Claim 6.4), and Case
  III's Claim 6.12 span break — three open cores.

## Blockers / open questions

- ~~W5-L5 cut arm (L5-cut-iv/v)~~ **CLOSED** (2026-07-25/29) — all four cut sub-cases discharge
  internally; the residual `hcutPendant3` DISCHARGED inline (v-g part 2, `Pair2.lean`). One
  residual note stands: feasibility propagation *as a proposition* is refuted for any purely
  combinatorial (`≤3`-closedHubNbhd) criterion (`not_pencilNondegFeasible_of_triangle_two_hubs`),
  but this doesn't touch L6's own habitat claim.
- ~~W5-L5 base-arm parallel-class blocker~~ **resolved** (2026-07-24) — user adjudicated route
  (b′) (Simple-condition `PencilPair`); base arm closed on top.
- ~~W5-L4 WF-conjunct / shared-`fill` blockers~~ **resolved** (2026-07-24) — motive gained its
  fourth conjunct; `fill` split into `fillHub`/`fillNbr`.
- ~~W5-L6 split-arm feasibility (safe-vertex existence)~~ **CLOSED** (2026-07-29/30) — both
  deficiency regimes' safe-vertex existence PROVEN minimality-free; the L6/L7 coupling is benign
  (KT Case III already splits a safe vertex, Lemma 6.13/4.6).
- ~~`hfresh`'s mechanical discharge~~ **CLOSED** (2026-07-30) — `freshEdgeSupply_of_card_lt_of_
  noRigid_of_degree_two` + `pencil_conjecture_of_hcontract_hK_hbareSplit_of_card` (`Escape.lean`).
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

> **Next concrete commit** — see *Current state* (authoritative; this is a thin pointer so the
> two cannot drift): dispatch the prepared three-way research fan-out,
> **`notes/Pencil-fanout.md`** (directions A/B/C, read-only, coordinator lands serially). The
> 2026-08-05 adjudication holds the Lean back pending a standalone-significant informal result,
> so **W4 stays parked** despite being fully decomposed and buildable — do **not** open a W4
> build without a fresh user adjudication.

The three carried items:

- **`hcontract`** (W4) — **decomposed 2026-07-30** (design doc §"W4 decomposition recon") and
  its **W4-L4 identification recon COMPLETE same day** (user-adjudicated "B: L4 recon first";
  design doc §"W4-L4 identification recon" — the canonical W4 leaf list now lives THERE, not
  in the decomposition section). No new motive: the constrained family lives inside kernel
  discharges only; the IH-interface remainder is settled by the landed `PencilPair`
  (consumption gated by the *contracted* graph's `Simple ∧ Feasible`). L4 verdict: both landed
  KT-6.5/6.6 lemmas (`Contraction.lean:1004/1171`) consume minimality only in their tails, and
  the pencil habitat's `hcard` bound (from feasibility) REPLACES it — a third edge at the
  removal vertex forces a 4-member `closedHubNbhd` — so the co-1 case (∃ proper rigid `H` on
  `|V|−1` vertices) closes minimality-free with `def(G) = def(G−v) = 0` for free, and KT's
  non-simple-contraction trigger provably reduces to it (the carrier bridge). The residual
  carry narrows to **`hnoGood'`** (no co-1 + no Simple∧Feasible contraction + 2EC), with
  **0 inhabitants found** by a two-run structured+random search
  (`notes/scripts/w4/no_good_search.py`) — but the vacuity conjecture is **REFUTED**
  (2026-08-02, `notes/scripts/w4/nogood_subdiv.py`, `|V| = 19` inhabitant): `hnoGood'`
  stays carried and branch 4 needs content. **Route ADJUDICATED (2026-08-02): route 3,
  packaging (b)** — the structure-theorem-pinned dispatch invariant (the W4 workbook
  `notes/Pencil-W4-informal.md` §(SAFE-RES)'s (C7)/(C8) two-way split at triangle-free
  residuals — *not* `notes/Pencil-informal.md` §(K-slide-comb)'s same-numbered labels),
  with **(K-res)** carried as a sibling hypothesis alongside the
  byte-identical `hK` (`hbareSplit` is unreachable at a residual) — **recorded, not built; W4
  stays parked**. The route's bundle: (K-res) + a residual-habitat L7a sibling + (T) + (V) +
  the reduced (E)/(E-loc) of W4-workbook §(SAFE-RES) — see that file's §"widened kernels
  (routes 1/3)" for the trace, statements, and exact-ℚ numerics
  (`notes/scripts/w4/widened.py`). **Next concrete commit (when the W4 build is
  commissioned): W4-L4b** — the co-1 identification lemma `exists_degree_two_of_co1_rigid`
  (pinned signature in the design section, spike-elaborated, all bricks landed, 1 commit).
  Then, order-flexible: W4-L1 (non-simple bare producer, KT 6.2 mirror), W4-L2 (the
  feasibility-based L7b sibling), W4-L3′ (the reshaped skeleton: ¬2EC → landed cut-arm reuse,
  co-1 → `hremove`, good contraction → `hKc` → W4-B, else `hnoGood'`; spike-COMPILED), and the
  W4-L5 arc (discharge `hremove`, the N9-validated re-add via the landed L5-cut-v/h65 steering
  patterns). Carried after L3′: kernels `hKc`/`hbareContract` (hK-posture), `hnoGood'`
  (research options: prove the vacuity conjecture first), `hremove` (until W4-L5). Numerics
  evidence: gates N8/N9(+rank-29 control)/N10/N10b all PASSED (`notes/scripts/w4/`,
  `hybrid_gates.py`).
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
  (K-pitch-∞), (K-Λ), (S1)/(K-slide), (K-slide-cl), (K-slide-comb), (C6), (C7), `P21`), each
  with status, what would close it, and what it is conditional on, plus the uncovered-shape list
  and a *settled, do not re-derive* block. Read that map, not this bullet, before any (K) work;
  update it in place rather than writing a fresh summary. Route history: design doc §"W5-L7
  research recon" "(K) route-1 gate" + "(K) non-constancy recon".
- **`hbareSplit`** (kernel (K-bare), research) — the bare-half-off-feasibility kernel; **carried
  as pinned (the standing GO), extension route recon'd NO-GO on landed machinery** (2026-07-30):
  the chart/reseed/engine device is definitionally dead at infeasible `G` (no nondeg realization
  exists to consume), and the kernel is corank-stratified by a landed-brick count dichotomy
  (dependent ⟹ spanning circuit ⟹ rigid) whose stressed stratum is NONEMPTY — the DZ gadget
  (subdivided `K3,3` + apex, corank-**2** split seeds) sits in the habitat, so `¬Feasible` buys no
  corank control. Minimal open statement: **(K-bare-ext)**, the arbitrary-seed insertion lemma
  (the def-equal caveat folds into its `∃` as a line-avoidance side condition; supply = the
  `pt(v)`-placement freedom, no device needed). Prerequisite for any discharge: the owed KT
  pp. 684–691 boundary-load re-pin + its arbitrary-seed extension. Numerics extended to the
  stressed stratum (`notes/scripts/kbare/danger.py`): off-line placements attain, on-line fail by
  exactly 1, 0 counterexamples. **Adjudicated ("C: cheap numerics extensions + A", verbatim,
  2026-07-30):** carry stands; option-C probes run same day (`notes/scripts/kbare/optc.py`) —
  chain-local adversarial degenerations are excluded by the rank antecedent itself; index-2
  gadgets EXIST (cube/Wagner skeletons, corank-**3** splits, same qualitative picture); the
  corank-2 failure set is exactly the line at every sampled seed. Option B (insertion-calculus
  research) NOT commissioned. Design doc §"(K-bare) extension-route recon" (options block
  marked ADJUDICATED, option-C results block appended).

Gates for any continuation: `lake build` (warning-clean) + `lake lint` when `.lean` is touched;
`blueprint/verify.sh` + `blueprint/lint.sh` (vocabulary gate bans "stratum"/"strata") when `.tex`
is touched. **When `notes/scripts/` is touched**, the gate is figure invariance: baseline every
driver in `notes/scripts/README.md` §3 before editing, re-run after, require byte-identical
output at pinned `PYTHONHASHSEED` (that README's *Hard rule — figures do not move*).

**Any (K)- or W4-side numerics dispatch starts from `notes/scripts/README.md`** — primitive index,
layering map, invocation table, conventions (degeneracy guards + a rank/dimension assert on every
sampled object are mandatory; the `plane_basis` precedent is cited there). Do not reimplement a
primitive it lists, and do not merge a *Divergences* row.

## Adjacent directions (orientation only, not this phase)

ORIGAMI (`notes/Origami.md`, next queued) is the bar-joint-side
analog; the wider unqueued survey — incl. IDENT-PANEL, the nearest
neighbor — is `notes/IdeaBacklog.md`.

## Decisions made during this phase

Reverse-chronological, one line per landing; full derivations live in git and
`notes/Phase39-design.md` (per-decision pointer where the design doc has a named section).

- **Workbook split by arc + *State of (K)* map** (2026-08-05, prep; no mathematics, no verdict
  changes) — `notes/Pencil-W4-informal.md` opened; `W19`/`S29` promoted to the shared
  dictionary — *Current state*.
- **Numerics-harness prep** (2026-08-05, no mathematics; 67/67 drivers re-run, 0 changed figures) — *Current state*.

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

- **(K-slide-cl) reduced to combinatorics — the tetrahedral collapse** (2026-08-04 fourth
  dispatch, docs+scripts-only, exact-ℚ `notes/scripts/w4/kslidecl.py`) — WW87 Thm-2.18
  specialization inside the decoration variety: six scalar forest systems; (W1)–(W2) ⟺ 3
  spanning trees + 3 `b|c`-separating forests, `V_bc` = the separators' opposite duals;
  (W3)–(W4) a finite local-type bracket monomial (one opposite pair required). Length
  dictionary proven complete (`def ≥ ℓ−6`; ℓ=6 ⟹ rigid complement, 5848/5848). Length-2 panel
  pincer proven and repaired (meet-plane extension). 7/7 members witnessed; the residue
  (K-slide-comb) refuted the next day (entry above). Workbook §(K-slide-cl).

- **(K-slide) slide-transfer theorem (S1) PROVEN — one exact limit witness closes a split;
  `K4`/`W4` control habitats closed at every split** (2026-08-04 third dispatch,
  docs+scripts-only, exact-ℚ `notes/scripts/w4/kslide.py`) — slide = chart automorphism at
  `ε ≠ 0`, row family polynomial through `ε = 0`; the rank-persistence proviso dissolved
  (a-posteriori corollary). 23/23 limit witnesses pitched (7 members, 11 split-classes;
  mixed-length + hub-hub flanks witnessed; hub-level serial-chain carrier machine-checked).
  Parallel `G°`-edges proven order-0-obstructed (repeated-line cycle stress); `P21` = the
  uncovered shape. Gaps now (K-Λ)/(K-slide-cl). Workbook §(K-slide).

- **(K-pitch) uniform-gap attack — naive collinear collapse REFUTED, slide-in named and
  validated; Λ-compression extends companions to length 4** (2026-08-04 second dispatch,
  docs+scripts-only, `pitch.py --companion4 | --slide`) — (T5): far data enters `Q(z)`
  only through the annihilator covector of `V_bc` in the companion span (`Φ_loc(λ)`
  quadratic; θ(3,4,5) + NT21, 5/5); slide-in limit = body-hinge on `G°` with per-edge
  serial triples (pencil, chord, pencil), rank-persistent, `O(ε)`-approached, pitched on
  simple `G°` (3/3) / null on parallel-edge `G°` (2/2). Gaps now (K-Λ)/(K-slide).
  Workbook §(K-pitch) Steps 5b/6; design-doc pointers updated.

- **(K-pitch) developed — motion-side transfer proven; bracket-monomial closed form at
  companion-chain splits; uniform gap narrowed to (K-wit)/(K-pitch-∞)** (2026-08-04,
  docs+scripts-only, exact-ℚ `notes/scripts/w4/pitch.py`) — the transmitted load spans the
  perp of `V_bc ⊕ ⟨C_ab, C_ac⟩` (`V_bc` = the chain ends' relative twist system through
  `G−v−a`; stress-free); sign law `Q(r)·Q(z) < 0`; escape ⟺ some `H`-motion pairs
  non-trivially with the meet line; `pt(a)`-sweep quartic with `a`-free leading term;
  θ(3,3,6) ((K-res) hard stratum) CLOSED via
  `Q(z) = 2[x,y,a,b][b,x,a,c][y,c,a,b][x,y,a,c][b,x,y,c]`; pitch nonzero 29/29 seeds.
  Workbook §(K-pitch); the design doc's (K)-sections carry dated pointers.

- **(K-tight) KT pp. 684–691 re-pin DONE — carrier escape criterion proven+validated; every
  recorded escape failure was a sampler artifact** (2026-08-02, docs+scripts-only, exact-ℚ
  `notes/scripts/w4/repin.py`) — M₁ carrier-dead, M₂/M₃ survive as point sweeps (routes A/B);
  attainment ⟺ two functionals independent on `U` (`dim U = dim R_a + 1` forced; 80/80
  per-placement); (K-tight) failure ⟺ `★r ∥ C(Π(b)∩Π(c))`; failure locus `line(ab) ∪ P′`.
  Seed 442 and the 94/96 non-escapes were `plane_basis` degeneracies (`n[2] = 0`); corrected
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
  *(K) non-constancy recon — PARTIAL*: corank stratification by `index(G) = 5|E| - 6(|V|-1)`
  (correcting N7's "nullity 1" fact -- theta(4,4,3) is a corank-2 both-ends-hubs witness);
  `dim R_a >= 2` makes the escape automatic, so the hard kernel is **(K-tight)**
  (`notes/scripts/escape/n9.py`). *(K-bare) extension-route recon -- NO-GO on landed machinery*:
  the devices are definitionally dead at infeasible `G`, and the count dichotomy confines stress
  to the rigid dependent stratum, which is NONEMPTY (DZ gadget) -- minimal open statement
  **(K-bare-ext)**. *W4 decomposition recon*: dispatch skeleton spiked, kernels (K-c)/(K-bare-c)
  pinned, gates N8/N9/N10/N10b PASSED (`hybrid_gates.py`). *W4-L4 identification recon*:
  minimality traded for feasibility (`Contraction.lean:1004/1171` tails; a third edge forces a
  4-member `closedHubNbhd`), W4-L4b pinned buildable, skeleton reshaped to L3', residual narrowed
  to `hnoGood'` with 0 search inhabitants (`no_good_search.py`; its vacuity later REFUTED). User
  adjudications that day, verbatim: **"C: literature hunt + A"** (K), **"C: cheap numerics
  extensions + A"** (K-bare -- the option-C probes ran same day, `notes/scripts/kbare/optc.py`:
  corank-2 failure set exactly `line(a,b)`, 0/179 off-line failures), **"B: L4 recon first"**
  (W4). Option B in both kernel cases: **NOT commissioned.**
- **(K) route-1 gate FIRED — locality REFUTED, NO-GO** (2026-07-30, docs-only; exact-ℚ scripts
  `notes/scripts/escape/localtest*.py`) — with identical radius-1 chain data the escape's
  zero locus moves with the far graph (within-habitat and cross-habitat; stress supported on every
  edge; sensitivity to a single distance-4 vertex move), killing route 1 and route 2's pointwise
  reuse; (K) reduced instead to *stress non-constancy* via the local 1-dim `S^⊥` lever. Design doc
  §"W5-L7 research recon" "(K) route-1 gate".
- **The 2026-07-30 W5-L7 build day (one-lined; `hsplit` is CLOSED IN FULL, so nothing upcoming
  leans on the detail — canonical record: `notes/Phase39-design.md` §"W5-L7 research recon" +
  git).** Recon isolated kernel **(K)** (route (b), the (6.44) identity, REFUTED) and the user
  adjudicated "route 3: build now"; L7a `hasGenericPencilRealization_of_splitOff_of_safe` landed,
  and the rigid `k=0` half closed minimality-free (`edgeBound_of_noRigid_of_degree_two` +
  `exists_adjacent_degree_two_pair_of_noRigid_of_degree_two`, KT Lemma 3.4). L7b re-pinned
  split-data-free as `hasGenericPencilRealization_of_independent_pencilRow_target` after
  `escapePoly` was refuted by a BLOCKED build, then landed with the `[Nonempty α]` →
  `[Inhabited α]` correction (dispatch-log F9 ×2). L7c decomposed into six leaves: L7c-1 by
  reuse of `simple_of_loopless_of_noRigid`, L7c-2 =
  `exists_splitOff_data_of_degree_eq_two_of_twoEdgeConnected`, L7c-3/4 =
  `pencilPair_of_habitat_ncard_eq_{three,four}` (whose numerics gate made route (a) — carry
  `hbareSplit` — GO; FRICTION [idiom] entries + TACTICS-QUIRKS §103/§104), L7c-5/6 =
  `pencilPair_of_splitOff_of_habitat` + `pencil_conjecture_of_hcontract_hK_hbareSplit`. Finally
  `hfresh`'s residue (iv) closed via `freshEdgeSupply_of_card_lt_of_noRigid_of_degree_two` and
  the consumer headline `pencil_conjecture_of_hcontract_hK_hbareSplit_of_card`; blueprint node
  `thm:pencil-conditional-realization-pair` restated + `\lean{...}` extended.
- **Older W5-L5/L6 / W0–W4 entries (one-lined; canonical detail in `notes/Phase39-design.md`
  + git).** L6b re-pinned triangle-free (spike refuted the `hcard`-only pin) + L6b-i assembly
  `pencilNondegFeasible_of_selectors_of_satisfiable` + L6b-ii engine
  `exists_coord_linearIndepOn_pencilChartPoint_of_idx` and headline
  `pencilNondegFeasible_of_ncard_closedHubNbhd_le_three_of_triangleFree` (`Steer.lean`;
  dispatch-log F9; FRICTION `exists_injOn_mapsTo_of_ncard_le` [mirror-candidate] +
  omega/`Set.ncard`-atom idiom). L6a invariant + safe-vertex transfer
  `ncard_closedHubNbhd_splitOff_le_three_of_safe` (bare pin was FALSE, 10-vertex
  counterexample) + `exists_adjacent_degree_two_pair_of_noRigid_of_deficiency_pos` + L6d
  `c4_isProperRigidSubgraph`/`splitOff_triangleFree_of_noRigid` (TACTICS-QUIRKS §46; F9 ×3);
  L6/L7 coupling benign (KT 6.13/4.6). L5-cut-v-a…v-g the full sub-case-(v) chain
  (`Witness.lean`/`Steer.lean`/`Pair2.lean`; TACTICS-QUIRKS §96/§101/§102; FRICTION
  `extensor_pair_smul` [mirror-candidate]) — L5-cut-v CLOSED, `hcutPendant3` inline.
  L5-cut-iv shell `pencilPair_of_not_twoEdgeConnected` + sub-cases (`Pair.lean`/`Pair2.lean`);
  L5-cut-i…iii the `Gᵢ⁺` structure layer + restriction infra (`Motive.lean`/`Bricks.lean`/
  `Arms.lean`). Base arm `pencilPair_of_ncard_le_two`; `PencilPair` route-(b′) restatement
  (user-adjudicated) + `not_simple_of_parallel`; loop arm `pencilPair_of_isLoopAt`. W5-L4
  `exists_pencilSeed_of_nondeg` (`Reseed.lean`); `Pencil.lean`→`Pencil/` split; W5 design pass.
  W3: L7 `pencil_conjecture_of_arms`, L4 cut arm `hasPencilRealization_of_not_twoEdgeConnected`,
  L1 `exists_isProperRigidSubgraph_of_three_le_degree`, L2 `Graph.pencil_reduction`. W2
  `exists_extensor_two_pencils_iff`; W1 `exists_concurrency_point_of_extensorInPanel_pair`; W0
  statement layer + self-duality; opening recon (R1–R3). Promotions: TACTICS-GOLF §11/§22/§23,
  TACTICS-QUIRKS §99/§100/§101.

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
