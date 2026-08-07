# PENCIL kernel-(K) research fan-out — dispatch specs

**Status: first and second fan-outs COMPLETE; the THIRD (G/Q/O, §"Third
fan-out") is DISPATCHED 2026-08-06.** The first (A/B/C below, prepared
2026-08-05) landed 2026-08-05/06; the second (T/R/M, §"Second fan-out") landed
2026-08-06 — T `fb84ab88` (§(K-grid)), M `72f05634` (§(K-mech)), R (the
§(K-ann) Steps A10–A13 continuation). This file remains the dispatch-scoping
template for any future fan-out. Three independent research
directions on kernel (K), specified here so a fresh session can dispatch them
at S=1 without re-deriving the scoping. User-adjudicated this session (verbatim
below). The mathematics lives in `notes/Pencil-informal.md` (the (K) workbook —
start from its *State of (K)* gap map); this file is dispatch scoping only.

## The adjudication that produced this

**2026-08-05, verbatim:** *"I still think we should hold off on doing more Lean
until we have an informal proof or disproof or any results that would be
significant as standalone pieces of math."* — so the W4 build stays parked
**even though it is fully decomposed and buildable**; the phase's next work is
research, and the bar is *standalone-significant*, not merely
progress-toward-(K).

**Same day, verbatim:** *"Since we're running opus, we don't have to worry quite
as much about token usage (except for the context of the coordinator). I think
we can potentially send off a few parallel research agents if there are a few
independent direcitons worth exploring"*, then, on the reorg-first question:
*"Let's do the rewire; I'm now thinking we should make the rest of this session
a planning / prep session and then do the actual fan-out in a fresh session
after this one."*

Standing kernel adjudications are **unchanged**: `hK` and `hbareSplit` stay
carried as pinned; option B (the stress-as-chart-rational-function
infrastructure) is **NOT** commissioned; W4 route 3(b) is recorded, parked.

## Why a fan-out now, and why these three

Class-uniformity of the escape has defeated **four structurally different**
routes: route 1 (locality — refuted by the gate), route 2 (pointwise reuse —
refuted with it), the naive collinear collapse (refuted as a chart move), and
the tetrahedral collapse (its combinatorial antecedent (K-slide-comb) refuted
class-wide, 2026-08-05). That is the coordinator playbook's recurring-wall
signature, and the newest refutation has a **ceiling** rather than a gap: no
four-hub-position decoration can beat `χ(K5) = 5`.

The three directions below are independent — none consumes another's result —
and each has a standalone-significant outcome:

| | direction | standalone-significant outcome |
|---|---|---|
| **A** | adversarial test at the shapes no mechanism covers | a **disproof** of the pencil conjecture, or the strongest positive evidence + mechanism data |
| **B** | **(K-Λ)** quadric-avoidance | the escape as a **bracket monomial** for companion chains of length ≤ 4 — a theorem in White–Whiteley's idiom |
| **C** | the **pure condition** of the limit carrier, un-specialized | a pure-condition characterization of the pencil escape — the natural publishable object |

Deliberately **not** commissioned: a `>4`-hub-position basis configuration
repairing the tetrahedral collapse. It patches a route with a proven ceiling,
and C subsumes its upside. Also not commissioned: the `ℓ ∈ {1,2,5}` dictionary
analogues and (C7)'s geometric witness — they extend *coverage* of a sub-class
device and, as §(K-slide-comb) *Step D5* proves, **cannot touch either
structural flank**.

## Shared mechanics (all three dispatches)

Rung: each is a research recon settling new mirror mathematics → **top rung**
(`recon-fable`; `recon-opus` when fable is unavailable, as in the session that
prepared this).

**Parallel dispatches must not collide on the working tree.** All five prior
research passes committed to the same files. So:

- Dispatch all three **un-named** and in parallel, as **read-only w.r.t. every
  shared file**. Each one **commits NOTHING**.
- Each may **create its own new** exact-ℚ driver at a pinned path — A:
  `notes/scripts/w4/flanks.py`, B: `notes/scripts/w4/lambda.py`, C:
  `notes/scripts/w4/pure.py` — importing the harness read-only. New files
  never collide; leave them untracked for the coordinator to gate and commit.
- Each writes its full mathematics as a **draft workbook section** to the
  session scratchpad (not the repo) at `fanout-<A|B|C>.md`, in the workbook's
  register, with an explicit confidence verdict
  (proven-informally / true-modulo-named-gap / open / refuted) and a "what
  would change this" line. Keep the **return message** to a tight verdict —
  the coordinator's context is the binding constraint this session, not tokens.
- **No agent edits** `notes/Pencil-informal.md`, `notes/Pencil-W4-informal.md`,
  `notes/Phase39.md`, `notes/Phase39-design.md` (frozen), or any existing
  script. The coordinator verifies each return and lands them **serially**,
  one commit per direction, merging the draft into the workbook and updating
  the *State of (K)* gap map row.

**Label non-collision — the document-side analogue of the tree-side mechanics
above** (added 2026-08-05, after the reorganization pass). The mechanics in this
section stop three concurrent dispatches contending for *files*; they do nothing
about three concurrent dispatches minting the **same label**, which is the
failure that produced the (C6)/(C7) fixup `86d77894`. So each direction of a
fan-out gets a **reserved label prefix and a reserved section name**, allocated
in **`notes/Pencil-labels.md`** *Reserved namespaces* and verified 0-hit across
the tree before dispatch. A dispatch prompt names its prefix; the draft uses it
for every label it mints; the coordinator can then land three returns serially
without a rename. `notes/Pencil-labels.md`'s four-clause minting rule binds every
dispatch — in particular, **qualify every citation of a label you did not mint**
with its owning section.

**Every dispatch carries these, from `notes/scripts/README.md`:** exact ℚ only;
degeneracy guards plus a rank/dimension assert on every sampled object (the
`plane_basis` precedent — a degenerate sampler silently contaminated several
passes' recorded escape-failure figures); seed all randomness; import from the
canonical layer, never reimplement (see the README's *Divergences* table for
the same-name-different-semantics traps).

> **The protocol has now been exercised twice, and the second time at a NEW
> shape (2026-08-05, second research day).** Three read-only recons ran
> concurrently with **one *committing* dispatch**, all four in a **single working
> tree**, with **zero collisions**: the committing dispatch's diff contained only
> its own files, and `git status` stayed clean. The mechanic that made it safe is
> exactly the one above — read-only agents commit nothing and draft **outside**
> the repo — so the committing agent's staging area is never contended.
> **Worktrees were explicitly NOT used, and that was the right call**: the
> contention here is over *shared documents* (`Pencil-informal.md`, the *State of
> (K)* map, `Phase39.md`), not over the tree, so a worktree would convert a
> scheduling problem into a merge problem. Serial landing by the coordinator is
> what resolves the document contention, and it is unaffected by where the agents
> ran.

**And the F11 requirement** (dispatch-log): *each headline claim needs a driver
that tests that sentence.* This arc's last three passes each corrected a
predecessor's "proven piece", every one of which survived a coordinator
scrutiny pass that reproduced the drivers faithfully — because the defects sat
in claims no driver tested (a premise discharged against the wrong invariant,
an exhaustiveness assertion backed only by per-instance asserts, a sampler
whose degeneracy suppressed the phenomenon it sampled). Treat
"forced" / "exhaustive" / "the only" as their own claim class needing their own
driver. Do not state a claim more strongly than the driver that tests it.

## Direction A — adversarial test at the uncovered flanks

**The question, in two halves — keep them distinct.**

1. **Does the pinned kernel `hK` hold at the uncovered flanks?** A failure
   refutes the *pin* and forces a re-pin — significant, but not a disproof of
   the conjecture.
2. **Does the pencil conjecture itself hold there?** — i.e. at a generic pencil
   realization of a flank shape, does the body-hinge rank reach the Tay
   target? **A failure here is a disproof**, and is the headline outcome.

Half 2 is the standalone-significant one; do not let half 1's answer stand in
for it.

**Coordinator's verified findings motivating this.** The flank shapes are
*certified class members* by exactly the criterion the (K-slide) battery uses
(`def = 0`, `hnoRigid`, both `e₀`-ends hubs, parallel-free) — and I confirmed
independently that they satisfy the hypotheses the (K) consumer actually
carries: `hasGenericPencilRealization_of_independent_pencilRow_target`
(`Molecule/Pencil/Escape.lean:186`) takes exactly `hGne` / `hcard` / `htf` /
`hEsc` and **nothing** that excludes `K5`-shaped or `Δ ≥ 5` hub graphs; and with
every length `≥ 3`, `Graph.closedHubNbhd`'s **body** (`Motive.lean:82` — the
pencil hubs among `v` and its neighbours) makes `closedHubNbhd` a singleton at
hubs and `≤ 2` at interiors, with girth `≥ 9`. So these shapes are in the
habitat and the consumer would have to cover them.

**They have never been rank-tested.** §(K-slide-comb) constructed them
*combinatorially only* — `def`, `hnoRigid`, chromatic/acyclic obstruction,
packing existence. No geometry was computed at any of them. Meanwhile the
(K-tight) re-pin left an **exact, checkable** criterion (attainment ⟺ two
functionals independent on the obstruction space `U`; hard-stratum failure ⟺
`★r ∥ C(meet line)`), and the matrices are small — the `K5` flank has
`|V| = 31`, `|E| = 36`, so `5|E| × 6|V| = 180 × 186` over ℚ. This is cheap and
close to decisive.

**Targets** (all from §(K-slide-comb) *Step D5* / the gap map's *Shapes no
mechanism covers*): the `K5` 5-chromatic flank with all-`{3,4}` lengths (84
qualifying assignments); the 6-vertex 11-edge acyclicity-obstructed shape; the
`K222` octahedron; the `P21` parallel-`G°`-edge shape; and a sample of the 438
menu-blocked exhaustive `K4` shapes. Reuse the existing generators —
`kslidecomb.py` already builds every one of them.

**Caveat to respect.** The opening recon's R2 ("the conjecture survives all
exact-rational rank tests") predates all of these shapes; it is not evidence
about them.

**Pivot rule — this is why A is dispatched first among equals.** If half 2
fails at any shape, **stop and report immediately**: the phase's target theorem
would be false, B and C go moot, and PENCIL pivots to "the pencil conjecture is
false — here is the counterexample and the corrected statement". That is a
phase-redefining event for the user to adjudicate, not a result to build on.

## Direction B — (K-Λ), the quadric-avoidance gap

**The question.** Close **(K-Λ)** (§(K-pitch) *Step 5b*): the Λ-compression
(T5) reduces the length-4-companion escape to finding one projective point `λ`
off one local quadric `{Φ_loc = 0}`. Does such a `λ` exist uniformly over the
class? Closing it extends the bracket-monomial closed form from length-3 to
length-4 companion chains.

**Coordinator's reading, to verify against Step 5b before relying on it.**
"A point off a quadric" is *cheap* over an infinite field whenever the quadric
is a proper subvariety — so the real content is almost certainly the **uniform
non-degeneracy of `Φ_loc`** (that `Φ_loc ≢ 0`, i.e. the quadric is not the whole
space), not the avoidance step. If that reading is right, say so explicitly and
attack non-degeneracy; if Step 5b means something stronger, correct me in the
draft. Do not report "(K-Λ) closed" on the strength of the avoidance step alone.

**Grounding.** (T1)–(T5) are proven-informally; `Φ_loc` is quadratic in `λ`;
validated exactly at θ(3,4,5) + NT21 (5/5). Far data enters `Q(z)` only through
the annihilator covector of `V_bc` in the companion span. Driver: `pitch.py
--companion4`.

**Also in scope, if cheap:** whether the same frame reaches `ℓ = 5, 6`
companions (the gap map lists the (T5) frame as the route for the
`bc`-parallel `ℓ ∈ {5,6}` shapes). Report separately from the (K-Λ) verdict.

## Direction C — the pure condition of the limit carrier, un-specialized

**The question.** The tetrahedral collapse was a *specialization* of White–
Whiteley 1987's Theorem-2.18 technique (one shared coordinate frame per
spanning tree, so a single Laplace term survives), run inside the decoration
variety — and the specialization is what carries the ceiling: the four
tetrahedron vertices cap the hub positions at four. **Can the class-uniform
escape be settled by working with the pure condition of the limit carrier
directly**, un-specialized — i.e. showing the pure condition `C(G°-limit)` is
not identically zero on the decoration variety, rather than exhibiting a
decoration where it survives?

**Grounding, verified.** WW87 §2 is verified against the `.refs` copy
(`notes/Phase39.md` *Citations*): Prop. 2.6 (the pure condition
`C(G) = det M(G,T)`, a bracket polynomial of degree `|V|−1`, linear per edge),
Cor. 2.7 (`C(G(p)) ≠ 0` ⟺ `G(p)` `k`-isostatic), Thm 2.18 (nonzero pure
`k`-condition ⟺ `k` edge-disjoint spanning trees ⟺ matroid union of `k` cycle
matroids), Cor. 2.19 (Tay's count). And **(C6)** now shows the packing half of
the collapse is *exactly* the Nash-Williams condition for the multiplicity-
weighted `Ĝ` — so the tree-packing input Thm 2.18 needs is available at every
class shape, un-specialized, and is Phase-12/13/14-reachable.

**What makes this the highest-ceiling direction.** The obstruction the collapse
hit is a property of the *specialization*, not of the pure condition. A
non-vanishing argument for the pure condition on the decoration variety would
be class-uniform by construction, would subsume the sub-class the collapse
covers, and is the natural form for a standalone result.

**Honest scope.** This is the most open-ended of the three, and the recon's own
"stop degenerating" alternative. A verdict of *"no route, and here is the
precise obstruction"* is a fine and useful outcome — say so rather than
manufacturing a partial. Note explicitly whether the route would need option B
(the uncommissioned stress-function infrastructure), since that determines
whether it can be pursued under the standing adjudications.

## Landing checklist (coordinator, per returned direction)

1. Re-run **every** driver the draft cites, plus its headline **figures** — not
   just its `--validate` mode (dispatch-log 2026-08-02: a transcription error
   in a headline figure surfaced only when a later pass re-ran the pool).
2. Ask of each "proven piece": **which driver tests this sentence?** (F11.)
3. Check the draft against the sections it touches for the
   claims-stronger-than-its-own-named-gaps defect.
4. Merge the draft into `notes/Pencil-informal.md`, update the matching **State
   of (K)** gap-map row(s), add a one-line *Decisions made* entry to
   `notes/Phase39.md`, and commit the new script in the same commit.
5. Keep `notes/Phase39.md` forward-weighted and under the ~500-line tripwire;
   the gap map is the canonical home for (K) status, so the phase note's
   kernel bullets stay thin pointers.

---

## Second fan-out — prepared and dispatched 2026-08-06 (directions T / R / M); **COMPLETE, all three landed 2026-08-06**

**User-adjudicated 2026-08-06**, this session, after the harness re-baselining
round closed: of the coordinator's proposed parallel package the user selected
*"OK, let's go with 1+2+3 in parallel"* — 1 = the §(K-clos) (AC-6)
tight-stratum residual (**T**), 2 = §(K-ann) (ANH-R1) (**R**), 3 = the
mechanisms pass (**M**; `notes/Phase39.md` *Current state* (a)). This resolves
the 2026-08-05 open ordering question (whether route σ or §4.6's shortlist
preempts the mechanisms pass): the mechanisms pass runs NOW, in parallel with
both. Route σ was **not** selected — its remaining substance is the Lean half,
which the standing 2026-08-05 adjudication keeps parked. Direction letters are
**T / R / M**, deliberately not A/B/C (already date-ambiguous —
`notes/Pencil-labels.md`).

**Shared mechanics: identical to the first fan-out's** (top of this file) —
each dispatch is a **top-rung research recon** (`recon-fable`, available this
session), **read-only w.r.t. every shared file**, **commits NOTHING**, may
create **its own new driver** at the pinned path below (importing the harness
read-only; left untracked for the coordinator to gate and commit), writes its
full mathematics as a **draft workbook section** in the session scratchpad
(`fanout-<T|R|M>.md`) in the workbook's register with an explicit confidence
verdict and a "what would change this" line, and keeps the return message to a
tight verdict. The F11 requirement binds (each headline claim needs a driver
that tests that sentence; "forced"/"exhaustive"/"the only" are their own claim
class), as do `notes/scripts/README.md`'s conventions (exact ℚ, seeded
randomness, degeneracy guards + rank/dimension asserts, import from the
canonical layer — check the *Divergences* table). Three deltas from the first
fan-out:

1. Reserved namespaces are the **2026-08-06 T/R/M table** in
   `notes/Pencil-labels.md` — clause L1 still binds *inside* a reservation
   (the (ANH-R1)/(ANH-R2) precedent).
2. Any sampled battery quoted as a **rate** or as evidence about a generic
   chart point must gate acceptance on the composite guard
   `repin.star_generic` — the re-baselining round's positive rule
   (`notes/scripts/README.md` *Harness debt* → CLOSED). Negatives and
   existence witnesses are exempt as before.
3. The coordinator checks live session budget between landings
   (`.claude/scripts/session-usage.py limits`) and lands serially, per the
   first fan-out's landing checklist.

### Direction T — the (AC-6) tight-stratum residual: discharge `hK` directly

**The question.** §(K-clos) (AC-6) settled the habitat-level grid-recipe
statement **negatively** (the bare odd cycle `C11`, permanent) but left the
**tight stratum** open with no obstruction identified (15/15 tight shapes
reach the Tay target). Deliver the pair the *State of (K)* map names: (i)
*Step Z4*'s contracted **direction network** proven isostatic whenever
(AC-4)(i)–(ii) hold, and (ii) **chart-image membership** of the grid
configurations verified against `pencilChartPoint` (`Molecule/Pencil/Chart.lean:393`)
and `pencilChartNormal` (`Chart.lean:412`) — currently "argued, not verified".
Delivering both discharges `hK` **on the tight stratum directly** — no escape
route, no split, no inductive hypothesis — and then over every infinite
characteristic-0 field by (AC-7).

**Cheap kill first.** The map names it: a census over the `kslidecomb`
class-shape pool hunting a tight shape where the recipe misses target rank. A
miss **with its mechanism** is a full deliverable; run the census before
investing in the argument.

**Coordinator's verified findings.** The two chart declarations exist at the
cited lines (checked this session). The (AC-1)–(AC-9) batch and the parity
characterization are settled — the workbook's "Settled 2026-08-06, the
over-`ℂ̄` batch" block binds; in particular **(AC-9)**: no σ-fixed witness
reads as *generic* (every σ-fixed body of degree ≥ 3 carries a coincident
hinge line). A rank-attainment witness at a σ-fixed point is still legitimate
by lower semicontinuity — state explicitly which kind of witness each claim
uses.

**Honest scope.** *"No route, and here is the precise obstruction"* is a fine
outcome. Nothing here re-opens the habitat-level statement.

**Driver** `notes/scripts/w4/grid.py` (imports `closure.py` read-only).
**Labels** per the reservation table.

### Direction R — (ANH-R1): pencil-rigidity of the contracted framework

**The question.** Is `H/P − β` **rigid at the pencil placement** (`τ_β ≠ 0`),
class-uniformly at `k = 4`? A positive closes the **whole length-4-companion
stratum** via §(K-Λ)'s Λ-completeness, with (ANH-7)'s one-bracket recipe as
the consumer. Equally deliverable: settle the recorded open half — is the
relocation genuinely *easier* than its parent, or merely smaller? The wall now
sits in **Tay's matroid**, whose independence IS combinatorially characterized
(Phases 12–15), so the sharp form is: does the pencil **pin respect the
matroid** — the weak-map / specialization-stability lead of
`Pencil-strategy.md` §4.6, which (ANH-R1) finally gives a statement.

**Smallest concrete probe** (already named in `notes/Phase39.md` (g)): a
census hunting a class seed with `supp_pen ⊊ supp_gen` at `k = 4` — a strict
support drop at the pencil placement would witness weak-map specialization
actually biting.

**Grounding (canonical §(K-ann); do not re-derive):** (ANH-1) `λ` is the
self-stress of `H/P`, dimension `k − 3`; (ANH-4) `E(H/P)` is a Tay circuit at
`k = 4` **only**, support the whole far edge set at 14/14 class seeds;
branch lengths ≤ 5 ((SD-6)); `supp(τ)` is a **circuit** and `supp(λ)` a
**cocircuit** — do not conflate them.

**Cautions.** (ANH-R1) is a rank **lower** bound — `Pencil-strategy.md` §2.3's
asymmetry is relocated, not evaded; **no counting / matroid / placement-blind
route to (OUT)'s hypothesis** ((OC-3) refutes the class); nothing here closes
`k ≥ 5`.

**Driver** `notes/scripts/w4/shrink.py` (imports `annih.py` read-only).
**Labels** per the reservation table.

### Direction M — the mechanisms pass (§(K-pure) P8/P9)

**The question.** Explain the arc's two remaining *measured anomalies with no
mechanism*: (i) **6v11e's `dim V_bc = 2` drop** — the slide device fails there
at every probed nonempty support, its chart certificate the only closure; (ii)
the **`V_bc ∩ Λ²π̂ ≠ 0` incidence** at `K222` and `K4 (1,1,3,5,4,4)`. Start at
6v11e (*P9* item 5); widen the slide-support menu; sweep the `|V°| ≤ 6`
strata. One rider probe from §(K-σ) *Step σ6*: `V_bc ∩ Λ²π̂ ≠ 0` is the
σ-image of `V_bc ∩ α(·) ≠ 0` at the dual seed — check whether the incidence
configurations are σ-images of one another.

**Why this is standalone-significant.** These anomalies are where either a
**new invariant** or a **near-counterexample** hides. By §(K-pure)'s (PC-Z),
`Q(z) = 0 ⟺ V_bc` meets one of the two maximal totally isotropic 3-spaces
containing `T` — so a structural characterization of *when the incidence
happens* is exactly the target shape of any future non-vanishing argument,
and a mechanism feeds **(K-chord)**, the live combinatorial residue. This is
also the last unstarted item of the user-adjudicated 2026-08-05 ordering.

**Cautions.** (K-slide-cl) **as stated** is refuted — the `∃Σ` form is the
open one; the pure condition is the **wrong invariant** (*P5*) — this pass
hunts mechanisms, not a revival of direction C; §(K-flank)'s per-shape rank
tests are settled — do not re-run them.

**Driver** `notes/scripts/w4/mech.py` (imports `pure.py` / `kslide.py`
read-only). **Labels** per the reservation table — M opens §(K-mech) rather
than minting in §(K-pure).

### Landing (coordinator, per returned direction)

The first fan-out's landing checklist (above) applies verbatim, plus: move
the direction's reservation row into the registry in the landing commit;
direction M's landing adds a *State of (K)* row (or extends (K-chord)'s);
re-check session budget before dispatching nothing further / the next round.

---

## Third fan-out — prepared 2026-08-06 (directions G / Q / O); dispatched SERIALLY, O → Q → G

**Landing status: COMPLETE — all three LANDED 2026-08-06** (O: §(K-out)
Steps O9–O12, (OC-10)–(OC-16). Q: §(K-ann) Steps A14–A17, (ANH-13)–(ANH-16)
— the dispatch's "upgrade" premise refuted by (ANH-9)(iii), the surviving
deliverable the bare-cycle universal polynomial. G: §(K-grid) Steps G8–G13,
(GR-7)–(GR-11) — cheap kill (ii) FIRED, (GR-4) refuted-as-stated and
repaired, the tree-triple theorem (GR-9) proven, the tight-stratum residual
merged into **(GR-10)** alone. Every direction's drivers coordinator-re-run,
all modes byte-identical.)

**User-adjudicated 2026-08-06**, this session, immediately after the second
fan-out landed: presented with the *Hand-off* blockquote's five live leads
(no pre-selection), the user selected **all four research leads** — (1) the
T/R convergence target, (2) the per-shape M2 identity, (3) (K-wit) via
(OC-8), (4) widening `outerline.py --comb` — and did **not** select (5), the
parked Lean half of route σ. The 2026-08-05 Lean-hold adjudication therefore
stands untouched; W4 stays parked; `hK`/`hbareSplit` stay carried as pinned;
option B in both kernel cases stays un-commissioned. A follow-up adjudication
the same session: **dispatch serially, not in parallel** (token budget), with
the rung mixed per direction — O and Q at **opus** (tightly pinned,
decisive-by-construction experiments; coordinator re-runs every driver at
landing), G at the **top rung** (the crux proof attempt, the one direction
where "settles new mirror math" fires).

**Dispatch shape (coordinator).** Leads (3) and (4) are one section's
continuations — the widening is §(K-out) *What would change this* items 1–2
and the (OC-8) attack is its item 6, and the widening's outcome can reframe
the attack (a `dim R ≤ 4` hit closes (OUT) unconditionally where it lands) —
so they run as ONE direction (**O**), widening first. Three directions,
letters **G / Q / O** (dated; A/B/C and T/R/M are taken by the earlier
fan-outs). Serial order **O → Q → G**: the two cheap decisive experiments
land and inform before the expensive deep attempt.

**Shared mechanics: identical to the second fan-out's** (§"Second fan-out",
including its three deltas — the reserved-namespace table is now the
2026-08-06 **G/Q/O** table in `notes/Pencil-labels.md`; any battery quoted as
a *rate* or as generic-chart-point evidence gates on `repin.star_generic`;
the coordinator lands each return before dispatching the next, with a budget
check between). Serial dispatch does not relax the mechanics: each dispatch
is **read-only w.r.t. every shared file**, **commits NOTHING**, creates only
its own pinned new driver(s) (untracked, for the coordinator to gate and
commit), writes its full mathematics as a draft workbook section
(`fanout-<G|Q|O>.md`, session scratchpad) in the workbook's register with an
explicit confidence verdict and a "what would change this" line, and keeps
the return message to a tight verdict. The F11 requirement binds ("forced" /
"exhaustive" / "the only" are their own claim class needing their own
driver), as do `notes/scripts/README.md`'s conventions (exact ℚ, seeded
randomness, degeneracy guards + rank/dimension asserts, import from the
canonical layer — check the *Divergences* table). A direction that opens
Macaulay2 work reads `notes/scripts/m2/README.md` first and budgets per
`Pencil-strategy.md` §5.3: gauge slice mandatory, local/contracted objects
only — the ungauged whole-frame expansion is a measured 600 s kill.

### Direction O — §(K-out) continuation: widen the combinatorial sweep, then attack (OC-8)

**Part 1 — the widening (run FIRST; cheap, decisive either way).** Extend the
(OC-2)-style combinatorial sweep past the `|V°| ≤ 5` cap and the `lmax`
bounds of `outer.sweep_shapes()` (the present scope ran 14 s), hunting the
two hits §(K-out) *What would change this* items 1–2 name: **`dim R = 6`**
(kills (OUT) at that shape; *Step O2*'s arithmetic says it needs `H/X`
non-rigid, hence a chord `χ ≥ 1` or a count violation — report the mechanism)
or **`dim R ≤ 4` / `μ ≥ 2`** (closes (OUT) *unconditionally* there — a
genuine partial closure; needs a chorded companion). Either hit is
standalone-significant; a no-hit widens (OC-2)'s measured base and is
reported as a rate over the widened pool.

**Part 2 — the (OC-8) attack.** (OC-8): at every class shape, a hard-stratum
target-rank point of the **whole-graph** chart with `L_b ⊄ R₁` or
`L_c ⊄ R₄`. §(K-out) (OC-3) proves no counting / matroid / placement-blind
route exists, so any discharge is a **genericity argument on the whole-graph
chart** — which the arc has never established, because `λ` is a far datum.
The one symbolically tractable piece is `L_b ⊄ R₁` as a polynomial
non-vanishing (*What would change this* item 6; `Pencil-strategy.md` §5.3) —
but `R₁` is a **far** object and `m2/lambda0.m2`'s gauge slice does not reach
it, so the first research content is **formulating the right variety**: a
contracted / quotient object small enough for M2 per §5.3's boundary, on
which `L_b ⊄ R₁` becomes a generic-point computation. *"No route, and here is
the precise obstruction"* is a fine outcome.

**Cautions.** Do **NOT** attempt *What would change this* item 4 (pushing the
constructed point to the bad point `p⁺` — deliberately not attempted,
recorded); item 5 is **spent** (the re-baselining round is CLOSED); do not
re-derive (OC-1)–(OC-7); POOL-G rates quote over the **318 coincidence-free**
frames, never the raw 357; claims touching **(K-wit)** are cited in the
qualified form and any new label is minted `OC-`, never in §(K-Λ)'s
namespace.

**Driver** `notes/scripts/w4/outerwide.py` (imports `outerline.py`
read-only); optional M2 leaf `notes/scripts/m2/outerwide.m2`. **Labels**
(OC-10)+, Steps O9+ (reservation table in `notes/Pencil-labels.md`).

### Direction Q — §(K-ann): the per-shape M2 identity `C(H/P − β) ≢ 0`

**The question.** Per shape: is `C(H/P − β) ≢ 0` as an identity over the
function field of the pencil chart (§(K-ann) *Step A13* item 4; *What would
change this (Steps A10–A13)* item (iii))? A positive at a shape upgrades that
shape's (ANH-10) census row from witness to **proof** of (ANH-R1) at the
generic point; a failure **refutes (ANH-R1) there**. Decisive both ways —
the cheapest decisive per-shape experiment left.

**Grounding (canonical §(K-ann); do not re-derive).** (ANH-1): `λ` is the
self-stress of the contracted framework `H/P`, dimension `k − 3`; (ANH-4):
`E(H/P)` is a Tay circuit at `k = 4` **only**; (ANH-9): the weak-map
formulation — one exact rank computation at one rational point decides
(ANH-R1) per triple; (ANH-11)/(ANH-12): the bad locus is **inhabited** by
exact rational guard-accepted points, so the pointwise statement is refuted
and the identity is exactly the *generic* statement, no more. Consistency
check, not a target: the identity's zero locus must contain the nine
(ANH-12) witnesses.

**Scope.** Start at the census's probed triples (the (ANH-10) pool); sweep as
many shapes as the M2 budget allows and report **per shape**. Method per
`m2/README.md` + `Pencil-strategy.md` §5.3/§5.4: gauge slice mandatory, the
contracted object only, respect the measured 600 s boundary. State explicitly
whether each proof step is per-shape or uniform — class uniformity moves
**only** if the identity's *proof* is uniform, and the draft must say which
it delivered.

**Cautions.** `supp(τ)` is a **circuit** and `supp(λ)` a **cocircuit** — do
not conflate; no counting / matroid route to (ANH-R1) exists ((ANH-11)/
(ANH-12), the τ-side analogue of §(K-out) (OC-3)) — the identity is a
per-shape genericity statement, not a class route; any battery quoted as a
rate gates on `repin.star_generic`.

**Driver** `notes/scripts/m2/anhr1.m2` (+ optional Python wrapper
`notes/scripts/w4/anhr1.py`, importing `shrink.py`/`annih.py` read-only).
**Labels** (ANH-13)+, Steps A14+.

### Direction G — §(K-grid)'s (GR-4) + (GR-6): the tight-stratum discharge

**The question.** Prove either or both of the two geometry-free residuals of
§(K-grid): **(GR-4)** — the counting criterion's missing `≤` direction at
conic labels, most plausibly the matroid-union tensor realization pushed
through the moment-curve confinement by a **valuation / degeneration**
refinement of the classical specialization argument (*What would change
this* item (iii)) — and **(GR-6)** — an admissible colouring satisfying
(GR-3)(a)/(b)/(c) in both blocks exists at every tight class shape:
Nash-Williams/Edmonds-shaped (cf. §(K-slide-comb) (C6)), 907/907 evidence,
**no min-max yet** (item (iv); until one exists `Pencil-strategy.md` §2.3's
base-rate warning applies). Either alone is standalone-significant; both
together discharge `hK` **on the tight stratum directly**, then over every
infinite characteristic-0 field by §(K-clos) (AC-7). This is the direction
both T and R converge on — the missing technology is uniform constructed
chart witnesses.

**Cheap kills first** (the section's own items (i)–(ii)): a tight class
shape where the census's early-exit + random-parameter retry finds **no**
target colouring (refutes (GR-6)); a colouring-block anywhere with generic
`dim Z` strictly **above** the (GR-3) max (a third obstruction family,
refuting (GR-4) as stated). The census stands at 907/907 — widening it is
evidence, not proof; the deliverable is the **argument**.

**Convergence rider (a note in the draft, not a second deliverable).** State
any recipe / min-max in a form whose evaluability on §(K-ann)'s **mixed
contracted object** can be assessed later ((ANH-9)(iii); §(K-ann) *What
would change this* item (ii)). Do not chase (ANH-R1) itself.

**Cautions.** Nothing here re-opens the habitat-level (AC-6) refutation
(`C11` is permanent); (GR-2)'s mono-hub-bond mechanism is settled — do not
re-derive it; §(K-clos) (AC-9) forbids reading any σ-fixed witness as
*generic*. *"No route, and here is the precise obstruction"* is a fine
outcome for either residual.

**Driver** `notes/scripts/w4/gridwit.py` (imports `grid.py` read-only);
optional M2 leaf `notes/scripts/m2/gridwit.m2`. **Labels** (GR-7)+, Steps
G8+; if a min-max development needs its own section, the reserved name is
**§(K-pack)**, tag `PK-`.

### Landing (coordinator, per returned direction)

The first fan-out's landing checklist applies verbatim, plus: move the
direction's reservation row into the registry in the landing commit; land
each return and re-check session budget **before dispatching the next
direction** (serial order O → Q → G); direction O's landing may move the
(OUT)-related cells of the (K-wit)/(K-out) rows, which the coordinator
folds into direction Q/G's prompts only if a hit actually landed.
