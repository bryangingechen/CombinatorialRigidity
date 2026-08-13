# PENCIL kernel-(K) research fan-out — dispatch specs

**Status: ALL FIVE fan-outs COMPLETE; the SIXTH direction (CFLANK,
§"Sixth direction") LANDED 2026-08-07; the SEVENTH direction (GCAP,
§"Seventh direction") LANDED 2026-08-13; the EIGHTH direction (GUNIF,
§"Eighth direction") LANDED 2026-08-13.** The
first (A/B/C
below, prepared 2026-08-05) landed 2026-08-05/06; the second (T/R/M,
§"Second fan-out") 2026-08-06; the third (G/Q/O, §"Third fan-out")
2026-08-06; the fourth (E/J, §"Fourth fan-out") 2026-08-07; the fifth
(PEX/TCOL, §"Fifth fan-out") 2026-08-07; the sixth (CFLANK, §"Sixth
direction") 2026-08-07 — no flank found, (GR-15) stays OPEN; the seventh
(GCAP, §"Seventh direction") 2026-08-13 — (GR-27)/(GR-28)(i)–(iii)
proven, (GR-28)(iv) then true-modulo-named-gap (**since REFUTED** — the
eighth, below), the certificate-3 target proven per swept shape,
still no flank, (GR-15) stays OPEN; the eighth (GUNIF, §"Eighth
direction") 2026-08-13 — **REFUTED both of its targets**: (GR-28)(iv)
at `k ≥ 3` is refuted with an exact boundary (theorem at `n_hub ≤ 6`,
false from `n_hub = 8`), the repair theorem is unprovable as posed;
per-shape (GR-15) HOLDS at every new witness and (GR-15) itself stays
OPEN, unchanged in status. CFLANK was a
**single direction**, not a fan-out — its selection was a **coordinator
delegation** (`notes/Phase39.md` *Current state*, the 2026-08-07 "keep
going on my own judgment" adjudication), not a user pick from a candidate
list; GCAP's selection was **delegated further to a top-rung fable
recon** (the 2026-08-12 adjudication, verbatim in `notes/Phase39.md`
*Current state*); GUNIF's selection follows the same standing delegation,
from the TERMINATION test checked (and not fired) on GCAP's return
(`notes/Phase39.md` *Hand-off*), not a fresh adjudication. This file
remains the dispatch-scoping template for any
future fan-out or single direction. Three independent research directions on kernel (K), specified
here so a fresh session can dispatch them at S=1 without re-deriving the
scoping. User-adjudicated this session (verbatim below). The mathematics
lives in `notes/Pencil-informal.md` (the (K) workbook — start from its
*State of (K)* gap map); this file is dispatch scoping only.

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
6. **A draft's closing *"Coordinator actions at landing"* block is
   scaffolding, not mathematics: execute it, then STRIP it — it must never
   be merged into the workbook.** Merged, it reads as an outstanding to-do
   list for work already done and will mislead the next reader into
   thinking status moves are pending. Also *audit* it while executing:
   verify each named action in tree (registry, gap map,
   `notes/scripts/README.md` §3, reserved namespaces) rather than assuming
   it was done — nothing here is gated. Four consecutive landings (E, TCOL,
   GCAP, GUNIF) merged the block verbatim, caught only by the coordinator's
   post-GUNIF verification sweep (2026-08-13). **Exact parallel to item 2 of
   the fifth fan-out's landing block** (the `notes/scripts/README.md` §3
   invocation rows), which was itself added after four consecutive landings
   skipped it — the recurring shape is a per-landing chore that no gate
   covers, so the checklist is the only mechanism.

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

---

## Fourth fan-out — prepared 2026-08-06 (directions E / J); dispatched SERIALLY, E → J

**Landing status: COMPLETE — both directions LANDED 2026-08-07.**
Direction J: the new workbook section **§(K-frame)** — *Step G13*'s lemma
shape delivered in minimal form ((FR-1): one witness point + irreducibility
of the source; "dominance" over-asks); both bad divisors **combinatorial at
grid points** ((FR-2)/(FR-3), `det = 128·Vdm(s)·Vdm(u)`); the transport
works by **regridding at `G′`** ((FR-4)); the (ANH-14) residue **discharged
at 1904/1904 enumerated sites** with 30 exact certificates ((FR-5));
(OC-8)'s non-containment **inhabited by construction** at θ(3,4,5), the
strict package 0/8 with the (AC-9) mechanism named ((FR-6)); residue
**(FR-R1)** (pattern-existence — no rank/count/balance/tree-triple
content). All five Python modes + the M2 leaf coordinator-re-run, figures
byte-identical. Direction E (landed first): §(K-grid) Steps G14–G18,
labels (GR-12)–(GR-15) — the (GR-10) **min-max REFUTED as posed**: (GR-13)
NP-completeness of the grouped packing at exact balance plus **18
counting-blind separators on the habitat**; (GR-10) itself **survives
exhaustive enumeration** (16600/17772 filter-passing colourings certified,
no shape misses — cheap kill (i) did not fire); the discharge residual
**re-aimed at (GR-15)**, one-point-decidable per shape, its per-block
min-max question (GR-4′), counting-shaped. Every driver mode
coordinator-re-run, figures byte-identical; §(K-pack) not opened;
`packmm.m2` not needed.)

**User-adjudicated 2026-08-06**, this session, immediately after the third
fan-out landed: presented with the *Hand-off* blockquote's four candidate
directions (no pre-selection), the user selected **(1) the (GR-10) min-max
attack** and **(2) the shared dominance lemma**, and did **not** select (3)
the unselected leads (b)–(f) or (4) the parked Lean half of route σ / the W4
build. The 2026-08-05 Lean-hold adjudication therefore stands untouched; W4
stays parked; `hK`/`hbareSplit` stay carried as pinned; option B in both
kernel cases stays un-commissioned. Dispatch is **serial** (the standing
session default; the user's check-in confirmed serial-unless-stated), order
**E → J** (the user's listed order; E's outcome cannot be reframed by J's,
so no cheap-first inversion applies). Direction letters are **E / J**, dated
— A/B/C (×2), S1–S4, T/R/M and G/Q/O are taken; both chosen off the
collision table's bare-token rows. One recorded hazard, not a rename:
**(E)** bare remains §(SAFE-RES)'s gap token (W4 workbook) — the direction
is always written *direction E*, with the date when ambiguity is possible.

**Rung (coordinator, playbook application — not a user adjudication):** both
directions run at the **top rung** (`recon-fable`). Each is a crux proof
attempt on which a positive verdict settles new mathematics and re-routes
the phase — the same trigger that put direction G at the top rung; neither
is a tightly-pinned decisive-by-construction experiment of the O/Q kind.

**Shared mechanics: identical to the second fan-out's** (§"Second fan-out",
including its three deltas — the reserved-namespace table is now the
2026-08-06 **E/J** table in `notes/Pencil-labels.md`; any battery quoted as
a *rate* or as generic-chart-point evidence gates on `repin.star_generic`;
the coordinator lands each return before dispatching the next, with a
budget check between). Serial dispatch does not relax the mechanics: each
dispatch is **read-only w.r.t. every shared file**, **commits NOTHING**,
creates only its own pinned new driver(s) (untracked, for the coordinator
to gate and commit), writes its full mathematics as a draft workbook
section (`fanout-<E|J>.md`, session scratchpad) in the workbook's register
with an explicit confidence verdict and a "what would change this" line,
and keeps the return message to a tight verdict. The F11 requirement binds
("forced" / "exhaustive" / "the only" are their own claim class needing
their own driver), as do `notes/scripts/README.md`'s conventions (exact ℚ,
seeded randomness, degeneracy guards + rank/dimension asserts, import from
the canonical layer — check the *Divergences* table). A direction that
opens Macaulay2 work reads `notes/scripts/m2/README.md` first and budgets
per `Pencil-strategy.md` §5.3/§5.4: gauge slice mandatory, local/contracted
objects only — the ungauged whole-frame expansion is a measured 600 s kill,
and §(K-ann) (ANH-16) brackets the reach from both sides (degree 12 in 24
indeterminates finishes at 578 s; the θ core at the generic point does not
finish at 600 s).

### Direction E — §(K-grid)'s (GR-10): a min-max for the partition-constrained tree-triple packing

**The question.** Prove **(GR-10)** — every tight class shape admits an
admissible ruling colouring whose classes partition, in **both** blocks,
into three groups with pairwise-union spanning trees of the respective
contracted multigraph (*Step G11*'s boxed statement; measured 907/907) —
by a min-max for the partition-constrained base packing, or refute it with
a structural flank. Discharging (GR-10), with the proven (GR-9), (GR-5) and
§(K-clos) (AC-7), discharges `hK` **on the tight stratum directly**, over
every infinite characteristic-0 field.

**Grounding (canonical §(K-grid) Steps G11–G12; do not re-derive).** The
named obstruction: grouped co-independence is not a matroid on the classes
(*Step G11*'s `U_{2,4}` example — the exchange axiom fails), so Edmonds /
Nash-Williams–Tutte supply the **unconstrained prototype but no
off-the-shelf min-max**; without the class constraint the packing side is
exactly §(K-slide-comb) (C6)'s Phases-12–15 territory. The natural min side
is (GR-3)(b)'s counting condition — `3(comp(G∖F) − 1) ≤ 2|F|` over class
unions — and **whether it (plus admissibility) is sufficient at tight
shapes IS the open question**. The finite-object structure is *Step G12*,
all proven: admissible colourings are one free bit per branch; the
both-classes-forests constraint sees only the hub-hub subgraph of `G°`;
balance is a signed subset-sum over odd-length branches; per hub multigraph
`G°`, (GR-10) is a finite CSP parametrized by the length profile — so a
min-max must be **uniform over `G°`**, not over subdivisions (§(K-ind)
(I4)).

**Cheap kill first** (the section's *What would change this* item (i)): a
tight class shape whose **every** admissible colouring leaves, in some
block, a group-obstructing pattern — refutes (GR-10); (GR-11)'s
hierarchical certificates and the (GR-4′) route then re-enter the critical
path, in that order. None surfaced in 907 shapes; widening the census
further is **evidence, not proof** — the deliverable is the **argument**.
Until a min-max exists, `Pencil-strategy.md` §2.3's base-rate warning
applies verbatim (every prior class-uniform combinatorial-existence claim
of this arc was eventually proven by a min-max or refuted by a flank).

**Tools.** (GR-11) (proven, undeveloped) is the fallback shape: ε-adic
hierarchical certificates whose order-0 system is (GR-9)'s three-point
collapse — a candidate induction skeleton for the sufficiency direction.
§(K-slide-comb) (C6)'s Edmonds argument is the reachable unconstrained
half. Phases 12–15 (matroid union, Tutte–Nash-Williams, Edmonds partition)
are in tree.

**Cautions.** Nothing here re-opens the habitat-level (AC-6) refutation
(`C11` is permanent — tight shapes have hubs and are never bare cycles); do
not re-derive (GR-1)–(GR-9) or (GR-4′); no σ-fixed witness is read as
generic (§(K-clos) (AC-9)); *"no min-max, and here is the precise
obstruction"* is a fine outcome.

**Driver** `notes/scripts/w4/packmm.py` (imports `gridwit.py` / `grid.py` /
`closure.py` read-only); optional M2 leaf `notes/scripts/m2/packmm.m2`.
**Labels** (GR-12)+, Steps G14+ (reservation table in
`notes/Pencil-labels.md`); if the min-max development needs its own
section, the reserved name is **§(K-pack)**, tag `PK-` (re-reserved from
the pool).

### Direction J — the shared chart-to-frame dominance lemma ((OC-16) / (ANH-14))

**The question.** Directions O and Q terminated on residues of one shape —
**chart-to-frame dominance**: §(K-out) (OC-16)'s gap (at degree-3 hubs,
availability ⟺ the hard-stratum target-rank locus `⊄ {pt(b) ∈ C₀}`;
3081/5226 POOL-CW pairs at the `b` end) and §(K-ann) (ANH-14)'s (the
universal irreducible degree-12 polynomial `C` nonzero somewhere on the
frame's reachable locus; 1904/6426 length-5-branch sites). §(K-grid) *Step
G13* names the candidate lemma shape serving both: *"an explicit
constructed rational point on the relevant stratum, off the explicit bad
divisor, plus irreducibility of the stratum, gives dominance."* Deliver
that lemma at either residue — or price precisely why the shape fails.

**The three research contents, in order.** (1) **Evaluability battery**
(*Step G13*'s assessment — one battery per residue): both bad divisors are
evaluable at the (GR-5)/(GR-9) grid points ((OC-16)'s
`Δ = [a,u,b] · C₀(pt b)` is closed-form at degree-3 hubs; (ANH-14)'s `C` is
one universal bracket polynomial) — run it. (2) **The transport, the
unattempted step**: the grid points live at the *pencil* placement of `G`;
serving the residues needs the construction transported to the contracted
objects — `H/{e₂,e₃,e₄}` for (OC-16), `H/P − β` for (ANH-14). Note
(OC-16)'s own residue framing: the far datum there is compressed to four
chain points, so its dominance question is *smaller* than (OC-8) as
recorded, and is a **finite check per chain hub pattern** (the census's
`(x₁,x₂,x₃)` histogram is the companion-side analogue). (3) **The
irreducibility ingredient** — irreducibility of the hard-stratum locus is
the ingredient none of the three directions owns; identify the smallest
object on which it must hold and what would prove it.

**Cautions.** The witness must certify through **rank semicontinuity off a
divisor**, never through guard genericity — σ-fixed points are never
composite-guard generic (§(K-clos) (AC-9)); no counting / matroid /
placement-blind route exists on either side ((OC-3); its τ-side analogue
(ANH-11)/(ANH-12)) — do not propose one; `supp(τ)` is a **circuit** and
`supp(λ)` a **cocircuit**; POOL-G figures are quoted over the **318
coincidence-free** frames, never the raw 357; do not re-derive §(K-out)'s
settled batch ((OC-1)–(OC-7)) or §(K-ann)'s ((ANH-1)–(ANH-6), (SD-6)); the
two pools are pinned and **disjoint**, never aggregated. *"No route, and
here is the precise obstruction"* is a fine outcome.

**Driver** `notes/scripts/w4/framedom.py` (imports `gridwit.py` /
`outerwide.py` / `anhr1.py` / `shrink.py` read-only); M2 leaf
`notes/scripts/m2/framedom.m2` (this direction is M2-heavy — budget per
§5.3/§5.4 as above). **Labels**: new section **§(K-frame)**, tag `FR-`,
labels (FR-1)+, Steps FR0+ (reservation table in
`notes/Pencil-labels.md`); cross-references into §(K-out)/§(K-ann) use the
qualified form (L3), and moving either section's gap-map cell is the
coordinator's action at landing, never the draft's.

### Landing (coordinator, per returned direction)

The first fan-out's landing checklist applies verbatim, plus: move the
direction's reservation row into the registry in the landing commit; land
each return and re-check session budget **before dispatching the next
direction** (serial order E → J); direction E's landing may move the
(GR-10) cell of the §(K-grid) row, which the coordinator folds into
direction J's prompt only if something actually landed (the grid witness
supply is *Step G13*'s candidate supplier for J's witness half).

## Fifth fan-out — prepared 2026-08-07 (directions PEX / TCOL); dispatched SERIALLY, PEX → TCOL

**Landing status: BOTH DIRECTIONS LANDED 2026-08-07 — the fifth fan-out is
COMPLETE.** PEX (§(K-frame) continuation, Steps FR7–FR11, (FR-8)–(FR-14) —
the bare-cycle stratum proven **finite** and exhaustively enumerated (22 iso
classes / 76 sites / 1976 labelled instances), **(FR-R1) PROVEN** with
(FR-4)'s named (GR-5)-at-`G′` gap the sole rider; driver `w4/patexist.py`'s
six modes coordinator-re-run, all byte-identical). TCOL (§(K-grid)
continuation, Steps G19–G23, (GR-16)–(GR-20) — the branch-level reduction to
a square system on the hub multigraph, the circuit run law, the
6-spanning-tree packing statement, and a collapse-order-4 certificate at all
18 habitat separators, all proven, but **(GR-15) stays OPEN, no flank
found**; driver `w4/gridcol.py`'s six modes coordinator-re-run, all
byte-identical). **Class uniformity of `hK` untouched by either; no
gap-map status moves.**

**User-adjudicated 2026-08-07**, this session, immediately after the fourth
fan-out landed: presented with the *Hand-off* blockquote's five candidate
directions (no pre-selection), the user selected **(1) prove (FR-R1)** and
**(2) the (GR-15)/(GR-4′) attack**, and did **not** select (3) the (FR-6)
follow-ons, (4) the unselected leads (b)–(f), or (5) the parked Lean half of
route σ / the W4 build. The 2026-08-05 Lean-hold adjudication therefore
stands untouched; W4 stays parked; `hK`/`hbareSplit` stay carried as pinned;
option B in both kernel cases stays un-commissioned. Dispatch is **serial**
(the standing session default), order **PEX → TCOL** — and here the order is
load-bearing rather than merely the user's listing: both residues are
colouring-existence statements over the *same* §(K-grid) *Step G12*
branch-bit structure, and (FR-R1) is the one without a spline/rank side, so
a technique that works there is the natural input to (GR-15). TCOL's prompt
therefore folds in whatever PEX actually lands (never a prediction of it).

**Direction codes are multi-letter from this fan-out on** (user call,
2026-08-07). Four fan-outs plus the harness round consumed A/B/C (×2),
S1–S4, T/R/M, G/Q/O and E/J; of the fourteen unused single letters only
**two** were 0-hit across the pencil doc set, and the corpus already carries
two recorded single-letter hazards (bare `(E)` = §(SAFE-RES)'s gap token;
the A/B/C date-ambiguity). That is the registry's own measured diagnosis
firing on the direction letters themselves — bare single-letter families
collide, topic-tagged ones have not. `PEX` (pattern-existence) and `TCOL`
(tight-stratum colouring) are verified **0-hit as raw substrings** across
`*.md`, `*.tex`, `*.lean`, `*.py`, `*.m2` — the substring check, not just
whole-token, because that is the trap that cost the third fan-out its first
`m2` driver name. Recorded as minting clause **(L5)** in
`notes/Pencil-labels.md`; the single-letter era is grandfathered under (L4)
and stays dated wherever it is written.

**Rung (coordinator, playbook application — not a user adjudication):** both
directions are mapped to the **top rung** — each is a crux proof attempt on
which a positive verdict settles new mathematics and re-routes the phase,
the same trigger that put directions G, E and J there. **The top rung is
unavailable this session** (user check-in, 2026-08-07: fable not
dispatchable), so both **substitute opus** (`recon-opus`), per the playbook's
*nearest available rung at or above the mapped one*. Recorded because it is a
deviation from the four preceding fan-outs' rung, not a re-rating.

**Shared mechanics: identical to the second fan-out's** (§"Second fan-out",
including its three deltas — the reserved-namespace table is now the
2026-08-07 **PEX/TCOL** table in `notes/Pencil-labels.md`; any battery quoted
as a *rate* or as generic-chart-point evidence gates on `repin.star_generic`;
the coordinator lands each return before dispatching the next, with a budget
check between). Serial dispatch does not relax the mechanics: each dispatch
is **read-only w.r.t. every shared file**, **commits NOTHING**, creates only
its own pinned new driver(s) (untracked, for the coordinator to gate and
commit), writes its full mathematics as a draft workbook section
(`fanout-<PEX|TCOL>.md`, session scratchpad) in the workbook's register with
an explicit confidence verdict and a "what would change this" line, and keeps
the return message to a tight verdict. The F11 requirement binds ("forced" /
"exhaustive" / "the only" are their own claim class needing their own
driver), as do `notes/scripts/README.md`'s conventions (exact ℚ, seeded
randomness, degeneracy guards + rank/dimension asserts, import from the
canonical layer — check the *Divergences* table), and F15's over-ceiling
shape for any invocation that cannot finish inside 600 s. A direction that
opens Macaulay2 work reads `notes/scripts/m2/README.md` first and budgets per
`Pencil-strategy.md` §5.3/§5.4 — neither direction here is expected to need
it, both questions being combinatorial.

**Both directions are proof attempts, and the deliverable is the ARGUMENT.**
Each has a measured record already at 100 % over its enumerated pool
(1904/1904 for PEX, 907/907 for TCOL), so *widening the pool is evidence,
not progress*. `Pencil-strategy.md` §2.3's base-rate warning applies to both
verbatim: every prior class-uniform combinatorial-existence claim of this arc
was eventually either proven by a min-max or refuted by a structural flank.
Run the cheap kill first; *"no proof, and here is the precise obstruction"* is
a fine outcome for either.

### Direction PEX — §(K-frame)'s (FR-R1): pattern-existence on the bare-cycle stratum

**The question.** Prove **(FR-R1)** — every bare-cycle site of every `k = 4`
class triple admits a *pattern colouring*, i.e. an admissible colouring of
`G′` meeting (FR-4)'s hypotheses: the six frame edges coloured **3–3** with
pairwise-distinct components per family, plus the two placement-free legality
clauses (all bodies distinct — the `(comp_A, comp_B)` pairs injective — and no
3-member closed hub neighbourhood mono-component in either family) — or refute
it with a structural flank. Proving it closes the §(K-ann) (ANH-14)
chart-to-frame residue on the **whole** bare-cycle stratum *as an argument*,
upgrading (FR-5)'s 1904/1904 measured record to a theorem modulo (FR-4)'s one
named gap.

**Grounding (canonical §(K-frame) Steps FR0–FR4 + §(K-grid) *Step G12*; do
not re-derive).** (FR-1): non-containment in the one named divisor needs
**one witness point + irreducibility of the source**, and on the (ANH-14)
side §(K-ann) (ANH-9)(ii) already owns the irreducibility — so the entire
remaining content is the witness point, and (FR-4) reduces *that* to the
colouring. (FR-3): at a σ-fixed grid configuration evaluation is **O(1)
reading of the colouring** — `det₆ ≠ 0 ⟺` the colours split 3–3 with the
three lines pairwise distinct in each family, on the nose
`det₆ = 128 · Vdm(s₁,s₂,s₃) · Vdm(u₁,u₂,u₃)`. (FR-4): transport is by
**regridding at `G′`**, where `a` has degree 2, alternation puts `(a,b)` and
`(a,c)` in opposite families, and `pt(a) ∈ Π(b) ∩ Π(c) = M` is automatic.
*Step G12*(i): admissible colourings are exactly **one free bit per branch**
(alternation chains = branches, hubs break chains; `closure.alternation_classes`
is the landed form).

**The sketch this direction is commissioned to complete or kill**
(§(K-frame) *What would change this* item (i), the section's own chief
hand-off): alternation around the cycle is nearly free — forced at real
degree-2 bodies, chosen at hubs — so the content is keeping the **three
same-family edges in three distinct components**. *Step G12*'s
one-free-bit-per-branch structure plus **girth 6** look sufficient for a
direct argument. Test that; if it is sufficient, the proof is the
deliverable, and if it is not, name exactly which configuration defeats it.

**Cheap kill first.** A bare-cycle site whose *every* admissible colouring
merges two non-adjacent frame edges in both families' component structures —
refutes (FR-R1). None among the 1904 enumerated sites.

**Cautions.**

- **The legality clause is placement-free by design; do not upgrade it into a
  feasibility criterion.** `notes/Phase39.md` *Blockers* records (verified,
  this file's coordinator read it) that feasibility propagation *as a
  proposition* is **refuted** for any purely combinatorial
  (`≤3`-closedHubNbhd) criterion — the landed
  `not_pencilNondegFeasible_of_triangle_two_hubs`. *Coordinator hypothesis,
  flagged as such (F14):* the two are compatible because (FR-4)'s clause is a
  sufficient condition **checked at a constructed point**, not a propagated
  proposition. A proof of (FR-R1) that generalizes the clause into a criterion
  would collide with that refutation, so **state explicitly which side of that
  line the argument sits on** — and if the coordinator's reading is wrong, say
  so, which is a fully successful outcome.
- **The pool is not the class.** (ANH-14)(b)'s boundedness caveat transports
  unchanged: the site pool is `outer.sweep_shapes` (`|V°| ≤ 5` families plus
  the named habitats), so "every class shape" is **not** established by the
  1904 record and a proof must not lean on it.
- (FR-4)'s **named gap** — §(K-grid) (GR-5) restated at `G′` — stays named;
  closing it is a bonus, not this direction's deliverable. Take it if the
  argument makes it cheap, and say so.
- No σ-fixed witness is read as generic (§(K-clos) (AC-9) — at grid points
  that anti-correlation is *forced*: a σ-fixed body of degree ≥ 3 has two
  same-colour edges, hence one coincident hinge line). Do not re-derive
  §(K-frame)'s (FR-1)–(FR-7) or §(K-ann)'s settled batch
  ((ANH-1)–(ANH-6), (SD-6)); the §(K-ann) and §(K-out) pools are pinned and
  **disjoint**, never aggregated.

**Driver** `notes/scripts/w4/patexist.py` (imports `framedom.py` /
`closure.py` / `annih.py` / `shrink.py` / `outer.py` read-only). No M2 leaf
expected — the question is combinatorial; if one is opened the reserved name
is `notes/scripts/m2/patexist.m2`. **Labels** (FR-8)+, Steps FR7+ (reservation
table in `notes/Pencil-labels.md`); if the argument needs its own section the
reserved name is **§(K-pat)**, tag `PAT-`. Cross-references into
§(K-ann)/§(K-grid) use the qualified form (L3); moving any gap-map cell is the
coordinator's action at landing, never the draft's.

### Direction TCOL — §(K-grid)'s (GR-15): colouring-existence on the tight stratum

**The question.** Discharge **(GR-15)** — every tight class shape admits an
admissible colouring with generic `dim Z₊ = dim Z₋ = 0` in **both** blocks
(*Step G17*'s boxed statement; measured 907/907, and by (GR-7) remark (i)
each exact hit is already a **per-shape proof**, so the gap is uniformity,
not rigor) — by either route *Step G18* item 3 names: **(a)** prove
**(GR-4′)** (`dim Z = a + max(0, max_P g(P))` at generic parameters) and give
a colouring-existence argument for *"some admissible colouring has
`a = 0 ∧ max g ≤ 0` in both blocks"*; or **(b)** develop **(GR-11)**'s ε-adic
hierarchy on the **18 separators** into a certificate covering exactly where
the tree-triple fails. Or refute (GR-15) with a structural flank.
Discharging (GR-15), with (GR-1)/§(K-clos) (AC-4), (GR-5) and (AC-7),
discharges `hK` **on the tight stratum**, over every infinite
characteristic-0 field.

**Grounding (canonical §(K-grid) Steps G11–G18; do not re-derive).**
(GR-13): the grouped packing is **NP-complete at exact balance**
(triple-existence ⟺ 3-colourability of `Γ`), so no counting condition can
characterize the *triple* unless NP = coNP — that is what re-aimed the
residual from (GR-10) to (GR-15), and it does **not** touch (GR-4′), which
is counting-shaped and which the 18 separators satisfy **exactly**
(`a = 0`, `max g = 0`, `dim Z = 0`). *Step G16*: those separators are **on
the habitat** — 4 blocks of `V6m10(3¹⁰)`, 14 of `V6m11(3⁸,4,4,4)` — generic
`dim Z = 0` proven at exact rational points yet no tree-triple; the pinned
exemplar's non-existence is exhausted over all `3¹¹` class colourings,
DFS-free, with a greedy unsatisfiable core of 13 circuit class-sets printed
as the conflict structure. They are the **first natural test set** for a
(GR-11)-style hierarchical certificate. (GR-4′) status: true-modulo-named-gap,
proven at **≤ 3 classes** and at **singleton classes**, the conic confinement
dissolved (any three distinct moment-curve points form a basis of `K³`) — the
live gap is **only the class structure**. *Step G12*: the finite-object
structure — one free bit per branch; the both-classes-forests constraint sees
only the hub-hub subgraph of `G°`; balance is a signed subset-sum over
odd-length branches; per hub multigraph `G°` a finite CSP parametrized by the
length profile, so any uniform argument must be uniform **over `G°`**, not
over subdivisions (§(K-ind) (I4)).

**Cheap kill first.** A tight class shape whose *every* admissible colouring
leaves, in some block, generic `dim Z > 0` — refutes (GR-15), and (GR-10)
with it. None in 907 shapes under exhaustive enumeration (16600/17772
filter-passing colourings certify; scarcest shape 12/16).

**Cautions.**

- **Do not re-attack the (GR-10) min-max.** (GR-13) closed it *as posed* and
  *Step G18* item 1 records why; the productive question is
  colouring-existence, not characterization. (GR-10) itself stays open as the
  strictly stronger statement — proving it would also do, but it is not the
  target.
- (GR-14)'s rainbow-Δ certificate has **measured-nil** habitat applicability
  (0/400 first-certified census blocks, 0/18 separators) — recorded so it is
  not re-hunted.
- Nothing here re-opens the habitat-level (AC-6) refutation: `C11` is
  permanent (tight shapes have hubs and are never bare cycles). Do not
  re-derive (GR-1)–(GR-9), (GR-4′)'s proven cases, or (GR-12)–(GR-15).
- No σ-fixed witness is read as generic (§(K-clos) (AC-9)); a rank miss of
  the literal `closure.build_fixed_config` construction at *one* parameter
  point is not a miss of the recipe (*Step G4* item 1 — component-index
  labels are not generic; retry at seeded random rational parameters before
  calling anything structural).
- *Coordinator hypothesis, flagged as such (F14):* direction PEX's technique
  may transfer here, both residues being colouring-existence over the same
  *Step G12* branch-bit structure. **Read PEX's landed §(K-frame) material
  first** and say explicitly whether it transfers. It may well not —
  (FR-R1) carries no spline/rank side at all, which is precisely why it was
  ordered first.

**Driver** `notes/scripts/w4/gridcol.py` (imports `packmm.py` / `gridwit.py`
/ `grid.py` / `closure.py` read-only); optional M2 leaf
`notes/scripts/m2/gridcol.m2`. **Labels** (GR-16)+, Steps G19+ (reservation
table in `notes/Pencil-labels.md`); if the (GR-11) hierarchy development needs
its own section, the reserved name is **§(K-pack)**, tag `PK-` — re-reserved
from the pool for the **third** time, having been returned unopened by
directions G and E.

### Landing (coordinator, per returned direction)

The first fan-out's landing checklist applies verbatim, plus:

1. Move the direction's reservation row into the registry in the landing
   commit (never delete it).
2. **Add the new driver's rows to `notes/scripts/README.md` §3's invocation
   table in the landing commit.** This is part of "commit the new script",
   not an optional extra — four consecutive landings skipped it (the third
   fan-out's three drivers plus `packmm.py`), caught only at direction J's
   landing; reproducibility survived only because the workbook *Verification*
   blocks carry the invocations.
3. Land each return and re-check session budget **before dispatching the
   next direction** (serial order PEX → TCOL).
4. Fold PEX's landed result into TCOL's prompt **only if something actually
   landed** — the transfer hypothesis above is a hypothesis, and a PEX
   refutation is just as much an input to TCOL as a PEX proof.

## Sixth direction — CFLANK (single direction, prepared 2026-08-07)

**Status: LANDED 2026-08-07.** §(K-grid) continuation, Steps G24–G28,
(GR-21)–(GR-26), driver `w4/cflank.py` — an exact **excess law** (GR-21)
pins TCOL's binding-circuit-rich stratum to `D = 0` (cubic hub multigraphs,
a constant length budget), **five sparsity caps** (GR-22) bound how many
binding circuits the habitat allows there, a **flip injection** (GR-23) and
a **private-branch repair theorem** (GR-24) turn NC1-satisfiability from
*measured* into *proven* wherever they apply, a **cut criterion** (GR-25)
reaches 18-hub/51-vertex targets, and an **exhaustive 40 742-shape hunt**
(GR-26) over the whole `D = 0` stratum at `n_hub ∈ {2,4,6}` finds not one
NC1-unsatisfiable shape. **No flank; TCOL's item (v) is CLOSED AS A
ROUTE.** (GR-15) stays OPEN, unchanged in status; class uniformity of `hK`
untouched, no gap-map status moves. Not a fan-out — a single direction.
The fifth fan-out (PEX/TCOL) is COMPLETE, and per the 2026-08-07 delegation
adjudication ("keep going on my own judgment" — `notes/Phase39.md` *Current
state*), next-direction **selection** is now the coordinator's call, not a
user pick from a candidate list; every standing constraint from the fifth
fan-out is otherwise unchanged. The coordinator selected this direction from
TCOL's own *What would change this* item (v) — the one thing the fifth
fan-out named as never attempted.

**Direction code CFLANK** (circuit-profile flank), minted under clause
**(L5)** as a multi-letter topic-tagged code. Verified **0-hit as a raw
substring**, case-insensitively, across `*.md`/`*.tex`/`*.lean`/`*.py`/`*.m2`
— as are the reserved section name **§(K-prof)** and tag **`PF-`**. Reserved
in `notes/Pencil-labels.md`.

### The question

Refute **(GR-15)** with a *targeted structural flank* — a tight class shape
whose **every** admissible colouring leaves generic `dim Z > 0` in some
block — or fail to, and name the precise obstruction. This is TCOL's *What
would change this* item **(v)**, the one thing the fifth fan-out named as
never attempted: "`--wide` sampled both and found nothing; a targeted
adversarial construction has not been attempted."

**Why now, and why it is newly cheap.** After **(GR-16)** the search is a
search over `(G°, ℓ, bits)` and is cheap per shape; **(GR-17)(d)** isolated
the only two binding circuit length-profiles. The two named places to look,
both from TCOL: (1) shapes whose `G°` is rich in **`(2,2,3)` and `(2,2,2,2)`
circuits sharing branches**, so the `h_≠ ≥ 2` requirements **conflict** — a
bit-assignment conflict is exactly the mechanism a class-uniformity
refutation would use; (2) hub multigraphs with **many parallel branch
pairs**. `--wide` sampled both families (7653/7653, no miss) — but **sampled
≠ constructed**. The deliverable is an adversarial **construction**, not a
wider sweep: widening a pool is evidence, not progress (standing rule).

**Both outcomes are fully successful, and the spec says so explicitly.** A
**flank** refutes (GR-15) and **(GR-10) with it**, re-routing the phase —
that is the headline. **No flank, with the obstruction named** — an argument
that the conflicting-`h_≠` mechanism cannot be made global — is a **positive
step toward (GR-15)**, because it closes the one family where a refutation
could live. `Pencil-strategy.md` §2.3's base-rate warning applies verbatim:
every prior class-uniform combinatorial-existence claim of this arc was
eventually either proven by a min-max or refuted by a structural flank.

**Grounding (canonical §(K-grid) Steps G19–G23 + *Step G12*; do not
re-derive).** (GR-16) the branch reduction — `dim Z` is a square `3c × 3c`
system read off `(G°, ℓ, bits)` alone; (GR-17) the run law
`2·runs(γ) = (L−r) + h_≠(γ)`, automatic whenever `Σ_{β∈γ}(ℓ_β−1) ≥ 5`,
binding only at profiles `(2,2,3)` and `(2,2,2,2)` when `Λ = ∅`; (GR-18) the
packing is never the obstruction, only the 3+3 grouping; (GR-19) the
collapse hierarchy, `κ ≤ 4` measured on the census pool; *Step G12*(i) one
free bit per branch.

**Cautions (all load-bearing).**

- **The shape must be IN the habitat.** A "flank" failing `hcard`,
  `hnoRigid`, or carrying a two-hub triangle refutes nothing `hK` needs —
  the θ(1,2,9) precedent under §(K-clos) (AC-6), where a miss was *correct
  behaviour* because the shape was out of habitat. Certify habitat
  membership before reporting any hit, and state which certificate.
- **`Λ ≠ ∅` is where (GR-17)(d) is only measured, not proven** (TCOL's item
  (iv)); a flank found there is *also* a witness for that open clause — say
  which side any hit sits on.
- A per-shape exact hit is already a per-shape proof ((GR-7) remark (i)), so
  a claimed flank needs the miss **exhaustive over bits**, not sampled.
  "Every admissible colouring" is an F11 claim class of its own and needs
  its own driver.
- No σ-fixed witness is read as generic (§(K-clos) (AC-9)); a rank miss of a
  literal construction at one parameter point is not a miss of the recipe
  (*Step G4* item 1) — retry at seeded random rational parameters before
  calling anything structural.
- Do not re-derive (GR-1)–(GR-19); do not re-attack the (GR-10) min-max
  ((GR-13) closed it as posed); do not re-run the (GR-14) rainbow-Δ hunt
  (habitat applicability measured nil, 0/400 + 0/18). All of
  `notes/Phase39.md` *Hand-off*'s "Deliberate non-goals" continue to bind.

**Driver** `notes/scripts/w4/cflank.py` (imports `gridcol.py` / `packmm.py`
/ `grid.py` / `closure.py` read-only). **Labels** (GR-21)+, Steps G24+;
section name if the argument needs one: **§(K-prof)**, tag `PF-`. Optional
M2 leaf `notes/scripts/m2/cflank.m2` (not expected — the question is
combinatorial).

**Rung.** Mapped **top rung** (a crux proof/refutation attempt whose verdict
re-routes the phase — the same trigger that put G, E, J, PEX and TCOL
there); fable unavailable this session, so **substitute opus**
(`recon-opus`), per the playbook's *nearest available rung at or above the
mapped one*.

**Mechanics: identical to the fifth fan-out's.** Read-only w.r.t. every
shared file; commits NOTHING; creates only its own pinned new driver
(untracked, for the coordinator to gate and commit); writes its full
mathematics as a draft workbook section `fanout-CFLANK.md` in the session
scratchpad, in the workbook's register, with an explicit confidence verdict
and a "what would change this" line; keeps the return message to a tight
verdict. F11 binds; `notes/scripts/README.md`'s conventions bind (exact ℚ,
seeded randomness, degeneracy guards + rank/dimension asserts, import from
the canonical layer — check the *Divergences* table); F15's over-ceiling
shape applies to any invocation that cannot finish inside 600 s.

### Landing (coordinator)

The fifth fan-out's landing checklist applies verbatim (which is the first
fan-out's plus its four additions) — including moving the reservation row
into the registry and adding the driver's rows to
`notes/scripts/README.md` §3's invocation table in the landing commit.

## Seventh direction — GCAP (single direction, prepared 2026-08-12)

**Status: LANDED 2026-08-13.** A **single direction**, not a fan-out; its
selection was made under the 2026-08-12 refinement of the standing
delegation (`notes/Phase39.md` *Current state*, verbatim there): the user
delegated the seventh-direction call to a **top-rung fable recon**, whose
verdict the coordinator verified and accepted; this section transcribed
that verdict's dispatch-grade spec. §(K-grid) continuation, Steps
G29–G33: **(GR-27)** proven — block additivity + exact computability of
the (GR-8) family, retiring the `structured_beta` proxy; **(GR-28)**
proven / true-modulo-named-gap — a closed defect formula and `a = 0` at
`Λ = ∅`, the `g ≤ 1` cap proven at `k = 2` and measured with 0 exceptions
over 549 172 blocks at all `k`, the `k ≥ 3` case the named gap; the
certificate-3 target (the general-`P` instance of (GR-20)'s third
certificate) **proven per swept shape** at every `D = 0` shape checked
(4920 + 884 + 972, no MISS), with a ≤2-flip repair and the odd-pair flip
closing CFLANK item (v) at `Λ ≠ ∅` too; the falsification control (323
exhaustive constructions) plus the F13 witness `θ(2,4,4)` found no flank.
**(GR-15) stays OPEN — the uniform (all-`n_hub`) statement is not
proven; no gap-map status moves.** Driver `w4/gcap.py`'s five modes
coordinator-re-run, byte-identical under `PYTHONHASHSEED` 0 vs 999
except each mode's own printed wall-clock annotation. No standing
constraint changes.

**Correction 1's honest fate.** This section's own correction 1 below —
"a `Λ = ∅` scoping would miss the live obstruction data" — rested on
*Step G23*'s recorded premise that the probe's 16 hits were all on
`Λ ≠ ∅` shapes. GCAP's own `--probe` **voids that premise**: the full
907-shape census has 955 such hits, 675 of them on `Λ = ∅` shapes (a
sample-bias artifact of the probe's own 45-shape prefix, corrected in
place at *Step G23*, canonical home *Step G30*). The correction was
nonetheless **harmless in effect** — it only pushed the direction to
reach `Λ ≠ ∅` in addition to `Λ = ∅`, which `--cap`/`--flip` did anyway
(*Step G32*'s three-pool table covers both, and the odd-pair flip
explicitly closes item (v) at `Λ ≠ ∅`). **Corrections 2 and 3 both
held**: certificate 3 is stated throughout **modulo (GR-4′)**, never
"outright" (correction 2), and the deliverable ran cap-proof-first with
the adversarial hunt as the falsification control, not the headline
(correction 3).

**Direction code GCAP** (g-cap: cap the structured (GR-8) family's
`g`), minted under clause **(L5)**. Verified **0-hit as a raw
substring**, case-insensitively, across
`*.md`/`*.tex`/`*.lean`/`*.py`/`*.m2` in the prep commit — as are the
driver name `gcap`, the reserved section name **§(K-gcap)** and tag
**`GC-`**. Reserved in `notes/Pencil-labels.md`.

### The question

For tight class shapes at `D = 0` (reaching toward `Λ ≠ ∅`): does every
shape admit an admissible colouring (balanced, both `Γ`-classes
forests, no monochromatic hub) with `a = 0` and structured-(GR-8)
`max_P g(P) ≤ 0` **in both blocks** — the general-`P` instance of
§(K-grid) (GR-20)'s certificate 3, whose `P = circuit` instance CFLANK
already solved ((GR-17) + (GR-22)–(GR-24))?

**Why this target survives adjudication rather than being inherited.**
CFLANK itself recommended this successor, and a successor proposed by a
direction that just failed to find a flank is exactly the claim that
needed independent adjudication — which it got. It stands on three
independent grounds: (a) it is the **only** route in the (GR-15) cell
backed by a positively witnessed obstruction datum — *Step G23*'s
scoping probe found 16 of 572 balanced, no-mono-hub, NC1-satisfying
blocks with generic `dim Z > 0`, each `a = 0` with structured (GR-8)
maximum 1, so the non-circuit members of (GR-8) provably bite and NC1
alone is provably not the colouring-existence target; (b) CFLANK did
not fail at this question — it **proved the circuit instance**, so the
successor is the next quantifier of the same induction, not a fresh
bet; (c) the (GR-15) residual is **not** of the
rank-lower-bound-on-a-contraction shape `notes/Pencil-strategy.md`
§2.3's recorded prediction says to stop surveying — it is the
"genuinely informative outcome" that prediction says deserves the
attention a surprise deserves, while the alternative candidates
(§(K-out) (OC-8), §(K-ann) (ANH-R1)) terminate at exactly the wall
shape.

**Three corrections to CFLANK's recommendation as written (adjudicated
2026-08-12; each load-bearing, each with its grounding).**

1. **A `Λ = ∅` scoping would miss the live obstruction data.** The
   scoping probe's 16 hits were **all on `Λ ≠ ∅` shapes** (§(K-grid)
   *Step G23*) — exactly the stratum where (GR-17)(d) is only measured
   and where (GR-23)/(GR-24) are **proven only at `Λ = ∅`**. The
   direction must carry CFLANK's *What would change this* item (v)
   (the balance-preserving odd-pair flip) toward `Λ ≠ ∅`.
2. **"Close (GR-15) at `D = 0` outright" overstates.** (GR-20)'s
   certificate 3 implies (GR-15) **modulo (GR-4′)**, which stays open
   (§(K-grid) *Step G23*, certificate 3); the closure chain below
   carries the rider explicitly, and so must the return.
3. **Cap-proof-first, flank-hunt-second** — inverting CFLANK's own
   framing. After 907 (census) + 7653 (TCOL `--wide`) + 40 742
   (CFLANK, exhaustive) verifications with zero shape-level misses,
   the prior is strongly on (GR-15) TRUE; CFLANK ran flank-first and
   spent its budget confirming absence. The deliverable priority is
   the cap/repair theorem; the adversarial hunt is the falsification
   control, not the headline.

**Step 0 — MANDATORY load-bearing pin, before any derivation.** The
adjudicating recon did **not** read the definitions this spec depends
on; the dispatch must. Pin from §(K-grid) Steps G8–G13: the exact
definition of `g(P)` and of "structured", and (GR-4′)'s proven-case
boundary (≤ 3 classes, singleton classes) against the class counts
that actually arise in admissible colourings' blocks. Then state the
closure chain explicitly in the draft, with **both riders**: cap ⟹
(GR-15) at `D = 0` **modulo (GR-4′)** ⟹ (with (GR-1)/§(K-clos)
(AC-4), (GR-5), (AC-7)) `hK` on the tight `D = 0` stratum over every
infinite characteristic-0 field; `D > 0` stays **unswept** (CFLANK
item (iii)). Never "outright".

### Decisive experiments, priority order

1. **`--probe`** — re-establish *Step G23*'s scoping figure as
   **committed evidence** (the original is recorded "measured, script
   not retained"): over the census + the 4920-shape `D = 0` pool,
   enumerate admissible, NC1-satisfying, `a = 0` blocks with generic
   `dim Z > 0`; extract the certifying `P` per block; classify (cycle
   rank, length profile, `Λ`-content). Decisive sub-question: is the
   binding non-circuit `P`-family at `D = 0` finite/bounded, the way
   (GR-17)(d) bounded circuits to two profiles?
2. **`--law`** — a (GR-21)-style budget argument: charge each binding
   non-circuit `P` against the constant length budget
   `Σ_β(ℓ_β − 2) = 6` at `D = 0`; target a finite list of binding
   `P`-profiles (the exact analogue of (GR-22)).
3. **`--flip` / `--cap`** — extend the (GR-23) flip injection /
   (GR-24) private-branch repair from binding circuits to the binding
   `P`-profiles found in 2, **including item (v)'s odd-pair flip** so
   the conclusion reaches `Λ ≠ ∅`. Target theorem: some admissible
   colouring has `a = 0 ∧ max_P g(P) ≤ 0` in both blocks at every
   `D = 0` class shape.
4. **`--adv`** — the falsification control: targeted constructions
   maximizing binding-`P` load at the cap's boundary. A claimed flank
   must be exhaustive over the `2^M` bits (F11), **habitat-certified**
   (the θ(1,2,9) precedent — state which certificate), and must say
   which side of the `Λ = ∅` line it sits on.
5. **Bonus, only if cheap:** CFLANK item (ii)'s mixed case, upgrading
   (GR-24) to the unconditional "(NC1) is satisfiable at every
   `D = 0`, `Λ = ∅` class shape".

### Termination — what a MISS looks like

The direction terminates after experiments 1–4 regardless of outcome —
no open-ended widening ("widening a pool is evidence, not progress",
standing rule). A MISS is: the budget law fails to bound the
binding-`P` family (name the unbounded family and why the length
budget does not charge it), **or** the repair fails at a named
configuration with no flank constructible either (record that
configuration, with its (GR-27)+ label, as the sharpest known (GR-15)
obstruction). Either is a genuine deliverable. A **flank** — a
habitat-certified shape where every admissible colouring leaves
`max_P g(P) > 0`, exhaustive over bits — refutes (GR-15) outright and
re-routes the phase, noting honestly that it kills the **grid route**
to `hK`, not `hK` itself (grids are sufficient, not necessary). The
line-level TERMINATION test that fires on GCAP's return is recorded in
`notes/Phase39.md` *Hand-off*.

### Cautions (binding)

- Do not re-derive (GR-1)–(GR-26); do not re-attack the (GR-10)
  min-max as a *characterization* ((GR-13): NP-complete at balance —
  the cap is an existence bound, which is why it is not barred); all
  of `notes/Phase39.md` *Hand-off*'s "Deliberate non-goals" bind.
- The (K-res)/(GR-15) quantification question — whether (GR-15) as
  quantified ("every tight class shape") also covers the `W19`-type
  (K-res) sibling habitat — is **explicitly NOT this direction's
  scope**; it is a coordinator hand-off note (`notes/Phase39.md`
  *Hand-off*).
- No σ-fixed witness is read as generic (§(K-clos) (AC-9)); a rank
  miss of a literal construction at one parameter point is not a miss
  of the recipe (*Step G4* item 1) — retry at seeded random rational
  parameters before calling anything structural.

**Driver** `notes/scripts/w4/gcap.py` (imports `cflank.py` /
`gridcol.py` / `packmm.py` / `grid.py` read-only); suggested modes
`--probe`/`--law`/`--cap`/`--flip`/`--adv`/`--validate`. **Labels**
(GR-27)+, Steps G29+; section name if the argument outgrows §(K-grid):
**§(K-gcap)**, tag `GC-` (do **not** reuse §(K-prof)/`PF-` — its
"profile" semantics are circuit-specific). No M2 leaf expected (the
question is combinatorial); `m2/gcap.m2` if a function-field identity
appears.

**Rung.** Mapped **top rung** (a crux proof/refutation attempt whose
verdict re-routes the phase — the same trigger that put G, E, J, PEX,
TCOL and CFLANK there); per the 2026-08-12 check-in all four rungs are
dispatchable, so **fable** (opus substitutes only if the weekly scoped
limit runs out).

**Mechanics: identical to the sixth direction's.** Read-only w.r.t.
every shared file; commits NOTHING; creates only its own pinned new
driver (untracked, for the coordinator to gate and commit); writes its
full mathematics as a draft workbook section `fanout-GCAP.md` in the
session scratchpad, in the workbook's register, with an explicit
confidence verdict and a "what would change this" line; keeps the
return message to a tight verdict. F11 binds;
`notes/scripts/README.md`'s conventions bind (exact ℚ, seeded
randomness, degeneracy guards + rank/dimension asserts, import from
the canonical layer — check the *Divergences* table); F15's
over-ceiling shape applies to any invocation that cannot finish inside
600 s.

### Landing (coordinator)

The fifth fan-out's landing checklist applies verbatim, as it did for
CFLANK — including moving the reservation row into the registry and
adding the driver's rows to `notes/scripts/README.md` §3's invocation
table in the landing commit.

## Eighth direction — GUNIF (single direction, prepared 2026-08-13)

**Status: LANDED 2026-08-13.** A **single direction**, not a fan-out.
Its target was named in `notes/Phase39.md` *Hand-off*: the recorded
TERMINATION test for the (GR-15)/grid line was checked on GCAP's return
and did **not** fire (a cap was proven and new mechanisms were named),
so the next step was an eighth direction, not a user escalation —
selected under the standing 2026-08-07 delegation ("keep going on my
own judgment") as refined 2026-08-12, the same standing delegation
CFLANK and GCAP were selected under; no fresh adjudication was sought
or needed. §(K-grid) continuation, Steps G34–G37: **(GR-29)** proven —
the finite dart-menu case analysis and a budget ledger killing every
`n_hub ≤ 6` parameter tuple by a named clause; **(GR-30)** proven —
target (a), (GR-28)(iv) at `k ≥ 3`, is **REFUTED** by four constructed
habitat witnesses (`n_hub = 8, 10, 12, 16`, `k = 3, 3, 4, 5`, exact
`g(S) = 2, 2, 2, 3`), with the boundary exact ((GR-29)'s ledger kills
every tuple below `n_hub = 8`); **(GR-31)** measured — per-shape
(GR-15) HOLDS at all four witnesses, and the flip distance to a
fully-good colouring (2/2/2/3) shows *Step G32*'s measured ≤ 2-flip
repair law is sweep-local, breaking at `n_hub = 16`. Target (b), the
(GR-24)-analogue repair theorem, is **unprovable as posed**: its
premise is false from `n_hub = 8` on and its measured conclusion also
fails independently at the same witness. **The salvage: the `g ≤ 1` cap
is a THEOREM exactly on the swept `n_hub ≤ 6` stratum** — the 549
172-block evidence was exhaustive over precisely the stratum that
provably cannot contain a counter-configuration. **(GR-15) itself stays
OPEN, unchanged in status** — the refutation kills the certificate-3
*uniformity route*, not the statement; no gap-map status moves beyond
recording (GR-28)(iv)'s own standing. No standing constraint changes;
the coordinator's next step is a **phase-shape decision surfaced to the
user** (`notes/Phase39.md` *Hand-off*), not a ninth direction — the
line's positive-termination path (cap + `Λ ≠ ∅` flip + `D > 0` lift +
(GR-4′) = (GR-15)) is dead as specified, since the cap is false in
general.

**Direction code GUNIF** (the deliverable is the **uniform**
statement), minted under clause **(L5)**. Verified **0-hit as a raw
substring**, case-insensitively, across
`*.md`/`*.tex`/`*.lean`/`*.py`/`*.m2` in this prep commit — as is the
driver basename `gunif`, and — checked but **not** used —
`GDART`/`gdart` and `K-unif`/`GU-` (see *Labels* below).

### The two targets

Both from §(K-grid) *Step G33*'s *What would change this* items (i)–(ii)
(§(K-grid) Steps G29–G33, `notes/Pencil-informal.md`):

**(a)** Close **(GR-28)(iv)'s `k ≥ 3` case** — the finite dart-menu case
analysis whose standing evidence is exhaustive at **549 172** NC1-passing
blocks of the whole `Λ = ∅` `D = 0` stratum with **0 exceptions**, but
which *Step G31* explicitly leaves open (the `k = 2` argument does not
generalize — see *Step 0* below, the crux of the whole direction).

**(b)** A **repair theorem** — the (GR-24) analogue for the g-family,
turning the *measured* ≤ 2-flip repair locality of *Step G32* into a
theorem. The measured figures: **23 950/23 950** binding NC1-passing
colourings of the `Λ = ∅` stratum reach a fully-good colouring by
balance-preserving flips of at most two even branches — **22 654** at
distance 1, **1 296** at distance 2, **0** unrepaired.

Together, (a) + (b) + (GR-23)/(GR-24) prove the certificate-3 target
(*Step G32*'s target statement) **uniformly** on the `Λ = ∅`, `D = 0`
stratum — i.e. **(GR-15) there, modulo (GR-4′)** (never "outright" — see
*Riders* below).

**This is the arc's first PROOF direction, not a numerics hunt, and
three consequences follow that invert the previous seven directions'
working assumptions — carry all three into the dispatch.**

**(i) The deliverable is a proof at the workbook's proven-informally
bar, not a sweep.** A wider `--law`/`--flip`-style sweep over more
shapes, more `k`, or more blocks is explicitly **not progress** here:
both pools are already exhaustive over the finite objects each target
quantifies (549 172 blocks, 0 exceptions; 23 950 colourings, 0
unrepaired). The deliverable is the *argument* that the finite dart-menu
case list is complete (a) and the argument that the repair hypothesis
holds universally (b).

**(ii) The driver's role inverts.** Every prior direction's driver
*produced* the headline figure (a census, a cap, a hunt). GUNIF's driver
instead **verifies the case menu's exhaustiveness** — enumerating every
dart menu *Step 0* below identifies, discharging each one, and checking
machine-checked agreement against the existing 549 172-block pool — and
**checks the repair theorem's hypothesis** at every configuration the
argument's case split produces. Concretely: **F11 becomes "which mode
certifies that this case list is complete?"**, not "which mode produces
the figure?" — name that mode explicitly for each of (a) and (b).

**(iii) The honest-MISS shape changes accordingly.** A MISS here is not
"the pool has a counterexample" (the arc's usual shape) — it is either
*"the case analysis has an irreducible case, named, with why the
ear-law / budget handle fails to charge it"* or *"the repair fails at a
named configuration"*. Either is a full deliverable on the same footing
as a proof: name the case or the configuration precisely, with its
(GR-29)+/Step G34+ label, as the sharpest known obstruction — do not
report an inconclusive "the case analysis is hard" without naming the
specific sticking case.

### Step 0 — mandatory load-bearing pin, before any derivation

Pin the following from the newly landed Steps G29–G33 before writing a
single line of argument (the GCAP dispatch's own Step 0 discipline: if a
prior dispatch has not read the definitions a spec depends on, the next
one must).

**The exact statement of (GR-28)(iv).** *"NC1 ⟹ `max_P g(P) ≤ 1` at all
`k` (`D = 0`, `Λ = ∅`)"* — currently **true-modulo-named-gap**: the `k = 2`
case (theta shapes) is proven (*Step G31* (iii)); the `k ≥ 3` case is
measured exhaustively (549 172 blocks, 0 exceptions) but not argued.

**What the `k = 2` proof does that `k ≥ 3` cannot reuse — name this
explicitly, it is the crux of the whole direction.** *Step G31*'s proof
of (iii): a **cost-0 path** has every branch length-1-in-`A` and every
interior hub `AA`; two cost-0 paths between the same core-pair form a
circuit whose own defect is `≤ 2` (cost `0 + 0` plus at most 2 non-`AA`
corner indicators) — **already an NC1 violation by (i)**, because at
`k = 2` the circuit *is* the whole theta, so a `defect(S) ≤ 1` hypothesis
forcing both of its two paths to cost 0 is a *direct* contradiction with
the standing NC1 hypothesis on the very same object. **At `k ≥ 3` this
collapses**: forcing `defect(S) ≤ 1` only forces **at least
`3(k−1) − 1` of the `k` core paths** to cost 0 (not all of them), and
`3(k−1) − 1 > 2(k−1) − 1` forces **a circuit of cost-0 paths inside the
core** of length `t`, but that circuit need not be the whole `S`
(`2 ≤ t < k`, or the whole core). A `t = 2` sub-circuit is dead by the
`k = 2` argument; but a `t ≥ 3` sub-circuit's defect is its non-`AA`
**corner** count, and corners are **degree-3-in-`S` hubs, which
contribute nothing to `defect_A(S)`** ((GR-28)(i)'s formula) — so NC1's
own `defect ≥ 3` requirement on that *sub*-circuit does **not** propagate
into a contradiction with `defect(S) ≤ 1` the way it did at `k = 2`,
where the sub-circuit and the whole object coincided. Closing `k ≥ 3`
needs a **finite dart-menu case analysis** at every `t ≥ 3` cost-0-path
sub-circuit with `≥ 3` non-`AA` corners under the mono-hub ban — *Step
G31* records that "every hand-attempt to realize `defect ≤ 1` died on
it, but the... case analysis is **not closed**."

**The ear-law handle (*Step G31*) and the named successor mechanisms
(*Step G33*).** For an open ear `E` on a sub-multigraph `P`:
`g(P ∪ E) = g(P) + 3 − #{X : X breaks E or separates its feet in P∖X}` —
so `max g ≤ 0` propagates whenever every ear carries three "cutting"
classes, with NC1 as the base case. *Step G33* names two successor
mechanisms explicitly as the residual's raw material: (1) the **uniform
existence gap** argument — the same constant-budget (GR-21) mechanism
that killed the NC1 flank and the g-flank in the falsification control,
stated as a theorem rather than a control; (2) the dart-menu
localization above (a cost-0 core circuit with `≥ 3` non-`AA` corners,
every core node mono-ban-fed by a single length-2 path) as the precise
site any `k ≥ 3` counter-configuration would have to occupy.

**(GR-24)'s proof shape — the template the repair theorem should
follow.** *Step G27*'s (GR-24): given a **privacy hypothesis** (every
binding circuit owns an even branch lying in no other binding circuit),
take any admissible colouring and flip the private branch of every
violated circuit **simultaneously**; each flip is (GR-23)'s singleton
flip, so each repairs its own circuit and — by privacy — disturbs no
other binding circuit's count; the no-monochromatic-hub property
survives because the two darts at a third branch of the same hub still
differ after the flip. The hypothesis's own **universality** is then
argued by a **local-configuration case analysis bounded by the excess
budget**: (GR-24)'s hypothesis can only fail at a local configuration
that a direct computation shows forces a specific dense graph
(`G° = Q₃` with all-length-2 branches, or an over-dense 6-set), which
then violates the (GR-21)/(GR-25) length budget — the failure mode is
itself finite and enumerable, and the budget rules it out. The
g-family repair theorem should follow exactly this two-part shape: (1) a
simultaneous-flip argument (using whichever move *Step G32*'s measured
≤ 2-flip data identifies — a single even-branch flip, two independent
even-branch flips, or the odd-pair flip) repairing independently-violated
configurations without disturbing others under a privacy-style
hypothesis; (2) a local-configuration case analysis, bounded by
(GR-21)'s constant length budget, showing the hypothesis's failure mode
is finite and does not survive the budget.

### Verification priority order — the driver's inverted role

1. **`--menu`** — enumerate and classify every `t ≥ 3` cost-0-path
   sub-circuit dart menu under the mono-hub ban; machine-check against
   the 549 172-block pool that no menu realizes `defect ≤ 1`.
2. **`--exh`** — the case-menu exhaustiveness certificate itself: the
   mode that answers F11's "which mode certifies the case list is
   complete?" for target (a).
3. **`--repair`** — construct and verify the repair theorem's
   simultaneous-flip argument against *Step G32*'s ≤ 2-flip data, for
   target (b); the mode that answers F11's certification question there.
4. **`--adv`** — a falsification control on both the case analysis and
   the repair hypothesis, in *Step G33*'s / CFLANK's idiom: targeted
   constructions at the cap's / repair's own worst case.
5. **`--validate`** — all modes, budgeted against the 600 s foreground
   ceiling (F15); split into separate invocations if the combination
   would exceed it, per every prior direction's `--validate` note.

The direction sets the final mode list; the above is a suggestion, not a
pin.

### Riders — carried explicitly, required in the return

- The result is at **`Λ = ∅`**, **`D = 0`**, and **modulo (GR-4′)**.
- The **`Λ ≠ ∅` closed-form analogue** (the (GR-28) analogue with
  `Γ`-merged classes, *Step G33*'s item (iii)) stays **unswept**.
- The **`D > 0` lift** (*Step G33*'s item 3, CFLANK item (iii)) stays
  **unswept**.
- **Never write that this closes (GR-15).** At best it closes (GR-15)
  on the `Λ = ∅`, `D = 0` stratum, modulo (GR-4′) — full (GR-15)
  quantifies over every tight class shape, and `Λ ≠ ∅` / `D > 0` remain.

### Cautions (binding)

- Do not re-derive (GR-1)–(GR-28); do not re-attack the (GR-10) min-max
  as a *characterization* ((GR-13): NP-complete at balance); all of
  `notes/Phase39.md` *Hand-off*'s "Deliberate non-goals" bind.
- The (K-res)/(GR-15) quantification question (whether (GR-15) as
  quantified also covers the `W19`-type (K-res) sibling habitat) is
  **explicitly NOT this direction's scope**; it is a coordinator
  hand-off note (`notes/Phase39.md` *Hand-off*).
- No σ-fixed witness is read as generic (§(K-clos) (AC-9)); a rank miss
  of a literal construction at one parameter point is not a miss of the
  recipe (*Step G4* item 1) — retry at seeded random rational parameters
  before calling anything structural.
- "Widening a pool is evidence, not progress" binds at its strongest
  here (consequence (i) above) — a wider sweep with no case-list /
  repair-hypothesis argument attached is not a deliverable.

**Driver** `notes/scripts/w4/gunif.py` (imports `gcap.py` / `cflank.py` /
`gridcol.py` / `grid.py` read-only); suggested modes
`--menu`/`--exh`/`--repair`/`--adv`/`--validate` — the direction sets the
final list. **Labels**: mint under **(GR-29)+** and **Steps G34+**, the
unclaimed tails of §(K-grid)'s live families (the owning section stays
authoritative). **On outgrowth, reuse the already-reserved §(K-gcap) /
`GC-`** rather than minting anything new — GCAP returned that pair
**unopened**, and its g-family-cap semantics are exactly GUNIF's
subject, so reusing it is the correct call under the registry's
anti-proliferation purpose. **Do not mint §(K-unif)/`GU-`** — considered
and deliberately not minted; both verified 0-hit above and recorded here
so a successor does not re-mint them. No M2 leaf expected — both targets
are finite combinatorial statements.

**Rung.** Mapped **top rung** — a crux proof attempt whose verdict
re-routes the line (the same trigger that put G, E, J, PEX, TCOL, CFLANK
and GCAP there); per the 2026-08-12 check-in all four rungs are
dispatchable, so **fable** (opus substitutes only if the weekly scoped
limit runs out — the same standing qualifier as GCAP's).

**Mechanics: identical to the seventh direction's.** Read-only w.r.t.
every **tracked** file; commits **NOTHING**; creates only its own
**untracked** driver at the pinned path above (importing the harness
read-only, left untracked for the coordinator to gate and commit);
writes its full mathematics as a **draft workbook section**
`fanout-GUNIF.md` in the session scratchpad (not the repo), in the
workbook's register, with an explicit confidence verdict
(proven-informally / true-modulo-named-gap / open / refuted) and a "what
would change this" line; keeps the **return message** to a tight
verdict. F11 binds ("forced"/"exhaustive"/"the only" are their own claim
class needing their own driver — doubly so here, since the whole
direction *is* an exhaustiveness claim); F15's over-ceiling shape
applies to any invocation that cannot finish inside 600 s.
`notes/scripts/README.md`'s conventions bind (exact ℚ, seeded
randomness, degeneracy guards + rank/dimension asserts, import from the
canonical layer — check the *Divergences* table).

### Landing (coordinator)

The fifth fan-out's landing checklist applies verbatim, as it did for
CFLANK and GCAP — including moving the reservation row into the registry
and adding the driver's rows to `notes/scripts/README.md` §3's
invocation table in the landing commit.
