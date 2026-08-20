# PENCIL kernel-(K) research fan-out — dispatch specs

**Status: EIGHT fan-outs and nine single directions dispatched; 33 of 37 directions
LANDED.** The seventh fan-out (YLOC / BALB / AGLU / ZNEQ / CIRR, §"Seventh fan-out") is
**COMPLETE** — all five directions landed 2026-08-19. The **EIGHTH fan-out** (GTMPL / GFLOW /
GCOLL / OSCHU / SIGZ, §"Eighth fan-out") was prepped and dispatched 2026-08-19: **GTMPL has
LANDED** — an exact `n_hub` boundary for ledger attack (c)'s AA-glue case — and **the other
four are in flight**; each direction's own Status line is authoritative for its state.
Ordinals run 1–29 (the eighth fan-out claims 25–29) and were assigned at dispatch, so
landing order differs from ordinal order.

**Ordinals 1–19 are archived** (2026-08-19, `notes/Pencil-structure.md` slice 2) —
their dispatch specs and landing write-ups moved verbatim to
`notes/Pencil-fanout-archive.md`. This file keeps the adjudication, the *Shared
mechanics*, the *Landing checklist*, and the seventh fan-out (ordinals 20–24) as
the worked exemplar a future wave copies from.

**What this file is:** dispatch scoping only — the specs, bars, riders, tier splits and
label reservations a direction is dispatched against, plus the per-direction landing
write-ups. It remains the **template for any future fan-out or single direction**. The
mathematics lives in `notes/Pencil-informal.md` (the (K) workbook — start from its *State
of (K)* gap map, which is authoritative for every status word). Label reservations and the
minting rule live in `notes/Pencil-labels.md`.

**Selection provenance is NOT duplicated here.** Which user adjudication or delegation
picked each direction is canonical in `notes/Phase39.md` *Current state*, as dated bullets
quoting the user verbatim, and in each direction's own section below. Do not restate it in
this header — reproducing it is what grew this header to 2 139 words of changelog across
thirteen directions, stale by two whole fan-outs, and still describing the file as scoping
"three independent research directions" long after there were twenty-four.

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
> tree**, with **zero collisions**. The general rule this exercises (serial
> coordinator landing; worktrees deliberately not used, and why) is promoted to
> **`RESEARCH-ARC.md`** §2 — read there, not here.

**And the F11 requirement** applies (dispatch-log): *each headline claim needs
a driver that tests that sentence*, with "forced"/"exhaustive"/"the only"
their own claim class. General statement and rationale: **`RESEARCH-ARC.md`**
§4 / `notes/dispatch-log.md` **F11** — not restated here.

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
7. **Sweep the four status surfaces as one deliberate pass**, not as a
   side effect of editing the prose around them. They go stale
   independently, they contradict each other when they do, and no gate
   covers any of them: **(i)** `notes/Phase39.md`'s top `**Status:**`
   header block — the COMPLETE roster, the date range, and its
   "next concrete task" sentence; **(ii)** the *Hand-off* next-task slot
   at the top of that section — **re-aim it, never delete it**;
   **(iii)** *Current state*'s (K)-arc paragraph — the dispatch count,
   the strategy-pass count, the date range; **(iv)** the ROADMAP Status
   cell (thin: marker + one clause); **(v)** **this file's own top
   `**Status:**` header** — the per-direction roll call, added at the
   fourteenth's prep (2026-08-18) after GPSA's landing updated its
   section's Status to LANDED and left the header still calling the
   same direction "PREPPED … not yet dispatched", the fifth instance of
   the shape and the first in *this* file. Three consecutive landings each
   missed a *different* one — GEXIST the ROADMAP cell, GORIENT the
   Hand-off slot (deleted with the prep text it replaced), GDEV the
   Status header — each caught only in coordinator verification, each
   costing a follow-up commit. Third instance of the same shape as
   item 2 of the fifth fan-out's block (`notes/Pencil-fanout-archive.md`) and item 6 above (dispatch-log
   F17). The generalization worth carrying: **a document's own header is
   a status surface, and it is precisely the part a section-scoped edit
   does not re-read.**

---

## Seventh fan-out — prepared and dispatched 2026-08-19 (directions YLOC / BALB / AGLU / ZNEQ / CIRR)

Five directions dispatched **concurrently** — **YLOC**, **BALB**, **AGLU**,
**ZNEQ**, **CIRR** — each independent, each returning its own untracked draft
(`notes/Pencil-draft-<CODE>.md`) and its own new driver, landed one at a time by
**separate serial coordinator commits**: the sixth fan-out's shape, repeated at
five directions. **User adjudication authorizing the multidispatch** — asked at
the session-start check-in how the twentieth direction's pick should be made
(delegate to a fable recon / coordinator-authored prep / multidispatch again /
coordinator picks under the standing 2026-08-07 delegation), the user elected
**"Multidispatch fan-out again"**, over a coordinator recommendation *against*
it on a 92 % `weekly_scoped` reading — then supplied the fact that overturned
the recommendation: *"weekly_scoped is only for fable so multidispatch should be
OK."* Same check-in: **rungs `sonnet` + `opus` only, top rung = opus** (fable
conserved), cap **lifted**, rescue §1 fixups **pre-authorized**. The **tier
split**, the **five directions themselves** and their **disjoint label
reservations** are **coordinator-set** — so the twelfth direction's disclosure
applies verbatim: *there is no independent top-rung ranking of the losers this
wave*, and a future top-rung recon may overturn the bars below freely.

**Roster** (updated per landing):

| direction | tier | target | status |
|---|---|---|---|
| **YLOC** | compute-licensed | input (Y), (a′)'s residual — GBAL's instrument localized to proper chunks | **LANDED 2026-08-19** — an honest MISS (§"Twentieth direction") |
| **BALB** | compute-licensed | (b′), the balance-layer bound `d_adm − d_par ≤ 2` | **LANDED 2026-08-19** — OPEN, NOT a HIT, half proven / half refuted with an exact boundary (§"Twenty-first direction") |
| **AGLU** | compute-licensed | ledger attack (c) — AA-glue realizability at `n_hub ≥ 8` | **LANDED 2026-08-19** — a HIT on the "not realizable" branch (§"Twenty-second direction") |
| **ZNEQ** | compute-licensed | (OC-19) input (a) — `Z ≠ ∅` at every class (shape, split) | **LANDED 2026-08-19** — OPEN, NOT an independent gap; it factors and one half is dominated (§"Twenty-third direction") |
| **CIRR** | derivation-first | chart irreducibility, written down once as a standalone statement | **LANDED 2026-08-19** — a HIT (§"Twenty-fourth direction") |

**Shared mechanics: §"Shared mechanics (all three dispatches)" above binds
verbatim**, at five directions instead of three, with three deltas. (1) Drafts
go to **`notes/Pencil-draft-<CODE>.md`, untracked** (the sixth fan-out's
convention, not the first's scratchpad path) — the coordinator merges and
deletes. (2) The rung is **opus**, not fable: the mapping for a research recon
settling new mirror mathematics is top rung, and top rung this session **is**
opus. (3) Each direction runs the **TERMINATION check (E1/E2/E3) and reports its
reading**; the coordinator re-runs it. **E3 is ARMED** by GBAL's entry-5 HIT, so
**YLOC can fire it** — a direction that believes it has an (a′) HIT says so and
states the E3 consequence, and does **not** fire it: firing is a coordinator
action.

### The coordinator's one routing sharpening, recorded because it overrides a landed hand-off clause

GLAW's *Step G79* hand-off recommends attacking input (Y) *"with
matching-flexibility instruments (alternating-cycle toggles on the `M`-avoiding
coset space, whose affine structure and dimension `n/2 − 1` are now exact)
rather than with local exchange."* **That clause was written blind to GBAL**,
which landed the same day in the same wave and discharged (Y)'s sibling **input
(X)** by an instrument that **absorbs the matching apparatus whole** — (GR-49)
replaces the (c, m)/coset/SDR/matching data by **one bit per branch**, (GR-50)
turns the question into a **degree-constrained orientation**, (GR-51) prices it
by a **local weight inequality**. Since (GR-56)(iv) makes (X) and (Y) the
whole-graph and proper-chunk instances of **one** inequality, the first thing to
try on (Y) is **GBAL's instrument at the chunk level**, not GLAW's suggested
toggles on the object GBAL's instrument dissolves. **YLOC is specced on that
reading**, and GLAW's clause is thereby **overridden as a routing
recommendation** — not contradicted as mathematics (the coset space's affine
structure and dimension stay exactly as (GR-55) Cor. 1 landed them, and remain
available as a fallback if the localization breaks). Same kind of override as
GPSA's of GADM's shift-metric routing clause: recorded, scoped to the routing
clause alone, and traceable.

## Twentieth direction — YLOC (seventh fan-out)

**Status: LANDED 2026-08-19 — an honest MISS, with substantial positive
content.** Second of the seventh fan-out's five directions to land, after
CIRR; one of **five** concurrent directions (BALB/AGLU/ZNEQ still in flight),
**compute-licensed** tier. §(K-grid) **extended**, **Steps G80–G85**, labels
**(GR-61)–(GR-66) CLAIMED exactly** — the full reservation consumed, nothing
returned to the pool (`(GR-64)(R1)`/`(GR-64)(R2)` are sub-items of (GR-64),
not separate mints). Driver **`notes/scripts/w4/yloc.py`** (seven modes;
`--validate` runs all seven but exceeds the 600 s foreground budget at
~890 s, so the landing gate ran three invocations instead: `--loc` alone
(274.7 s, coordinator-reproduced at landing), `--coll` alone (359.0 s,
coordinator-reproduced), and the remaining five modes together (139.7 s,
coordinator-reproduced) — `notes/scripts/README.md` §3).

**The target — input (Y), (a′)'s named residual ((GR-60)), verbatim as landed:**
*at every habitat shape there exist a perfect matching `M`, a minimum-weight
`M`-avoiding representative `y ∈ Φ`, and an injective end-selection `φ` of
`supp(y)` — together with, when `d_adm > d_par`, an `M`-avoiding matching `Z`
disjoint from `y` with `|y| + 2|Z| = d_adm` and `φ` avoiding `V(Z)` — such that
the resulting minority map `m` is balanced and satisfies, for every proper chunk
`S`, `z_mono(S) + |δ_S − σ_S| ≤ cap(S) − 6`.* (a′) is the only remaining
entry-1 attack, carries **no bar**, and is **the only thing between the arc and
E3**.

**The route to try FIRST (coordinator-pinned; the sharpening above):** push
GBAL's (GR-49)–(GR-54) chain down to the chunk level, in three steps.

1. **Re-express the (GR-56) chunk invariants `cap(S)`, `z_mono(S)`, `δ_S`,
   `σ_S` in (GR-49)'s one-bit-per-branch coordinate `z`.** GBAL proved the
   *whole-graph* instance is `δ = 0` at a balanced `z`; the question is what the
   *per-chunk* instance becomes in `z`. (GR-56)(v) already says
   admissibility and full-goodness are functions of the minority map alone, and
   (GR-49) says the minority map is `z` — so the translation should exist.
2. **Ask whether (GR-50)'s degree-constrained orientation acquires per-chunk
   in-degree constraints**, and whether **(GR-51)'s local weight inequality has
   a per-chunk analogue whose only negative term is again a
   monochromatic-pair hub.**
3. **If it does, whether (GR-53)'s exhaustion over maximal constraint
   structures still closes** with the chunk constraints added — the structures
   were 1 / 44 / 4837 at `2k = 2/4/6`, so an enlarged exhaustion is a
   compute question, not a new idea.

**The obstruction to expect, and to report exactly if it bites:** GBAL's
argument is whole-graph-only because **(GR-52)'s parity contradiction uses
`2 e_H(S)` over the whole side** — a violating hub set would have odd total
internal even-degree. At a *proper* chunk that global count is not available.
If the localization breaks there, say so in those terms and name what would
replace the parity contradiction; that is a more valuable return than a
measurement.

> **REFUTED as stated — see (GR-63)(i), recorded rather than deleted.** The
> predicted obstruction was **wrong**, and YLOC's refutation is **correct**:
> in (GR-52)'s landed proof `S` already ranges over **hub subsets** (the
> two-sided Hall violator), not chunks, and `Σ_{v∈R} a_v = 2 e_H(R)` is a
> **per-subset** double count valid at *every* `R` (305 704 pairs, 0
> failures). (GR-52) would localize for free. The chain breaks two links
> **earlier**, at (GR-50)→(GR-51): full goodness is not a function of
> `(odd pattern, in-degree vector)`, because in-degree fixes the majority
> colour `c(v)` and both chunk terms read the minority-dart identity `m(v)`.

**Calibrating opening cases** (GLAW's measurements, *Step G79*): the **965**
stratum shapes whose worst optimal cell needs the `M` rung, and the **13**
shapes at balance gap 2.

**Bars.** Do **not** re-attack (a′)'s **per-matching** variant — **REFUTED**
((GR-59): `min_M` is load-bearing, no (a′) proof may fix its anchor matching).
Do **not** re-run the bounded {T1, T2} descent (**DEMOTED by witness**,
(GR-48)(iii)) or the extended {T1, T2, K3} catalogue. Do **not** re-derive
(GR-58)'s census — it is landed and **exhaustive** at `n_hub ≤ 6` with no cap;
extend it only if a genuinely new stratum is needed, and disclose the cap if so.
**(b′) is BALB's target this wave** — report any (b′)-relevant by-product as a
finding and do not develop it (GBAL's precedent with (a′)).

**Riders, verbatim.** `Λ = ∅`, `D = 0`, and modulo (GR-4′) where a closure chain
is concerned; the `Λ ≠ ∅` closed-form analogue and the `D > 0` lift stay
**unswept**; **none of this closes (GR-15)**; an (a′) HIT **fires E3** (ARMED by
GBAL) — state the consequence, do not fire it.

**The verdict, as landed: the localization FAILS and (Y) is NOT discharged.**
**(GR-61)** carries the (GR-56) chunk invariants into the `z`-form exactly —
step 1 of the pinned route succeeds, buying notation and one structural fact
(`Z2(S) = ∅ ⟺ S = E(G°)`, the unique chunk whose inequality reads only the
odd bits) but nothing more; the localization's *premise* — every chunk
invariant a function of the odd pattern — survives on an exact **10-shape**
exceptional family (nine one-even-branch θ shapes, the all-length-3 `K4`) and
dies at all **4914** others. **(GR-62) REFUTES step 2 by witness:** full
goodness is not a function of the (GR-50) degree data — two admissible
balanced configurations share the same odd pattern and even-branch
in-degree vector yet split on full goodness (7982 of 217 468 fibres, at
1499/4924 shapes, the smallest witness rank-certified at `n_hub = 4`) — so
**no (GR-51)-shaped criterion applies to the chunk system**. **Scoped
honestly:** this excludes a *(GR-51)-shaped* criterion (feasible set cut out
by in-degree bounds), not every conceivable existence criterion — a shape's
existence question is trivially a function of its odd pattern alone. The
positive content is **(GR-64)**, the collision bound — a colouring-free
lower bound on `d_fg` pricing the coupling between (Y)'s distance quantifier
and its chunk constraints, with a **proven `≤ 2` per-chunk ceiling**
(attained), a packing form, and a **sound** 1250-of-24 671 anchor-matching
prune (incompleteness 7856 disclosed) — and **(GR-65)**, the fit identity:
`dist(m, M)` and `z_mono(S)` are the *same statistic* (the minority dart on
a prescribed selection), naming what any successor instrument must control.
**(GR-66)** measures GBAL's own certificate against (Y): it misses the
distance optimum at 3514/4924 shapes and full goodness at 651/4924.
**`min_M B(M) = 0` at every one of the 4924 inventory shapes is MEASURED,
not proven** — named as sub-target **(GR-64)(R2)**, the sharpest cheap
successor the pass produced. Input (Y) stays **OPEN**, (a′) is **NOT** hit,
**E3 (ARMED by GBAL) does NOT fire**; (GR-15) **OPEN**, no gap-map status
moves; class uniformity, `hK`, and the balance layer (route-ledger entry 5)
all untouched.

**Two coordinator adjudications on landing.** *(1)* The predicted-obstruction
refutation above is genuine, not a partial hit: the prediction was **wrong**
and (GR-63) is **right** — recorded plainly, not softened. *(2)* GLAW's
*Step G79* routing override (§"The coordinator's one routing sharpening"
above) is **SPLIT by this landing, not simply upheld**: the override was
right to try GBAL's `z`-form first and right about the **chunk/balance**
rung, but **GLAW's matching-flexibility clause is reinstated for the
*distance* rung specifically** — exactly the rung GBAL's instrument
dissolves and loses ((GR-65): distance and `z_mono` are one statistic;
(GR-66): GBAL's own certificate sits above `d_adm` at 3514/4924 shapes).
Neither clause is wrong; they address different rungs of one statement. The
successor's natural routing, carried forward to BALB/the next primary:
(GR-61)'s `z`-form for the chunk arithmetic, (GR-55)'s coset/SDR coordinates
for the distance, (GR-65)'s `fit` as the bridge, and a Hall/deficiency
condition over the tight-chunk hypergraph of exit selections (GORIENT
*Step G43*'s frame) in place of degree-constrained orientation.

**What did NOT move.** No gap-map status moves: (GR-15), class uniformity,
`hK`, the balance layer and route-ledger entry 5 are exactly where they
were. (GR-62)'s refutation is scoped honestly (excludes a (GR-51)-shaped
criterion only). (GR-64)'s prune is sound but incomplete (1250 of 24 671
kills, incompleteness 7856 — both numbers disclosed). **TERMINATION: E1, E2
and E3 all NO; E3 stays ARMED (by GBAL) and does not fire.** One
(b′)-relevant by-product reported and **not developed** (BALB's target this
wave, per the bar): (GR-65)(ii) expresses the deviation count in the same
dart-colour language (GR-49) that (GR-50) uses to decide balance, so
`d_adm − d_par` becomes a statement about two `fit` counts on one colouring.
**Not pre-empting BALB:** (GR-65)(i)'s identity (`n − #agree = #differ`) is
the general statement, for any selection `β`; BALB's independently-derived
perfect-matching-anchored instance is its own label, cross-cited from that
side, not minted here.

## Twenty-first direction — BALB (seventh fan-out)

**Status: LANDED 2026-08-19 — (b′) stays OPEN, NOT a HIT, with its
decomposition half proven and half refuted at an exact boundary.** Third
of the seventh fan-out's five directions to land, after CIRR and YLOC
(AGLU/ZNEQ still in flight), **compute-licensed** tier. §(K-grid)
**extended**, **Steps G86–G91**, labels **(GR-67)–(GR-72) CLAIMED
exactly** — the full reservation consumed, nothing returned to the pool.
Driver **`notes/scripts/w4/balb.py`** (six modes;
`--validate` runs all six inside the 600 s foreground budget, measured
~105 s).

**The target — (b′), the balance-layer bound `d_adm − d_par ≤ 2`.** OPEN and
supported (no growing gap ever found); ridden as a *secondary* three times
(GADM, GPSA, GDESC) and **never a primary**. This wave makes it one.

**Why now.** (GR-54) proves `d_adm < ∞` and says **nothing** about the gap —
GBAL's own scope line is explicit: *"It does not move (b′)."* What changed is
the instrument, not the evidence: **(GR-50)** decides balance **exactly, in
polynomial time**, over at most 20 odd-branch patterns, and **(GR-51)** prices
feasibility by a **local weight inequality**. That is the first apparatus in
the arc that could deliver a *bound* rather than a measurement.

**Two halves — keep them distinct.**

1. **Is `|δ|` at a parity-optimal map bounded by 2?** GDESC measured
   `{0: 92, 2: 2}` at parity-optimal maps over 94 odd-carrying shapes, exact
   gaps `{0: 92, 1: 2}`, 0 mechanism violations. A shape with a parity-optimal
   floor `|δ| > 2` **refutes this half** (and is E1 clause (v)'s named
   trigger — surface it as such).
2. **Does repairing balance from a parity-optimal map cost `≤ 2` deviations?**
   (GR-45) prices **one T1 at exactly 2 deviations**, so a single T1 repair
   gives exactly 2 and the question is whether one T1 always suffices —
   which **(GR-46)'s one-move transitivity makes precise** (any two
   parity-consistent minority maps differ by a single legal move, so "one
   move" is not a restriction on reachability, only on *cost*).

**What counts as a HIT** — a proof of `≤ 2`; **or** a proof of a *different*
constant **with the exact boundary named**: the (GR-29)/(GR-30) precedent makes
an exact-boundary refutation a **valued outcome, not a failure** (a theorem at
`n_hub ≤ 6`, false from `n_hub = 8`, with witnesses, is how (GR-28)(iv) landed);
**or** a witness at gap `> 2`, which moves (b′) to refuted-with-successor.

**Bars.** Entry 5 is **PROVEN** ((GR-54)) — do not re-attack it. **(a′) /
input (Y) is YLOC's target this wave** — report any (Y)-relevant by-product as a
finding and do not develop it. Do **not** re-open the bounded-deviation
selection form (**REFUTED as posed**, (GR-41)+(GR-42): `d(NK(m)) ≥ m/2`
unbounded while every member stays fully-good) — (b′) is a statement about the
*gap between two layers*, not about the deviation count, and the necklaces are a
test bed for it, not a refutation of it.

**Riders.** As YLOC's, verbatim. Additionally: the shift-metric layer is
**UNBOUNDED** ((GR-43), `d_par = d_adm = d_fg = m` exactly at the necklaces) —
so (b′) must be stated as a bound on the **difference**, never on `d_adm`, and
any figure quoting a necklace member carries that qualifier.

**The verdict, as landed: (b′) stays OPEN, NOT a HIT — its decomposition is
now half proven outright and half refuted at an exact boundary**, the
(GR-29)/(GR-30)-shaped outcome named above as a valued result, not a
failure. **(GR-67)** anchors the z-form at a perfect matching `M`: the
deviation count from `M` is a **2-factor sign-change count**, and a
one-line branch sum gives the **PARITY LAW** — every per-matching layer
gap is EVEN, so per-matching (b′) is the dichotomy *gap 0 or gap ≥ 2*, and
a counterexample must show a gap of 4, never 3. **(GR-68)** prices
**every** legal move in closed form: matching branches and whole 2-factor
cycles are FREE, and a single-path repair costs at most 2 **regardless of
its length** — this **proves (b′)'s price half outright**, at every shape,
with no cap and no length restriction. **(GR-69)** proves the imbalance
ceiling `|δ| ≤ 2·min(k, ⌊n_hub/4⌋)` from the *necessity* half of
(GR-51)(i)(a) alone, so `|δ| ≤ 2` is a **theorem at `n_hub ≤ 6`** — the
whole stratum, hence *this row's own* and GDESC's *Step G66*'s measured
`|δ|` figures there are arithmetic, not evidence — and **FALSE from
`n_hub = 8`**, realized at the Wagner habitat shape **V8** (accepted by
both `cflank.cubic_habitat` and `gdev.habitat_by_lemma`, `|δ| = 4` at 4 of
418 configurations), tight at every rung reached. **(GR-70)** reduces
per-matching (b′) to **one availability clause** (Clause A′) and verifies
it **EXHAUSTIVELY** over the whole stratum (4780 shapes, 23 939 (shape,
matching) pairs, all 96 930 unbalanced parity-optimal configurations, full
`3^n` censuses, no cap) — while **REFUTING** the landed T1-only instance of
that clause **from `n_hub = 8`**, with stuck witnesses at 32/15 088,
120/16 502 and 52/15 904 configurations at `n = 8/10/12`, every one
repaired at price **0** by a named **mixed-pair** move. **(GR-71)** carries
(b′) to 536 exact shapes at `n_hub = 8/10/12` and to cap-free per-matching
certificates at `n = 30`. **(b′) stays OPEN, NOT a HIT** — price half
proven, availability half not; **(GR-15) stays OPEN, no gap-map status
move on `hK` itself**.

**E1(v)'s named trigger does NOT fire.** The V8 `|δ| = 4` configurations
are **not parity-optimal** (they sit at `|δ| = 4` among a spectrum
`{0: 230, 2: 184, 4: 4}`, none of the four the parity-optimal member) — a
careless reading of "half 1 refuted" would think this fires it; it does
not, and the pass says so explicitly.

**Three coordinator adjudications on landing.** *(1)* **The
cross-direction duplicate is a corroboration, not a rediscovery.**
(GR-67)(i) and YLOC's landed (GR-65)(i) are **the same identity** —
`dist(m, M) = #{v : the two non-M darts differ}` is exactly
`n − #{v : they agree}` — derived independently by two directions blind to
each other in the same concurrent fan-out. (GR-67)(i) lands as the
**perfect-matching-anchored instance** of the landed (GR-65)(i), cross-cited
in that qualified form, with the independent double-certification recorded
as **corroboration** — the wave's third such convergence (after
OCON/FRES, and now YLOC/BALB here). What (GR-67) adds beyond the shared
identity is new: the parity law (ii) and the changeover parametrization
(iii), both BALB's own. *(2)* **The flagged-unverified by-product is
already verified.** BALB's report that (GR-67) Cor. 1 extends to
`d_fg(M)` — hence `d_fg(M) − d_adm(M)` even, hence GLAW's (GR-59)
per-matching (a′) witnesses must all carry a gap `≥ 2`, never exactly 1 —
is **corroborated against a landed figure**, not left unverified: GLAW's
own landed (GR-59) measurement of that very gap distribution is
`{2: 1251, 4: 27}` — every one of the 1278 gaps is already even, from a
different direction in an earlier wave. *(3)* **The retroactive
reading-downgrade lands at the figures it downgrades, not only in BALB's
own section.** (GR-69) proves `|δ| ≤ 2` is forced on the whole
`n_hub ≤ 6` stratum, so GDESC *Step G66*'s `{0: 92, 2: 2}` and this pass's
own exhaustive `{0: 4641, 2: 139}` carry **no evidential weight for
`n_hub ≥ 8`** — the figures stand, only the *reading* is downgraded, and
the annotation is recorded at *Step G66* itself in `Pencil-informal.md`,
not only here.

**The cap disclosed, with its reason.** The necklace leg stops at `m = 6`
because `gadm.dp_pref`'s table is `2^dim` (dim 16/21/26/31 at
`n = 30/40/50/60`, guarded by `assert dim ≤ 18`), and **GBAL's
`n = 40..60` reach does not transfer**: (GR-54) needs only balance
*existence*, decided polynomially by (GR-50), whereas any (b′) statement
needs `d_par(M)`, the exponential object. An exhausted table is not `∞`
and a `m = 6` leg is not an `m = 12` leg.

**TERMINATION: E1, E2, E3 all NO.** No `g`-flank (rank-free throughout,
no `d_fg` claim made); entry 5 (PROVEN, GR-54) is untouched, and (b′) —
not a ledger entry in E2's sense — leaves an open, named, dispatchable
attack either way. **E3 stays ARMED by GBAL and is neither fired nor
disarmed** — its target is entry 1, (a′), which this pass does not
attempt (YLOC's target this wave).

**The residual, named exactly: *Clause A′*, doubly-blocked sub-clause.**
The one-end-blocked case is nearly done — the mixed-pair mechanism prices
it at the unblocked T1's price, because an `M`-branch is free. The
doubly-blocked case, (GR-48)'s named kill realized at `n = 30`, is the
real gap: the chain must be followed at both ends, and (GR-68) prices it
only `≤ 4` unless both extra endpoints land on deviating hubs. **The
recommended untried alternative:** minimizing `dist(·, M)` at a *fixed*
balanced pattern is, by (GR-50), a min-cost degree-constrained
orientation — polynomial; per-matching (b′) is then an exchange argument
between two such flow problems (pattern-free vs pattern-fixed), and flow
theory's exchange machinery is untried on this arc.

**What did NOT move.** No gap-map status moves: (GR-15), class
uniformity, `hK`, entry 5 and route-ledger entry 1/(a′) are exactly where
they were. Every figure above at `Λ = ∅`, `D = 0`, modulo (GR-4′) where a
closure chain is concerned; `Λ ≠ ∅` and `D > 0` stay **unswept**.

## Twenty-second direction — AGLU (seventh fan-out)

**Status: LANDED 2026-08-19 — a HIT on the "not realizable" branch, with
one correction to the dispatch's predicted consequence.** Fifth and last
of the seventh fan-out's five directions to land, after CIRR, YLOC, BALB
and ZNEQ — **this landing closes the seventh fan-out**. Labels reserved:
`GR-` **(GR-73)–(GR-78) CLAIMED exactly**, **Steps G92–G97**; owning
section **§(K-grid)** (extends). Driver: **`notes/scripts/w4/aglu.py`**
(six modes `--pool`/`--pin`/`--kill8`/`--lam8`/`--adv`/`--val`, `--lam8`
run in three slices `--slice i/3`).

**The target — ledger attack (c): AA-glue realizability at `n_hub ≥ 8`**, the
**only surviving case** of the (GR-38) intersection kill. (GR-38)(iii): a
crossing pair of same-block binding chunks forces
`slack + defect(S ∩ S′) ≤ 1`, which forces the **AA-glue** configuration; over
the **complete** `n_hub ≤ 6` stratum that configuration has **0 instances**
(0 / 53 740 instances over 4920 shapes — binding is *provably laminar* there,
so the kill is **vacuously strong**), and whether the configuration is
**realizable** from `n_hub = 8` on is open.

**The two outcomes, and what each buys — both are wins, say which you got.**

- **NOT realizable** ⟹ the intersection kill extends past its vacuous stratum
  and **binding laminarity becomes a theorem**, which organizes the whole
  binding family that (GR-35)'s submodularity and (GR-36)/(GR-40)'s charges
  already circle.
- **Realizable** ⟹ the kill has a **real case**, and the charge apparatus must
  handle it. Name the witness exactly, **rank-certify** it, and check whether it
  is fully-good (a realized AA-glue that is still fully-good is a much weaker
  event than one that is not).

**Method.** An exhaustive-or-provably-complete search at `n_hub = 8`, using the
landed oracles rather than new ones: **(GR-25)**'s `2^{n_hub}` cut criterion as
the canonical `D = 0` membership oracle, `cflank.cubic_habitat` as the habitat
gate, `cflank.admissible` for colouring acceptance, and (GR-42)'s polynomial
habitat-membership criterion where a shortcut is wanted. **Cap disclosure is
mandatory** — the §(K-grid) cap-exhaustion hazard is a recorded gate
(`731b3e33`), and LTWO's *"4 of 8 patterns"* correction is the precedent for
what a silently-capped leg costs: **an exhausted cap is not a proof of
nonexistence.** If the search is capped, the return says "not found under cap
C", never "does not exist".

**Bars.** Do **not** re-open (GR-28)(iv)'s `g ≤ 1` cap — **REFUTED with an exact
boundary** ((GR-29) a theorem at `n_hub ≤ 6`, (GR-30) false from `n_hub = 8`
with four witnesses, per-shape (GR-15) holding at all four (GR-31)); its
`n_hub = 8` witnesses are **available as constructions to reuse**, which is the
one thing to take from it. Do **not** re-run the (GR-39)/(GR-40) fully-hot
census (landed **exhaustive** over all 4920 `n_hub ≤ 6` shapes). **(d′)** — the
corner-armed realized-binding fully-hot seed hunt past GDEV's caps — is **NOT**
this direction (E1's own clarification: not a flank by itself).

**Riders.** As YLOC's, verbatim. Every obstruction figure carries its **family
qualifier** — (GR-36)'s **binding-capable** family strictly contains the
capacity-tight one, and (GR-40)'s 815 → 573 is a **prune, not a zero**.

**The verdict.** **(GR-73)** proves `slack = 0` ⟺ no X-hub, pinning the
crossing interface to a rigid `{2,3}`-degree subgraph with two disjoint
`≥ 2`-member attachment families, and extends the J-charge from chunks to
arbitrary branch sets. **(GR-74)** proves the AA-glue configuration at
`n_hub = 8` has exactly **one** combinatorial template — `T` covers all 8
hubs at 10 branches, `R`/`R′` single branches, `S ∪ S′ = E(G°)` —
EXHAUSTIVE at all 44 premise-satisfying pairs of all 20 classes, and
explains the `n_hub ≤ 6` vacuity combinatorially, before any colouring.
**(GR-75)** proves the configuration and its whole kill residual (not just
the named case) are **NOT realizable** at `n_hub = 8` — a four-line
contradiction with (GR-32)(iii)'s balance identity, independently certified
by an EXHAUSTIVE, uncapped scan of the complete stratum (39 689 shapes,
9 617 854 admissible colourings, 0 instances) that also reproduces
(GR-38)'s own `n_hub ≤ 6` headline exactly (4 920 / 284 512 / 53 740 / 0) —
so the (GR-38) intersection kill is a **THEOREM at `n_hub = 8`,
non-vacuously**, and the **maximal** binding chunk family of each block is
laminar. **(GR-76)** derives a general-`n` charge `|W| ≥ |F₂| + q_T` that
forces `n_hub ≥ 10` with no pinning needed — an `n`-free strengthening of
(GR-75)(i) that also re-explains (GR-38)(iii)'s `n ≤ 6` vacuity — and
narrows `n_hub = 10` to exactly **three** counting-satisfiable templates.

**The correction, landed plainly, not softened.** The dispatch predicted
*"NOT realizable ⟹ the intersection kill extends past its vacuous stratum and
**binding laminarity becomes a theorem**."* **(GR-77) REFUTES that exactly as
stated:** exhaustive over the complete `n_hub = 8` stratum, there are
**3 774** crossing same-block binding chunk pairs (nested 457 244) against
**0** over the whole `n_hub ≤ 6` stratum. **Outright binding laminarity is
FALSE at `n_hub = 8`.** What (GR-75) actually buys is the **uncrossing**: the
kill is a theorem non-vacuously, so the **maximal** binding family is
laminar **per block** — 1 424 of the 3 774 pairs by exhaustive measurement
(all at `slack + defect(T) = 2` exactly), the other 2 350 by the (F-c)
charge bound, with no claim about their `(slack, defect(T))` distribution
beyond `≥ 2`. This is the **second** coordinator-predicted consequence this
wave to be refuted by the direction it primed (after YLOC's (GR-63)).

**(GR-78), a real E1 detector, not an omission.** Every one of the **39 689**
shapes of the complete `n_hub = 8` stratum carries a fully-good admissible
colouring (`a = 0 ∧ max_P g ≤ 0`); **8 543 304 / 9 833 022** (86.9 %) of
colourings are fully good, every shape `≥ 10`; `assert flank == 0` per
shape, no g-flank. This yields per-shape (GR-15) at `n_hub = 8` on the
complete stratum, **modulo (GR-4′)**, counting-side only — **no rank was
computed anywhere in this pass** — a substantial positive that is **not** a
(GR-15) status move: uniformity stays open.

**Cap disclosure.** `n_hub ≥ 10` is **OPEN with no search run there and no
cap exhausted** — (GR-76)(iv) narrows it to three templates, it does not
search it. The **592 shapes skipped by `--kill8`**'s length filter are
**proven residual-free by the (GR-36)/(F-c) charge bounds**, not budgeted
away. The `--lam8` three slices are an exhaustive **partition** of the 11
habitat-carrying classes, not a sample. The shape pool is the **complete**
stratum (every iso class of connected loopless cubic multigraph on 8 hubs ×
every excess profile, gated by the landed (GR-25) criterion). `--val` was
run by the dispatch (not re-run at landing) and reproduced item 7's
`n ≤ 6` headline exactly, which is what licenses this pass's `n_hub = 8`
numbers; `--pool`/`--pin`/`--kill8`/`--lam8` (all three slices)/`--adv`
were all independently re-run by the coordinator at landing and reproduced
every quoted figure above.

**Riders, verbatim.** Everything at `Λ = ∅`, `D = 0`, modulo (GR-4′)
wherever (GR-15) is mentioned; `Λ ≠ ∅` and `D > 0` stay **unswept**. **None
of this closes (GR-15)**; **no gap-map status move on `hK`**. Every
obstruction figure carries its **family qualifier** — (GR-36)'s
binding-capable family strictly contains the capacity-tight one, and
(GR-40)'s 815 → 573 is a **prune, not a zero**. **(GR-74)** is exhaustive
and colouring-free (all 44 premise-satisfying pairs across all 20 classes,
nothing else).

**TERMINATION: E1 does not fire (on the (GR-78) detector's evidence); E2
does not fire — attack (c) narrows rather than dies, with (GR-76) named as
its instrument, and (a′)/(b′)/(d′) stay dispatchable; E3 stays ARMED by
GBAL and is neither fired nor disarmed.** (E1) — (GR-78) is a real
exhaustive detector: every one of the 39 689 shapes carries a fully-good
colouring, so no g-flank exists at `n_hub = 8`; nothing about the 3 774
crossing pairs is a flank — they are pairs of binding chunks at
*particular* colourings, and every one of their shapes still carries ≥ 10
fully-good colourings. (E2) — attack (c) moves from "open at `n_hub ≥ 8`"
to **"settled negative at `n_hub = 8`, open at `n_hub ≥ 10` with (GR-76) as
the named instrument"** — a narrowing with a successor named, which the E2
carve-out explicitly does not fire on; attacks (a′), (b′) and (d′) are
untouched and remain dispatchable. (E3) — AGLU is a §(GR-38) pass and
touches neither entry 1 nor (a′); the arming state is unchanged from GBAL's
entry-5 HIT.

**So: no escalation from this direction. The coordinator re-runs the
check.**

**The seventh fan-out is now COMPLETE — all five directions landed
2026-08-19.** Full per-direction detail: CIRR §"Twenty-fourth direction",
YLOC §"Twentieth direction", BALB §"Twenty-first direction", ZNEQ
§"Twenty-third direction", above.

## Twenty-third direction — ZNEQ (seventh fan-out)

**Status: LANDED 2026-08-19 — input (a) is OPEN as a class-uniform statement
and is NOT an independent gap.** Fourth of the seventh fan-out's five
directions to land, after CIRR, YLOC and BALB (AGLU still in flight),
**compute-licensed** tier. §(K-out) **extended**, **Steps O19–O24**, labels
**(OC-23)–(OC-28) CLAIMED exactly** — the full reservation consumed, nothing
returned to the pool. Driver **`notes/scripts/w4/zneq.py`** (four modes,
no `--validate`; `--factor` 97 s, `--sweep` 242 s, `--reject` 76 s,
`--transfer` 106 s — run individually rather than as one foreground call,
all byte-identical under `PYTHONHASHSEED` 0 and 12345 modulo `--sweep`'s
wall-clock progress marks).

**The target — (OC-19) input (a), `Z ≠ ∅`, as a statement in its own
right:** *at every class (shape, split), the chart carries a target-rank
point with `s₀ = 0`.* OCON ranked this **#2 of its five** hand-off items and
called it *"cheap to state and would clean up several rows at once"*; it is
a prerequisite of the **whole (K-tight) criterion — not (OUT)'s to pay** —
and is currently carried **implicitly by every route on the (K-wit) row**.

**The verdict, as landed: input (a) FACTORS, and the two halves have very
different severity.** **(OC-23)** peels the pendant edge `ac` exactly the
way (OC-17) peels `ab`: `s₀ = corank R(H)` at **every** legal chart point,
`H = G − v − a`, so the `s₀` half of input (a) contains no `v`, no `a`, no
split edge — it is **independence of the far framework `H` alone**.
**(OC-24)** proves the dichotomy the chart's irreducibility buys — with
CIRR's **(CH-1)(a)** now proven rather than cited, `Z ≠ ∅ ⟺` both halves
nonempty, each **one-point witnessable** — and the sharper finding the
dispatch's wording did not anticipate: `{σ = 0} = ∅` at a class shape would
make `hK` **FALSE there** (`E(H) ⊆ E(G)`, `G` tight with `def(G) = 0`, so a
self-stress of `H` at every chart point is a self-stress of `G` that blocks
its own Tay target). That branch is a **PENCIL event** — a disproof at that
shape, §(K-flank) direction-A pivot class — **strictly stronger** than the
`{target rank} = ∅` branch, which is exactly the **(K-tight) event** the
dispatch named (routes A and B dead at that split, `hK` at the shape
untouched). So the `s₀` half is a **necessary condition** for `hK` at the
shape and can **never be the binding obstruction**: any proof of `hK`,
including the grid route, hands it over for free. **(OC-25)** shows the
target-rank half **is** §(K-tight) *Step 2* item 1's own attainment
criterion, applied one split down (`(G, v, a, b) ↦ (G′, a, b, c)`), the
regress terminating in one step because `orient`'s chain has exactly two
interior vertices. **(OC-26)** derives the closed form of that half's
failure: along the meet line `M = Π(b) ∩ Π(c)`, badness is three quadratics
in one parameter, hence generically empty, and bad-at-every-`t` is a
**disjunction** — `dim(D ∩ (M̂ ∧ W)) ≥ 3` or `M̂ ∧ w ⊆ D` for some `w ∈ W`
— both forcing a **codimension-2 Schubert jump**. **This pass refuted its
own first closed form by construction** (POOL-ZQ Case C: a nonsingular
hyperplane of `M̂ ∧ W`, `dim(D ∩ M̂ ∧ W) = 3`, **no** pencil inside it, yet
identical badness), correcting the single-containment reading to the
disjunction — adversarial work against its own claim, landed as such, not
tidied away. **(OC-27)** measures **138/138** (shape, split) witnesses of
`Z ≠ ∅` (90 companion-bearing, 48 others), no miss — witnesses, never a
rate, caps disclosed (shape cap 4/family, 6-seed window, stride 4; 142 of
190 non-companion splits uncovered). **(OC-28)** proves the shared-sub-tower
clause against §(K-chart) **(CH-2)**'s stage table (both chain interiors are
non-hubs, so stage 2's hub-only dependence makes the `H`-projections of
`G` and `G′`'s charts identical) and constructs 30/30 transfers, then shows
the `s₀` half is **dominated** by §(K-grid) (GR-10): one grid point per
shape covers **every** split at once, free at 907/907 of that pool — a
**conditional** reduction to an open gap, not a discharge, since (GR-10)
is itself open (its min-max form refuted as posed, the statement itself
staying open, per §(K-grid)'s own row). `{σ = 0}` is exhibited as a
**proper** open, not a tautology: at the (K-res) shape `P21` (fails
`hnoRigid`), 5 of 35 valid seeds sit off it, the only recorded mechanism
being a self-stress of a short theta sub-multigraph inside `H`.

**Four coordinator adjudications on landing.**

1. **The spec's wording was incomplete, and ZNEQ's correction is right.**
   The dispatch called a `Z = ∅` negative "a (K-tight) event, not an (OUT)
   event" — true only for the target-rank branch. The `s₀` branch is a
   **PENCIL event**, strictly stronger, and — the structural point — it can
   never be the *binding* obstruction, because it is implied by `hK` at the
   shape and its only known failure mechanism (§(K-flank) *F5(d)*'s theta
   sub-multigraph at `P21`) sits outside `hK`'s habitat (`hnoRigid` false
   there). This is why input (a) is **not an independent gap**: one branch
   is dominated, the other is a disproof route. (OC-8)'s residue is
   **sharpened, not shrunk** by this: the `s₀` half is dominated, and the
   target-rank half — `(a₁)`, the Schubert non-jump
   `dim(D ∩ M̂ ∧ W) ≤ 1` — remains a real open input of the same shape as
   (OC-19)(c), one-point decidable with the recipe missing.
2. **(OC-28)'s positive is CONDITIONAL, not a discharge.** §(K-grid) (GR-10)
   is itself OPEN (its min-max refuted as posed, the statement staying open
   as the strictly stronger form), so "(GR-10) ⟹ the `s₀` half at 907/907"
   is a **reduction to an open gap**, per-shape evidence rather than
   uniformity. The named cheap follow-on — a purely combinatorial cross-pool
   re-keying of §(K-grid)'s 907 against §(K-out)'s class-shape population,
   no new mathematics — is carried to the hand-off, not attempted here (the
   two pools are labelled-instance pools with different keys and are
   **not** re-keyed by this pass).
3. **The wave's THIRD cross-direction convergence, recorded as a finding
   about the fan-out shape itself.** ZNEQ wrote its mathematics **blind to
   CIRR**, which landed mid-run, flagging (OC-28)(i)'s shared sub-tower as
   "this pass's one structural input, owned by CIRR". CIRR's same-day
   **(CH-2)** — the tower written down stage by stage — then turned that
   flagged input into a proof outright, and its **(CH-1)(a)** supplied the
   ℚ-descent step (OC-28)(iii) needed. This is the **same shape** as the
   sixth fan-out's OCON/FRES pair and this wave's own YLOC/BALB pair on the
   fit identity: three independent convergences in two waves, every one a
   direction discovering it needs a fact another concurrent direction was
   independently landing, neither seeing the other. **Worth naming as a
   property of the fan-out shape**: a multidispatch surfaces cross-cutting
   dependencies a single serial dispatch would have had to name explicitly
   in advance or miss, and this wave found three without any coordinator
   foresight.
4. **The self-refutation stands, as adversarial work, not a hedge.** POOL-ZQ
   Case C is a constructed counterexample to this pass's *own* first
   derivation. It is landed in full in (OC-26)'s "refuted by construction"
   clause above, not tidied into a footnote.

**Not a dispatchable candidate — awaiting user adjudication.** *Step O24*
names a `σ > 0`-everywhere hunt at class shapes whose `H` carries a short
theta sub-multigraph as the only known failure mechanism for the necessary
half. A hit there is a **PENCIL event**, which under the direction-A pivot
rule (`notes/Pencil-fanout-archive.md` §"Direction A", *Pivot rule*) is *"a phase-redefining event for
the user to adjudicate, not a result to build on."* It is named here and in
the hand-off for completeness, and is explicitly **excluded** from the pool
a future coordinator may pick from under the standing 2026-08-07 delegation
until the user has adjudicated it.

**The cap disclosed, with its reason.** POOL-ZN's shape cap is 4 per family,
seed window 6, stride 4 on non-companion splits — 142 of 190 non-companion
eligible splits, and every shape past each family's fourth, are **not
covered**. This is a witness census, not a rate: each of the 138 hits is an
individual proof that `Z ≠ ∅` at that (shape, split), so the cap bounds
*coverage*, not *confidence* in what was measured.

**TERMINATION: E1, E2, E3 all NO.** *(E1)* no g-flank: this direction
touches no admissible colouring and exhibits no `D = 0` shape whose every
admissible colouring is binding — per-shape §(K-grid) (GR-15) is untouched.
*(E2)* the target is neither refuted nor unprovable-as-posed — it is
**reduced**, with two named, one-point-decidable, dispatchable attacks
(the re-keying job and the Schubert non-jump). *(E3)* the target is **not
proven** class-uniformly; **E3 stays ARMED by GBAL's entry-5 HIT, neither
fired nor disarmed**.

**Harness debt recorded, not paid.** `ocon.meet` — the dimension-asserting
wrapper of `lambda.span_meet` — now has **two** consumers (OCON's and this
pass's), tripping `notes/scripts/README.md` §2 rule 2's own move-down
trigger. This pass may not modify a landed file, so the move is recorded as
a **new, dated, unpaid** debt item for a successor (README *Harness debt*)
— that section is otherwise CLEARED / round CLOSED (S1–S4, 2026-08-06), and
this is a **separate** entry, not a reopening of that round.

**Riders, verbatim.** The standing **(OC-7) rule**: no `place_pencil_general`
battery may be quoted as a **rate** or as evidence about a **generic** chart
point; POOL-G figures are quoted over the **318 coincidence-free** frames,
never the raw 357. The two settled pools **POOL-G and POOL-S are pinned and
disjoint** — not aggregated, not re-sampled. ZNEQ's own **138/138** are
**witnesses, never a rate**, caps disclosed as above.

**What did NOT move.** No gap-map status moves: (OC-8), class uniformity,
`hK`, (GR-15) and route-ledger entry 5 are exactly where they were. §(K-out)'s
*State of (K)* status cell was **recomputed from scratch** (790 → 649 words)
to make room for (OC-23)–(OC-28) rather than bumped past its cap; the
close-it cell gained the two-half breakdown (323 → 438 words), still well
under cap. `notes/check-gapmap-cells.py` passes on the changed row.

## Twenty-fourth direction — CIRR (seventh fan-out)

**Status: LANDED 2026-08-19 — a HIT.** First of the seventh fan-out's five
directions to land; one of **five** concurrent directions (YLOC/BALB/AGLU/
ZNEQ still in flight), **derivation-first** tier. §(K-chart) **OPENED**,
**Steps CH1–CH8**, labels **(CH-1)–(CH-8)** claimed exactly (nothing returned
to the pool, `notes/Pencil-labels.md`). Driver `notes/scripts/w4/cirr.py`,
three modes, ~1 s total — written, contrary to this direction's "expected
unused" driver clause, because two of its sentences are sampler-behaviour
claims no amount of prose settles (F11).

**The verdict: the pencil chart is irreducible, written down once, and all
four consumers audit clean.** **(CH-1)** states it: for `Γ` loopless with
`hcard`, min degree 2 and **girth ≥ 4**, the pencil incidence locus `𝒜(Γ)` is
a nonempty, irreducible, ℚ-rational variety, and so is its image
`Chart(Γ)` — a tower of affine-linear fibres (hub points free; hub normals in
the nullspace of hub-neighbour differences; interiors on `meet_line` /
`in_plane_point` / free), with `hcard` exactly the hypothesis that keeps the
normal-space fibre nonzero. **(CH-6)** identifies the tower's
constant-fibre-dimension restriction — the clause the dispatch asked to be
made explicit — as **`IsNondegPencilRealization`'s own conjunct 3**
(`LinearIndepOn K normal (closedHubNbhd v)`, `Motive.lean:110`), which `hK`'s
hypothesis `HasGenericPencilRealization K 3 G′` and the harness guard
`repin.star_generic` both already carry about `G′`. **(CH-4)** shows the
restriction costs no closure — `𝒜(Γ) = \overline{𝒫(Γ)}`, so a legal
realization off the restriction is still a point of the same irreducible
variety, which is exactly what §(K-slide) (S1)(e) needs. **(CH-5)** is the
one correction: *Step FR13*'s stated hypotheses (girth ≥ 3) do **not** give
nonemptiness — a Λ-triangle carrying a non-hub on two of its hubs empties the
tower's stage-3 locus at **every** seed (`Γ_bad`, 0/200 placeable, the reason
asserted, not just the symptom) — and girth ≥ 4 does, free at `G′` **three**
independent ways: the girth-6 table row, `gridcol.class_shape`'s two-hub-
triangle filter, and (see below) the landed Lean theorem. **(CH-7)** audits
all four named consumers — §(K-out) (OC-19) input (b), §(K-slide) (S1)(e),
§(K-dom) (D4), §(K-ann) (ANH-9)(ii) — clean, with two needing strictly more
than bare irreducibility (rationality; the closure clause (CH-4)) and both
supplied.

**One self-correction, recorded because it is the point the duplicate check
(CH-8) itself introduced.** (CH-8) reached the coordinator as a new
incidental claim (a triangle with two adjacent hubs makes the pin infeasible)
and coordinator verification found it **subsumed by a landed,
compiler-checked theorem** — `not_pencilNondegFeasible_of_triangle_two_hubs`
(`Motive.lean:563`, not `Witness.lean`, whose hits are call sites) — in a
**strictly stronger** form (two hubs, arbitrary third vertex, no `hcard`
hypothesis at all). (CH-8) lands as a **pointer, not a claim**; this
direction's own addition there is only the chart-side contrast the landed
theorem does not state — `𝒜(Γ) ≠ ∅` at 174/200 seeds of a triangle-carrying
control while `PencilNondegFeasible` is false there — and the duplicate check
it forced across (CH-1)–(CH-7) found one further partial duplicate:
(CH-6)(i)'s hub-side mechanism runs inline inside the landed theorem's proof,
but only for the **triangle** configuration — the tower's own Λ-**path** case
(`h₁ – x – h₂`, `h₁ ≁ h₂`) is outside the landed theorem's reach, and the
driver carries a witness asserting the graph has **no** two-hub triangle so
the non-duplication is itself driver-tested.

**What did NOT move.** No gap-map status moves: (OC-8), (ANH-R1), (GR-15),
`hK`'s class uniformity, the balance layer and route-ledger entry 5 are
exactly where they were — writing down a consumed fact is insurance, not a
status move. §(K-frame) (FR-7) **stays struck** (not re-opened): (OC-17)
already struck it as unnecessary, and (CH-1) is the chart's irreducibility
that struck it, not a new foothold. Two wording-only cells the coordinator
approved: §(K-out)'s (OC-19) confidence row now reads *"(b) proven,
§(K-chart) (CH-1)"* in place of *"conditional on (b)"*; §(K-frame) (FR-16)'s
rider list gains the girth ≥ 4 correction. Every bar held: no counting /
matroid route was proposed, and (GR-15)/class uniformity/the `g`-detector/the
balance layer were not touched. The TERMINATION check fires nothing: E1 (no
g-flank, no colouring examined), E2 (entry 5 untouched) and E3 (stays ARMED
for YLOC, not fired — (CH-1) is not a ledger entry) are all unchanged.

**Compute.** Three modes, `--empty`/`--guard`/`--fibre` (`--all` runs all
three), ~1 s total, `PYTHONHASHSEED=0`; one driver added, nothing existing
modified, so the figure-invariance gate discharges by that check alone.
Invocation rows landed in `notes/scripts/README.md` §3.

### Not selected, and why — the coordinator's ranking of the losers

Disclosed per the twelfth direction's precedent: **this ranking is the
coordinator's, with no independent top-rung reader.** A future recon may
overturn any of it.

- **(OC-19) input (c), class-uniformly** (`H/X` infinitesimally rigid at one
  chart point, at every class (shape, split, length-4 companion)) — OCON ranked
  it **#1 by value** (*"This is the whole residue"*), and it is deliberately
  **not** dispatched: OCON's own verdict says it is
  **(GR-15)-flavoured, not (FR-R1)-flavoured** — a rank condition inside a
  pattern-colouring existence question — so it re-enters the arc's **oldest
  missing technology** rather than adding an independent idea. It is the natural
  primary once a working chunk-level instrument for input (Y) exists — **YLOC's
  own attempt (twentieth direction) was DEMOTED BY WITNESS, not a success**
  (§"Twentieth direction"); the missing technology is still arriving from the
  other side, just not yet.
- **§(K-out) hand-off item 3** — `T_u^{⊥_B} ∩ β_b = 0` at the **1715**
  slide-legal `b` ends, where **(OC-21) makes it an iff**; measured
  `dim(T_u ∩ β_b) = 1` at 38/38 POOL-W degree-3 ends and 4/4 POOL-OC ones. A
  good, cheap, well-posed target; dropped **only** because ZNEQ already occupies
  §(K-out) this wave and item 3 rides the same measurement infrastructure.
  **Queue it.**
- **§(K-out) hand-off item 4** — the one-hub-neighbour extension of the slide
  ((OC-21)'s second bullet) and its census share. A `--wide`-style leg, **too
  small to be a direction**; fold it into whichever §(K-out) direction runs
  next.
- **(d′)** — the corner-armed realized-binding fully-hot seed hunt past GDEV's
  caps. **E1's own clarification says it is not a flank by itself**, so its best
  outcome is a measurement. Lowest value of the six considered.
- **Route σ's parked Lean half** and **the W4 build** — both **BLOCKED by the
  standing 2026-08-05 Lean hold** (general, not W4-scoped). Not eligible without
  a fresh user adjudication, and **none was sought** at this session's check-in.
- **`Pencil-strategy.md` §4.6's U3** — still unrun, but the shortlist is
  **partially superseded** for the tight stratum (U2 delivered by (GR-16)'s
  reduction, U3's negative-form insight already exploited) and §5.3's own
  local-frame feasibility boundary rules out the symbolic meta-option. Two
  **durable negatives** — do not re-run.

---

## Eighth fan-out — prepared and dispatched 2026-08-19 (directions GTMPL / GFLOW / GCOLL / OSCHU / SIGZ)

Five directions dispatched **concurrently**, each independent, each returning its
own untracked draft (`notes/Pencil-draft-<CODE>.md`) and its own new driver,
landed one at a time by **separate serial coordinator commits**: the seventh
fan-out's shape repeated, the **third consecutive** multidispatch wave.

**User adjudication authorizing the multidispatch.** Asked at the session-start
check-in how the twenty-fifth direction's pick should be made (top-rung recon /
coordinator-authored prep / multidispatch again / a user-named single direction),
the user elected **"Multidispatch fan-out again"** — an **option selection, not
free text** (the GEXIST precedent for how such a pick is recorded), and against a
coordinator recommendation *for* the recon shape. Same check-in: rungs
**`sonnet` + `opus` only, top rung = opus** (fable conserved — `weekly_scoped`
read 92 % at prep, and per the seventh fan-out's settling fact that limit gates
fable alone), cap **lifted**, rescue §1 fixups **pre-authorized**.

**And this check-in DOES move a standing constraint — the first check-in of the
arc to do so since 2026-08-05.** On ZNEQ's carried `σ > 0`-everywhere item the
user elected **"Authorize the hunt"**, whose offered text — accepted as the terms
of the authorization — reads: *"Add it to the dispatchable pool. If it hits, `hK`
is false at those shapes and the phase's target needs redefinition — you would
adjudicate that at the return."* So the item leaves the awaiting-adjudication
pool and becomes direction **SIGZ**, **with the direction-A pivot rule in force**
and with the adjudication moved from *before* the dispatch to *at the return*.
Everything else stands unchanged: phase OPEN, the 2026-08-05 Lean hold, W4
PARKED, `hK`/`hbareSplit` pinned, option B un-commissioned.

**Selection disclosure — the twelfth direction's, for the third consecutive
wave.** The **five directions themselves**, the **tier split** and the **label
reservations** are **coordinator-set**, so there is **no independent top-rung
ranking of the losers** this wave either; a future top-rung recon may overturn
§"Not selected — the eighth fan-out's losers" freely. What is **not** the
coordinator's: every one of the five is a successor **named by a landed
direction's own hand-off** — GTMPL by AGLU's hand-off item 1, GFLOW by BALB's
*Clause A′ sub-clause 2* plus its untried third route, GCOLL by YLOC's
**(GR-64)(R2)**, OSCHU by ZNEQ's input-(a) hand-off item 2, SIGZ by its item 3.
The *candidate pool* is the arc's; only the ranking is the coordinator's.

**Roster** (updated per landing):

| direction | ordinal | tier | owning § | target | status |
|---|---|---|---|---|---|
| **GTMPL** | 25th | compute-licensed | §(K-grid) | AA-glue realizability at `n_hub ≥ 10` — (GR-76)(iv)'s three templates | **LANDED 2026-08-19** — an EXACT BOUNDARY: impossible at every `n_hub ≤ 14`, REALIZED at 16 (§"Twenty-fifth direction") |
| **GFLOW** | 26th | derivation-first | §(K-grid) | (b′)'s availability half — *Clause A′* sub-clause 2, the doubly-blocked case | **DISPATCHED 2026-08-19** |
| **GCOLL** | 27th | compute-licensed | §(K-grid) | **(GR-64)(R2)** — every habitat shape carries an anchor matching with `B(M) = 0` | **DISPATCHED 2026-08-19** |
| **OSCHU** | 28th | derivation-first | §(K-out) | **(a₁)** class-uniformly — the Schubert non-jump `dim(D ∩ M̂ ∧ W) ≤ 1` (+ the (a₂) re-keying leg) | **DISPATCHED 2026-08-19** |
| **SIGZ** | 29th | compute-licensed | §(K-out) | the `σ > 0`-everywhere hunt — newly authorized, **pivot rule in force** | **DISPATCHED 2026-08-19** |

**Shared mechanics: §"Shared mechanics (all three dispatches)" above binds
verbatim**, at five directions, with the seventh fan-out's three deltas
unchanged (drafts to `notes/Pencil-draft-<CODE>.md` untracked, the coordinator
merging and deleting; rung **opus**, top rung this session; each direction runs
the **TERMINATION check (E1/E2/E3)** and reports its reading, the coordinator
re-running it). **E3 stays ARMED** by GBAL's entry-5 HIT and is **not** fired by
any of the five: GCOLL is the only one on the (a′) path and it attacks a
sub-target strictly smaller than (a′), so a HIT there does **not** fire E3 —
say so and do not fire it. **Firing is a coordinator action.**

**On the tier split, recorded honestly.** `RESEARCH-ARC.md`'s *Genuinely
unsettled* item 2 says the compute-licensed / derivation-first split is
**untested** as a predictor of dispatch risk. It is used here for framing
(what instrument a direction reaches for first), not as a rung input — all
five are opus regardless — and this wave is **not** evidence either way.

### Two status cells need a recompute inside this wave, with explicit targets

`RESEARCH-ARC.md` §6's refinement — *a cap bounds growth but cannot express
purpose; dispatch a recompute with an explicit target that leaves headroom for
landings already queued into that row* — applies to this wave before its first
landing, because two rows are carrying three and two queued landings against
thin headroom. Measured at prep (`notes/check-gapmap-cells.py`, full table, all
27 rows within cap):

- **§(K-grid)**: status **1706 / 2035** words — **329 free against three
  queued landings** (GTMPL, GFLOW, GCOLL). **The wave's FIRST §(K-grid)
  landing recomputes the status cell to `≤ 1550` words** before adding its own
  content, leaving ≥ 485 for the three. **Do not bump the cap** — the cap is
  bumped only after an honest recompute, per the script's own docstring rule.
- **§(K-out)**: status **649 / 800** words — **151 free against two queued
  landings** (OSCHU, SIGZ). **The wave's FIRST §(K-out) landing recomputes to
  `≤ 560` words**, leaving ≥ 240 for the two. ZNEQ recomputed this cell
  790 → 649 one landing ago, so the target is deliberately a modest trim, not
  a second aggressive compression.

Both recomputes **verify label preservation by a scripted set-diff, never by
eye** (§6's other clause — a coordinator hand-recompute once dropped a live
label and only a script caught it).

### GTMPL — twenty-fifth direction (eighth fan-out)

**Status: LANDED 2026-08-19 — BOTH dispatched outcomes fired, on different strata.** First of the eighth fan-out's five to land. §(K-grid) **extended**, **Steps G98–G103**, labels **(GR-79)–(GR-84) CLAIMED EXACTLY** — nothing returned to the tail. Driver **`notes/scripts/w4/gtmpl.py`** (eight modes `--charge`/`--frame`/`--tpl`/`--min`/`--wit`/`--e1`/`--lam`/`--val`, ~352 s total, each inside the 600 s foreground budget with no split needed; all eight re-run by the coordinator at landing, every quoted figure reproduced).

**The verdict.** The dispatched three-template question is **NOT realizable**, by two new `n`-free charges each of which kills all three independently: **(GR-80)** the corner charge `n_3 ≥ 2n_2 + 2q_T` (a factor-3 strengthening of (GR-74)(iii), and a **third** independent proof of (GR-75)(i)) and **(GR-81)** the X charge `|X| ≥ n_2 + 2q_T`, resting on a universal dart identity that pins `#{B-darts at X}` **exactly** — of which **(GR-76)(i) is the `≥ 0` instance**, so this is precisely the ingredient AGLU's own *What would change this* named as unexploited. **(GR-82)** chains them to the `n`-free `n_hub ≥ 4(n_2 + q_T) ≥ 16`, killing `n_hub = 10, 12, 14` as well — **a finite bound, not a contradiction, so attack (c) does NOT close outright**, the distinction the spec asked to be precise about. And **(GR-83)** shows the bound is **EXACT**: a constructed `n_hub = 16` witness, habitat-gated by (GR-25), admissible by the canonical predicate, all three charges tight, rank-certified twice over — at which **the (GR-38) kill FAILS** (proper 22-branch union of defect 4). **(GR-84)** measures what else goes: the **whole** kill residual is inhabited there and **(GR-75)(iii)'s maximal-family uncrossing does not reach `n_hub = 16`** — all three maximal binding pairs cross — which costs the charge apparatus an **organizational** tool but no ledger entry its dispatchable state. **No pool was ever built**: the spec's cost-check-first instruction was followed and the template-restricted route needed none.

**Three coordinator adjudications on landing.** *(1)* **The spec's own dichotomy was defective and the correction is right.** It asked, on the realizable branch, *"whether it is fully-good"* — but a binding chunk **is** a `g ≥ 1` obstruction, so a realized AA-glue can never sit at a fully-good colouring: the case is **empty**, not weaker. The meaningful question is E1 (does the witness *shape* still carry a fully-good colouring?), and it does — the first of its 123 740. This is the **second** consecutive wave in which a coordinator-authored spec clause needed correcting by the direction it primed (ZNEQ's `(K-tight)`-vs-PENCIL-event wording was the first), and it is inherited from AGLU's spec verbatim, which is how it survived a re-read. *(2)* **(GR-76)(iii) is SUPERSEDED, not refuted** — its proof is independent and stands; a one-line forward pointer is added at *Step G95* rather than editing it, the arc's practice for a superseded-not-refuted bound. *(3)* **The sibling-import call was the coordinator's to make and is recorded, not defaulted:** `gtmpl.py` imports seven read-only devices from `aglu.py`, none catalogued in `notes/scripts/README.md` §1 — in policy as the documented sibling-import pattern, but tripping §2 rule 2's move-down trigger, so a new dated **UNPAID** debt item is recorded there on ZNEQ's `ocon.meet` precedent.

**Cap disclosure, verified at landing.** No cap is exhausted anywhere and no negative rests on one: (GR-82) is a proof plus an exhaustive walk of a **finite** parameter box, `--min`'s `n_hub ≤ 40` is a display window over a bound proven for all `n`, and no `n_hub = 10` or `16` stratum was enumerated or claimed. (GR-83) is **one constructed witness** plus a 30-member family, not a census; **(GR-84)'s counts are at ONE colouring of ONE shape and must never be quoted as an `n_hub = 16` rate**; `--val`'s `n_hub = 8` chunk-enumerator check is a seeded 6-of-20 subsample. The witness's habitat rests on the (GR-25) oracle, `kslide.no_rigid_branch_union` being a `2^M` scan out of reach at `M = 24` — **the same dependency AGLU's exhaustive `n_hub = 8` scan already has**, cross-checked by three of `gridcol.class_shape`'s four conjuncts run directly.

**TERMINATION: E1, E2, E3 all NO** — coordinator-re-run and agreed. E1: the witness shape carries a fully-good colouring, so no g-flank; binding chunks at one colouring are not flanks ((GR-77)'s distinction). E2: the target is **settled**, not unprovable, and narrows with a named successor; (a′)/(b′)/(d′) untouched. E3: GTMPL is on the §(GR-38) path, not (a′) — **stays ARMED by GBAL, not fired.**

**What did NOT move.** **(GR-15) OPEN**, unchanged in both directions; **no gap-map status move on `hK`**; class uniformity untouched; the one rank computed is a single witness's `dim Z`, not a per-shape (GR-15) claim. §(K-grid)'s gap-map status cell was **RECOMPUTED** (1706 → 1730 words while absorbing six new labels, i.e. the pre-existing content compressed ~13%) rather than bumped, with label preservation verified by a **scripted set-diff** — 79 labels in, 85 out, zero dropped; the cap stays 2035, leaving 305 words for GFLOW and GCOLL. AGLU's hand-off item 2 was **not** attempted (it needs a stratum); the datum added is that `(0,1)`/`(1,0)` occur at `n_hub = 16`, so a `= 2` law would be `n_hub = 8`-specific.

**The target — AA-glue realizability at `n_hub ≥ 10`, ledger attack (c)'s only
surviving case**, verbatim from AGLU's hand-off item 1: by **(GR-76)(iv)** the
only possible profiles are `(|F₁|, |F₂|, |W|) ∈ {(4,0,1), (2,1,2), (0,2,3)}`
with `(n_2, n_3, |X|) = (4,4,2)`, `|T| = 10`, `q_T ≤ 1`. **This is a
three-template question, not a search.** The counting side is **satisfiable**
there (a worked profile in §(K-grid) *Step G95*), so what must be added is the
**colouring** side: the 2-1 dart pattern at each of the two `X` hubs, the
mono-hub ban, and the (GR-25) cut criterion.

**Why now.** AGLU settled `n_hub = 8` **negative as a non-vacuous theorem** and
(GR-76) is an `n`-free charge that already forces `n_hub ≥ 10` with no pinning.
Attack (c) is therefore one stratum from being closed outright, and (GR-76)(iv)
is the arc's sharpest specification of a remaining case: **three templates,
enumerated, with the counting already discharged.**

**Method, and the cost check that comes FIRST.** AGLU's hand-off is explicit:
*"Estimated cost is the one thing to check first — the `n_hub = 10` labelled
enumeration is ~50× the `n_hub = 8` one, so the canonicalizer, not the scan, is
the bottleneck. A `--pin`-style colouring-free pass restricted to the three
templates avoids the pool entirely and is the cheap route."* Take that route
first. `aglu.py` is `n`-generic apart from the pool (`cubic_iso_classes(8)` →
`(10)`, `excess_profiles(12,6)` → `(15,6)` runs the same three modes), but do
**not** launch the full pool scan before the template-restricted pass has said
what it can. Use the landed oracles, not new ones: **(GR-25)**'s `2^{n_hub}` cut
criterion as the `D = 0` membership oracle, `cflank.cubic_habitat` as the habitat
gate, `cflank.admissible` for colouring acceptance, **(GR-42)**'s polynomial
habitat-membership criterion where a shortcut is wanted.

**The two outcomes, and what each buys — both are wins, say which you got.**

- **NOT realizable at `n_hub = 10`** ⟹ attack (c) closes at `n_hub ≤ 10`, and
  if the argument is `n`-free (as (GR-76)(iii) was) **attack (c) closes
  outright**. State explicitly which of the two you got: an `n = 10`-specific
  kill and an `n`-free kill are very different results.
- **Realizable** ⟹ the (GR-38) kill has a **real case** at last. Name the
  witness exactly, **rank-certify** it, say which of the three templates it
  realizes, and check whether it is fully-good (a realized AA-glue that is
  still fully-good is a much weaker event than one that is not).

**Cap disclosure is mandatory** and is the standing hazard on this leg: an
exhausted cap is **not** a proof of nonexistence. If any leg is capped the
return says **"not found under cap C"**. AGLU's own `n_hub ≥ 10` line is the
model — *"OPEN with no search run there and no cap exhausted"* — and LTWO's
"4 of 8 patterns" correction is the precedent for what a silently-capped leg
costs.

**Bars.** Do **not** re-run the `n_hub = 8` scan — (GR-75) is **exhaustive and
uncapped** over the complete stratum (39 689 shapes, 9 617 854 admissible
colourings, 0 instances) and reproduces (GR-38)'s `n ≤ 6` headline exactly.
Do **not** re-derive (GR-74)'s template classification at `n_hub = 8`
(exhaustive, colouring-free, all 44 premise-satisfying pairs of all 20
classes). Do **not** re-open (GR-28)(iv)'s `g ≤ 1` cap — **REFUTED with an
exact boundary**; its `n_hub = 8` witnesses are available as **constructions to
reuse**, which is the one thing to take from it. Do **not** attack **(d′)** (the
corner-armed realized-binding fully-hot seed hunt) — not this direction, and
E1's own clarification says it is not a flank by itself. AGLU's hand-off item 2
(the `(slack, defect(T)) = (0,2)/(1,1)` tightness) is **available as a
secondary** if the primary closes early; report it as a by-product, do not let
it displace the primary.

**Riders, verbatim.** Everything at `Λ = ∅`, `D = 0`, and **modulo (GR-4′)**
wherever (GR-15) is mentioned; `Λ ≠ ∅` and `D > 0` stay **unswept**. **None of
this closes (GR-15)**, and a counting-side result is not an `hK` status move.
Every obstruction figure carries its **family qualifier** — (GR-36)'s
binding-capable family strictly contains the capacity-tight one, and (GR-40)'s
815 → 573 is a **prune, not a zero**. **(GR-77) stands:** outright binding
laminarity is FALSE at `n_hub = 8` (3 774 crossing pairs), so do not quote
(GR-75) as laminarity — it buys the **uncrossing** of the **maximal** binding
family per block, nothing more.

**Reservation.** §(K-grid) **extends**; labels **(GR-79)–(GR-84)**, **Steps
G98–G103**; driver **`notes/scripts/w4/gtmpl.py`**. The owning section stays
authoritative. Consume fewer than reserved ⇒ **return the remainder to the
tail** in the landing commit.

### GFLOW — twenty-sixth direction (eighth fan-out)

**The target — (b′)'s availability half: *Clause A′*, sub-clause 2, the
doubly-blocked case.** Clause A′ verbatim as BALB landed it: *at every
unbalanced parity-optimal configuration there is a legal flip set `F` with
`z + χ_F` balanced and `|W(F) ∖ S| − |W(F) ∩ S| ≤ 2`.* Sub-clause 1 (the
one-end-blocked case) is **nearly done** — the mixed-pair mechanism prices it at
the unblocked T1's price because an `M`-branch is free, leaving only the far-end
side condition `m(w_β) ≠ β` for at least one of the two available `β`, *"a
short, bounded derivation"* that covers **every** stuck witness BALB found
(48/48 at `n = 8`, cheapest price 0). **Sub-clause 2 is the real residual:**
(GR-48)'s named kill, realized at `n = 30`, where the chain must be followed at
both ends, `t(F) = 2`, and (GR-68) gives only `≤ 4` unless both extra endpoints
land on deviating hubs.

**The two routes BALB names, in its order.**

1. **What would close it directly:** *a proof that at a parity-optimal
   configuration the second chain's endpoint is forced onto `S`.* (GR-68)'s own
   minimality corollary is the named input — optimality already forbids
   `Δdist < 0`, hence constrains where dart-free `F`-branches can sit.
2. **The untried alternative, and the reason this direction is
   derivation-first:** minimizing `dist(·, M)` over admissible `z` at a *fixed*
   balanced pattern is, by **(GR-50)**, a **minimum-cost degree-constrained
   orientation** — a min-cost flow, hence polynomial. Per-matching (b′) is then
   an **exchange statement between two such flow problems** (pattern-free vs
   pattern-fixed), and **flow theory's exchange machinery is untried on this
   arc.** This is the first genuinely new instrument offered to the balance
   layer since (GR-50); if it works it is worth more than the direct route,
   because an exchange argument is `n`-free by construction.

**Finish sub-clause 1 first, and say so separately.** It is a bounded
derivation, it is a *theorem* the arc does not yet have, and landing it makes the
residual exactly one clause. Do not fold it into the sub-clause-2 write-up.

**What counts as a HIT** — a proof of Clause A′ (hence, with (GR-70)(i), of
**per-matching (b′)**). Also valued, on the (GR-29)/(GR-30) precedent: a proof
of a **different constant with the exact boundary named**, or a **witness at
per-matching gap 4** (never 3 — **(GR-67) Cor. 1**'s parity law makes every
per-matching layer gap **even**), which moves (b′) to refuted-with-successor.
State which of the three you got.

**Bars.** Entry 5 is **PROVEN** ((GR-54)) — do not re-attack it. Do **not**
re-run BALB's stratum verification — **(GR-70)(ii)** is EXHAUSTIVE and uncapped
(4780 shapes, 23 939 (shape, matching) pairs, all 96 930 unbalanced
parity-optimal configurations, full `3^n` censuses). Do **not** re-derive
(GR-68)'s move pricing or (GR-67)'s parity law — landed, and they are your
inputs. Do **not** re-open the bounded-deviation **selection** form
(**REFUTED as posed**, (GR-41)+(GR-42): `d(NK(m)) ≥ m/2` unbounded while every
member stays fully-good) — (b′) is a statement about the **gap between two
layers**, and the necklaces are a test bed for it, not a refutation of it. Do
**not** attempt the `|δ| ≤ 2` half: **(GR-69)** settled it — a theorem at
`n_hub ≤ 6`, **FALSE from `n_hub = 8`** at the Wagner shape **V8** — and E1
clause (v) does **not** fire on those witnesses (they are not parity-optimal).
**(GR-64)(R2) / input (Y) is GCOLL's target this wave** — report any
(Y)-relevant by-product as a finding and **do not develop it** (YLOC/BALB's
mutual precedent).

**Riders, verbatim.** As GTMPL's, plus: the **shift-metric layer is UNBOUNDED**
((GR-43), `d_par = d_adm = d_fg = m` exactly at the necklaces), so (b′) must be
stated as a bound on the **difference**, never on `d_adm`, and any figure
quoting a necklace member carries that qualifier. **Disclose the table cap:**
BALB's necklace leg stops at `m = 6` because `gadm.dp_pref`'s table is `2^dim`
(`assert dim ≤ 18`), and **GBAL's `n = 40..60` reach does not transfer** —
(GR-54) needs only balance *existence* (polynomial by (GR-50)) whereas any (b′)
statement needs `d_par(M)`, the exponential object. An exhausted table is not
`∞`.

**Reservation.** §(K-grid) **extends**; labels **(GR-85)–(GR-90)**, **Steps
G104–G109**; driver **`notes/scripts/w4/gflow.py`**. Owning section stays
authoritative; return any unconsumed remainder to the tail.

### GCOLL — twenty-seventh direction (eighth fan-out)

**The target — (GR-64)(R2), verbatim as YLOC named it:** *"every habitat shape
carries an anchor matching `M` with `B(M) = 0`"* — **measured at all 4924
inventory shapes, open as a theorem.** YLOC called it *the sharpest cheap
successor the pass produced*, and stated exactly what it buys: **it would prove
the collision mechanism can never obstruct (a′)**, and it is *"a statement about
matchings and small-boundary hub sets alone: no colouring, no rank, no deviation
ladder."*

**Why now.** (a′) is entry 1's only remaining attack and **the only thing
between the arc and E3**, and YLOC's localization failure ((GR-62): full
goodness is not a function of the (GR-50) degree data) leaves the arc without a
chunk-level instrument. (GR-64)(R2) is the one sub-target on that path that is
**strictly smaller than (Y)**, colouring-free and rank-free — the cheapest
genuine progress toward (a′) currently on the board.

**Method.** The statistic is landed: `pack_bound` is (GR-64)'s, `dist_of` /
`fit_M` are (GR-65)'s, and `yloc.py --coll` asserts (GR-64)(i)–(v) at
**209 432 030** (shape, `z`, matching, proper chunk) instances with **3 449 374**
tight. The question is a **proof**, not a bigger sweep: the object is a matching
and the small-boundary hub sets, so the natural attacks are (a) an exchange
argument on the anchor matching (swap along an alternating cycle and show the
collision term cannot rise at every chunk simultaneously), (b) the parity
constraint **(GR-64)(v)** `coll_M(S) ≡ |W_S| (mod 2)`, and (c) the **ceiling
profile** — the per-chunk term reaches its proven maximum 2 **only** at
`(z, exc) ∈ {(3,1), (4,0)}` with `coll = z` — which is a very thin extremal
family to rule out at a well-chosen `M`.

**The second, cruder deliverable, if the theorem resists: (GR-64)(R1)** — the
large-`n` extension of the collision sweep as a **bounded-boundary enumeration**
rather than a `2^M` scan. That converts the measurement from
"exhaustive at `n_hub ≤ 6` plus four named shapes" into a statement with real
reach, and it is a compute question, not a new idea. **Say which you delivered.**

**What counts as a HIT** — a proof of (GR-64)(R2) at every habitat shape.
Also valued: a **witness shape with `B(M) ≥ 1` at every matching**, which per
YLOC's own reading turns (GR-64) into *"a genuine floor on `d_fg`"* — a
strictly informative refutation, not a failure. **A HIT here does NOT fire
E3**: (R2) is a sub-target of (Y), not (a′) itself. State the consequence for
(a′) precisely and **do not fire E3**.

**Bars.** **(b′) / Clause A′ is GFLOW's target this wave** — report any
(b′)-relevant by-product as a finding and **do not develop it**. Do **not**
re-attack (a′)'s **per-matching** variant — **REFUTED** ((GR-59): `min_M` is
load-bearing, 1278 of 24 638 pairs, so no (a′) proof may fix its anchor
matching); note the tension and use it, since (R2) is precisely a statement
about the **existence** of a good anchor, not about fixing one. Do **not**
re-run the bounded {T1, T2} descent (**DEMOTED by witness**, (GR-48)(iii)) or
(GR-58)'s census (landed **exhaustive** at `n_hub ≤ 6`, no cap). Do **not**
re-attempt the (GR-51)-shaped chunk criterion — **(GR-62) refutes it by
witness** (7982 of 217 468 fibres, at 1499/4924 shapes, smallest witness
rank-certified at `n_hub = 4`); the refutation is scoped to a
*(GR-51)-shaped* criterion only, and that scope is **not** an invitation to
re-run it.

**Riders, verbatim.** As GTMPL's. Additionally: **(GR-64)(iii)'s prune is
sound but INCOMPLETE** (1250 of 24 671 killed, incompleteness **7856**) — both
numbers travel with any figure derived from it, and **disjointness is
load-bearing** (the naive sum is unsound against a realized fully-good
distance). **(GR-65)'s fit identity is the bridge** — `dist(m, M)` and
`z_mono(S)` are the **same statistic** — and it is a landed input, not
something to re-derive.

**Reservation.** §(K-grid) **extends**; labels **(GR-91)–(GR-96)**, **Steps
G110–G115**; driver **`notes/scripts/w4/gcoll.py`**. Owning section stays
authoritative; return any unconsumed remainder to the tail.

### OSCHU — twenty-eighth direction (eighth fan-out)

**The target — (a₁) class-uniformly**, verbatim from ZNEQ's input-(a) hand-off:
*at some pencil chart point where `H = G − v − a` has independent rows,
`D = {m(b) − m(c) : m ∈ Mot(H)}` contains **no** pencil `M̂ ∧ w` with `w` on the
line `pt(b) pt(c)`* — equivalently the **Schubert non-jump**
`dim(D ∩ (M̂ ∧ W)) ≤ 1`, with `D` the far framework `H`'s relative twist space
and `W` the hub line's 2-space. **One condition, `x₁`-free, `λ`-free,
stratum-free, one-point decidable.** Measured to fail **nowhere** (GCD degree 0
and `dim(D ∩ M̂ ∧ W) = 1` at 32/32 POOL-ZF frames). **A recipe is what is
missing** — exactly as for (OC-19) input (c).

**The route to try FIRST, from the same hand-off.** `D` is the relative twist
space of `H` with **no** hinge deleted and **no** weld, so §(K-out) **(OC-18)**'s
`H/X`-rigidity criterion and `D` are **near neighbours**: `H/X` rigid forces
`W₁ = 0`, and `D` is the un-welded analogue. **Second:** `D` depends only on the
`H`-part, so **(OC-28)(i)** makes this too a statement about `G`'s **own** chart
— which is what would make it class-uniform rather than per-split.

**Why now, and why this rather than (OC-19) input (c).** Input (c) is OCON's #1
by value but is **(GR-15)-flavoured** — a rank condition inside a
pattern-colouring existence question — so it re-enters the arc's oldest missing
technology. (a₁) is the *same object class* ((OC-20)'s perp form, a
subspace-meets-subspace count in `Λ²K⁴`) with **no colouring quantifier**, and
after ZNEQ it is the **only** half of input (a) that can be the binding
obstruction: the `s₀` half is **necessary for `hK`** and therefore
**dominated** ((OC-24), (OC-28)).

**The cheap secondary leg, folded in deliberately: the (a₂) cross-pool
re-keying.** By **(OC-28)(iii)** the `s₀` half is implied by §(K-grid)
**(GR-10)** and free at **907/907** of that pool, so the cheapest genuine
progress there *"is **not** a new argument but a re-keying: check that every
§(K-out) class shape carrying a length-4 companion is in §(K-grid)'s certified
set (the two pools are keyed differently, (OC-28)(a))"* — **a combinatorial job
with no new mathematics**, and the transfer itself is already **machinery**
(`zneq --transfer` turns any target-rank chart point of `G` into a
guard-accepted point of `Z` on every eligible split's `G′`-chart, 30/30). Run
it, and state plainly that the result stays **CONDITIONAL** on (GR-10), which
is itself **OPEN** (its min-max form refuted as posed, the statement standing).
§(K-out) hand-off item 4 — the one-hub-neighbour extension of the slide,
(OC-21)'s second bullet, *"a cheap `--wide`-style leg, too small to be a
direction"* — may be folded in as a third leg if budget allows; it is the
lowest priority of the three.

**What counts as a HIT** — a class-uniform proof of (a₁) (with the (a₂) leg,
that is input (a) reduced to (GR-10) alone). Also valued: a **shape where the
non-jump fails**, which per (OC-25)/(OC-26) is a **(K-tight) event** at that
split — routes A and B dead there, `hK` at the shape **untouched** — and which
must be reported as such and **not** as a PENCIL event. Getting that distinction
right is load-bearing: ZNEQ's own spec was corrected on exactly this point.

**Bars.** Do **not** re-derive **chart irreducibility** — §(K-chart)
**(CH-1)(a)** is PROVEN, unconditional at `Γ = G′`; **cite** it. Do **not**
attack **(OC-19) input (c)** (`H/X` rigid class-uniformly) — OCON's verdict
stands and it is deliberately not this wave's. Do **not** pursue any
**counting / matroid route to (OUT)'s hypothesis** — **(OC-3)** refutes the
whole class (`{λ₁ = 0}` is nonempty at every class shape's chart). Do **not**
push a constructed point to `p⁺` (§(K-out) *What would change this* item 4),
the coupled two-end slide (item 5), or any §(K-frame) *What would change this*
item (ii)–(iv). Do **not** re-run (OC-27)'s witness census (138/138, caps
disclosed). **The `σ > 0` hunt is SIGZ's target this wave** — if a by-product
bears on it, report it as a finding and **do not develop it**.

**Riders, verbatim.** The standing **(OC-7) rule**: no `place_pencil_general`
battery may be quoted as a **rate** or as evidence about a **generic** chart
point; POOL-G figures are quoted over the **318 coincidence-free** frames,
never the raw 357. **POOL-G and POOL-S are pinned and disjoint** — not
aggregated, not re-sampled. Any census this direction runs reports **witnesses,
never a rate**, with caps disclosed. **`Z ≠ ∅` alone does NOT give (OC-8)**:
the reduction needs openness **plus** irreducibility **plus** a witness, and
`--control`'s three constructed points in `Z` with `L_b ⊆ R₁` are why.

**Harness debt, carried in and payable here if convenient.** `ocon.meet` (the
dimension-asserting wrapper of `lambda.span_meet`) now has **two** consumers,
tripping `notes/scripts/README.md` §2 rule 2's move-down trigger — a dated
**unpaid** debt item recorded by ZNEQ. This direction is the natural third
consumer; if it uses `ocon.meet`, say so and either pay the debt or re-date it.

**Reservation.** §(K-out) **extends**; labels **(OC-29)–(OC-34)**, **Steps
O25–O30**; driver **`notes/scripts/w4/oschu.py`**. Owning section stays
authoritative; return any unconsumed remainder to the tail. **Two directions
share §(K-out) this wave** (OSCHU and SIGZ) — the protection is the **disjoint
reserved range**, not the section, exactly as three directions shared §(K-grid)
at the sixth and seventh fan-outs.

### SIGZ — twenty-ninth direction (eighth fan-out)

**Newly authorized this session, and the arc's first authorized DISPROOF
direction.** It is ZNEQ's input-(a) hand-off item 3, held out of the
dispatchable pool since 2026-08-19 pending adjudication, released by the
user's **"Authorize the hunt"** selection at this session's check-in on the
terms quoted in this fan-out's header. **The direction-A pivot rule is in
force**, verbatim: *"If half 2 fails at any shape, **stop and report
immediately**: the phase's target theorem would be false … That is a
phase-redefining event for the user to adjudicate, not a result to build on."*
Read for this direction: **a hit is reported and NOT built on.**

**The target.** By **(OC-23)**, `s₀ = corank R(H)` at **every** legal chart
point, so `{σ = 0}` is the locus where the far framework `H = G − v − a` has
independent rows. By **(OC-24)**, **`{σ = 0} = ∅` at a class shape makes `hK`
FALSE there** (`E(H) ⊆ E(G)`, `G` tight with `def(G) = 0`, so a self-stress of
`H` at every chart point is a self-stress of `G` blocking its own Tay target).
The hunt: **is there a class shape — inside `hK`'s habitat — at which
`σ > 0` everywhere?** The only known failure mechanism is a **self-stress of a
short theta sub-multigraph inside `H`** (§(K-flank) *F5(d)*: at `P21`, 5 of 35
valid seeds, support the theta `{12, 13, 23a, 23b}`, **12 edges, line rank 6**,
forcing `dim R_a = 0`).

**The obstruction the hunt must confront head-on, and why this direction has
two valuable outcomes rather than one.** `P21` **fails `hnoRigid`** — it is a
**(K-res) residual, not a tight class member** — so *Step O24*'s only recorded
mechanism sits **outside** `hK`'s habitat. And the gap map's `P21` row records
more than that: **(S5)'s `(3,3)` row-dependence mechanism is proven impossible
inside tight + `hnoRigid`**, because `C_k` rigid for `k ≤ 6` forces
`ℓ₁ + ℓ₂ ≥ 7`. So:

- **A HIT** — a class shape (tight, `def(G) = 0`, `hnoRigid`) with
  `{σ = 0} = ∅` — is a **PENCIL event**: `hK` is FALSE there, the phase's
  target needs restating, and the return **stops** at that and reports. Name
  the shape, the split, the stress support, its line rank, and **rank-certify**
  it; then stop. Do **not** develop consequences, do **not** re-plan the arc,
  do **not** touch any gap-map status.
- **A PROOF THAT THE MECHANISM CANNOT OCCUR inside tight + `hnoRigid`** —
  i.e. pushing the `ℓ₁ + ℓ₂ ≥ 7` bound (or its theta-multigraph generalization)
  to exclude *every* `H`-supported theta stress at a class shape — makes
  **(a₂) free at class shapes unconditionally**, which is **strictly stronger
  than (OC-28)'s conditional reduction** (that one is conditional on (GR-10),
  itself open). **Say which of the two you got**, and if neither, say exactly
  which theta lengths remain uncovered.

**Method.** Exact ℚ throughout; the object is a self-stress space, so a
**rank/corank assert on every sampled framework** is mandatory (the
`plane_basis` precedent — a degenerate sampler silently contaminated several
passes' recorded escape-failure figures). Enumerate class shapes by the theta
sub-multigraphs their `H` can carry rather than by sampling seeds blindly: the
theta's branch-length triple is the natural index, `ℓ₁ + ℓ₂ ≥ 7` is the landed
constraint, and §(K-Λ) **(Λ4)**'s branch calculus reduces class membership to a
finite statement about the hub multigraph `G°` alone. `{σ = 0}` is a **proper
open** — witnessed as such at `P21` (5 of 35 valid seeds off it) — so
`{σ = 0} = ∅` is a **closed** condition to certify, never something a finite
sample can establish: a shape where every *sampled* seed has `σ > 0` is
**"not found under cap C"**, not a hit. **State that boundary explicitly in the
return.** A hit needs an argument (or an exhaustive, uncapped chart-level
certificate), not a tally.

**Bars.** Do **not** re-derive §(K-chart) (CH-1)/(CH-2) — landed; cite. Do
**not** work the target-rank half of input (a) — **(a₁) is OSCHU's target this
wave**; report by-products as findings and do not develop them. Do **not** move
any gap-map status: `{σ = 0}`'s row, (OC-8), (GR-15), class uniformity and `hK`
all stay exactly where they are, **whatever this direction finds** — a status
move on a PENCIL event is a user adjudication, not a landing. Do **not** re-run
the `P21` battery (`flanks.py --rzero`, landed: 30/5/5 seeds, `dim U = 1`, 8/8
placements fail).

**Riders, verbatim.** As OSCHU's, plus: every figure is a **witness, never a
rate**, with the cap disclosed; and `P21` figures carry the **`hnoRigid`-false
qualifier** in every sentence that quotes them, because the whole question is
whether the mechanism crosses into the habitat.

**Reservation.** §(K-out) **extends**; labels **(OC-35)–(OC-40)**, **Steps
O31–O36**; driver **`notes/scripts/w4/sigz.py`**. Owning section stays
authoritative; return any unconsumed remainder to the tail.

### Not selected — the eighth fan-out's losers

Disclosed per the twelfth direction's precedent: **this ranking is the
coordinator's, with no independent top-rung reader** (third consecutive wave).
A future recon may overturn any of it.

- **(OC-19) input (c), class-uniformly** — OCON's **#1 by value** and, for the
  second consecutive wave, deliberately **not** dispatched, on OCON's own
  grounds: it is **(GR-15)-flavoured, not (FR-R1)-flavoured**, so it re-enters
  the arc's oldest missing technology rather than adding an independent idea.
  YLOC's chunk-level instrument attempt was **DEMOTED BY WITNESS**
  ((GR-62)), so the technology is still not arriving. **GCOLL is this wave's
  bet on that supply line** — (GR-64)(R2) is the smaller sub-target on the
  same path.
- **§(K-out) hand-off item 3** — `T_u^{⊥_B} ∩ β_b = 0` at the **1715**
  slide-legal `b` ends, where **(OC-21)** makes it an **iff**; measured
  `dim(T_u ∩ β_b) = 1` at 38/38 POOL-W degree-3 ends and 4/4 POOL-OC ones. A
  good, cheap, well-posed target, **queued for the second consecutive wave**
  and dropped for the same reason — §(K-out) already carries two directions
  (OSCHU, SIGZ) and item 3 rides the same measurement infrastructure. **Queue
  it again**, and note that a third §(K-out) direction is the cheapest thing
  on the board once one of this wave's two lands.
- **§(K-out) hand-off item 4** — folded into **OSCHU** as its lowest-priority
  third leg, per the seventh fan-out's own instruction to *"fold it into
  whichever §(K-out) direction runs next."*
- **AGLU hand-off item 2**, the `(slack, defect(T)) = (0,2)/(1,1)` tightness —
  folded into **GTMPL** as an optional secondary. If it is a theorem the
  (GR-38) kill has an exact form (`= 2`, not `≥ 2`) on the candidate family.
- **(d′)** — the corner-armed realized-binding fully-hot seed hunt past GDEV's
  caps. **E1's own clarification says it is not a flank by itself**, so its
  best outcome is a measurement. Lowest value for the third consecutive wave;
  at some point it should either be dispatched cheaply or struck.
- **(GR-64)(R1)** — folded into **GCOLL** as its cruder fallback deliverable.
- **Route σ's parked Lean half** and **the W4 build** — both **BLOCKED by the
  standing 2026-08-05 Lean hold** (general, not W4-scoped). Not eligible
  without a fresh user adjudication, and none was sought at this check-in:
  the check-in's one standing-constraint move was the `σ > 0` hunt, nothing
  else.
- **`Pencil-strategy.md` §4.6's U3** — still unrun; the shortlist is
  **partially superseded** for the tight stratum and §5.3's own local-frame
  feasibility boundary rules out the symbolic meta-option. Two **durable
  negatives** — do not re-run.
