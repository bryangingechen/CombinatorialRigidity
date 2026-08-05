# PENCIL kernel-(K) research fan-out — dispatch specs

**Status: prepared 2026-08-05, not yet dispatched.** Three independent research
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

**Every dispatch carries these, from `notes/scripts/README.md`:** exact ℚ only;
degeneracy guards plus a rank/dimension assert on every sampled object (the
`plane_basis` precedent — a degenerate sampler silently contaminated several
passes' recorded escape-failure figures); seed all randomness; import from the
canonical layer, never reimplement (see the README's *Divergences* table for
the same-name-different-semantics traps).

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
