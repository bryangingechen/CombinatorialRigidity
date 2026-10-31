# Phase 42i — PD-STEPS: open ears with three interior bodies in dimensions four to six (work log)

**Status:** in progress, opened 2026-10-31 at the PI's word ("All 4 nodes as written
(Recommended)", design doc §1), a sub-phase of Phase 42 and the fourth and last of PD-STEPS.
Forward mode, the Lean under `/coordinate-phase`: the four red nodes of
`blueprint/src/chapter/pencil-d.tex`'s `sec:pencil-d-short` for the open ear with three interior
bodies (`-short-three`: `lem:pencil-d-stars-three`, `lem:pencil-d-glued-ends`,
`lem:pencil-d-planes-meet`, `thm:pencil-d-open-ear-three`, the theorem at `4 ≤ d ≤ 6`), on the
`Pencil/Grade/` carrier and 42h's Lean. The open's consistency read found every proof routing
through the argument its statement claims, every outside dependency green, and no `-short-four`
node using one of the four (*Decisions made*). It also found that the factoring's insertion
hypothesis, as landed, may not be dischargeable at three bodies (*Blockers*). Next (*Hand-off*):
the pre-build recon of the four nodes.

## Current state

**Next: the pre-build recon** (*Hand-off*). Opened; no Lean yet. The four targets, leaf-first:
`lem:pencil-d-stars-three` rests on 42h's two-stars and kernel curve; `lem:pencil-d-glued-ends` on
Phase 40's lifting planes, Jackson and Jordán's equality and the merged deficiency, with no `P³`
counterpart; `lem:pencil-d-planes-meet` on 42e's `lem:pencil-d-condition-linear` and the
lifting-planes dimension; `thm:pencil-d-open-ear-three` on those three, on
`thm:pencil-d-open-ear-four` and on 42h's two-stars, insertion and both ear-data lemmas. Every
dependency outside the four is green. The chapter is the lemma index (forward mode).

## Architectural choices made up front

- **Scope** (the PI's, verbatim in design doc §1): the four nodes as the chapter states them, the
  theorem at `4 ≤ d ≤ 6`, though the coverage uses it only at `d = 4`
  (`thm:pencil-d-chain-or-core`). Their close closes PD-STEPS.
- **Encoding** as 42h (`notes/Phase42h.md` *Architectural choices*): `m = d − 2` heights at grade
  `k = m + 1`, so `4 ≤ d ≤ 6` is `2 ≤ m ≤ 4`; annihilators are read on the forms on `⋀²` (42h's
  recon, `fe5baf0f`), no exterior power past `⋀²`.
- **What 42h hands on** (`notes/Phase42h.md` *Hand-off*, each type-checked at its close): the
  factoring `Graph.X0AttainsGrade.of_openEar_splitOff` at `k = 2`, with `splitOff_ear_succAbove`
  at `k = 0`, leaving `G″`'s link and `hins` (whether `hins` can be met is under *Blockers*); the
  dual route for stars-three's last step, `finrank_add_two_le_of_forall_ιMulti_eq_zero` (two-stars
  (3) as landed), with the kernel curve on forms `exists_mvPolynomial_dual_kernel_curve`.
- **The standing rule** (design doc §3): the recon and every build add a row to
  `notes/Cleanup42.md` §2 where their Lean departs from the chapter's proof, in the same commit
  (R-9 to R-12 open, R-7 and R-8 aligned).

## Lemma checklist

- [ ] **Pre-build recon**: the factoring question first, then exact Lean signatures for the four
  nodes, their files, and spikes of the questions under *Blockers*, on 42h's landed Lean.
- [ ] `lem:pencil-d-stars-three`, on 42h's two-stars and kernel curve.
- [ ] `lem:pencil-d-glued-ends`, on Phase 40's planar carrier.
- [ ] `lem:pencil-d-planes-meet`, on 42e's condition-linear lemma.
- [ ] `thm:pencil-d-open-ear-three`, on the other three and 42h's four-body Lean.
- [ ] **Close** 42i, an intermediate sub-phase close that completes PD-STEPS
  (`PHASE-BOUNDARIES.md`).

## Blockers / open questions

- None blocking the recon. Its questions:
  - **The factoring's insertion hypothesis (first).** `of_openEar_splitOff`'s `hins`
    (`Grade/Short.lean`) is quantified over every base datum `(q, z, la, lb)` and every `ρ`. The
    chapter proves the three-body condition only at the base data its first stage picks (`q*` off
    glued-ends' polynomial and off the first coordinate of `q_a − q_b`, `z*` off planes-meet's)
    and, when `r ≤ 2`, only for `G[V₁]`'s own `ρ`. The open's reading, not witnessed in Lean: at
    `m = 2` the base datum `la = lb` puts `p_a`, `y_1`, `y_3` and `p_b` in one 3-space `U`
    (`earConfigGrade` gives `x_f` the heights `la` and `x_l` the heights `lb`). The `ρ` of the
    chapter's remark after stars-three, the joins meeting `U`, has codimension one at `d = 4` and
    contains every join of both ears, so no `x₂` gains a dimension. `hins` then fails at every `q`
    where `G″` has an admissible ear picture. If the reading holds, the theorem needs a factoring
    whose insertion hypothesis is taken at the first stage's base data and `G[V₁]`'s relative
    screws. The recon pins that variant, or refutes the reading, before any build.
  - **Stars-three on forms.** The chapter's proof reads annihilators in `⋀^{d−1}`, with
    `M(y₁, y₃)` on `⋀^{d−3}`; 42h's Lean has neither. Carry it onto forms as stars-four's Lean did
    (`exists_mvPolynomial_starsFour`, `eq_zero_of_starsFour_firstOrder`), on the dual kernel curve
    and the radical bound above. Also: the polynomial's domain `Π_a × Π_b` (through
    `gradeSigma la`, `gradeSigma lb`), the four-independent-points minor at `κ ≤ 1`, and how the
    theorem pulls the polynomial back to the ear data (`lem:pencil-d-ear-data` (3)). Whether the
    chapter proof then follows its Lean, as stars-four's does at the PI's word, goes to the PI or
    the ledger.
  - **Glued-ends**, new planar mathematics. In hand: `Graph.liftingPlanes`,
    `Graph.finrank_liftingPlanes`, `Graph.deficiencyMerged`, Jackson and Jordán's
    `Graph.exists_mvPolynomial_finrank_liftingSpace_eq`. Needed: the graph with `a` and `b`
    identified (`def:rigid-contraction`'s Lean, or a direct one), `Z⁰(q)` as the kernel of a
    polynomial matrix and its minor, the projection `⋀²π` onto `⋀²K³` with
    `lem:pencil-flat-split`'s affine reading, and the statement's quantifier order (`g` before
    `d` and `z`). The node writes `b` both for an end and for the configuration's points, as the
    section's overview does; a build may rename the points.
  - **Planes-meet.** The functionals `λ^i_v` of a height (the inverse of the lifting-planes
    isomorphism), the differences space `E` and its extension along a two-body ear, and the minor
    `R` of `L(z)` as a polynomial on `L_G(q)^{d−2}` (as the fibre-intersection lemma reads one).
  - **Dimensions.** Stars-three needs `d ≥ 4` and `d + κ ≤ 6`, the theorem `2 ≤ m ≤ 4`;
    glued-ends and planes-meet say `d ≥ 3`. Whether their Lean holds at every `m`, as 42e–42h's.
  - **Files.** New `Grade/` file(s), at the recon's choice. A variant of the factoring would edit
    `Grade/Short.lean`, which no deferral targets.

## Hand-off / next phase

The next concrete commit is the **pre-build recon** (a `recon-opus` dispatch, read-only or a
design-pass commit at the coordinator's choice), spiking the four nodes against the carrier on
42h's landed Lean as `fe5baf0f` did for 42h's eight. It settles the factoring question first
(*Blockers*), then pins the exact Lean signatures of the four against the landed `Pencil/Grade/`
API (`Grade/Stars.lean`, `Grade/EarData.lean`, `Grade/Short.lean`) and Phase 40's lifting-planes
and Jackson–Jordán Lean, spikes each under `lake lean`, settles *Blockers*, and records the
signatures here. Then build leaf-first, roughly 3–6 commits by the coordinator's estimate in the
option the PI chose, before any variant of the factoring the recon finds needed. Each build adds
its node's `\lean{}` and `\leanok`.
- **The standing rule** (*Architectural choices*): a row in `notes/Cleanup42.md` §2 per departure.
- **Deferred, where it lands** (design doc §3; FRICTION's `[open]` entries): the home debts of
  42b–42h are unchanged, each riding with the next commit that edits its target file
  (`notes/Phase42h.md` *Hand-off* lists 42h's); `starGrade_smul` moves with the next edit of
  `Grade/Stars.lean`.
- **After 42i:** PD-STEPS is complete. PD-COVERAGE (`-chains`, `-coverage`, 4 red nodes),
  PD-REDUCTION and PD-HEAD open at the PI's word (design doc §3).

## Decisions made during this phase

- **PI, 2026-10-31 (42i's open):** the PI answered "All 4 nodes as written (Recommended)", whose
  option read: "The theorem at 4 ≤ d ≤ 6, as the chapter states it. An Opus open commit, a
  pre-build recon that spikes the four against the carrier on 42h's Lean, then roughly 3–6 builds.
  Closes PD-STEPS." The question as put, the other options and a note on them: design doc §1.
- **The question's wording, checked** (not the PI's text; design doc §1): stars-three's
  environment is 98 lines (2682–2779 at `59ceecee`), not about 430; the range 2683–3111 ran on to
  glued-ends' label, through 42h's green ear-data nodes and four-body theorem. "Leaving only the
  insertion condition" holds at the type level; whether that condition can be met at three bodies
  is the recon's first question (*Blockers*).
- **Consistency read at the open:** all four PASS. Each was read in full against the nodes it
  cites: every proof routes through the argument its statement claims, and no wording needs a
  repair. With every `\uses` list parsed whole, the 30 dependencies outside the four (13
  definitions, 15 lemmas, 2 theorems) are green, proofs too, none superseded. Within the four only
  the theorem uses the other three; outside the section only `thm:pencil-d-coverage` uses the
  theorem; no `-short-four` node uses or cites any of the four.
