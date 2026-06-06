# Phase 22c — Case III at `d=3` (KT Lemma 6.10) (work log)

**Status:** in progress (opened 2026-06-05). **Design-pass-first** —
this phase opens on a *layer-level design recon* of the whole
Case-III-at-`d=3` argument (KT §6.4.1, Lemma 6.10, Claims 6.11/6.12)
against the green Phase-17 Lemma 2.1 and the green Phase-21b/22a/22b
infra, **before** any Lean node-cut or grinding. The opening commit is
**docs-only** (this file + the phase-open surface sync); the Lean
node-cut follows in subsequent commits, once the recon settles what each
piece needs from the shared candidate structure.

Stratum 5 of the molecular-conjecture program, continued: **Track B at
`d=3`** — the Case II/III reducible-vertex producer (KT's *Case III*),
the single largest proof in KT and the conjecture's crux. This is
`theorem_55`'s `hsplit` branch at `k=0`: a `2`-edge-connected minimal
`0`-dof-graph with no proper rigid subgraph and a reducible degree-2
vertex `v`, target full rank `D(|V|−1)`. At `d=3`, `D = (4 choose 2) =
6`.

Forward-mode / **structural-edit** discipline (`blueprint/CLAUDE.md`):
22c opens *no* new blueprint chapter — its target nodes
(`lem:case-II-realization` = KT's Case III, `lem:case-III`) are already
stubbed red in `algebraic-induction/case-ii.tex` / `case-iii.tex`. Lean
lands in `Molecular/AlgebraicInduction/`. The KT math is in
`notes/Phase21b.md` *Finding A/B* + `notes/Phase22-realization-design.md`;
22c **formalizes** it, it does not re-derive it. Cross-cutting rationale:
`DESIGN.md` *Constructibility recon before a producer build → Scale-up:
design the LAYER, not just the node* (the design-pass-first rule this
phase is built around) + *Match the source's argument structure, not
just its conclusion* + *Phase Case-naming vs. KT's k-bookkeeping*.

## Current state

22c is **open and at the design-recon stage**. The opening commit
(docs-only) settles the sub-phase scope cut (below), seeds this file
with the layer-level design-recon plan, and lands a *first recon pass*
that reads the whole Case-III-at-`d=3` argument against the primary
source. **No Lean this commit.** The next concrete commit is the
continuation of the design recon (not a build): trace each piece of KT
Lemma 6.10's argument — the `D` candidate frameworks, the eq. (6.12)
degenerate placement giving `+(D−1)`, Claim 6.11's redundant-`ab`-row
(combinatorial↔linear), Claim 6.12's extensor-span genericity via
Lemma 2.1 — and decide what each needs *from* the shared candidate
structure and *supplies* to the producer node, **before** the first
Lean node lands. The Case-I composer `case_I_realization` is fully green
(Phase 22b) and ready to wire into `theorem_55_generic`'s Case-I branch;
that wiring + the Case-III producer + the `d=3` assembly is the 22c (and
likely 22d) territory.

## Sub-phase scope cut (SETTLED this commit)

The parked "22c+" territory bundled two independent bodies of work; this
phase cuts it as follows.

- **22c = Case III at `d=3` / Track B — THE CRUX (this phase).** KT
  §6.4.1, **Lemma 6.10** at `D = 6` (`d = 3`): the `theorem_55.hsplit`
  producer. Target nodes `lem:case-II-realization` (KT's Case III, the
  eq. (6.12) `+(D−1)` degenerate placement) and `lem:case-III` (the
  missing row via the `D`-candidate-frameworks argument, Claims
  6.11/6.12). Bottoms out on the green Phase-17 Lemma 2.1
  (`omitTwoExtensor_linearIndependent`); reuses the green Phase-21b row
  infra (N7b-0/1/2/3, N7a, `linearIndependent_sum_pinned_block`) + the
  Phase-22b Claim-6.4 bricks.

- **22d (LIKELY further cut, DEFERRED until 22c's shape is clear) = the
  `d=3` assembly.** The genericity-free `hub` partition brick of
  `prop:rigidity-matrix-prop11` (a Phase-19-partition obligation,
  Track-independent, itself multi-commit — decompose math-first before
  scheduling) + the `thm:theorem-55` flip (one-line once the three case
  producers land) + wiring `case_I_realization` into
  `theorem_55_generic`'s Case-I branch. The finer 22c/22d cut is
  deferred exactly as 22a deferred the 22b+ cut and 22b deferred the
  22c+ cut: name the *next* distinct sub-phase, do not pre-commit its
  internal node list before its shape is clear. **General-`d` (Lemma
  6.13) → Thm 5.5 → Thm 5.6 → Conjecture 1.2 stays Phase 23** (integer
  phase numbers 23–26 unchanged).

Rationale: each sub-letter names *one* distinct sub-phase (the
discipline that renamed 22b+ → 22c+). 22c is the crux producer; the
assembly is a separable downstream concern that should not share its
label. Whether the assembly is a true 22d or folds into 22c's tail is a
contact decision deferred to when 22c closes.

## The design-recon plan (this phase's organizing principle)

**Why design-pass-first.** Case I (Track A) burned ~10 incremental
node-by-node commits before a one-commit *layer* design pass surfaced
the binding gap — a too-weak shared induction motive, invisible to every
per-node arithmetic recon (`DESIGN.md` *Scale-up: design the LAYER, not
just the node*). Case III is *more* research-shaped and *more*
interlocking (three candidate frameworks + Claim 6.11 wiring the row
matroid to `M(G̃_v^{ab})` + Claim 6.12's extensor-span genericity, all
sharing one candidate structure), and is the single largest proof in KT
(~12 pages). Do not repeat the Case-I node-by-node-then-wall pattern:
**design the layer first.** The recon answers, for each piece of Lemma
6.10, "what does it need *from* the shared candidate structure and what
does it *supply* to the producer node", before any Lean node is cut.

The recon runs in `notes/Phase22-realization-design.md` (the running
design doc, §1.x continuation) and is summarized here. It proceeds:

1. **Read the whole Lemma 6.10 argument end-to-end** against KT §6.4.1
   (pdf pp. 34–45) — the `D = 6` candidate frameworks
   `(G,p₁),(G,p₂),(G,p₃)`, the degenerate eq. (6.12) placement, Claim
   6.11, Claim 6.12 — *and* against the green Lemma 2.1 it bottoms out
   on. (First pass: this commit, below.)
2. **Identify the shared candidate structure** — what data parametrizes
   a "candidate", what is common across all `D` of them, and what the
   degree-2 condition forces (KT eq. (6.44): all candidates test the
   *same* `r ∈ ℝ^D`).
3. **Map each piece to what it needs / supplies** — Claim 6.11 needs the
   IH + Lemma 4.3(ii) and supplies the redundant-row fact; Claim 6.12
   needs Lemma 2.1 and supplies "some candidate is full rank"; the
   eq. (6.12) placement needs the green row infra and supplies `+(D−1)`.
4. **Decide the abstraction** — KT repeats the row-ops three times (one
   per candidate); consider a "candidate normal form" lemma so the
   per-candidate work is stated once (KT's own suggestion-shaped
   structure). Decide *before* cutting nodes whether the formalization
   abstracts the candidate or inlines three copies.
5. **Only then cut the Lean nodes** and order them (leaf-most-buildable
   first, the device/Lemma-2.1 bottoming-out node identified).

## First design-recon pass (this commit) — the Case-III-at-`d=3` shape

Read against KT §6.4.1 (verified in the primary source PDF, pp. 34–45):

- **Target (Lemma 6.10).** `G` a 2-edge-connected minimal 0-dof-graph,
  `|V| ≥ 3`, *no* proper rigid subgraph, (6.1) holds ⟹ a *nonparallel*
  panel-hinge realization `(G,p)` in 3-space with `rank R(G,p) =
  6(|V|−1)` (full; `D = 6` at `d=3`). This is the `theorem_55.hsplit`
  branch at `k=0`.

- **The one-row shortfall (the reason this is Case III, not Case II).**
  A *single* candidate, KT's eq. (6.12) degenerate placement `p₁`
  (`p₁(va) = L ⊂ Π_q(a)` a `(d−2)`-hinge, `p₁(vb) = q(ab)` placing the
  `vb`-hinge at the very `e₀ = ab` hinge of the IH realization `q`, so
  the `vb`-row *reproduces* the `e₀`-row), gives via column ops a
  block-triangular `R(G,p₁)` with `R(G_v^{ab},q)` a submatrix, hence
  `rank R(G,p₁) ≥ (D−1) + D(|V∖{v}|−1) = D(|V|−1) − 1` — **one row
  short** (KT printed p. 680, verbatim "does not complete the proof"
  for `k=0`). The `+(D−1)` step reuses the green row infra
  (N7b-0/1/2/3 + the device-closure glue); the missing row is the
  Case-III content proper.

- **The `D`-candidate argument (the crux).** KT build `D` candidate
  realizations `(G,p₁), (G,p₂), (G,p₃)` (for `d=3`, three: KT pdf
  p. 37) differing in *which* hinge of `v` is placed degenerately, and
  show at least one is full rank.
  - **Claim 6.11 (combinatorial↔linear; the hardest non-linear-algebra
    step).** `R(G_v^{ab}, q)` has a *redundant* `(ab)i*`-row: removing
    it preserves rank (eq. 6.23, `rank R(G_v^{ab}∖(ab)i*, q) = rank
    R(G_v^{ab}, q) = 6(|V∖{v}|−1)`), via KT Lemma 4.3(ii) + the IH. This
    wires `M(G̃_v^{ab})` (Phase 19) to the *row matroid* of `R`.
  - **Claim 6.12 (extensor-span genericity; bottoms out on Lemma 2.1).**
    If *all* `D` candidates failed (each one row short), a nonzero `r ∈
    ℝ^D` would be orthogonal to all the extensors on `d+1` generic
    panels — which by **Lemma 2.1** (Phase 17,
    `omitTwoExtensor_linearIndependent`: the `D = (d+1 choose 2)`
    many `(d−1)`-extensors of `d+1` affinely independent points are
    independent) span `ℝ^D` — contradiction. The degree-2 condition
    forces all candidates to test the *same* `r` (KT eq. (6.44)). This
    is the load-bearing use of Lemma 2.1 the whole program was built
    toward.

- **Reuse map (what is already green and feeds this).**
  - Phase 17 Lemma 2.1 `omitTwoExtensor_linearIndependent` — the
    extensor-span fact Claim 6.12 contradicts against.
  - Phase 21b: the device, the `V(G)`-relative count bridge (N1–N3),
    the row sub-nodes N7b-0/1/2/3, N7a, `linearIndependent_sum_pinned_block`.
  - Phase 22a/22b: the block-triangular coupling / device-row-closure
    machinery (`isInfinitesimallyRigidOn_vertexSet_of_independent_rigidityRows`),
    the exterior-column projection `extProj`, the Claim-6.4 bricks.
  - Phase 20: the reducible-vertex / splitting-off operations + Lemma
    4.3 dof-tracking; the `hsplit` premise already carries `v`'s
    reducible-degree-2 data (the two edges `e_a, e_b`, their links, the
    degree-2 closure), strengthened in step with `minimal_kdof_reduction`.

- **Open recon questions (to settle in the next, still-docs-only,
  recon commits before any build).**
  1. The **candidate normal form**: abstract a single "candidate"
     lemma (one per-candidate row-op argument, instantiated `D` times)
     vs. inlining three copies at `d=3`. KT's prose repeats the row-ops
     three times; an abstraction is the cleaner formalization but must
     be designed against what is genuinely common.
  2. Whether to **build the `d=3` case fully concretely** (`D = 6`,
     three candidates) first, with the general-`d` Lemma 6.13 (Phase 23)
     generalizing the bookkeeping — KT itself does `d=3` (§6.4.1) then
     general `d` (§6.4.2), so following that cut is natural.
  3. The exact Lean shape of Claim 6.11's row-matroid↔`M(G̃_v^{ab})`
     bridge — which green Phase-19 fact (`matroidMG_indep_iff`,
     `def=corank`) it routes through.
  4. Whether Claim 6.12's "same `r`" (eq. 6.44) is a separate brick or
     folds into the candidate normal form.

## Lemma checklist

The Lean node cut is **deferred to the post-recon commits** (design-pass
-first; the recon settles it). The target *blueprint* nodes (already
stubbed red in `algebraic-induction/`):

- [ ] `lem:case-II-realization` (KT's Case III; `case-ii.tex`) — the
  eq. (6.12) degenerate placement giving `+(D−1)`, then the Case-III
  missing row. Discharges `theorem_55.hsplit`.
- [ ] `lem:case-III` (`case-iii.tex`) — the `D`-candidate-frameworks
  argument (Claims 6.11/6.12), bottoming on Lemma 2.1.
- [ ] (22d, deferred) `prop:rigidity-matrix-prop11` `hub` brick + the
  `thm:theorem-55` flip + the `case_I_realization` → `theorem_55_generic`
  Case-I wiring.

## Blockers / open questions

- **Sub-phase cut — SETTLED** (above): 22c = Case III at `d=3`; the
  `d=3` assembly is the likely 22d, deferred until 22c's shape is clear.
- **Design-recon-first — IN PROGRESS** (this phase's organizing
  principle): no Lean node is cut until the layer recon settles the
  candidate structure (the four open recon questions above).
- **Recurring Lean traps** (carry from 22a/22b, FRICTION): the heavy
  `IsInfinitesimallyRigidOn`/framework defeq across `ofNormals`/`withGraph`
  graph-swaps can `isDefEq`-timeout — make the two frameworks
  *syntactically* equal (rewrite the placement/selector) before a
  `convert`, rather than relying on defeq; pre-convert rigidity
  hypotheses; transfer across an `infinitesimalMotions` equality via a
  `mem_infinitesimalMotions` round-trip.

## Hand-off / next phase

22c is open at the design-recon stage. **The next concrete commit is the
continuation of the layer design recon (still docs-only): settle the
four open recon questions above — the candidate normal form, the `d=3`-
first cut, Claim 6.11's row-matroid bridge shape, and Claim 6.12's "same
`r`" packaging — then cut the Lean nodes leaf-most-first.** Do *not* open
a Lean build before the recon settles the candidate structure
(design-pass-first; `DESIGN.md` *Scale-up: design the LAYER, not just the
node*).

The green infra 22c builds on: the fully-green Case-I composer
`case_I_realization` (Phase 22b), the Phase-21b device + count bridge +
N7b row sub-nodes + splice/union glue, the Phase-22b Claim-6.4 bricks,
and — the load-bearing input — Phase-17 Lemma 2.1. The KT math is in
`notes/Phase21b.md` *Finding A/B*, `notes/Phase22-realization-design.md`,
and KT §6.4.1; 22c formalizes it.
