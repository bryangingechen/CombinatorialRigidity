# Phase 22c — Case III at `d=3`, first chunk (KT Lemma 6.10, the eq. (6.12) `+(D−1)` placement) (work log)

**Status:** in progress (opened 2026-06-05; scope re-cut to the *first
tractable chunk* 2026-06-05). **Design-pass-first** — this phase opened
on a *layer-level design recon* of the whole Case-III-at-`d=3` argument
(KT §6.4.1, Lemma 6.10, Claims 6.11/6.12) against the green Phase-17
Lemma 2.1 and the green Phase-21b/22a/22b infra, **before** any Lean
node-cut or grinding. The recon (two docs-only passes) has now settled
the candidate structure, answered its four open questions, and **cut
22c's scope to the first chunk only** (below). The Lean node-cut follows
in subsequent commits.

Stratum 5 of the molecular-conjecture program, continued: **Track B at
`d=3`** — the Case II/III reducible-vertex producer (KT's *Case III*),
the single largest proof in KT (~12 pages) and the conjecture's crux.
This is `theorem_55`'s `hsplit` branch at `k=0`: a `2`-edge-connected
minimal `0`-dof-graph with no proper rigid subgraph and a reducible
degree-2 vertex `v`, target full rank `D(|V|−1)`. At `d=3`, `D = (4
choose 2) = 6`. **22c does NOT attempt to land all of Lemma 6.10 in one
phase** — Case III at `d=3` is multi-phase (the user's explicit
direction, 2026-06-05: "let's not try to cram too much into 22c"); 22c
claims only the *first* of three difficulty strata (the eq. (6.12)
`+(D−1)` block-triangular placement). The harder D-candidate crux (the
Claim 6.11 redundant row + the Claim 6.12 / candidate-normal-form
assembly) is a **likely later sub-phase**; the `d=3` assembly later
still.

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

22c's **design recon is settled** (two docs-only passes), and a **third
docs-only commit (this one) reconciled the blueprint** to the corrected
understanding before any Lean build. The first recon pass read the whole
Case-III-at-`d=3` argument against the primary source; the second pinned
the **shared candidate structure**, answered the **four open recon
questions**, and **re-cut 22c's scope to the first tractable chunk** (the
eq. (6.12) `+(D−1)` block-triangular placement). This commit closed a
**concrete blocker the recon surfaced**: the live blueprint prose for the
exact nodes 22c builds (`lem:case-II-realization`,
`lem:case-II-realization-placement`) still routed the live route through
two superseded dead-ends (the motion-side M3
`lem:case-II-placement-motion-side-assembly` and the unbuildable row-side
N7b-4 `lem:case-II-placement-e0-recovery`), while the corrected eq. (6.12)
degenerate-placement route lived only in the notes. The reconciliation
(§1.27): both nodes' **statements and proofs** now consistently describe
the eq. (6.12) row-side route (`p₁(vb)=q(ab)` → the `vb`-row reproduces the
`e₀`-row → the green N7b-0/1/2/3 + `linearIndependent_sum_pinned_block`
bricks transport the old block); M3 and N7b-4 are **collapsed out of the
live route**, retained with explicit "superseded — not on the live route"
markers (conservative retain-with-marker choice; M1/M2 helpers likewise);
the green N7b-0/1/2/3 sub-nodes stay green (reused by Case I and this
route). **No Lean / `\leanok` flips this commit** (docs+blueprint TeX
only). The next concrete commit is the **first Lean node of stratum 1** —
see *Hand-off*. The Case-I composer `case_I_realization` is fully green
(Phase 22b) and ready to wire into `theorem_55_generic`'s Case-I branch;
that wiring + the `d=3` assembly is the deferred 22d territory.

## Sub-phase scope cut (SETTLED; re-cut to first-chunk 2026-06-05)

The parked "22c+" territory bundled the Case-III-at-`d=3` crux with the
`d=3` assembly; **and Case III at `d=3` is itself multi-phase** (the
recon's first-chunk cut, §1.26, folding in the user's direction that
Case III at `d=3` and the `d=3` assembly may *each* need multiple
phases). The cut:

- **22c = Case III at `d=3`, FIRST CHUNK ONLY — stratum 1, the eq. (6.12)
  `+(D−1)` placement (this phase).** KT §6.4.1, the *first* of three
  difficulty strata of Lemma 6.10: the eq. (6.12) degenerate placement
  `p₁(va) = L ⊂ Π(a)`, `p₁(vb) = q(ab)` (the `vb`-row reproducing the
  `e₀ = ab` row), giving via column ops (eq. (6.16)) a block-triangular
  `R(G,p₁)` with `R(G_v^{ab},q)` a submatrix ⟹ `rank ≥ 5 +
  6(|V∖{v}|−1) = D(|V|−1)−1`. `buildable` from the green Phase-21b row
  infra (N7b-0/1/2/3, N7a, `linearIndependent_sum_pinned_block`). This is
  the largest self-contained green-infra-fed piece and sets up the
  candidate scaffold the crux completes. **22c does NOT claim the full
  `lem:case-II-realization` + `lem:case-III`** — those stay red, with the
  eq. (6.12) `+(D−1)` lower-bound brick landing toward them.

- **The D-candidate crux (LIKELY its own later sub-phase; named, NOT
  scoped this phase) = strata 2–3 of Lemma 6.10.** Stratum 2 = **Claim
  6.11** (the redundant `(ab)i*`-row, the combinatorial↔linear conversion
  via KT Lemma 4.3(ii) + the IH applied at the rigidity matrix — the
  single highest-risk node in Phases 22–23). Stratum 3 = the **candidate
  normal form + Claim 6.12** assembly (the three candidates' residual
  normals `r/r'/r''`, the eq. (6.44) "same `r`" degree-2 forcing, and the
  Lemma-2.1 extensor-span contradiction). These complete `lem:case-III`
  and `lem:case-II-realization`. Defer the finer cut until stratum 1's
  shape is clear — name the next distinct sub-phase, do not pre-commit its
  internal node list (the same discipline as 22a→22b+, 22b→22c+).

- **The `d=3` assembly (deferred, downstream of the crux) = the
  genericity-free `hub` partition brick of `prop:rigidity-matrix-prop11`
  (a Phase-19-partition obligation, Track-independent, itself multi-commit
  — decompose math-first before scheduling) + the `thm:theorem-55` flip
  (one-line once the three case producers land) + wiring
  `case_I_realization` into `theorem_55_generic`'s Case-I branch.**
  **General-`d` (Lemma 6.13) → Thm 5.5 → Thm 5.6 → Conjecture 1.2 stays
  Phase 23** (integer phase numbers 23–26 unchanged).

Rationale: each sub-letter / sub-phase names *one* distinct chunk. The
recon (§1.26) shows Lemma 6.10 partitions into a `buildable` first
stratum (stratum 1, this phase) and a research-shaped crux (strata 2–3),
which the user's direction makes explicit: do not cram all of Case III at
`d=3` into 22c. Stratum 1 first de-risks the crux's recon (it makes the
candidate structure concrete in Lean) and yields a green `+(D−1)` brick
even before the crux lands.

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

## Recon resolution (SETTLED 2026-06-05 — second pass; full record §1.26)

The four open recon questions, resolved against the primary source (KT
pp. 34–37, 44–45). The detailed reasoning is
`notes/Phase22-realization-design.md` §1.26 (canonical); the answers:

1. **Candidate normal form — ABSTRACT one candidate lemma, instantiate
   ×3.** The three candidates are symmetric (`p₂` = `p₁` with `a↔b`; `p₃`
   = `p₁∘ρ` for the iso `ρ : G_a^{vc} ≅ G_v^{ab}`), and KT does the
   row-ops once ("the same analysis" for the others). State the
   per-candidate row-op + `+(D−1)` argument once, parametrized by
   `(degenerate hinge, free panel line L)`.
2. **`d=3`-first — YES.** Concrete `D=6` / 3-candidate case first;
   general `d` (Lemma 6.13, the length-`d` chain) stays Phase 23, KT's
   own §6.4.1-then-§6.4.2 cut. The candidate normal form is the right
   *internal* abstraction even at `d=3` (Lemma 6.13 re-instantiates it).
3. **Claim 6.11's bridge — routes through KT Lemma 4.3(ii) + the IH,
   landing as a redundant-row existence fact** (a non-base `ãb` fiber
   edge ⟹ a redundant rigidity row at the IH realization). The Lean lever
   is the green Phase-19 `M(G̃)`↔row-independence machinery
   (`matroidMG_indep_iff`, `thm:def-eq-corank`), but the *conversion* is
   genuinely new analytic content — **the D-candidate crux**, not the
   first chunk.
4. **Claim 6.12's "same `r`" (eq. 6.44) — FOLDS into the candidate normal
   form's contradiction step, not a separate brick.** `r' = r` (symmetry),
   `r'' = −r` (eq. 6.44, forced because `a` is degree-2 in `G_v^{ab}` —
   only `ab, ac` incident, so the `a`-block of the row-dependency (6.43)
   has two terms). Then four aff.-indep. points `p₁ = Π(a)∩Π(b)∩Π(c)`,
   …, and **Lemma 2.1** (`omitTwoExtensor_linearIndependent`, `(4 choose
   2)=6`) contradicts `r ≠ 0`.

**First-chunk cut (this phase = stratum 1).** Lemma 6.10 partitions into
three difficulty strata: (1) the eq. (6.12) `+(D−1)` block-triangular
placement (`buildable`, green-infra-fed — **22c**); (2) Claim 6.11's
redundant row (`research-shaped`, the highest-risk node — later
sub-phase); (3) the candidate-normal-form + Claim-6.12 + eq.-(6.44)
assembly (bottoms on green Lemma 2.1, composes after 1+2 — later
sub-phase). See the *Sub-phase scope cut* section above + §1.26.

## Lemma checklist

The blueprint reconciliation lands this commit; the Lean node cut for
**stratum 1** is the next commit; strata 2–3 are deferred. The target
*blueprint* nodes stay red — 22c lands the eq. (6.12) `+(D−1)` brick
toward them, not the full nodes.

- [x] **(this commit, docs+blueprint)** Reconcile `lem:case-II-realization`
  (`case-ii.tex`) + `lem:case-II-realization-placement`
  (`genericity-and-count.tex`) so statement+proof of each describe the
  eq. (6.12) row-side route; collapse M3 + N7b-4 out of the live route,
  retain-with-marker (§1.27).
- [ ] **(22c, stratum 1)** eq. (6.12) `+(D−1)` block-triangular placement
  — the next Lean node, the new producer behind `lem:case-II-realization-placement`.
  `buildable` from the green N7b row infra. Cut leaf-most-first (the
  ordering, §1.27 / *Hand-off*): (a) a placement def `p₁` with the
  `p₁(vb)=q(ab)` row-reproduction `hrow` (the one new geometric brick);
  (b) feed N7b-1 (`exists_independent_panelRow_subfamily_of_edge`, +(D−1)),
  N7b-0 (`exists_independent_panelRow_subfamily_of_rigidOn`, D(|V|−2) old),
  N7b-2 (`exists_independent_panelRow_transport`, the transport whose
  `hrow` IS the eq. (6.12) reproduction), N7b-3
  (`linearIndependent_sum_pinned_block`, joint independence = KT eq. (6.16));
  (c) `hasFullRankRealization_of_independent_panelRow` (N7a) closure.
  Count: `(D−1) + D(|V∖{v}|−1) = D(|V|−1)−1 = 6|V|−7` at `D=6`. A
  lower-bound brick *toward* `lem:case-II-realization`, not the full node.
- [ ] (later sub-phase) `lem:case-II-realization` (KT's Case III;
  `case-ii.tex`) + `lem:case-III` (`case-iii.tex`) — the D-candidate crux
  (Claim 6.11 redundant row + the candidate-normal-form / Claim-6.12
  assembly, bottoming on Lemma 2.1). Discharges `theorem_55.hsplit`.
- [ ] (22d, deferred) `prop:rigidity-matrix-prop11` `hub` brick + the
  `thm:theorem-55` flip + the `case_I_realization` → `theorem_55_generic`
  Case-I wiring.

## Blockers / open questions

- **Blueprint divergence — RESOLVED** (this commit, §1.27): the live
  `lem:case-II-realization` / `lem:case-II-realization-placement` prose no
  longer routes through the superseded M3 / N7b-4; both describe the
  eq. (6.12) row-side route consistently in statement+proof. This was the
  binding doc-blocker the design recon surfaced (corrected understanding
  was in the notes only).
- **Sub-phase cut — SETTLED** (re-cut to first-chunk): 22c = Case III at
  `d=3` *stratum 1* (the eq. (6.12) `+(D−1)` placement) only; the
  D-candidate crux (strata 2–3) is a likely later sub-phase, the `d=3`
  assembly the deferred 22d — each deferred until the prior shape is clear.
- **Design-recon — SETTLED**: the four open recon questions are answered
  (§1.26); the layer is designed. The next commit cuts the first Lean node.
- **Reuse-from-22b — ANSWERED** (the de-risking question, §1.27): stratum 1
  reuses the green **N7b row infra** (N7b-0/1/2/3 + N7a + `_transport`)
  near-wholesale — they were *built* for exactly this `1`-extension
  placement (Phase 21b). 22b's `degeneratePlacement`/`extProj`/
  `panelRow_collapseTo_comp_extProj_dualMap` machinery is **NOT** reused:
  it is the *block-collapse* relabel for Case I's contraction (`Gc.map
  (collapseTo r V(H))`), structurally heavier than stratum 1's single-vertex
  `p₁(vb)=q(ab)`. Stratum 1's *one* genuinely-new brick is the per-row
  reproduction `hrow` (the eq. (6.12) row-equality feeding N7b-2's transport).
- **Recurring Lean traps** (carry from 22a/22b, FRICTION): the heavy
  `IsInfinitesimallyRigidOn`/framework defeq across `ofNormals`/`withGraph`
  graph-swaps can `isDefEq`-timeout — make the two frameworks
  *syntactically* equal (rewrite the placement/selector) before a
  `convert`, rather than relying on defeq; pre-convert rigidity
  hypotheses; transfer across an `infinitesimalMotions` equality via a
  `mem_infinitesimalMotions` round-trip.

## Hand-off / next phase

The design recon is **settled** (four questions answered, first-chunk
scope cut; §1.26) **and the blueprint is now reconciled to it** (§1.27,
this commit) — so the next agent does not re-fight the divergence. **The
next concrete commit is the FIRST LEAN NODE of stratum 1: the eq. (6.12)
degenerate-placement producer behind `lem:case-II-realization-placement`.**

Precise target. A producer (working name
`PanelHingeFramework.case_II_placement_eq612` / `…_independent_panelRow`)
that, from the inductive realization of the split-off `G_v^{ab}` (rigid on
`V(G)∖{v}` = the IH at full rank, since `k=0` ⟹ `G_v^{ab}` minimal 0-dof
by KT Lemma 4.8(i)) and `v`'s reducible-degree-2 data (the two edges
`e_a=va, e_b=vb`, their links, the degree-2 closure — already carried on
`theorem_55.hsplit`), constructs a free normal assignment `q₀` for `G`
**and** a linearly independent `panelRow ends q₀` subfamily of size
`D(|V(G)|−1)`, i.e. `rank R(G,p₁) ≥ D(|V|−1)−1 = 6|V|−7` at `D=6`.

Leaf-most-first node order (each mapped to a green input; the only red
leaf is the new placement+`hrow` brick):
1. **placement `p₁` + the row reproduction `hrow`** (the one new brick):
   `p₁` agrees with `q` on `G−v`, sets `p₁(va)=L⊂Π_q(a)` and `p₁(vb)=q(ab)`;
   prove `R(G,p₁)`'s `vb`-row equals `R(G_v^{ab},q)`'s `e₀=ab` row (the
   per-row match `hrow` that `exists_independent_panelRow_transport` (N7b-2)
   takes). This is the eq. (6.12) content; recon-before-build the `hrow`
   row-equality specifically (it is the structural-fidelity crux — see below).
2. **new block** `exists_independent_panelRow_subfamily_of_edge` (N7b-1, green):
   `v`'s two transversal hinges ⟹ `D−1` independent rows in `v`'s column block.
3. **old block** `exists_independent_panelRow_subfamily_of_rigidOn` (N7b-0,
   green): the IH rigidity ⟹ `D(|V|−2)` independent old rows; transport them
   onto `G` through `G−v` by `exists_independent_panelRow_transport` (N7b-2,
   green) using `hrow` from step 1.
4. **joint independence** `linearIndependent_sum_pinned_block` (N7b-3, green,
   in `RigidityMatrix.lean`): pin-a-body column split = the Lean form of KT
   eq. (6.16); makes `Sum.elim new old` independent at the full count.
5. **closure** `hasFullRankRealization_of_independent_panelRow` (N7a, green):
   lift the witnessed corank to a generic realization rigid on `V(G)`.

Honesty-gate checks confirmed at recon (re-verify at the build's open):
- **2nd half (count):** `(D−1) + D(|V∖{v}|−1) = (D−1) + D(|V|−2) =
  D(|V|−1)−1`; at `D=6` that is `5 + 6(|V|−2) = 6|V|−7`. Closes from the
  named green inputs (N7b-1 gives `D−1`; N7b-0 gives `D(|V|−2)` because the
  `k=0` IH is *full* rank on `V(G_v^{ab})`). One short of `D(|V|−1)` — the
  Case-III missing row, deferred to strata 2–3. ✓
- **3rd half (structural fidelity — the trap that bit Case I):** KT's
  eq. (6.16) **column operations making `R(G,p₁)` block-triangular with
  `R(G_v^{ab},q)` a submatrix** is reproduced by the project's
  `linearIndependent_sum_pinned_block` (pin-a-body, new rows in `v`'s screw
  column, old rows off it) — NOT re-expressed as a different motion-space
  obligation. The eq. (6.12) `p₁(vb)=q(ab)` *row reproduction* is exactly
  the per-row match `hrow` of the N7b-2 transport. So the construction
  matches KT's argument structure. (Contrast Case I, where a motion-space
  splice glue silently swapped KT's block-triangular structure for a
  common-seed one and accreted bridge hypotheses — `DESIGN.md` *Match the
  source's argument structure*.)

22c lands this `+(D−1)` brick *toward* `lem:case-II-realization` /
`lem:case-III` — those nodes stay red; the D-candidate crux (strata 2–3) is
a later sub-phase, named but not scoped here. The deferred crux's
load-bearing input is Phase-17 Lemma 2.1 (`omitTwoExtensor_linearIndependent`).
KT math: `notes/Phase21b.md` *Finding A/B*,
`notes/Phase22-realization-design.md` §1.25–§1.27, KT §6.3 (Lemma 6.8) +
§6.4.1; 22c formalizes it.
