# Phase 22c — Case III at `d=3`, first chunk (KT Lemma 6.10, the eq. (6.12) `+(D−1)` placement) (work log)

**Status:** in progress (opened 2026-06-05; scope re-cut to the *first
tractable chunk* 2026-06-05; first Lean node landed 2026-06-05). **Design-pass-first** — this phase opened
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

22c's **design recon is settled** (two docs-only passes), the **third
docs-only commit reconciled the blueprint** to the corrected understanding,
and a **fourth docs-only commit signature-verified the stratum-1
node cut** against the real Lean signatures of the green bricks it composes
with (§1.28) — the user asked for one more design pass before any build, a
node-level constructibility recon against actual signatures. **Outcome: the
composition verifies CLEANLY, no mismatch.** The critical check (does N7b-2's
`hrow` accept the eq. (6.12) reproduction?) passes — with one *labelling*
refinement: the `p₁(vb)=q(ab)` reproduction is the **new-block** content (it
lands the `vb`-row in `v`'s screw column for N7b-3's pin-a-body split), while
N7b-2's `hrow` is the **old-block** `ends`/`q₀`-agreement `rfl`; the two were
conflated in the prior *Hand-off*, corrected below (not a blocker — count +
composition unchanged). The build agent now has a precise, signature-checked,
leaf-most-first target. The first recon pass read the whole
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
route). The Case-I composer `case_I_realization` is fully green
(Phase 22b) and ready to wire into `theorem_55_generic`'s Case-I branch;
that wiring + the `d=3` assembly is the deferred 22d territory.

**First Lean node landed (2026-06-05).** The 2nd of stratum 1's two
genuinely-new facts — `hnewpin`, the new-block column independence — is
green as `BodyHingeFramework.linearIndependent_panelRow_comp_single_of_edge`
in `Pinning.lean` (right after N7b-1). It takes N7b-1's `D−1` panel rows on
one of `v`'s incident edges `e` and shows they remain independent after the
pin-a-body column composite `.comp (LinearMap.single ℝ _ (ends e).1)`, which
is exactly N7b-3's `hnewpin` parameter. Axiom-clean, warning-clean,
lint-clean. **No `\leanok` flips** (Lean-only infra; the target nodes
`lem:case-II-realization` / `lem:case-III` stay red). The remaining stratum-1
work is the **shared-seed selector geometry** (eq. (6.12) `q₀` placing the
`vb`-hinge extensor to reproduce the `e₀`-hinge, the genuinely-new geometric
construction, fact 1 of 2) and the green-brick composition (N7b-0/1/2/3 +
N7a form (b)); see *Hand-off*.

**Fifth docs-only commit (this one) — step-1 constructibility recon, the
planning gate before the build (§1.29).** Per the user's standing direction
("very intricate part; never dispatch a build before the plan is clear"), a
focused read-only recon resolved the one piece §1.28 left at the *requirements*
level: the **shared-seed selector geometry** (fact 1 of 2). **Verdict: PLAN
CLEAR.** Two load-bearing resolutions: **(A)** the **single-seed coupling is
sound** — `q₀ := Function.update q v (placement)` leaves the old block untouched
because the IH's rigidity quantifies only over `V(G)∖{v}` and its motions read
only `G−v` edges; the green lever is `toBodyHinge_withNormal_infinitesimalMotions_eq`
(`PanelHinge.lean:594`), whose `hv` holds exactly because `v ∉ V(G_v^{ab})`. **(B)**
the placement is `q₀(v,·) := n_a + t·n_b` with **`t ≠ 0`** (`n_a=q(a,·)`, `n_b=q(b,·)`),
**NOT `q₀ v = q₀ a`** — the wedge fact `normalsJoin (n_a+t·n_b) n_b = normalsJoin n_a n_b`
makes the `vb`-row reproduce the `e₀`-row for *any* `t`, but `t=0` zeros the `va`-hinge
extensor and builds a *degenerate* candidate (a genuine trap); `t≠0` keeps the `va`-line
nondegenerate, matching KT's eq. (6.12) candidate (`DESIGN.md` *Match the source's
argument structure*). No `\leanok`/Lean/blueprint changes; the next commit is the build.

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

- [x] **(prior commit, docs+blueprint)** Reconcile `lem:case-II-realization`
  (`case-ii.tex`) + `lem:case-II-realization-placement`
  (`genericity-and-count.tex`) so statement+proof of each describe the
  eq. (6.12) row-side route; collapse M3 + N7b-4 out of the live route,
  retain-with-marker (§1.27).
- [x] **(commit bea3217, docs only)** Signature-level verification of the
  stratum-1 cut against the real Lean signatures (§1.28): pulled the verbatim
  heads of N7b-0/1/2/3 + N7a (two forms), traced the critical `hrow` check,
  confirmed the composition + count close cleanly, and corrected the
  `hrow`/eq.-(6.12)-reproduction conflation (the reproduction is new-block,
  `hrow` is old-block `rfl`). No Lean / `\leanok` / blueprint flips.
- [x] **(this commit, docs only)** Step-1 constructibility recon — the planning
  gate before the build (§1.29): resolved the **single-seed coupling** (sound via
  `toBodyHinge_withNormal_infinitesimalMotions_eq`, `q₀ := update q v (placement)`,
  `hv` holds because `v ∉ V(G_v^{ab})`) and pinned the **placement geometry**
  (`q₀(v,·) := n_a + t·n_b`, `t ≠ 0`, NOT `q₀ v = q₀ a` — the `t=0` trap zeros the
  `va`-hinge). Verdict PLAN CLEAR; sub-lemma cut + Case-I precedent recorded. No
  Lean / `\leanok` / blueprint flips.
- [x] **(commit aeadb45, Lean — stratum-1 leaf 1)** `hnewpin`, the new-block column
  independence (§1.28 / *Hand-off* step 2): `linearIndependent_panelRow_comp_single_of_edge`
  in `Pinning.lean` (right after N7b-1). The 2nd of the two genuinely-new facts.
  From N7b-1's `D−1` panel rows on one edge `e` (subfamily `s`, all `i.1 = e`), they
  stay independent after `.comp (LinearMap.single ℝ _ (ends e).1)` — feeds N7b-3's
  `hnewpin` directly (`ιn := ↥s`). Proof = the pin-at-`v` identity
  `hingeRow v w r ∘ₗ single v = r` (one shared edge ⟹ one shared `screwDiff`) +
  `LinearIndependent.of_comp` stripping the injective `(screwDiff …).dualMap`. Axiom-clean
  (`propext`/`Classical.choice`/`Quot.sound`), warning-clean, lint-clean. No `\leanok` flip
  (the target `lem:case-II-realization` / `lem:case-III` stay red; this is Lean-only infra).
- [ ] **(22c, stratum 1 — remaining; construction PINNED §1.29)** eq. (6.12)
  `+(D−1)` block-triangular placement — the producer behind
  `lem:case-II-realization-placement`. `buildable` + **signature-verified** (§1.28)
  + **construction-verified** (§1.29: single-seed coupling sound, `q₀(v,·):=n_a+t·n_b`
  with `t≠0`). Cut leaf-most-first (the *exact* ordering, §1.28+§1.29 / *Hand-off*):
  the **two** new facts are (1) the shared-seed selector `q₀`/`ends` making the
  `vb`-hinge reproduce the `e₀`-hinge extensor + agreeing on `G−v` edges, and (2)
  `hnewpin` (N7b-1's `D−1` rows stay independent after `.comp (single … v)`);
  then green: N7b-1 (`exists_independent_panelRow_subfamily_of_edge`, `D−1`),
  N7b-0 (`exists_independent_panelRow_subfamily_of_rigidOn`, `D(|V|−2)` old,
  fed by `exists_rigidOn_ofNormals_of_hasFullRankRealization` from the IH),
  N7b-2 (`exists_independent_panelRow_transport`, `hrow := rfl` from (1)),
  N7b-3 (`linearIndependent_sum_pinned_block`, `Sum.elim` = KT eq. (6.16)),
  N7a form (b) `isInfinitesimallyRigidOn_vertexSet_of_independent_rigidityRows`
  closure (takes the `Sum`-index directly). Count: `(D−1) + D(|V|−2) =
  D(|V|−1)−1 = 6|V|−7` at `D=6`. A lower-bound brick *toward*
  `lem:case-II-realization`, not the full node.
- [ ] (later sub-phase) `lem:case-II-realization` (KT's Case III;
  `case-ii.tex`) + `lem:case-III` (`case-iii.tex`) — the D-candidate crux
  (Claim 6.11 redundant row + the candidate-normal-form / Claim-6.12
  assembly, bottoming on Lemma 2.1). Discharges `theorem_55.hsplit`.
- [ ] (22d, deferred) `prop:rigidity-matrix-prop11` `hub` brick + the
  `thm:theorem-55` flip + the `case_I_realization` → `theorem_55_generic`
  Case-I wiring.

## Blockers / open questions

- **Blueprint divergence — RESOLVED** (commit 7ba0266, §1.27): the live
  `lem:case-II-realization` / `lem:case-II-realization-placement` prose no
  longer routes through the superseded M3 / N7b-4; both describe the
  eq. (6.12) row-side route consistently in statement+proof. This was the
  binding doc-blocker the design recon surfaced (corrected understanding
  was in the notes only).
- **Recurrence prevention — DONE** (docs-only follow-up commit): the
  *process* fix so superseded-route rot cannot survive into a phase
  opening again. Three gates landed: a **supersession-ownership rule** +
  a standardized greppable title marker (`[… (superseded, …): …]`,
  applied to N7b-4 + M1/M2/M3) + a scriptable `awk`/`comm` check
  (`blueprint/CLAUDE.md` *Static checks before commit → the supersession
  gate*), and a **phase-open red-node consistency gate** (root
  `CLAUDE.md` *When this commit opens a phase*). Incident + lesson:
  `FRICTION.md` *[process][blueprint] Phase 22c open — superseded-route
  rot …*. No Lean / `\leanok` / `\lean{}` changes.
- **Sub-phase cut — SETTLED** (re-cut to first-chunk): 22c = Case III at
  `d=3` *stratum 1* (the eq. (6.12) `+(D−1)` placement) only; the
  D-candidate crux (strata 2–3) is a likely later sub-phase, the `d=3`
  assembly the deferred 22d — each deferred until the prior shape is clear.
- **Design-recon — SETTLED**: the four open recon questions are answered
  (§1.26); the layer is designed.
- **Signature-level verification — DONE** (§1.28, commit bea3217): the stratum-1
  composition is verified against the *actual* current Lean signatures of all
  five green bricks (N7b-0/1/2/3 + N7a). The critical `hrow` check passes (the
  `panelRow` term depends only on `ends`+`q`, not the graph, so the old-block
  `hrow` is `rfl`); the count `(D−1)+D(|V|−2)=D(|V|−1)−1` closes from the named
  `Nat.card` bounds; the IH from `hsplit` feeds N7b-0 via
  `exists_rigidOn_ofNormals_of_hasFullRankRealization`. **One labelling
  refinement** (not a blocker): the eq. (6.12) `p₁(vb)=q(ab)` reproduction is
  **new-block** content (feeds `hnewpin`/N7b-3's `v`-column), NOT N7b-2's
  `hrow` (which is the old-block `ends`/`q₀`-agreement `rfl`). The two new
  facts are the shared-seed selector + `hnewpin`; everything else is green.
- **Step-1 constructibility — RESOLVED** (§1.29, this commit): the one piece
  §1.28 left at the *requirements* level — the shared-seed selector geometry
  (fact 1 of 2) — is now construction-verified. **(A)** the **single-seed
  coupling** (reconcile the IH's *existential* seed with the one shared `q₀`)
  is sound: `q₀ := Function.update q v (placement)` leaves the old block
  untouched via `toBodyHinge_withNormal_infinitesimalMotions_eq` (`PanelHinge.lean:594`),
  whose `hv` holds because `v ∉ V(G_v^{ab})`. **(B)** the placement is
  `q₀(v,·) := n_a + t·n_b` with **`t ≠ 0`** — the wedge fact `normalsJoin
  (n_a+t·n_b) n_b = normalsJoin n_a n_b` reproduces the `vb`→`e₀` row for any
  `t`, but `t = 0` (`q₀ v = q₀ a`) **zeros the `va`-hinge** (degenerate
  candidate, a trap). Verdict **PLAN CLEAR**. The next commit cuts the build.
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
scope cut; §1.26), **the blueprint is reconciled to it** (§1.27), **the
stratum-1 cut is SIGNATURE-VERIFIED against the real Lean signatures**
(§1.28), **the first Lean node — `hnewpin` (fact 2 of 2) — has landed**
(`linearIndependent_panelRow_comp_single_of_edge`, `Pinning.lean`), **and the
remaining fact 1 (the shared-seed selector geometry) is now
CONSTRUCTION-VERIFIED** (§1.29: single-seed coupling sound, placement pinned).
So the next agent does not re-fight the divergence, does not hit a signature
surprise, has the column-independence brick in hand, and **knows the exact
`q₀` construction**. **The next concrete commit is the eq. (6.12) shared-seed
selector geometry (fact 1 of 2) + the green-brick composition into the
lower-bound producer behind `lem:case-II-realization-placement`.** The full
signature record is §1.28; the construction resolution (single-seed coupling +
placement geometry + sub-lemma cut + Case-I precedent) is §1.29; this is the
build-agent summary.

Precise target. A producer (working name
`PanelHingeFramework.case_II_placement_eq612` / `…_independent_panelRow`)
that, from the inductive realization of the split-off `G_v^{ab}` and `v`'s
reducible-degree-2 data (`e_a=va, e_b=vb`, links, degree-2 closure — carried
on `theorem_55.hsplit`), constructs a shared free normal assignment `q₀` for
`G` **and** a linearly independent `panelRow`-row family of size
`D(|V(G)|−1)−1`, i.e. `rank R(G,p₁) ≥ D(|V|−1)−1 = 6|V|−7` at `D=6`. This is
a **lower-bound brick** toward the red `lem:case-II-realization` — explicitly
**not** `HasFullRankRealization` (one row short, the Case-III missing row).

**Signature-verified input wiring (§1.28).** The IH from `theorem_55.hsplit`
is `HasFullRankRealization k (G.splitOff v a b e₀)`;
`exists_rigidOn_ofNormals_of_hasFullRankRealization` (`GenericityDevice.lean:1078`)
repackages it to `∃ ends₁ q, (ofNormals G_v^{ab} ends₁ q).toBodyHinge.IsInfinitesimallyRigidOn V(G_v^{ab})`
— exactly N7b-0's `hrig` input (put on the shared seed `q₀`). `|V(G_v^{ab})| =
|V(G)|−1` (`vertexSet_splitOff`), so N7b-0 yields `D(|V|−2)` old rows. The
**load-bearing structural fact** (the reason `hrow` is cheap): `panelRow` of
`ofNormals G ends q` reads only `ends`+`q`, **not** `G`
(`panelRow` ∘ `toBodyHinge_supportExtensor` ∘ `ofNormals_normal`, all `rfl`).

Leaf-most-first node order (the only red leaf is the new placement brick;
steps 2–6 are green-brick applications):
1. **shared seed `q₀` + two selectors `ends_G`, `ends₁`** (the one new brick,
   eq. (6.12) geometric content; **construction PINNED §1.29**): take the IH's
   `(ends₁, q)` from `exists_rigidOn_ofNormals_of_hasFullRankRealization`, then
   **`q₀ := Function.update q v (n_a + t·n_b)`** with `n_a := q(a,·)`, `n_b := q(b,·)`,
   `t ≠ 0` (concretely `t = 1`). The **single-seed coupling is sound** — overriding
   only the fresh vertex `v` leaves the old block untouched
   (`toBodyHinge_withNormal_infinitesimalMotions_eq`, `PanelHinge.lean:594`; `hv`
   holds because `v ∉ V(G_v^{ab})`). The wedge fact `normalsJoin (n_a+t·n_b) n_b =
   normalsJoin n_a n_b` makes the `vb`-hinge extensor `panelSupportExtensor (q₀ v)(q₀ b)`
   reproduce the `e₀=ab`-hinge extensor `panelSupportExtensor (q₀ a)(q₀ b)` (the
   `p₁(vb)=q(ab)` **new-block** reproduction); `t ≠ 0` keeps the `va`-hinge
   `panelSupportExtensor (q₀ v)(q₀ a) = −t·panelSupportExtensor (q₀ a)(q₀ b) ≠ 0`
   nondegenerate (**NOT `q₀ v = q₀ a`** — `t=0` zeros it, building a degenerate
   candidate). `ends_G`/`ends₁` record their links (`hends`) **and agree on every
   `e₀`-free `G−v` edge** (so step 5's `hrow` is `rfl`). New sub-lemmas: the wedge
   identity in `PanelLayer.lean` + the `withNormal`/`withGraph` glue (rfl-adjacent);
   mirror the Case-I composer's shared-seed→`Sum.elim`→form-(b) pattern
   (`CaseI.lean:1754–1831`).
2. **`hnewpin` (new-block column independence)** — **DONE** (2026-06-05,
   `linearIndependent_panelRow_comp_single_of_edge` in `Pinning.lean`): from
   N7b-1 (`exists_independent_panelRow_subfamily_of_edge`, green) `D−1`
   panel rows on `e_b`, they stay independent after `.comp (LinearMap.single ℝ _ v)`
   (the `hingeRow v w r ∘ single v = r` pin-at-`v` identity; `of_comp` strips
   the shared `(screwDiff …).dualMap`). Feeds N7b-3's `hnewpin`. Axiom-clean.
3. **new block** `exists_independent_panelRow_subfamily_of_edge` (N7b-1, green):
   `v`'s transversal hinge ⟹ `D−1` independent new rows.
4. **old block** `exists_independent_panelRow_subfamily_of_rigidOn` (N7b-0,
   green): IH rigidity at `q₀` ⟹ `D(|V|−2)` independent old rows.
5. **transport** `exists_independent_panelRow_transport` (N7b-2, green):
   carry the old block onto `G` along the identity-on-common-edges injection
   `f` (drops the `e₀` index); `hrow i := rfl` from step 1's `ends`/`q₀`
   agreement (the **old-block** agreement, NOT the eq. (6.12) reproduction —
   the labelling correction of §1.28).
6. **joint independence** `linearIndependent_sum_pinned_block` (N7b-3, green,
   `RigidityMatrix.lean:548`): `hold` (old rows vanish at `update 0 v x` — their
   edges avoid `v`) + `hnewpin` (step 2) + `holdindep` (step 5) ⟹ `Sum.elim
   rn ro` independent = the Lean form of KT eq. (6.16) block-triangular.
7. **closure** `isInfinitesimallyRigidOn_vertexSet_of_independent_rigidityRows`
   (N7a form (b), `CaseI.lean:1631`, green): takes the `Sum.elim`-indexed family
   directly (no `Set s` repackage) + `hmem : ∀ i, family i ∈ rigidityRows` +
   the `D(|V|−1)−1` card bound. (Same closure path the green Case-I composer
   uses, `CaseI.lean:1794–1831`.) Yields the lower-bound deliverable.

Honesty-gate checks (signature-confirmed §1.28; re-verify at build's open):
- **2nd half (count):** `(D−1) + D(|V∖{v}|−1) = D(|V|−1)−1`; at `D=6` that is
  `5 + 6(|V|−2) = 6|V|−7`. Closes from the named green inputs (N7b-1 gives
  `D−1`; N7b-0 gives `D(|V|−2)` because `|V(G_v^{ab})|=|V(G)|−1` and the `k=0`
  IH is full rank). One short of `D(|V|−1)` — the Case-III missing row,
  strata 2–3. ✓ (verified against the actual `Nat.card` bounds in each brick)
- **3rd half (structural fidelity — the trap that bit Case I):** KT eq. (6.16)'s
  **block-triangular column ops** are reproduced by `linearIndependent_sum_pinned_block`
  (pin-a-body: new rows in `v`'s screw column via `hnewpin`, old rows off it via
  `hold`), NOT re-expressed as a different motion-space obligation. The eq. (6.12)
  `p₁(vb)=q(ab)` row reproduction is the **new-block** placement (step 1), feeding
  the `v`-column. So the construction matches KT's argument structure. (Contrast
  Case I, where a motion-space splice glue silently swapped the block-triangular
  structure — `DESIGN.md` *Match the source's argument structure*.) ✓

22c lands this `+(D−1)` brick *toward* `lem:case-II-realization` /
`lem:case-III` — those nodes stay red; the D-candidate crux (strata 2–3) is
a later sub-phase, named but not scoped here. The deferred crux's
load-bearing input is Phase-17 Lemma 2.1 (`omitTwoExtensor_linearIndependent`).
KT math: `notes/Phase21b.md` *Finding A/B*,
`notes/Phase22-realization-design.md` §1.25–§1.27, KT §6.3 (Lemma 6.8) +
§6.4.1; 22c formalizes it.
