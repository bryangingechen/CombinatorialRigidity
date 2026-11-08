# Phase 43d — EXPO: a road map of the pencil proof (work log)

**Status:** in progress (opened 2026-11-08 with the PI), the fourth and last sub-phase of Phase 43
(PENCIL-NATURAL): layer EXPO as one sub-phase, at the PI's word, with the PI's three answers on
where the road map goes, how much intuition it carries and how flatness is treated (design doc §1,
2026-11-08, EXPO's open). No main result changes. In order: slice 1 the road map (`pencil.tex`),
slice 2 the removal of the two main-component statements (inserted at the PI's word, design doc
§1; the one slice with Lean code), slice 3 the flatness remark (`main-component.tex`), slices 4
and 5 point the chapters at the road map, slice 4 with the PI's fold of a duplicate theorem, then
the close, which is Phase 43's close too. Slices 1–3 landed; the next concrete commit is slice 4,
pinned below.

## Current state

**Next concrete commit: slice 4, the road-map pointers in `pencil.tex` and `main-component.tex`,
with the fold of `thm:pencil-x0-generic-attains` into `thm:pencil-x0-coverage`** (checklist
item 4; the fold at the PI's word, design doc §1). Mode: a structural edit of existing chapters.
Slices 4–5 add or restate no dep-graph node (a subsection and a remark are not nodes); slice 4
deletes one, the duplicate, whose pin stays on the coverage, so the deletion and moved-pin gates
apply there (`CombinatorialRigidity/CLAUDE.md` *Forward-mode slices*). Each slice re-reads every
node its prose cites. Plan: `notes/Phase43-design.md` §2, EXPO (the 43a read's inputs),
corrected by *Verified at the open* below.

**Verified at the open (HEAD `172b5b9f`).**
- **KT's pages**, read in `.refs/katoh-tanigawa-2011-molecular-conjecture.pdf`: §1.1 *Road Map of
  the Proof* is journal pp. 649–650 (the coordinator's hypothesis holds): Cases (I)–(III) on
  p. 649, their implementation (§6.2, §6.3, §6.4) on p. 650. Lemma 4.5 p. 663, Lemma 4.6 p. 664,
  Theorem 4.9 pp. 666–667, as `pencil.tex` cites them.
- **Two stale clauses from 43c, fixed in this commit:** `intro.tex`'s "steps by splitting off" (the
  split-off step left `def:pencil-x0-reduces` in 43c slice C), and `formalization.yaml`'s
  Jackson–Jordán source note "transfers their splitting-off case" (that comparison paragraph went
  with `sec:main-component-splitoff`). `main-component.tex`:23–24 ("We also use splitting off")
  stays true: the ear steps compare with `G` with `x₂` suppressed.
- **(F) holds as the design doc states it**, at every main picture, for the heights and for the
  panels. Its five lemmas say what it needs: `lem:pencil-contract-standing-rigid` (deficiency zero
  at some `d ≥ 1`, so at `d = 2`); `thm:pencil-jj-equality` (needs every closed neighbourhood of
  at least three members, which `def:pencil-x0-standing` gives); `lem:pencil-lifting-space-affine`;
  `lem:pencil-lifting-restrict` part (1); `lem:pencil-condition-linear` (the plane is unique). The
  by-hand step must carry the lifting system's coefficient vectors `h_v`
  (`def:pencil-lifting-system`), not only the heights: at a main picture of `G` that is not
  admissible for `G[W]`, the panel clause comes only that way (slice 3). At such pictures the 43a
  probe found one plane at every body of `W`, at all 1,371 it reached (`specialpanel.py`).
- **The degeneracy holds in one direction only.** A bad pair (two members of one closed
  hub-neighbourhood in one planar-rigid set) makes every configuration over a main picture
  degenerate: proved, from (F). The converse is probe evidence: re-run here, `flatprobe.py` at
  `n ≤ 8` has 55 graphs with no bad pair, one of them degenerate, at a closed hub-neighbourhood of
  four members, so nondegeneracy-infeasible (`lem:pencil-feasible-hub-conditions`): among feasible
  graphs the probe found no counterexample to the converse. The design doc's "exactly when" is not
  written.
- **I1–I4** (`notes/PencilNatural.md` §5) against the chapters at HEAD, as slice 1 writes them:
  - **I1, the gap: holds, restated.** At a main picture the flat configuration has rank exactly
    the target less `def₂ − def_d` (`thm:pencil-flat-rank`, `thm:pencil-d-flat-rank`, with
    `thm:pencil-jj-equality`), so the heights recover the gap; at equal deficiencies there is none
    (`cor:pencil-jj-flat`). The per-step clause goes: N4 found the gap not monotone, and its table
    is not landed.
  - **I2, degree-two bodies: holds, restated.** A body of degree two imposes nothing on the heights
    (`lem:pencil-three-points`); the conditions sit on hubs' closed neighbourhoods, and a non-hub
    carries nondegeneracy's independence condition (`def:pencil-nondegenerate`). The chain is the
    unit removed at `k ≥ 5` and `k = 1`; at `k = 2` (ends not adjacent), `3` and `4` the step also
    compares with `G` with `x₂` suppressed (`def:pencil-x0-reduces`). "(pre-N3) open-ear-two" goes.
  - **I3, one body: restate.** By (F), at a main picture a planar-rigid set has one panel, and
    `cor:pencil-x0-contract-rigid` contracts a maximal one to a body; the additive cores
    (`thm:pencil-x0-contract-additive`) are rigid but need not be planar-rigid. In the lift, the rest
    `X` of a minimal planar-rigid set (planar deficiency one, `lem:pencil-d-good-ear` (iii)) lifts
    only trivially, by one linear form (`lem:pencil-d-ear-free`).
  - **I4, slack at larger `D`: holds, restated.** The count needs `3(ℓ + 1) ≤ D`
    (`lem:pencil-d-chain-count`) and forces a core at a chain with `2 ≤ k ≤ ℓ`; where every chain
    has one interior body the core comes from `def₃ > 0` by tight parts
    (`lem:pencil-d-core-positive-deficiency`), and otherwise the embedding applies
    (`thm:pencil-d-chain-or-core`). "The `P³` rows" are now two, named:
    `thm:pencil-x0-open-ear-one` and `thm:pencil-x0-open-ear-two-orbit`, which run at `d = 3`
    through the embedding (`sec:pencil-d-coverage`'s lead). W8 (no node) goes.
- **The forcing reasons** (Q2): `K₄ ⊃ C₄` (`sec:pencil-reduction`), parallel edges (one hinge
  `p_u ∨ p_v` for both; `sec:pencil-nondegenerate`'s two bodies joined by two edges), `K_{2,3}`
  (`lem:pencil-x0-two-hubs-obstruction`) hold. "No induction on `d`" is a route choice, not forced
  (`notes/PencilNatural.md` §3): fixing heights and adding one breaks the contraction step, which
  moves the picture along a curve and every height with it (`sec:main-component-contract`,
  `sec:pencil-d-contract`). The road map says so.

## Architectural choices made up front

- **No main result changes; Lean code and node statements only in slice 2** (the PI's later
  word). Slice 4's fold deletes one node and edits one Lean docstring, no code (the PI's word
  again, design doc §1). Elsewhere two labels are added, `sec:pencil-roadmap` and
  `rem:pencil-x0-flatness` (both landed). A `\uses` edge changes only where a cut sentence was its
  node's only citation of it (slice 5), and then only after `scripts/blueprint-deps.py --label`
  shows the Lean does not reach it.
- **One home for the route.** The road map carries the route across the three chapters and the KT
  correspondence; the chapters keep their section guides and point at it (the PI, Q1).
- **Every claim cites a landed node or a KT page.** An intuition is written only as far as the nodes
  bear it out; probe evidence stays in the notes.
- **Register:** `blueprint/AUTHORING.md` (*Audience & vocabulary*, *Citations*, *Proof
  verbosity*); no phase or Lean name in chapter prose (`lint.sh` check 5).

## Lemma checklist

- [x] **1. Slice 1 — the road map** (`pencil.tex`; Opus). `\subsection{Road map of the proof}`,
  `sec:pencil-roadmap`, after the introduction, which gains one sentence naming it (its other route
  sentences are slice 4's). KT pp. 649–650 cited once; the shape and the three parts (A with
  `K₄ ⊃ C₄` and KT Theorem 4.9's role, D-d; B with the steps, the coverage, the base through
  Jackson–Jordán, KT Cases I–III and Lemmas 4.5–4.6, D-e; C with `K_{2,3}` and `K₄`), the
  dependencies (D-h), no induction on `d` (a choice), and I1–I4 as four short paragraphs, I3
  without its panel sentence (slice 3). About 230 TeX lines, over the pinned ~200. KT's II/III split:
  no step of `def:pencil-x0-reduces` (nor of the `d ≥ 4` ear steps) splits on zero or positive
  deficiency; only the search for a core does, which the road map says.
- [x] **2. Slice 2 — the main-component statements go** (Lean and the four chapters; Opus; at the
  PI's word, design doc §1, D-c). Deleted: `X0Dist`, `X0Gen` (`Pencil/X0.lean` whole), `x0Dist`,
  `x0Gen`, and three `d = 3` lemmas orphaned with them, each with a kept every-dimension form:
  `Graph.X0Attains.of_twoEdgeConnected`, `Graph.X0Attains.hasDistinctPencilRealization`,
  `Graph.IsAdmissiblePicture.hasDistinctPencilRealization`. Nodes deleted:
  `def:pencil-main-component-statements`, `lem:pencil-x0-distinct-statement`,
  `lem:pencil-x0-attains-distinct`. Restated to their remaining pins: `thm:pencil-x0-generic-attains`
  (the attaining claim), `thm:pencil-x0-coverage` (without its two-edge-connected corollary),
  `thm:pencil-x0-main-component` (without the distinct realization) and
  `lem:pencil-config-distinct-realization` (without its rank clause). The prose mentions reworded
  (D-i); the main results' statements and axioms unchanged.
- [x] **3. Slice 3 — the flatness remark** (`main-component.tex`; Opus).
  `rem:pencil-x0-flatness`, *Planar-rigid sets over a main picture*, after the two `K_{2,3}`
  paragraphs: (F) at `d = 3` with its proof, steps (1)–(4) as pinned, each checked against the
  cited node's statement (the by-hand step runs on `lem:pencil-polynomial-section` at the
  non-roots of `A·D·P_W`, `A` admissible for `G`, `P_W` the equality's polynomial for `G[W]`);
  the degeneracy, one direction only, for every pencil realization with the configuration points
  as concurrency points; the two-hubs lemma as its instance over a main picture; the doubled
  triangle (singleton count by hubs in `Z`, feasibility construction checked by hand); C's ear
  step and the pendant triangle; one `d ≥ 4` sentence. The road map's C part and I3 cite it.
  Written otherwise than pinned, no pinned step failing: the pair is "two pencil hubs adjacent or
  with a common neighbour" (the same condition, no new term in the road map); at `d ≥ 4` the
  points of `W` *lie in* one three-dimensional subspace, not *span* it (spanning needs three
  non-collinear picture points in `W`, which a main picture of `G` is not shown to give); the
  `K_{2,3}` paragraph proves `def₂ = 0` for the five bodies by `lem:deficiency-singleton-bound`
  (every nonempty set of them has nonnegative singleton value in `K_{2,3}`) rather than citing
  `rem:pencil-x0-theta`, which only asserts it; C's step is "over a main picture the panels of
  `a` and `b` coincide", with no claim about the closure `X₀`. The construction needs only
  pairwise independent hub normals and nonzero points on the lines; it is written with
  independent normals and distinct points, as `K_{2,3}`'s is.
- [ ] **4. Slice 4 — `pencil.tex` and `main-component.tex` point at the road map** (Opus).
  - `pencil.tex` introduction: the sentences restating the route across chapters (from "It is the
    case $d = 3$ of the conditioned pair" to "…gives the third") go for the pointer (decision D-f).
  - `sec:pencil-reduction`'s lead: the KT Lemmas 4.5–4.6 sentences and the KT Theorem 4.9 paragraph
    become the PI's one glue sentence with a pointer, and one that the cases ask neither a proper
    rigid subgraph nor a vertex of degree two; first confirm the road map carries what is cut.
  - `sec:pencil-main-component-route`: keep the lifting idea; the route sentences the road map
    carries go for a pointer.
  - `main-component.tex` introduction: the first paragraph's route sentences (`\Cref{sec:pencil-d}`
    runs the argument … needs a further argument) go for one pointer; the notation list and the
    section guide stay.
  - **The fold** (the PI, design doc §1, with the coordinator's slice-number correction beside
    it). Delete `thm:pencil-x0-generic-attains` (its statement is the coverage's second claim, its
    pin `Graph.IsX0Graph.x0Attains` already on `thm:pencil-x0-coverage`; no node `\uses` it) with
    its lead ("We close with the main theorem …"), keeping anything there the road map lacks.
    Repoint every citation of it tree-wide to `thm:pencil-x0-coverage`: at HEAD `47116a52`,
    `main-component.tex`:7 and :150 (introduction and section guide), `pencil.tex`:1006
    (`sec:pencil-main-component-route`), `intro.tex`:328, and the one Lean docstring,
    `Graph.IsX0Graph.x0Attains`'s in `Pencil/MainComponent/CoverageTheoremS.lean` (comment only).
    `pencil-d.tex`, named in the PI's option text, has none at HEAD; grep again at the slice.
    Retitle `sec:main-component-statements` again, as "and the main theorem" no longer fits once
    the theorem goes (D-i; label kept). Gates beyond slice 1's: the deletion gate (grep the label
    tree-wide), the moved-pin gate (`scripts/check-docstring-labels.py` diffed against the
    parent), and a foreground `lake build` for the docstring edit.
  - **Gates** as slice 1.
- [ ] **5. Slice 5 — `pencil-d.tex`** (Opus).
  - The introduction gains the pointer; its section guide and the polar paragraph stay.
  - `sec:pencil-d-reduction`'s `d = 3` sentences per decision D-b; the commit message lists each
    with its verdict. After slice 2: :4200–4202 and :4218–4228 (keep; slice 2 cut that paragraph's
    other `d = 3` clause with its node); :4298–4304, :4358, :4385, :4422, :4482–4485, :4559–4566,
    :4667–4674, :4725–4734 (judge by the rule). `lem:pencil-d-cut-case`'s
    proof `\uses` `lem:pencil-cut-nondegeneracy` only for its comparison sentence: drop the edge
    only if that sentence goes and `blueprint-deps.py --label lem:pencil-d-cut-case` shows no reach.
  - Read against the road map, change only where they duplicate it: `sec:pencil-d-coverage`'s lead,
    the remark after `thm:pencil-d-generic`'s proof (D1's; keep). The end of that proof now names
    the third conjunct of `thm:pencil-realization-theorem` (slice 2).
  - **Gates** as slice 1, plus `blueprint-deps.py` if a `\uses` changed.
- [ ] **6. Close (43d, and with it Phase 43).** `PHASE-BOUNDARIES.md`'s full-phase close: ROADMAP
  row 43 to ✓ and §43 to one paragraph; README, `home_page/index.md` (row 43) and `intro.tex`
  re-summarized, the road map linked from `intro.tex`; `formalization.yaml`'s scope, and the
  headline-axioms harness run byte-compared with 43c's (no new main result); the end-to-end re-read
  of the three chapters' touched prose and the ledger's Phase-43 section
  (`notes/BlueprintExposition.md`); the design doc compressed (layers to verdicts, its header
  closed); `notes/MolecularConjecture.md`, `notes/PencilNatural.md`'s header; the dispatch log
  groomed; `.claude/autopilot/queue.toml`'s `PENCIL-NATURAL` row `done = true`; the project
  organization review. Next: ORIGAMI's open, with the PI.

## Blockers / open questions

None. (The duplicate theorem slice 2 left is settled: the PI chose the fold, design doc §1; it is
item 4's.)

## Hand-off / next phase

The next concrete commit is *Current state*'s: slice 4, whole, with the fold, at the Opus rung (the
PI: Opus throughout). Then slice 5, then the close, which closes Phase 43; ORIGAMI opens after it,
with the PI.

## Decisions made during this phase

The PI's answers of 2026-11-08 (where the road map goes, structure and intuitions, the flatness
remark unpinned, open now) are design doc §1. The open settled EXPO's small items (design doc §2):

- **D-a. `thm:pencil-reduction` stays in `pencil.tex`.** The road map introduces A there, its
  statement has no dimension, and its motivation (`K₄ ⊃ C₄`, the cross-incidences) is that
  chapter's; KT too state their induction (§4) apart from its cases' implementation (§6).
- **D-b. `sec:pencil-d-reduction`'s `d = 3` sentences:** keep one that states a route fact (what the
  case `d = 3` gives, or which node it is) or reads a polar object at `d = 3` in one clause; cut one
  that compares a proof with a `d = 3` proof ("the dimension enters in … places"), since 43b left
  no `d = 3` proof of these cases.
- **D-c. The main-component statements go** (the PI, design doc §1, the 43d coordinator's session;
  the open had kept them). Slice 2 removed them with their node and what only they used (item 2).
  `thm:pencil-x0-generic-attains` kept its attaining claim alone, the coverage's second claim
  under the same pin; at the PI's later word (design doc §1) slice 4 folds it into
  `thm:pencil-x0-coverage`, as the every-dimension chapter has one node for that claim.
- **D-d. The KT Theorem 4.9 correspondence goes in the road map,** with Cases I–III, since it spans
  A and B and only the road map covers both; `sec:pencil-reduction` keeps the PI's one glue
  sentence, with a pointer (slice 4); no remark in the coverage.
- **D-e. Not "heir of KT Lemmas 4.5–4.6":** two counterparts, both without minimality, from
  sparsity. Part (1) of `lem:pencil-x0-sparse-count` is the degree count by which KT's proof of
  Lemma 4.6 finds a vertex of degree two from Lemma 4.5's bound (KT p. 664);
  `lem:pencil-d-chain-count` is Lemma 4.6's count along the chains, where a short chain gives a
  rigid set (`lem:pencil-d-chain-core`) as KT's absence of one gives a long chain.
- **D-f. The chapter introductions keep their section guides** (the PI, Q1); a sentence that
  restates the route across chapters goes for one pointer to `sec:pencil-roadmap`.
- **D-g. The flatness remark sits in `main-component.tex`** after the `K_{2,3}` paragraphs (Q3's
  first place), labelled so the road map can point at it; `d = 3`, with one `d ≥ 4` sentence.
  Landed in slice 3 (item 3, with what it writes otherwise than pinned).
- **D-h. The dependency sentence holds for the inductions, with one refinement** (slice 1, against
  the `\uses` closure of the three nodes; measured, script not retained). A reaches B only through
  `lem:pencil-d-distinct-statement`; C reaches B's conclusion only in `thm:pencil-d-generic`'s case
  without a planar-rigid set, but also uses lemmas of B's chapter (Jackson–Jordán, the partition
  estimates, five of `sec:main-component-statements`), which the road map says. Nothing in B or C
  reaches `thm:pencil-reduction` or A's cases; B reaches nothing of C. Shared lemmas in A's
  subsection: `lem:pencil-contraction-deficiency` (A's case (iv), B's contractions) and
  `lem:pencil-cut-nondegeneracy` (A's cut case; C's cut-edge step cites its construction).
- **D-i. Slice 2's wording.** `sec:main-component-statements` is retitled *Nondegeneracy, and the
  main theorem*, and `sec:pencil-main-component-route` *Lifting planar pictures, and the theorem*;
  both labels kept, as renaming one would touch ten Lean module headers for an internal name.
  `lem:pencil-d-distinct-statement` keeps its label under a reworded title, and the prose calls its
  content an adjacent-distinct realization of the whole multigraph. `intro.tex` and the README keep
  Phase 39's reduction as history, in words. The fold retitles the first subsection again (item 4).
