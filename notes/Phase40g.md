# Phase 40g — PENCIL-X0 / CHAIN: the ear steps and the cycle (work log)

**Status:** in progress (opened design-first 2026-09-27). STEPS' third group (`notes/Phase40-design.md`
§3 STEPS). It lands the base of the `X₀` induction and its two unconditional ear steps: every
cycle attains (BASE, (MC-21)(a)'s base), and if `X₀(G[V₁])` attains, `X₀(G)` attains for an open
ear with `k ≥ 5` interior bodies, its ends possibly adjacent, or a closed ear with `k ≥ 2`
((MC-20)). The design recon's spike proved the whole group sorry-free; it landed in two build
commits (the coordinator's decision), and all fourteen nodes are green. **Next: the close** (docs
and blueprint only) — see *Hand-off*.

## Current state

**Both builds landed; all fourteen nodes are green**, with statements from the spike and
`ledger.py --brief` on (MC-16)–(MC-21), (MC-134) and (MC-177) (Steps MC10, MC13, MC20):
- `rigidity-matrix.tex` §`sec:molecular-rigidity-matrix-blocks` (build 1): `def:relative-screws`
  (it pins the landed `BodyHingeFramework.relScrews` and `jointRows`, part of Phase 39's D5 debt),
  `lem:block-rank-two-cut` (B5′/B6′, then B5/B6 as their induced corollaries),
  `lem:block-rank-path`, `lem:block-rank-ear`;
- `deficiency.tex` (build 1): `lem:deficiency-ear`;
- `main-component.tex`, §`sec:main-component-chain` (build 2): six lemmas and the three theorems
  `thm:pencil-x0-cycle`, `thm:pencil-x0-open-ear`, `thm:pencil-x0-closed-ear`; the unpinned
  `rem:pencil-x0-ear-class` records that (MC-21)(a)'s class theorem is not stated (PI decision 4).

**Headline axioms** (build 2; `lake lean` on a scratch `#print axioms` file against the built
tree): `Graph.X0Attains.of_cycle`, `Graph.X0Attains.of_openEar` and `Graph.X0Attains.of_closedEar`
each print `[propext, Classical.choice, Quot.sound]`.

**The next concrete commit is the close** (*Hand-off*).

- **The spike** (gitignored `scratch/40g/`, local to this checkout) has landed except its two
  instances (`StepG`, `StepH`) and the step-contract prerequisites `S40gPrereq.lean`. Before build 2
  its parts, assembled under `import …MainComponent.Ear`, gave 0 errors and 90 warnings under
  `lake lean`; all were fixed at the source (*Decisions made*).
- **Satisfiability (kernel-checked in the spike, not landed).** θ(1,2,6), a triangle with an open
  ear of five interior bodies on two adjacent bodies (`of_cycle`, then `of_openEar`), and the
  bowtie, a triangle with a closed 2-ear, attain over every infinite field with no hypotheses; (H)
  is proved in Lean for both. By hand, a square with a 5-ear joining opposite corners satisfies
  `of_openEar` with `a ≁ b`.
- **Faithfulness** (the coordinator, against Step MC10): the ear is `a − x₁ − ⋯ − x_k − b`, open iff
  `a ≠ b`, closed iff `a = b` with `k ≥ 2`; (MC-20) is the closed ear or the open ear with `k ≥ 5`.
  The Lean asks less of `G′` than the workbook ((H) at `G`, attainment at `G[V₁]`, no (H) at `G′`),
  so it is a stronger theorem. BASE's `k ≥ 1` is a cycle of length at least 3.

## Architectural choices made up front

- **The route** (the recon's verdict; design doc §3 STEPS, *CHAIN*):
  - **Rank.** B6′ glues ranks at a 2-cut whose sides are any two graphs partitioning the links
    (the landed B6 takes induced sides, and with `a ∼ b` the induced far side is the path plus `ab`). The path brick (MC-177)(i)(ii)
    holds both ways: rank `(D − 1)(k + 1)`, and `relScrews` is the span of the hinges. So the ear
    rank law, (MC-16) in rank form, holds at every adjacency and every `k`:
    `rank F = rank F[V₁] + (D − 1)(k + 1) + dim(ρ ⊔ Λ) − D`.
  - **Deficiency.** Only (MC-17)'s lower half, `def(G[V₁]) + k + 1 − D ≤ def(G)`, open or closed;
    `Graph.x0Attains_of_exists` supplies the upper rank bound.
  - **Open ear, `k ≥ 5`.** One picture off `G[V₁]`'s attainment polynomial, `G`'s main-picture
    polynomial and the span polynomial `Plam`; heights at a common non-root in `L_G(q)` of `G[V₁]`'s
    restricted attainment polynomial and `Rlam` (`exists_mem_eval_ne_zero₂`); six ear joins give
    `Λ = ⊤`. (MC-19)(b)'s "for any flag pair" becomes a witness inside the fibre: the height `1`
    at `x₂`, `x₃` and `0` elsewhere lies in `L_G(q)` at every admissible `q` (it needs `k ≥ 4`), and
    the hexagon certificate at a collapsed picture (`p_a = p_b`) makes `Plam` nonzero.
  - **BASE.** Every height on `V(G)` lifts (three points impose nothing); certificates for
    `n = 3..6`, and `n ≥ 7` collapses onto the hexagon; the edge `ab` is the path brick at `k = 0`.
  - **Closed ear.** `of_cutVertex` plus `of_cycle` on `G[{c} ∪ range x]`, reusing the ear's labels
    (closing edge `e 0`); no `β`-headroom, and `ChainData` is never needed.
  - Neither step-contract prerequisite is used (design doc §3 STEPS, the step contract).
- **The PI's decisions, verbatim** (2026-09-27; also `notes/pencil/adjudications.md`):

  ```adjudication
  PI decisions, 2026-09-27, on the CHAIN design recon's verdict (verbatim answers to the coordinator's questions):
  1. Placement — "Where should CHAIN's new declarations go? The recon's layout: the 2-cut generalization in RigidityMatrix/Bricks.lean; pathVertex lemmas + a three-point lemma in MainComponent/Cut.lean (922→~1010); the point-join/flat pieces in Flat.lean (692→~870); a new MainComponent/Ear.lean (~960: path brick, ear rank law, ear deficiency bound, certificates) and a new MainComponent/Chain.lean (~890: the three step theorems). Carrier.lean and Contract.lean untouched.": "As listed, B5/B6 in place (Recommended)" — the recon's layout; B5/B6 re-proved as corollaries of the new B5′/B6′ with unchanged statements and pins (40f precedent); Bricks stays near 1450 lines.
  2. Closed ear — "The closed ear (half of (MC-20)) is off (MC-89)'s route: COVERAGE never consumes it. Keep it as a named theorem?": "Named theorem (Recommended)" — keep Graph.X0Attains.of_closedEar (~130 lines, faithful to (MC-20), already spiked: of_cutVertex + of_cycle).
  3. BASE form — "How should BASE (a cycle attains) take its cycle?": "Edge + ear (Recommended)" — as spiked: 'edge ab plus the path a…b', the same explicit-path format as the ear steps. A CycleData adapter (~60 lines) lands later only if COVERAGE's cycle case produces CycleData.
  4. Scope — "The design doc's CHAIN scope lists items CHAIN never consumes: (MC-169), (MC-134)(b) at k ≤ 4, (MC-134)(c), (MC-19)(c), (MC-18)(b), exact (MC-17), and the A2/A3, jointMotions, weldedRank pins; also (MC-21)(a)'s class theorem, which dissolves into COVERAGE's strong induction. What happens to them?": "Move to first consumer (Recommended)" — re-home each item to SHORT or ORBIT, whichever consumes it first; leave (MC-21)(a)'s class theorem unstated (a remark records that it dissolves into COVERAGE).
  ```
- **The coordinator's decision: two build commits, by fresh opus builders, split at the spike's
  part boundary** (the recon's own alternative). Build 1 is `S40gRank.lean` + `S40gDef.lean` (spike
  lines 1–593): the rank and deficiency side, turning the three red `rigidity-matrix.tex` nodes and
  `lem:deficiency-ear` green. Build 2 is `S40gGeom.lean` + `S40gCert.lean` + `StepA`–`StepF` (lines
  594–2 160): the nine `main-component.tex` nodes. Two, because the spike is 2 414 lines with 323
  warnings of lint debt and build 1 re-proves B5/B6 in the fragile zone; 40f's single build of a
  ~1 500-line file took 362k tokens / 59 min.
- **Decision 4's two items with no consumer.** (MC-19)(c) and (MC-134)(c), the closed-ear span, are
  not in (MC-89)'s tree (Step MC20, Part I), and neither SHORT nor ORBIT consumes them; the design
  doc lists them as off the route (§2) rather than naming a consumer.

## Lemma checklist

The lemma index is the blueprint's `\lean{}` lists (forward mode); files and nodes here.

- [x] `def:relative-screws` — the landed `BodyHingeFramework.relScrews`, `jointRows` (Phase 39),
  green at the open.
- [x] **Build 1** — `RigidityMatrix/Bricks.lean` (B5′/B6′ over link-partitioning sides, B5/B6 as
  corollaries → `lem:block-rank-two-cut`), `Cut.lean` (`pathVertex_last`, `pathVertex_injective`),
  new `Ear.lean` (the path brick → `lem:block-rank-path`, the ear rank law → `lem:block-rank-ear`,
  `Graph.deficiency_induce_add_le_of_ear` → `lem:deficiency-ear`).
- [x] **Build 2** — `Cut.lean` (the three-point lemma → `lem:pencil-three-points`, three
  `pathVertex` helpers), `Flat.lean` (`pointJoin` and the join polynomials →
  `lem:pencil-join-flat`, `lem:pencil-join-independence-open`), `Ear.lean` (the ear's heights, the
  certificates, the hinge span → `lem:pencil-ear-fibre`, `lem:pencil-chain-span-certificates`,
  `lem:pencil-ear-hinge-span`), new `Chain.lean` (`Graph.X0Attains.of_cycle`, `…of_openEar`,
  `…of_closedEar` → the three theorems).
- [ ] **The close** (docs and blueprint only) — see *Hand-off*.
- **Not landed:** the instances (`StepG`, `StepH`) and `S40gPrereq.lean`.

## Blockers / open questions

- None. The spike compiles the whole group; what remains is transcription with the placement.

## Hand-off / next phase

**Next: the close** (docs and blueprint only; the checklist's last item and
`PHASE-BOUNDARIES.md` *When this commit closes a phase*):
- the end-to-end re-read of `main-component.tex` §`sec:main-component-chain` against the landed
  Lean (every node is pinned and green; the prose was written at the open);
- the exposition ledger `notes/BlueprintExposition.md` — a candidate: the witness inside the fibre
  that replaces (MC-19)(b)'s "for any flag pair" (`thm:pencil-x0-open-ear`);
- the headline axioms (recorded in *Current state*), the design doc's §3 STEPS (CHAIN done; SHORT
  and ORBIT inherit the re-homed items of PI decision 4), the ROADMAP row and §40g;
- the public surfaces stay unchanged (the PI's standing call, recorded at 40f's close).

## Decisions made during this phase

- **2026-09-27 — opened design-first from one opus recon** (read-only, 718k tokens / 176 tools /
  78 min). The coordinator re-ran its spike under both `lake env lean` and `lake lean` (*Current
  state*), checked its statements against Step MC10, and chose two build commits. The recon's
  verdict is in the design doc's §3 STEPS.
- **2026-09-27 — build 1 landed** (the rank and deficiency side, one fresh opus builder): the spike's
  proofs with the binder fix and the deprecations replaced; B5′/B6′ over any two link-partitioning
  graphs, B5/B6 one-term corollaries, the induced-side privates gone. FRICTION: the
  `Set.ncard_range_le` mirror candidate and one elaboration idiom.
- **2026-09-27 — build 2 landed** (the steps, one fresh opus builder). The spike's proofs, its 90
  `lake lean` warnings fixed at the source: `if_pos`/`if_neg` → `ite_eq_left`/`ite_eq_right`, `show`
  → `change`, `simp?` lists for the flexible certificate eliminations, `one_add_one_eq_two` for the
  `<;> norm_num` tails, reflowed lines. Every declaration has a docstring; the nine nodes are pinned.
  FRICTION: the `Molecular.Matrix` capture of `open scoped Matrix` (lifted to TACTICS-QUIRKS § 56),
  the certificate idiom, a `crossProduct` ring-hom mirror candidate, `Set.ncard_range_le`'s second
  call site.
