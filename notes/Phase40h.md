# Phase 40h — PENCIL-X0 / SHORT: the open ears with two, three and four interior bodies (work log)

**Status:** ✓ complete (opened design-first, built and closed 2026-09-27). SHORT, STEPS' fourth
group (`notes/Phase40-design.md` §3 STEPS), proved the open-ear steps with `k = 2, 3, 4` interior
bodies, the ends possibly adjacent: if `X₀(G[V₁])` attains, `X₀(G)` attains for `k = 2` when
`def₃(G[V₁]) ≤ def₃(G)` ((MC-54); PI decision 4(a)), and for `k = 3, 4` when `X₀` also attains at `G`
with its second interior body suppressed ((MC-181), (MC-180): found by formalization, second-read).
**Next: 40i = ORBIT, opened 2026-09-28** — see `notes/Phase40i.md`.

## Current state

**Closed.** Six build commits (B1 `89a9c446`, B2 `ca7c2f43`, B3–B4 `8fc12079`, B6 `57a07b77`, B5
`fd24389c`, B7 `a3ec5a8d`), the `Carrier.lean` split (`3f7f272d`) and the close landed. The fourteen
nodes are green:
- `main-component.tex` §`sec:main-component-short`: the line geometry (`def:pencil-line-pairing`,
  `lem:pencil-line-pairing-join`, `lem:pencil-tetrahedron`, `lem:pencil-two-stars`,
  `lem:pencil-plane-lines`, `lem:pencil-bilinear`, `lem:pencil-insertion`), `lem:pencil-ear-data`,
  and `thm:pencil-x0-open-ear-two`, `…-four`, `…-three`, with the unpinned remarks after the three
  theorems and `rem:pencil-x0-theta` (PI decision 3);
- §`sec:main-component-carrier`: `lem:pencil-picture-local`;
- `molecular-induction.tex`: `lem:splitoff-deficiency-reuse`; `deficiency.tex`:
  `lem:deficiency-ear-merge`.

The Lean is `Molecule/Pencil/MainComponent/Lines.lean`, `EarGen.lean` and `Short.lean` (their module
docstrings list the statements), with `Configuration.lean` split out of `Carrier.lean`, and pieces
placed by PI decision 5's convention in `Carrier.lean`, `Flat.lean`, `Ear.lean`, `Cut.lean`,
`RigidityMatrix/Bricks.lean`, `AlgebraicInduction/Pinning.lean` and
`Induction/SplitOffDeficiency.lean`. The spikes (`scratch/40h/`, `scratch/40h-read/`,
`scratch/40h-eargen/`, gitignored and local to this checkout) are all consumed.

**Headline axioms, re-verified at the close** on 49 declarations: the eighteen `formalization.yaml`
main results and the thirty-one pins of the fourteen nodes. All 49 are exactly
`[propext, Classical.choice, Quot.sound]`. *Measured, script not retained*: one `#print axioms` line
per declaration under `import CombinatorialRigidity`, run with `lake lean` on the fully built tree
(a full `lake build` first: 2 982 jobs, 0 warnings).

- **Satisfiability (kernel-checked in the steps spike, not landed).** θ(1,2,4), the triangle `0 1 2`
  with the open ear `0 − 3 − 4 − 5 − 1`, meets `of_openEar_three`'s hypotheses, and its antecedent
  `θ(1,2,4).splitOff 4 3 5 4` is θ(1,2,3) in `of_openEar_two`'s format, so the antecedents chain. By
  hand, not kernel-checked: `hdef` there is `def₃(K₃) = 0 ≤ def₃(θ(1,2,3))`, and θ(1,2,5) is the
  `k = 4` pattern.
- **Faithfulness** (against (MC-180), (MC-181), (MC-54)): the Lean's `x 0, …, x (k − 1)` are the
  workbook's `x₁, …, x_k`, so `G.splitOff (x 1) (x 0) (x 2) (e 1)` suppresses the workbook's `x₂` and
  relinks the label of `x₁x₂` to `x₁x₃`, as (MC-180) states. The steps ask (H) at `G` only, as 40g's
  do. `of_openEar_two` takes `hdef` in place of (MC-54)'s `δ = 0` (PI decision 4(a)).
- **`rem:pencil-x0-theta`'s counts** (measured, script not retained; an exhaustive partition
  enumeration): `def₂ = def₃ = 0` at `K₄ − e` and `K_{2,3}`, and `def₃(C_s) = 0` for `s ≤ 6`.

## Architectural choices made up front

- **The route** (the recon's verdict, second-read; as landed, the *SHORT done* paragraph of
  `notes/Phase40-design.md` §3 STEPS): the ear rank law reduces each step to
  `dim(ρ ⊔ Λ_k) ≥ k + 1 + def₃(G[V₁]) − def₃(G)`; `k = 2` at one picture; `k = 3, 4` by putting `x₂`
  back into `G″`, over base data fixed before the ear data (EARGEN), counted with (MC-182) and the
  landed `Graph.deficiency_induce_add_le_of_ear`.
- **The PI's decisions, verbatim** (2026-09-27; also `notes/pencil/adjudications.md`, the SHORT
  entry and the *SHORT opens as 40h* entry):

  ```adjudication
  PI decisions, 2026-09-27, on the SHORT design recon's verdict (verbatim answers to the coordinator's questions):
  1. The k = 3, 4 proofs — "The recon re-proved the k = 3 and k = 4 open-ear steps by a new, shorter route. Remove one ear body; putting it back raises dim(ρ + Λ) by one unless the span already holds every line meeting a fixed line. At k = 4 a tetrahedron rules that out; at k = 3 a bilinear (Klein-pairing) lemma does. This replaces (MC-24)/(MC-136)'s four-orbit collision and (MC-45)'s r-split. It is new mathematics, found by formalization. How should it be handled?": "Workbook, 2nd read, then open" — the ORBIT precedent: a workbook commit of the new claims (next MC labels, 'found by formalization') first, then a fresh read-only opus second reading, then 40h opens.
  2. The k = 1 cell — "Where should the k = 1 cell ((MC-54) at k = 1, with (MC-174) and (MC-48)(ii)) go? The recon proposes 40h = B1–B7 (the k = 2, 3, 4 steps and their infrastructure, about 7 builds + open + close) and moving the k = 1 cell (about 2 builds) out.": "Fold into ORBIT" — ORBIT already consumes (MC-174), (MC-48)(ii) and Jackson–Jordán at the split-off, so the k = 1 cell's two builds join ORBIT's group; 40h stays at 7 builds.
  3. THETA — "THETA ((MC-139): every simple θ-graph attains) turns out to be an assembly of step theorems plus FLAT at K₄ − e and K₂,₃. How should it land?": "Dissolve into COVERAGE" — no named theorem; a remark records that COVERAGE's strong induction covers θ-graphs, as with (MC-21)(a)'s class theorem in 40g.
  4. Small calls — "(a) The k = 2 step takes the hypothesis def₃(G[V₁]) ≤ def₃(G), with a bridge lemma from δ = 0, not δ = 0 through the δ machinery. (b) Off-route items (MC-44), (MC-136), (MC-24), exact (MC-17) and (MC-134)(b) at k = 3, 4 go to 'Not needed'; the jointMotions/weldedRank/A2/A3 pins go to their first consumers (SPLITOFF/ORBIT/COVERAGE); (MC-175)(iii) goes to ORBIT. (c) The label-reusing split-off deficiency bound lands as an additive successor lemma, with no landed call site moved.": "Accept all three".
  ```

  ```adjudication
  PI decision, 2026-09-27, on 40h's placement (verbatim answer to the coordinator's question):
  5. Placement — "Where should 40h's new general pieces go? The recon's layout: new MainComponent/Lines.lean (line geometry, including two pointJoin lemmas), new EarGen.lean (including the picture-locality congr lemmas for liftingSpace/IsAdmissiblePicture), new Short.lean (the three step theorems), plus SplitOffDeficiency.lean and Ear.lean. Convention would put the congr lemmas in Carrier.lean (1 496 lines; the plan recorded at 40b is to split it first) and the pointJoin lemmas in Flat.lean (865).": "Convention, split Carrier" — one extra commit at B3 splits Carrier.lean along its section headers (as planned at 40b; rebuilds the downstream Phase-40 modules once), then the congr lemmas go beside their definitions; the pointJoin lemmas go in Flat.lean. The 40f 'convention everywhere' precedent.
  ```
- **The builds** were the design doc's plan table, B1–B7 with the `Carrier.lean` split before B3;
  they landed as six commits and the split (B3–B4 as one, B6 before B5: the coordinator's calls).
- **Blueprint placement.** The general pieces sit beside their related nodes, as 40g's did; the
  steps are ordered two, four, three, as the workbook states (MC-180) before (MC-181).

## Lemma checklist

All landed with the standard axioms (*Current state*); pins in **bold**.

- [x] **B1** (`89a9c446`) — new `Lines.lean`: **`kleinLin`** → `def:pencil-line-pairing`, and the
  pins of the six line-geometry lemmas; five `pointJoin` helpers in `Flat.lean`.
- [x] **B2** (`ca7c2f43`) — **`Graph.splitOff_deficiency_le_of_eq_left`** →
  `lem:splitoff-deficiency-reuse`; **`Graph.deficiency_induce_le_of_ear_of_merge`** →
  `lem:deficiency-ear-merge`.
- [x] **The `Carrier.lean` split** (`3f7f272d`) — new `Configuration.lean`; no pin moved.
- [x] **B3–B4** (`8fc12079`) — **`Graph.isAdmissiblePicture_congr`**, **`Graph.liftingSpace_congr`**
  → `lem:pencil-picture-local`; new `EarGen.lean`, nine pins → `lem:pencil-ear-data` (restated to
  the EARGEN spike's shape).
- [x] **B6** (`57a07b77`), **B5** (`fd24389c`), **B7** (`a3ec5a8d`) — new `Short.lean`:
  **`Graph.X0Attains.of_openEar_four`**, **`…_two`**, **`…_three`** → the three theorems.
- [x] **The close** (docs and blueprint only): the end-to-end re-read, the exposition ledger, the
  headline axioms, the design doc, ROADMAP and `MolecularConjecture.md`; the public surfaces left
  unchanged (the PI's standing call, recorded at 40f's close).
- **Not 40h's:** the `k = 1` cell `of_openEar_one` (ORBIT, PI decision 2) and a named THETA theorem
  (PI decision 3).

## Blockers / open questions

- **None for 40h.** Four cleanup-round items from the close are tracked in the design doc's §3
  STEPS SHORT entry, none of them a gate for ORBIT.

## Hand-off / next phase

**40h is closed. The next step moved to `notes/Phase40i.md`:** ORBIT opened as 40i (2026-09-28),
design-first from a compiler-checked recon with no new mathematics, which also settled the tracked
`hδ₂` trace (the design doc's ORBIT entry).

**The cleanup-round items** (the design doc's SHORT entry, with line counts and plans):
- the split plans for `Short.lean` (1 366 lines) and `Bricks.lean` (1 458), for the next commit to
  grow either past ~1500;
- the B2 dedupe of `splitOff_deficiency_le_of_eq_left` against `splitOff_deficiency_le`;
- the three-body step's near-copies (open in FRICTION);
- the nine pins of `lem:pencil-ear-data`.

## Decisions made during this phase

- **2026-09-27 — the close.** The re-read made the preamble's three-body dichotomy precise (a
  relative screw pairs nonzero with some line joining the ends' planes, then with `x₁x₃` for a
  general ear), said the two-body witness picture need not be admissible, and fixed a wording each
  in the four- and three-body proofs; a remark after the three-body theorem is the exposition-ledger
  entry. The six unpinned helpers the prose names match landed declarations. `lem:pencil-ear-data`'s
  nine pins were recorded as a tracked item, not split: `EarGen.lean`'s docstrings cite it by clause.
- **B7** — the case split is one round-1 polynomial (Case A's condition a span bound);
  `exists_insertion_three` takes "both stars in `W` → `W = ⊤`"; `splitOff_ear_three` mirrors the
  four-body lemma (FRICTION: the near-copies).
- **B5** — mirrors `of_openEar`, not EARGEN: one picture, the heights `0`, `certHexagon`'s joins 4,
  5, 0 as the flat witness (the route note's `certSquare` witness was wrong: height `1`).
- **B6 before B5** (the coordinator's call); Steps 1–2 factored as `Graph.exists_earBase_splitOff`
  for B7; in the branch `W = Λ²K⁴`, `x₂` at `x₁`'s point (the collision witness).
- **B3–B4 as one commit** (the coordinator's call), by convention; `relScrews_congr` proved directly
  in `Bricks.lean`, which `Pinning.lean` imports (FRICTION: two downstream general facts).
- **The split** landed as `Configuration.lean` (the builder's name), cut at the C3 section header.
- **B2** — two direct per-partition extensions, no shared infrastructure (the dedupe is tracked).
- **B1** — a shorter insertion route (`exists_ne_zero_add_smul_notMem`); the `pointJoin` facts in
  `Flat.lean`.
- **At the open** — (MC-182) got its own red node; `isAdmissiblePicture_congr` and
  `exists_insertion_ge` stay pinned although the route does not consume them.
