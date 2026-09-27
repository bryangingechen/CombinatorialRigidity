# Phase 40h — PENCIL-X0 / SHORT: the open ears with two, three and four interior bodies (work log)

**Status:** in progress (opened design-first 2026-09-27). STEPS' fourth group
(`notes/Phase40-design.md` §3 STEPS, the SHORT entry). It lands the open-ear steps with `k = 2, 3, 4`
interior bodies, the ends possibly adjacent: if `X₀(G[V₁])` attains, `X₀(G)` attains for `k = 2`
when `def₃(G[V₁]) ≤ def₃(G)` ((MC-54); PI decision 4(a)), and for `k = 3, 4` when `X₀` also attains
at `G` with its second interior body suppressed ((MC-181), (MC-180): found by formalization,
second-read). Fourteen red nodes; seven builds B1–B7, plus the `Carrier.lean` split before B3 (PI
decision 5). **Next: B1, the line geometry** — see *Hand-off*.

## Current state

**Opened.** Fourteen red nodes, with statements from the recon's compiled step statements, the second
reader's compiled line geometry, and `ledger.py --brief` on (MC-54), (MC-179)–(MC-182) (Steps MC13,
MC14):
- `main-component.tex`, the new §`sec:main-component-short` (before the final statements subsection;
  the chapter preamble names it):
  - the line geometry (MC-179): `def:pencil-line-pairing` and the lemmas
    `lem:pencil-line-pairing-join`, `lem:pencil-tetrahedron`, `lem:pencil-two-stars`,
    `lem:pencil-plane-lines`, `lem:pencil-bilinear`, `lem:pencil-insertion`;
  - EARGEN: `lem:pencil-ear-data`;
  - the theorems `thm:pencil-x0-open-ear-two`, `thm:pencil-x0-open-ear-four`,
    `thm:pencil-x0-open-ear-three`;
  - the unpinned `rem:pencil-x0-theta`: θ-graphs are covered by COVERAGE's strong induction (PI
    decision 3);
- §`sec:main-component-carrier`: `lem:pencil-picture-local`, beside the definitions it reads (PI
  decision 5);
- `molecular-induction.tex`: `lem:splitoff-deficiency-reuse` ((MC-182)), after `lem:splitoff-deficiency`;
- `deficiency.tex`: `lem:deficiency-ear-merge` (COVERAGE's bridge from `δ = 0`), after
  `lem:deficiency-ear`.

No Lean has landed. **The next concrete commit is B1** (*Hand-off*): seven nodes green.

**The spikes** live in the gitignored `scratch/40h/` and `scratch/40h-read/`, local to this checkout
(builder pointers, not evidence):
- `scratch/40h-read/S40hReadGeom.lean` (563 lines), the second reader's line geometry. It supersedes
  the recon's `scratch/40h/S40hGeom.lean`. **`lake lean`**, re-run at this open (`f3c46221`, ~35 s):
  exit 0, 0 errors, 44 warnings, no `sorry`; its eighteen `#print axioms` lines are each
  `[propext, Classical.choice, Quot.sound]`.
- `scratch/40h/S40hSteps.lean` (177 lines): the four step statements (`of_openEar_one` is ORBIT's) and
  the two deficiency lemmas, proofs `sorry`, and the θ instances. **`lake lean`**, re-run at this
  open: exit 0, 0 errors, 14 warnings, six of them the disclosed `sorry`s.
- **Satisfiability (kernel-checked in the steps spike, not landed).** θ(1,2,4), the triangle `0 1 2`
  with the open ear `0 − 3 − 4 − 5 − 1`, meets `of_openEar_three`'s path hypotheses, and its
  antecedent `θ(1,2,4).splitOff 4 3 5 4` is θ(1,2,3) in `of_openEar_two`'s format (the ear
  `0 − 3 − 5 − 1` on the labels `3, 4, 6`, the freed label `4` relinked). So the antecedents chain.
  By hand, not kernel-checked: `hdef` there is `def₃(K₃) = 0 ≤ def₃(θ(1,2,3))`, and θ(1,2,5) is the
  `k = 4` pattern.
- **Faithfulness** (against (MC-180), (MC-181), (MC-54)): the Lean's `x 0, …, x (k − 1)` are the
  workbook's `x₁, …, x_k`, so `G.splitOff (x 1) (x 0) (x 2) (e 1)` suppresses the workbook's `x₂` and
  relinks the label of `x₁x₂` to `x₁x₃`, as (MC-180) states. The steps ask (H) at `G` only, as 40g's
  do. `of_openEar_two` takes `hdef` in place of (MC-54)'s `δ = 0` (PI decision 4(a)).
- **`rem:pencil-x0-theta`'s counts** (measured, script not retained; an exhaustive partition
  enumeration): `def₂ = def₃ = 0` at `K₄ − e` and `K_{2,3}`, and `def₃(C_s) = 0` for `s ≤ 6`.

**Statement provenance (the transcription guard: a red node's statement is checked by no gate).**
- The three theorems and the two deficiency lemmas come from `S40hSteps.lean` and `ledger.py
  --brief`.
- The seven geometry nodes come from `S40hReadGeom.lean`'s statements. The pairing identity is the
  compiled `kleinLin (pointJoin r s) (pointJoin p q) = det ![p, q, r, s]`; the spike's module
  docstring ("−det") and the theorem's docstring ("up to sign") are stale.
- `lem:pencil-picture-local` comes from the design doc's step-contract signatures (compiled in 40g's
  prerequisite spike).
- **`lem:pencil-ear-data` has no compiled statement.** It is transcribed from (MC-180)'s Steps 1–2
  (the base data, the ear data, (E1)–(E3)) and the recon's EARGEN description. If the Lean shape
  differs, B3–B4 restates it in the same commit (the changed-statement gate).

## Architectural choices made up front

- **The route** (the recon's verdict, second-read; the design doc's §3 STEPS, SHORT entry). The
  landed ear rank law reduces each step to `dim(ρ ⊔ Λ_k) ≥ k + 1 + def₃(G[V₁]) − def₃(G)` at one
  configuration where `G[V₁]` attains. `k = 2` is CHAIN-style, at one picture. For `k = 3, 4`, the
  body `x₂` is put back into `G″` along an insertion curve, with the tetrahedron (`k = 4`) or the
  bilinear lemma (`k = 3`) excluding failure. The count needs only (MC-182) and the landed
  `Graph.deficiency_induce_add_le_of_ear`. The `V₁` data are fixed before the ear data (EARGEN).
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
- **The builds** are the design doc's plan table: B1–B7, one commit each (B3–B4 may take two), with
  the `Carrier.lean` split as its own commit before B3.
- **Blueprint placement.** The general pieces sit beside their related nodes, as 40g's did. The
  steps are ordered two, four, three, as the workbook states (MC-180) before (MC-181) and as B6
  precedes B7.

## Lemma checklist

Planned names from the spikes. Pins in **bold**; the other names are helpers, unpinned.

- [ ] **B1, new `MainComponent/Lines.lean`** (source `S40hReadGeom.lean`):
  - **`kleinLin`** → `def:pencil-line-pairing`;
  - **`klein_pointJoin_pointJoin`**, **`eq_zero_of_kleinLin_eq_zero`** (`kleinLin_apply`,
    `kleinLin_comm`, `klein_pointJoin_same`, `flatSigma_pointJoin`, `flatPi_pointJoin`) →
    `lem:pencil-line-pairing-join`;
  - **`linearIndependent_pointJoin_tetra`**, **`span_pointJoin_tetra_eq_top`** (`tetA`, `tetB`) →
    `lem:pencil-tetrahedron`;
  - **`star`**, **`star_sup_star_le_ker_klein`**, **`five_le_finrank_star_sup_star`**
    (`pointJoin_mem_star`, `pointJoin_mem_star_right`) → `lem:pencil-two-stars`;
  - **`planeLines`**, **`finrank_planeLines_le`**, **`pointJoin_liftPlane_mem_planeLines`**
    (`liftPlane`, `planarProj_liftPlane`, `mem_planeLines`) → `lem:pencil-plane-lines`;
  - **`klein_liftPlane`**, **`finrank_sup_le_three_of_klein`** → `lem:pencil-bilinear`;
  - **`exists_insertion_ge`**, **`exists_insertion_gain`** (`exists_ne_zero_linearIndependent_affine`,
    `linearIndependent_basis_sumElim_one`, `…_two`) → `lem:pencil-insertion`.
  - In `Flat.lean`, beside `pointJoin` (PI decision 5): `pointJoin_add_smul_left`, `pointJoin_self`
    (helpers). The spike's `pointJoin_swap` is a `pointJoin` fact too; the same convention may put it
    there (the builder's call).
- [ ] **B2** — `Induction/SplitOffDeficiency.lean`: **`Graph.splitOff_deficiency_le_of_eq_left`** →
  `lem:splitoff-deficiency-reuse`, and the module docstring's "KT 4.3(ii)" corrected to 4.3(i);
  `MainComponent/Ear.lean`: **`Graph.deficiency_induce_le_of_ear_of_merge`** →
  `lem:deficiency-ear-merge`.
- [ ] **The `Carrier.lean` split** (its own commit, before B3; PI decision 5; the plan is the design
  doc's §3 CARRIER): C3–C5′ to a second file, C1–C2 left in `Carrier.lean`, the root import
  updated. No declaration is renamed, so no pin moves.
- [ ] **B3–B4** — `Carrier.lean`, beside their definitions: **`Graph.liftingSpace_congr`**,
  **`Graph.isAdmissiblePicture_congr`** → `lem:pencil-picture-local`; new `MainComponent/EarGen.lean`:
  the EARGEN device → `lem:pencil-ear-data` (names are the build's; the node may be restated,
  *Current state*).
- [ ] **B5**, new `MainComponent/Short.lean`: **`Graph.X0Attains.of_openEar_two`** →
  `thm:pencil-x0-open-ear-two`.
- [ ] **B6**: **`Graph.X0Attains.of_openEar_four`** → `thm:pencil-x0-open-ear-four`; its docstring
  cites (MC-180), not (MC-25).
- [ ] **B7**: **`Graph.X0Attains.of_openEar_three`** → `thm:pencil-x0-open-ear-three`; its docstring
  cites (MC-181), not (MC-45).
- [ ] **The close** (docs and blueprint only): the end-to-end re-read of the new subsection, the
  exposition ledger (a candidate: the insertion argument, which replaces the informal proof's orbit
  case analysis), the headline axioms, the design doc's §3 STEPS, ROADMAP; the public surfaces stay
  unchanged (the PI's standing call, recorded at 40f's close).
- **Not 40h's:** the `k = 1` cell `of_openEar_one` (ORBIT, PI decision 2; its compiled statement is in
  the steps spike and the design doc's ORBIT entry), and a named THETA theorem (PI decision 3).

## Blockers / open questions

- None blocking B1.
- **B3–B4 is the high-risk build** (MvPolynomial substitution), and its node has no compiled statement
  (*Current state*).
- **Two pieces of the step proofs have no compiled form**, which the recon left open: the affine
  witness of a nonzero bilinear form (B7) and the meet-to-join transport of `ρ ⊔ Λ` (B6, B7). The
  design doc records them under the plan table.
- **ORBIT's open flag is not 40h's.** The supply of `of_openEar_one`'s `hδ₂`, which fails at `K_{2,3}`,
  is the tracked item in the design doc's §3 STEPS, ORBIT entry.

## Hand-off / next phase

**Next: B1, the line geometry (fresh builder).** Source: `scratch/40h-read/S40hReadGeom.lean`
(gitignored, local to this checkout), not the recon's superseded `S40hGeom.lean`. Targets: the seven
B1 nodes (the checklist's names). Chores:
- **`lake lean` the source first** (TACTICS-QUIRKS §55): 44 warnings of lint debt at this open.
- **New `Lines.lean`**, importing the least module that provides what it uses. The spike imports
  `…MainComponent.Chain`; `pointJoin`, `planarProj` and `flatScrewEquiv` are in `Flat.lean`, and the
  rest is to be checked by name. Add it to the root import.
- **`Flat.lean`** (865 lines): the two `pointJoin` lemmas of the checklist, beside `pointJoin`.
- **Docstrings**: a module docstring for `Lines.lean` listing its statements (the `Cut.lean`
  pattern), and one per declaration, with the pairing identity's sign as compiled (*Current state*).
- **Lint debt**: judge by `lake lint` (TACTICS-QUIRKS §55), not by the spike's warnings.
- **Pin and flip** the seven nodes, with a role-labelled map where a node carries two or three pins.
  Gates: `lake build`, `lake lint`, `blueprint/verify.sh`, `blueprint/lint.sh`,
  `notes/check-phase-note.py`.

**Then B2, the `Carrier.lean` split, B3–B4, B5, B6, B7, then the close.**

## Decisions made during this phase

- **2026-09-27 — opened design-first** from the SHORT recon (opus, read-only) and its second reading
  (a fresh opus, read-only; confirmed, with repairs). This commit re-ran both spikes at `f3c46221`
  and got the coordinator's counts. PI decision 5 added the `Carrier.lean` split before B3.
- **(MC-182) gets its own red node**, `lem:splitoff-deficiency-reuse`, not a third pin on the green
  `lem:splitoff-deficiency`. The successor is a separate Lean statement (PI decision 4(c)), and a red
  node keeps it on the dep graph's to-do list until B2.
