# Phase 40i — PENCIL-X0 / ORBIT: the open ears with one or two interior bodies at non-adjacent ends (work log)

**Status:** in progress (opened design-first 2026-09-28; B1, B2 landed 2026-09-28). STEPS' fifth
group (`notes/Phase40-design.md` §3 STEPS, the ORBIT entry). It lands the open-ear steps with one
interior body, and with two with no bound on the deficiency, both at non-adjacent ends `a ≁ b` and
under `δ₂ ≥ 2` in the merged form `deficiencyMerged₂(G[V₁]; a, b) + 2 ≤ def₂(G[V₁])`: if `X₀(G[V₁])`
attains, `X₀(G)` attains for `k = 1` when `def₃(G[V₁]) ≤ def₃(G)` ((MC-54) at `k = 1`), and for
`k = 2` when `X₀` also attains at `G` with its second interior body suppressed ((MC-176)). No new
mathematics. Eight nodes: six green after B1+B2 (`def:deficiency-merged` at the open,
`lem:splitoff-deficiency-merged`, `lem:pencil-flag-genericity` from B1, `lem:pencil-one-ear-
incidence`, `lem:pencil-one-ear-base`, `thm:pencil-x0-open-ear-one` from B2), two still red (the
`k = 2` cell); three builds, B1 and B2 done. **Next: B3, the `k = 2` cell** — see *Hand-off*.

## Current state

**Opened.** Eight nodes, with statements from the spike's exact statements (40h's
`lem:pencil-ear-data` precedent) and workbook labels from `ledger.py --brief`:
- `main-component.tex`, the new §`sec:main-component-orbit` (before `sec:main-component-statements`;
  the chapter preamble names it):
  - `lem:pencil-flag-genericity` — U2, (MC-48)(ii)'s argument, on the lifting system's kernel;
  - `lem:pencil-one-ear-incidence` — (MC-174), its family restricted to `w ∈ K z₀`;
  - `lem:pencil-one-ear-base` — (MC-176)'s Steps 1–2 and (MC-54) at `k = 1`: (MC-174) at `X₀(G′)`,
    U2, Jackson–Jordán at `G′ + ab` ((MC-172)), (MC-4)(b), (MC-175)(iii), (MC-18)(b);
  - `thm:pencil-x0-open-ear-one` — (MC-54) at `k = 1`, with (MC-169) by admissibility;
  - `lem:pencil-insertion-two` — (MC-173) in existence form: its four curves, the chart polynomial
    off route;
  - `thm:pencil-x0-open-ear-two-orbit` — (MC-176), with (MC-175)(i)(ii) as the landed
    `lem:splitoff-deficiency-reuse` and `lem:deficiency-ear`, and (MC-18)(a) through
    `lem:pencil-ear-data`;
- `molecular-induction.tex`: `lem:splitoff-deficiency-merged` — (MC-175)(iii), the `≤` half, after
  `lem:splitoff-deficiency-reuse`;
- `deficiency.tex`: **`def:deficiency-merged`, green at the open**, pinning Phase 39's landed A2
  declarations `Graph.deficiencyMerged` and `Graph.partitionDef_le_deficiencyMerged`, after
  `lem:deficiency-ear-merge`.

No Lean has landed. The seven red nodes carry no `\lean{…}` yet, 40h's open convention: each build
adds its pins with `\leanok` (*Lemma checklist*).

**The spikes** (gitignored `scratch/40i/`, local to this checkout; builder pointers, not evidence):
- `S40i.lean` (1 657 lines, 31 declarations): the whole group, sorry-free. **`lake lean`**, re-run at
  this open (`0689dfa3`): exit 0, no errors, no warnings, no `sorry`; of its 31 `#print axioms`
  lines, 28 are `[propext, Classical.choice, Quot.sound]`, `planeDiff` and `planeDiff_apply`
  `[propext, Quot.sound]`, and `Graph.splitOff_simple_of_not_adj` `[propext]`, identical to the
  coordinator's re-run.
- `S40iInst.lean`: the two instances' structural hypotheses. **`lake lean`**: exit 0, no output.
- **Satisfiability** (not landed). `k = 1` at `x8_60101824`, the 8-cycle `4 0 5 2 7 3 6 1` with the
  chords `4–7`, `5–6`, ear `4 − 0 − 5`: the eight structural hypotheses kernel-checked;
  `def₂(G[V₁]) = 2` with merged value `0`, so `hδ₂` holds, and `def₃(G[V₁]) = def₃(G) = 0`, so `hdef`
  holds (measured, script not retained); `h₁` by hand (`G[V₁]` is θ(1,2,2), covered by THETA's
  assembly). `k = 2` at `K₄` with every edge subdivided twice, ear `0 − 4 − 5 − 1`: the structural
  hypotheses kernel-checked; (S) holds and `δ₂ = 3` (measured, script not retained); `h₁`, `h₂` from
  the workbook's certificates. At `K_{2,3}` (`δ₂ = 1`) `hδ₂` fails, and FLAT covers it.
- **Faithfulness** (against (MC-54), (MC-176)): `of_openEar_one` is (MC-54) at `k = 1`, with `hdef`
  for `δ = 0` (PI decision 4(a)) and `hδ₂` for `dim U ≥ 2`, sufficient by U2; `hnadj` holds in 𝒮 by
  (MC-79)(ii). `of_openEar_two_of_splitOff` is (MC-176): attainment at `G[V₁]` and at
  `G.splitOff (x 1) (x 0) b (e 1)` (the workbook's `G₁`, its `x₂` suppressed), `a ≁ b`, `δ₂ ≥ 2`.
  Both ask (H) at `G` only, as 40g's and 40h's do.

## Architectural choices made up front

- **The route** (the recon's verdict; the design doc's §3 STEPS, ORBIT entry). U2 and (MC-174) run
  on the lifting system's kernel. One base lemma (`Graph.exists_oneEar_base`) serves both cells.
  `k = 1` is one picture and the ear rank law. `k = 2` counts against `G₁`, with (MC-173) as the
  polynomial-free insertion `exists_insertion_two` and EARGEN's landed span transfer for the open
  condition. The ear law is applied at `(ofNormals …).toBodyHinge`, as CHAIN and SHORT do.
- **The coordinator's calls** (2026-09-28). The PI's session-start configuration was **"follow
  precedent"**: where a 40e–40h precedent answers a recon question, the coordinator applies it and
  records it as its call, citing the precedent; only a genuinely new question goes to the PI. These
  are the coordinator's calls, not PI decisions, so they are not in `notes/pencil/adjudications.md`.
  1. **No new mathematics: 40i opens directly**, with no workbook commit and no second reading.
     (MC-173)'s second-read proof already spans `Λ²K⁴ / Λ₁(y)` by four curve limit directions and
     picks one outside `W`; the spike's `y∧u₀`, `u₀∧p_b`, `p_a∧u₀`, `p_a∧p_b` are that basis modulo
     `Λ₁(y)` in the frame `p_a, y, u₀, p_b`. Its polynomial conclusion is replaced by EARGEN's span
     transfer, as 40h did at `k = 4`; (MC-174)'s restricted family and U2 on the kernel are
     formalization-level. Precedent: 40f and 40g (40h's workbook-first path fired only because its
     claims were new). No workbook statement changes; the proof-map row records (MC-173)'s form.
  2. **`hδ₂`, in both cells, is the `deficiencyMerged` form**, (MC-176)'s and (MC-175)(iii)'s
     `δ₂ ≥ 2` over Layer A's carrier, which COVERAGE supplies from (S) ((MC-79)(ii) at `k = 1`;
     (iii) with (vi) at `k = 2`). The compiled split-off form would be a double split-off at `k = 2`,
     and PI decision 4(a) does not answer this directly (no δ machinery is added). Reversible in
     about three lines per call site. `dim U ≥ 2` in Lean form is rejected (COVERAGE would re-run
     U2). The tracked trace is settled (the ORBIT entry); COVERAGE's supplier is tracked in its
     section of the design doc.
  3. **Placement: PI decision 5's convention.** A new `MainComponent/Orbit.lean` holds the steps and
     their ORBIT-specific pieces; the general pieces go beside their definitions. `Operations.lean`
     (3 334 lines) gains about 20, by 40h's `Pinning.lean` precedent; no split fires.
  4. **Pins: PI decision 4(b)'s first-consumer rule.** ORBIT pins only `deficiencyMerged` and
     `partitionDef_le_deficiencyMerged`, on a definition node (40g's `def:relative-screws`
     precedent); the rest of A2/A3, `jointMotions` and `weldedRank` wait for COVERAGE or SPLITOFF.
  5. **The nodes follow the spike's statements** (40h's `lem:pencil-ear-data` precedent), as the
     recon's node list. The open kept its labels and grouping: no node has four or more planned
     pins (`blueprint/AUTHORING.md` D).
  6. **The builds: B1 the general pieces, B2 the `k = 1` cell, B3 the `k = 2` cell.** B1 and B2 may
     land as one commit (40h's B3–B4 precedent); the coordinator decides at dispatch. Estimate: open,
     2–3 builds, close.
- **Blueprint placement.** In the new subsection, the general lemmas before the steps and `k = 1`
  before `k = 2`; the split-off bound after its label-reusing sibling; the definition after
  `lem:deficiency-ear-merge`, the lemma about partitions with the ends in one part.

## Lemma checklist

Planned names from the spike; pins in **bold**, the other names helpers, unpinned. The spike's
section headers P1–P10 are the recon's pieces.

- [x] **B1, the general pieces** (P1, P2, P4, P5 but `splitOff_oneEar`, P9's `pointJoin` lemmas) —
  landed 2026-09-28:
  - `Induction/SplitOffDeficiency.lean`: **`Graph.splitOff_deficiency_add_le_of_deficiencyMerged`**
    → `lem:splitoff-deficiency-merged`;
  - `Carrier.lean`, beside `liftingMatrix`: **`Graph.two_le_finrank_map_planeDiff`**,
    **`planeDiff`** → `lem:pencil-flag-genericity` (`planeDiff_apply`,
    `Graph.injective_liftingMatrix_ker_proj`); also `Graph.IsAdmissiblePicture.three_le_ncard_closedNbhd`
    and `Graph.IsAdmissiblePicture.linearIndependent_of_closedNbhd_subset` (placed beside
    `isAdmissiblePicture_congr`, both unpinned helpers);
  - `Lines.lean`: `linearIndependent_pointJoin_pair`; `Flat.lean`, beside `pointJoin`:
    `linearIndependent_pencilConfigPoint_triple` and the seven `pointJoin_{zero,add,smul,sub}_left`,
    `pointJoin_{add,smul,sub}_right`; `Induction/Operations.lean`, beside `splitOff_simple`:
    `Graph.splitOff_simple_of_not_adj`.
- [x] **B2, the `k = 1` cell**, new `MainComponent/Orbit.lean` (P3, `Graph.splitOff_oneEar`, P6, P7)
  — landed 2026-09-28: **`exists_incidence`** → `lem:pencil-one-ear-incidence`
  (`exists_dotProduct_eq_zero_ne_zero`; `finrank_span_singleton_le_one'` inlined as a local `have`,
  per the recon's note); **`Graph.exists_oneEar_base`** → `lem:pencil-one-ear-base`
  (`incidencePoly`, `eval_incidencePoly`); **`Graph.X0Attains.of_openEar_one`** →
  `thm:pencil-x0-open-ear-one`. `Orbit.lean` imports `MainComponent/EarGen.lean` (confirmed minimal
  by a `lake lean` probe against every identifier the four pieces use: `Ear.lean` alone is missing
  `linearIndependent_pointJoin_pair`, `EarGen.lean` = `Ear` + `Lines` supplies everything).
- [ ] **B3, the `k = 2` cell** (P8, the rest of P9, P10): `Lines.lean`: **`exists_insertion_two`** →
  `lem:pencil-insertion-two` (`exists_insertion_two_aux`); `Orbit.lean`:
  **`Graph.X0Attains.of_openEar_two_of_splitOff`** → `thm:pencil-x0-open-ear-two-orbit`
  (`splitOff_ear_two`, `splitOff_ear_two_simple`).
- [ ] **The close** (docs and blueprint only): the end-to-end re-read of the new subsection; the
  exposition ledger (candidates: the one-ear base, where the ear body's picture is chosen with the
  heights, and the insertion that replaces the orbit table); the headline axioms; the design doc's
  §3 STEPS, ROADMAP and `MolecularConjecture.md`; the public surfaces unchanged (the PI's standing
  call, recorded at 40f's close).

## Blockers / open questions

- None blocking B1.
- **Builder notes** (the recon's): inline `mem_of_add_smul_mem`; `finrank_span_singleton_le_one'` is
  a one-liner through mathlib's `finrank_span_le_card` (inline it, or name it without the prime);
  TACTICS-QUIRKS §48 (`a - b - c` and `linear_combination h0 - h1` misparse under
  `open scoped Graph`), met twice in the spike. Every new top-level name greps to no prior definition
  (the recon's check, TACTICS-QUIRKS §65).
- **A stale Lean docstring, not a gate.** `Deficiency.lean`'s section docstring for the merged and
  separated deficiencies cites a label `def:pencil-deficiency-pair` that does not exist, and says none
  of its declarations has a node; since this open `def:deficiency-merged` pins two of them. Repoint it
  the next time `Deficiency.lean` is edited (a docstring edit there rebuilds everything downstream, so
  not on its own), or at the close.

## Hand-off / next phase

**B1 and B2 landed 2026-09-28.** Six of eight nodes are green (see *Status*). Gates green each
build: `lake build` (whole tree, no warnings), `lake lint`, `blueprint/verify.sh`,
`blueprint/lint.sh`.

**Next: B3, the `k = 2` cell (fresh builder).** Source: `scratch/40i/S40i.lean` (gitignored, local
to this checkout; a builder pointer, not evidence), P8 (the antecedent of the two-body ear is a
one-body ear, and simple with non-adjacent ends), the rest of P9 (`exists_insertion_two`'s curve
family, `exists_insertion_two` itself — the `pointJoin` linearity lemmas already landed in B1), and
P10 (`Graph.X0Attains.of_openEar_two_of_splitOff`). Targets: `Lines.lean`:
**`exists_insertion_two`** → `lem:pencil-insertion-two` (`exists_insertion_two_aux`); `Orbit.lean`:
**`Graph.X0Attains.of_openEar_two_of_splitOff`** → `thm:pencil-x0-open-ear-two-orbit`
(`splitOff_ear_two`, `splitOff_ear_two_simple`). Chores:
- **`lake lean` the spike first**, never `lake env lean` (`CombinatorialRigidity/CLAUDE.md` *Lean LSP
  MCP*); it is clean at this open, so judge lint by `lake lint`.
- **Pin and flip** each node with the checklist's bold names. Gates: `lake build`, `lake lint`,
  `blueprint/verify.sh`, `blueprint/lint.sh`, `notes/check-phase-note.py`.

**Then the close** (see the checklist's last item: end-to-end re-read, exposition ledger, headline
axioms, design-doc/ROADMAP/`MolecularConjecture.md` sync).

## Decisions made during this phase

- **2026-09-28 — opened design-first** from ORBIT's design recon (opus, read-only, compiler-checked).
  This commit re-ran both spikes at `0689dfa3` and got the coordinator's counts. The coordinator's
  calls are under *Architectural choices*.
- **`def:deficiency-merged` is green at the open**: both pins landed in Phase 39 (A2), and
  `checkdecls` resolves them. Definition faithfulness: the Lean restricts the labeling supremum to
  `f u = f v`, which at bodies `u, v` of `G` is the maximum over the partitions with `u`, `v` in one
  part, as the node states; the cheapest witness is the one-part partition, of value `0`.
- **2026-09-28 B1 — one import-order deviation from the spike.** `Graph.two_le_finrank_map_planeDiff`
  (in `Carrier.lean`) used `Graph.closedNbhd_subset_vertexSet` verbatim from the spike, but that
  lemma lives downstream in `MainComponent/Bridge.lean` (which imports `Carrier.lean`, not the
  reverse); its three-line proof (`rcases hw with rfl | ⟨e, he⟩; exacts [hv, he.right_mem]`) is
  inlined at the one call site rather than moved or duplicated as a named declaration. No other
  placement changed from the checklist.
- **2026-09-28 B2 — `Orbit.lean`'s import, confirmed by probe.** `EarGen.lean` (= `Ear.lean` +
  `Lines.lean`) is the least existing module supplying every identifier the four transcribed pieces
  use; a `lake lean` probe file (`#check` on all of them against `import … .Ear` alone) showed only
  `linearIndependent_pointJoin_pair` missing, which `Lines.lean` supplies. No other import needed
  (in particular `Graph.splitOff_deficiency_add_le_of_deficiencyMerged`, from a different directory
  tree, `Induction/SplitOffDeficiency.lean`, already resolves transitively).
