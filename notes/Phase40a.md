# Phase 40a — PENCIL-X0 / SPINE2: the Katoh–Tanigawa spine at `n = 2` (work log)

**Status:** in progress (opened 2026-09-25). A **structural edit**: the landed Theorem 5.5/5.6
chain and the molecular conjecture weaken their dimension floor in place, from
`6 ≤ Graph.bodyBarDim n` to `3 ≤ Graph.bodyBarDim n` and from `hd : 3 ≤ n` to `2 ≤ n`. One
triangle case is repaired. That makes them hold at `n = 2`, the planar case, over every infinite
field. It is the `X₀` route's replacement for Jackson–Jordán (`notes/Phase40-design.md` §3,
SPINE2). **Slice 1 (the leaf layer) LANDS.** **Next: Slice 2**
(`AlgebraicInduction/Theorem55.lean`). The program plan is `notes/Phase40-design.md`.

## Current state

**Slice 1 landed** (`three_le_bodyBarDim_of_two_le`, `chainData_extract`, `cycle_realization`,
`case_III_hsplit_producer_all_k` incl. the triangle repair, `case_III_realization{,_all_k}`, the
one `Theorem55.lean` caller repaired with `(by omega)`, and the three chapters' blueprint
restatements — `molecular-induction.tex`, `algebraic-induction/case-iii.tex`; `case-i.tex`'s
`cycle_realization` node needed no edit, its statement is already phrased generically as
`3 ≤ m ≤ D`). **Next: Slice 2**, `AlgebraicInduction/Theorem55.lean` (*Layer plan*). The plan was
compiler-checked by the 2026-09-25 sizing recon: the landed proofs were copied, the floor
weakened, and the copies elaborated against the built tree. Its diffs are verbatim in
`notes/Phase39-design.md` § *`n = 2` sizing recon (2026-09-25)*, with hunks keyed to line numbers
at `c05f7df7`. **Lean has changed since** — Phase 39 L0a/L0b landed `Pencil/{Arms,Statement,X0}.lean`
(disjoint from every Slice 1–4 target) and this commit landed Slice 1 itself — but no Slice 2–4
target file has changed, so those hunks still apply as written. One correction to the recon's
verbatim hunk: its `push_neg at hcon` is `push Not at hcon` in the built tree (mathlib deprecated
`push_neg`, `notes/FRICTION.md` — not a markdown-rendering artifact, confirmed by elaborating both
against the tree). The site list below was recomputed on 2026-09-25 by grepping every
`6 ≤ Graph.bodyBarDim` / `6 ≤ bodyBarDim` / `six_le_bodyBarDim` site, which completes the recon's
list (its closure report stopped at ten declarations).

## Architectural choices made up front

- **Weaken in place; no `n = 2` siblings** (PI, 2026-09-25). A weaker hypothesis is a stronger
  theorem, and every existing use is an instance.
- **What keeps `6 ≤ D`.** These stay as they are:
  - `Graph.exists_adjacent_degree_two_pair` and its four `ReducibleVertex.lean` siblings
    (`_of_edgeBound`, `_of_noRigid_of_deficiency_pos`, `edgeBound_of_noRigid_of_degree_two`,
    `_of_noRigid_of_degree_two`). The adjacent-pair lemma is false at `D = 3`: `K_{2,3}`
    (Prospect G2).
  - `Graph.pencil_reduction` and `exists_chain_data_of_noRigid` (`ForestSurgery/Reduction.lean`).
    They are off the `n = 2` closure.
  - The `hD6 := six_le_bodyBarDim …` lines at `n = 3` in `Molecule/` (Pencil `Arms`, `Escape`,
    `Pair2`; `Theorem56`). These stay valid.
- **The `d = 3`-only wrappers weaken too.** These are the declarations with
  `hn : bodyBarDim n = screwDim 2`: `case_I_realization_h65`, `theorem_55_minimalKDof_k`,
  `case_III_realization`. The hypothesis is redundant there, but uniformity keeps the docstrings
  honest (the recon did the same).
- **New lemma** `Graph.three_le_bodyBarDim_of_two_le` in `BodyBar/Framework.lean`, beside
  `six_le_bodyBarDim`. The recon's proof:
  ```lean
  theorem three_le_bodyBarDim_of_two_le {n : ℕ} (hn : 2 ≤ n) : 3 ≤ bodyBarDim n := by
    have hbb : 2 * bodyBarDim n = n * (n + 1) := by
      rw [bodyBarDim, Nat.mul_div_cancel' (Nat.even_mul_succ_self n).two_dvd]
    nlinarith
  ```
- **Caller repair.** A caller holding `hD : 6 ≤ D` now passes `(by omega)` where a `3 ≤ D` is
  wanted.
- **The statement-change gate binds every slice** (`CombinatorialRigidity/CLAUDE.md`
  *Forward-mode slices*). In the same commit, restate every blueprint node and every docstring
  that states the old floor (`n ≥ 3`, `D ≥ 6`, "d = 3 (D ≥ 6)", `3 ≤ n`). `checkdecls` cannot
  see a stale statement.
- **Rung.** The files are in the fragility zone (`AlgebraicInduction/`), but the work is a
  mechanical refactor with one compiler-checked, pasted proof edit, which the playbook keeps at
  the mapped rung. If a build wall appears, escalate to opus.

## Layer plan (the to-do list)

- [x] **Slice 1 — the leaves.** LANDED. `BodyBar/Framework.lean` (`three_le_bodyBarDim_of_two_le`),
  `ChainExtraction.lean` (`chainData_extract`'s floor only — its proof already derived `hD3`/`hD2`
  by `omega`, so the body needed no other change), `CaseIII/Arms.lean` (`cycle_realization`'s
  `hm : cy.m ≤ n + 1`; `case_III_hsplit_producer_all_k`'s floor + the triangle repair via
  `Graph.exists_degree_eq_two_of_noRigid` + any companion vertex), `CaseIII/Realization.lean`
  (`case_III_realization_all_k` and `case_III_realization`, the latter per the phase's "`d = 3`-only
  wrappers weaken too" call). One caller repair: `Theorem55.lean`'s `hsplitZero` branch now passes
  `(by omega)` in place of `hD` to `case_III_realization_all_k` (Slice 2 still holds `hD : 6 ≤ D`
  there). Blueprint: `molecular-induction.tex`'s `lem:chain-data-extract` floor, and
  `algebraic-induction/case-iii.tex`'s `lem:case-III` floor + its triangle-base proof prose (which
  named `lem:adjacent-degree-two-pair`, no longer invoked there); `case-i.tex`'s `cycle_realization`
  node needed no edit (already phrased as `3 ≤ m ≤ D`, not tied to the Lean binder's exact value).
- [ ] **Slice 2 — `AlgebraicInduction/Theorem55.lean`.** Rated S1/P1/B2.
  - The `hD` floor in: `case_I_realization_h65_gen`, `case_I_realization_h65`,
    `case_I_dispatch_gen`, `case_I_hcontract_gen`, `theorem_55_minimalKDof_k_all_k`,
    `theorem_55_minimalKDof_gen`, `theorem_55_minimalKDof_k`,
    `rankHypothesis_genuine_of_theorem_55_gen`,
    `rankHypothesis_genuine_recordsLinks_of_theorem_55_gen`, `theorem_55_6_multigraph_of_two_le`,
    `theorem_55_6_multigraph`.
  - `hd : 3 ≤ n` becomes `2 ≤ n`, with `have hD := three_le_bodyBarDim_of_two_le hd`, in:
    `rankHypothesis_of_theorem_55_gen`, `molecular_conjecture`, `theorem_55_6_multigraph_gen`, and
    the `hd` declaration near the file's end (the recon's hunk `@@ -3379`).
  - The recon's Theorem55 hunks list every line.
  - **Callers** outside the file: `Molecule/Theorem56.lean`, `AlgebraicInduction/Nonvacuity.lean`
    (`molecular_conjecture_witness`), `GenericityDevice.lean`, `Coupling.lean`, `PanelHinge.lean`,
    `CaseI.lean`, `CaseII.lean`, `Deficiency.lean`. Many of these are docstring mentions, so read
    each hit.
  - **Blueprint.** Restate:
    - `algebraic-induction/panel-layer.tex`: seven `n \ge 3` / `6 \le D` lines, among them the
      nodes `thm:theorem-55-6`, `thm:molecular-conjecture` and
      `thm:theorem-55-6-multigraph`;
    - `algebraic-induction.tex`: line 12, the chapter preamble, `n \ge 3, i.e. D \ge 6`;
    - `case-i.tex`: `case_I_realization_h65_gen`, `case_I_dispatch_gen`.
  - **The docstrings** of `rankHypothesis_of_theorem_55_d3` and `theorem_55_6_multigraph{,_d3}`
    say "equivalently `6 ≤ bodyBarDim n`"; restate them.
- [ ] **Slice 3 — `GenericLift/`.** Rated S1/P1/B1.
  - `PanelGeneric.lean`: `finrank_span_rigidityRows_ofNormals_of_isGenericNormals`,
    `isInfinitesimallyRigidOn_ofNormals_isGenericNormals_iff`.
  - `HingeGeneric.lean`: `exists_hingePoints_independent_hingePointRow`,
    `finrank_span_rigidityRows_ofHinge_of_isGenericHingePoints`,
    `isInfinitesimallyRigidOn_ofHinge_isGenericHingePoints_iff{,_spanningTrees}`.
  - **Callers:** `Molecule/Pencil/Steer.lean` uses the first.
  - **Blueprint:** `generic-lift.tex`, three lines (`n \ge 3 (equivalently D \ge 6)`).
- [ ] **Slice 4 — the non-spanning row-rank form** (the core BRIDGE consumes). Rated S2/P2/B1.
  - Land the recon's `spike_nonspanning_rows_n2` (about 40 lines, via
    `exists_isMinimalKDof_spanning_subgraph`; first try in the recon) in `Theorem55.lean`, beside
    the private `reaimSubLink` helpers it needs. Give it a real name, e.g.
    `PanelHingeFramework.exists_rankHypothesis_rows_of_simple`.
  - **State it at general `(n, k)`** (`3 ≤ bodyBarDim n`, `bodyBarDim n = screwDim k`) if the
    proof is uniform; otherwise at `n = 2`. The statement as recon-pinned at `n = 2`:
    ```lean
    theorem spike_nonspanning_rows_n2 [Infinite K] [Finite α] [Finite β] [DecidableEq β]
        (hfresh : ∀ (c : ℤ) (G' : Graph α β), G'.IsMinimalKDof 2 c → ∃ e₀ : β, e₀ ∉ E(G'))
        (G : Graph α β) (hV : 2 ≤ V(G).ncard) (hSimple : G.Simple) :
        ∃ Q : PanelHingeFramework K 1 α β, Q.graph = G ∧ Q.IsGeneralPosition ∧
          (∀ e u v, G.IsLink e u v → G.IsLink e (Q.ends e).1 (Q.ends e).2) ∧
          (Module.finrank K (Submodule.span K Q.toBodyHinge.rigidityRows) : ℤ)
            = screwDim 1 * ((V(G).ncard : ℤ) - 1) - G.deficiency 2
    ```
  - **Blueprint:** a new node in `panel-layer.tex` beside `thm:theorem-55-6`, green on landing.
- [ ] **Slice 5 — close 40a** (a docs commit):
  - **Public surfaces.** README and `home_page/index.md` say "every dimension `d ≥ 3`", and so do
    `intro.tex` (Organization and *Reading this blueprint*) and `formalization.yaml`'s
    `main_results`. Each becomes `d ≥ 2`, and each names the planar case, the pin-collinear
    theorem of Jackson–Jordán (DCG 40, 2008), now proved over every infinite field. Re-verify
    `#print axioms` for the restated headline declarations.
  - **The PI's call on PIN** (ROADMAP *Queued*): its target, the 2-d molecular conjecture, is
    delivered here by Katoh–Tanigawa's route at `d = 2` rather than Jackson–Jordán's.
  - Then the next layer's sub-phase opens: CARRIER, from `notes/Phase40-design.md` §3,
    design-first at the top rung.

## Blockers / open questions

- None. The one PI call, PIN's disposition, is due at Slice 5.

## Hand-off / next phase

**Next concrete commit: Slice 2** (*Layer plan*), `AlgebraicInduction/Theorem55.lean`. Apply the
recon's Theorem55 hunks (all `6 ≤ Graph.bodyBarDim n` → `3 ≤`, and `hd : 3 ≤ n` → `2 ≤ n` with
`have hD := three_le_bodyBarDim_of_two_le hd`, per the *Layer plan*'s declaration list), repair the
callers outside the file (`Molecule/Theorem56.lean`, `AlgebraicInduction/Nonvacuity.lean`,
`GenericityDevice.lean`, `Coupling.lean`, `PanelHinge.lean`, `CaseI.lean`, `CaseII.lean`,
`Deficiency.lean` — read each hit, many are docstring mentions only), and restate
`panel-layer.tex` / `algebraic-induction.tex` / `case-i.tex` per the *Layer plan*. Run it with
`/coordinate-phase 40a`.

## Decisions made during this phase

- **2026-09-25 — opened** (PI: SPINE2 is the first sub-phase of Phase 40; weaken in place).
  Verbatim `notes/pencil/adjudications.md`.
- **2026-09-25 — Slice 1 lands.** The recon's hunks applied verbatim except one tactic-name fix
  (`push_neg` → `push Not`, mathlib deprecation, already an idiom in `notes/FRICTION.md`) and the
  case-iii.tex triangle-base proof prose, which needed rewording (not just the floor numeral)
  since the proof no longer invokes `lem:adjacent-degree-two-pair`. Gates: `lake build` (full
  tree, 2968 jobs, zero warnings), `lake lint`, `blueprint/lint.sh`, `blueprint/verify.sh`
  (`checkdecls` clean) — all green.
