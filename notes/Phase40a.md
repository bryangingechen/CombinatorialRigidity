# Phase 40a — PENCIL-X0 / SPINE2: the Katoh–Tanigawa spine at `n = 2` (work log)

**Status:** in progress (opened 2026-09-25). A **structural edit**: the landed Theorem 5.5/5.6
chain and the molecular conjecture weaken their dimension floor in place, from
`6 ≤ Graph.bodyBarDim n` to `3 ≤ Graph.bodyBarDim n` and from `hd : 3 ≤ n` to `2 ≤ n`. One
triangle case is repaired. That makes them hold at `n = 2`, the planar case, over every infinite
field. It is the `X₀` route's replacement for Jackson–Jordán (`notes/Phase40-design.md` §3,
SPINE2). **Slices 1–3 LAND** (Slice 2's own build forced Slice 3's `GenericLift/` floor weakening
into the same commit — see *Decisions made*). **Next: Slice 4** (the non-spanning row-rank form).
The program plan is `notes/Phase40-design.md`.

## Current state

**Slices 1–3 landed** (`three_le_bodyBarDim_of_two_le`, `chainData_extract`, `cycle_realization`,
`case_III_hsplit_producer_all_k` incl. the triangle repair, `case_III_realization{,_all_k}`, the
full `Theorem55.lean` `hD`/`hd` floor per the *Layer plan*'s declaration list, its eight named
callers, `GenericLift/{PanelGeneric,HingeGeneric}.lean`'s six declarations, and every named
blueprint restatement across `molecular-induction.tex`, `algebraic-induction.tex`,
`algebraic-induction/{case-i,case-iii}.tex`, `panel-layer.tex`, `generic-lift.tex`). **Next: Slice
4**, the non-spanning row-rank form (*Layer plan*). The plan was
compiler-checked by the 2026-09-25 sizing recon: the landed proofs were copied, the floor
weakened, and the copies elaborated against the built tree. Its diffs are verbatim in
`notes/Phase39-design.md` § *`n = 2` sizing recon (2026-09-25)*, with hunks keyed to line numbers
at `c05f7df7`; Lean had changed since only outside the Slice 1–4 targets, so those hunks applied as
written. The site list was recomputed on 2026-09-25 by grepping every
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
- [x] **Slice 2 — `AlgebraicInduction/Theorem55.lean`.** LANDED. The `hD` floor weakened in the
  eleven named declarations and the four `hd : 3 ≤ n` → `2 ≤ n` declarations (each with
  `have hD := three_le_bodyBarDim_of_two_le hd`, except the file-end `molecular_conjecture_multigraph`,
  which threads `hd` straight through). One caller repair reverted: `theorem_55_minimalKDof_k_all_k`'s
  `hsplitZero` branch passes plain `hD` again (its own `hD` is now `3 ≤ D`, matching
  `case_III_realization_all_k`). **Caller repair:** `Molecule/Theorem56.lean`'s
  `exists_rankHypothesis_isGeneralPosition4_of_two_le` had a literal
  `hD : (6 : ℕ) ≤ Graph.bodyBarDim 3 := Graph.six_le_bodyBarDim …` feeding the weakened
  `rankHypothesis_genuine_recordsLinks_of_theorem_55_gen` directly — repointed to
  `three_le_bodyBarDim_of_two_le`. The other seven named callers (`Nonvacuity.lean`,
  `GenericityDevice.lean`, `Coupling.lean`, `PanelHinge.lean`, `CaseI.lean`, `CaseII.lean`,
  `Deficiency.lean`) were docstring-only mentions or independent local floors (the Pencil `hD6`
  sites feed `_of_edgeBound`/`pencil_reduction`, off the `n = 2` closure per *Architectural choices*)
  — no repair needed. **Blueprint:** `panel-layer.tex` (all seven sites), `algebraic-induction.tex`
  line 12; `case-i.tex`'s two named nodes carried no numeral (no edit needed).
- [x] **Slice 3 — `GenericLift/`.** LANDED, merged into the Slice-2 commit: `PanelGeneric.lean`'s two
  decls and `HingeGeneric.lean`'s four call the Slice-2-weakened Theorem55 producer
  (`rankHypothesis_genuine_recordsLinks_of_theorem_55_gen`) with their own `hD` verbatim, so the
  build fails at Slice 2 alone until these six floors weaken too — not optional scope creep, a
  forced dependency the recon's own hunk list already carried (its diff blob includes
  `PanelGeneric.lean`/`HingeGeneric.lean` hunks alongside Theorem55's). `Molecule/Pencil/Steer.lean`'s
  mention is docstring-only. Blueprint: `generic-lift.tex`'s three sites.
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

**Next concrete commit: Slice 4** (*Layer plan*), the non-spanning row-rank form. Land the recon's
`spike_nonspanning_rows_n2` (about 40 lines, via `exists_isMinimalKDof_spanning_subgraph`) in
`Theorem55.lean` under a real name (e.g. `PanelHingeFramework.exists_rankHypothesis_rows_of_simple`),
state it at general `(n, k)` if the proof is uniform (otherwise at `n = 2`), and add its
`panel-layer.tex` node beside `thm:theorem-55-6`. Run it with `/coordinate-phase 40a`.

## Decisions made during this phase

- **2026-09-25 — opened** (PI: SPINE2 is the first sub-phase of Phase 40; weaken in place).
  Verbatim `notes/pencil/adjudications.md`.
- **2026-09-25 — Slice 1 lands.** The recon's hunks applied verbatim except the case-iii.tex
  triangle-base proof prose, which needed rewording (not just the floor numeral) since the proof
  no longer invokes `lem:adjacent-degree-two-pair`. Gates: `lake build` (full tree, 2968 jobs, zero
  warnings), `lake lint`, `blueprint/lint.sh`, `blueprint/verify.sh` (`checkdecls` clean) — all
  green.
- **2026-09-25 — Slices 2–3 land as one commit.** Slice 3 was pulled in: Slice 2 alone breaks the
  build, since `GenericLift/{PanelGeneric,HingeGeneric}.lean` call the weakened Theorem55 producer
  with their own still-`6`-pinned `hD` (a genuine dependency, already in the recon's hunk blob, not
  scope creep). Repairs beyond the recon's hunks: `Molecule/Theorem56.lean`'s literal
  `Graph.six_le_bodyBarDim` repointed to `three_le_bodyBarDim_of_two_le`; one docstring rewrap for
  `longLine`; `case-i.tex`'s `lem:cycle-realization` bound restated `m ≤ k+2`; `case-iii.tex`'s
  `lem:case-III` proof gained `lem:low-degree-vertex` in `\uses` (pins
  `Graph.exists_degree_eq_two_of_noRigid`'s `exists_degree_le_two` root). Gates all green.
