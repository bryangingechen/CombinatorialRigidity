# Phase 40a — PENCIL-X0 / SPINE2: the Katoh–Tanigawa spine at `n = 2` (work log)

**Status:** ✓ complete (opened and closed 2026-09-25). A **structural edit**: the landed Theorem
5.5/5.6 chain, the generic-lift rank theorems and the molecular conjecture (simple and multigraph)
weakened their dimension floor in place, from `6 ≤ Graph.bodyBarDim n` to `3 ≤ Graph.bodyBarDim n`
and from `hd : 3 ≤ n` to `2 ≤ n`; one triangle case was repaired; and the non-spanning row-rank
form of Theorem 5.6 landed. They hold at `n = 2`, the planar case (Jackson–Jordán's pin-collinear
theorem), over every infinite field. **Next: CARRIER**, Phase 40's next layer
(`notes/Phase40-design.md` §3), **not yet opened** — see *Hand-off*.

## Current state

**Closed.** Slices 1–5 landed. Phase 40 continues with **CARRIER** (*Hand-off*); nothing of it is
started. The two Slice-4 follow-ups were routed at the close to the layers that land them
(`notes/Phase40-design.md` §3 FLAT and BRIDGE). Headline axioms were re-verified at the close on
25 declarations: the seventeen `formalization.yaml` main results, the conditional
`pencil_conjecture_of_X0`, `theorem_55_6_multigraph`, `rigidityMatrix_prop11`, the three other
restated generic-lift rank theorems and the two Slice-4 declarations. Each is exactly
`[propext, Classical.choice, Quot.sound]` (*measured, script not retained*: one `#print axioms`
line per declaration under `import CombinatorialRigidity`, run with `lake env lean` on the built
tree).

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
  - The `hD6 := six_le_bodyBarDim …` lines at `n = 3` in `Molecule/Pencil/` (`Arms`, `Escape`,
    `Pair2`, and `X0`'s two `six_le_bodyBarDim` uses). These stay valid. (`Molecule/Theorem56.lean`'s
    `hD` line did *not* stay: Slice 2 repointed it to `three_le_bodyBarDim_of_two_le`, since its
    callee now wants `3 ≤ D`.)
- **The `d = 3`-only wrappers weaken too.** These are the declarations with
  `hn : bodyBarDim n = screwDim 2`: `case_I_realization_h65`, `theorem_55_minimalKDof_k`,
  `case_III_realization`. The hypothesis is redundant there, but uniformity keeps the docstrings
  honest (the recon did the same).
- **New lemma** `Graph.three_le_bodyBarDim_of_two_le` in `BodyBar/Framework.lean`, beside
  `six_le_bodyBarDim` (the recon's two-line `nlinarith` proof, landed as written).
- **Caller repair.** A caller holding `hD : 6 ≤ D` passes `(by omega)` where a `3 ≤ D` is wanted.
- **The statement-change gate bound every slice** (`CombinatorialRigidity/CLAUDE.md`
  *Forward-mode slices*): every blueprint node and docstring stating the old floor was restated in
  the same commit.

## Layer plan (the to-do list)

- [x] **Slice 1 — the leaves.** LANDED (`three_le_bodyBarDim_of_two_le`, `chainData_extract`,
  `cycle_realization`, `case_III_hsplit_producer_all_k` incl. triangle repair,
  `case_III_realization{,_all_k}`). Detail: *Decisions made*.
- [x] **Slice 2 — `AlgebraicInduction/Theorem55.lean`.** LANDED (the full `hD`/`hd` floor weakening,
  eight named callers repaired). Detail: *Decisions made*.
- [x] **Slice 3 — `GenericLift/`.** LANDED, merged into the Slice-2 commit (six declarations forced
  by the same dependency). Detail: *Decisions made*.
- [x] **Slice 4 — the non-spanning row-rank form** (the core BRIDGE consumes). LANDED:
  `PanelHingeFramework.finrank_span_rigidityRows_genuine_recordsLinks_of_theorem_55_gen` (the
  five-conjunct form, no `[Nonempty α]`/`hspan`) and its corollary
  `hasGenericFullRankRealization_of_theorem_55_gen`, in `Theorem55.lean`. Blueprint node
  `thm:theorem-55-6-rows`. Detail: *Decisions made*.
- [x] **Slice 5 — close 40a** (a docs commit). LANDED:
  - **Public surfaces.** README and `home_page/index.md` say "every dimension `d ≥ 3`", and so do
    `intro.tex` (Organization and *Reading this blueprint*) and `formalization.yaml`'s
    `main_results`. Each becomes `d ≥ 2`, and each names the planar case, the pin-collinear
    theorem of Jackson–Jordán (DCG 40, 2008), now proved over every infinite field. Re-verify
    `#print axioms` for the restated headline declarations. — *Delivered* (all four surfaces;
    axioms: *Current state*).
  - **The PI's call on PIN** (ROADMAP *Queued*): its target, the 2-d molecular conjecture, is
    delivered here by Katoh–Tanigawa's route at `d = 2` rather than Jackson–Jordán's. —
    *Delivered*: re-scoped (*Decisions made*).
  - Then the next layer's sub-phase opens: CARRIER, from `notes/Phase40-design.md` §3,
    design-first at the top rung. — **Not delivered by this commit, by scope**: the closing
    dispatch was barred from opening it. Re-flagged as the next task in *Hand-off*.

## Blockers / open questions

- None. The one PI call, PIN's disposition, was made at the close (*Decisions made*).

## Hand-off / next phase

**40a is closed. Phase 40 continues with CARRIER** (`notes/Phase40-design.md` §3), the next layer,
**not yet opened**. Its first commit is a **design-first, compiler-checked top-rung recon**. That
recon settles CARRIER's new mirror definitions: the picture, admissibility, the lifting space, and
"attains at the generic point". It also decides the β-headroom question (design doc §4). The
commit that opens CARRIER mints its letter and its work log. Two follow-ups from Slice 4 ride with
the layers that consume them (routed into design doc §3):
- **FLAT**: pin `BodyHingeFramework.finrank_span_rigidityRows_add_deficiency_le`, and repoint the
  stand-in `\uses{lem:trivial-motions-rank-bound}` of `thm:theorem-55-6-rows`;
- **BRIDGE** (optional): re-base the spanning
  `rankHypothesis_genuine_recordsLinks_of_theorem_55_gen` as a corollary of the row-rank form.

## Decisions made during this phase

- **2026-09-25 — opened** (PI: SPINE2 is the first sub-phase of Phase 40; weaken in place).
  Verbatim `notes/pencil/adjudications.md`.
- **Slice 1** landed the recon's hunks verbatim, except `case-iii.tex`'s triangle-base proof prose,
  reworded since the proof no longer invokes `lem:adjacent-degree-two-pair`.
- **Slices 2–3 landed as one commit**: Slice 2 alone breaks the build, since `GenericLift/` calls the
  weakened producer with its own `6`-pinned `hD`. Repairs beyond the recon's hunks: the
  `Theorem56.lean` `hD` line; `lem:cycle-realization`'s bound restated `m ≤ k+2`; and
  `lem:case-III`'s proof `\uses` gained `lem:low-degree-vertex`.
- **Slice 4** was transcribed verbatim from read-only opus/fable A/B spikes. Its two follow-ups were
  routed at the close (*Hand-off*). Its BRIDGE open point is design doc §3 BRIDGE.
- **2026-09-25 — PIN re-scoped** (PI, at the close; verbatim `notes/pencil/adjudications.md`).
  PIN stays queued. It is re-scoped to formalizing Jackson–Jordán's own pin-collinear proof: a
  second, independent proof of the planar theorem 40a already proves by KT's route. Its seed is the
  staged field-general write-up in `notes/w4-pending/JJ-field-general/`. It is multi-phase.
- **2026-09-25 — Slice 5, the close.** The JJ citation was verified against Crossref: *Discrete
  Comput. Geom.* 40(2) (2008) 258–278, doi:10.1007/s00454-008-9100-z. It enters
  `formalization.yaml` as an `independently-proves` source, and the `n ≥ 3` scope restriction left
  its `fidelity`. The re-read restated changelog asides in `case-iii.tex` and
  `molecular-induction.tex`, and `pencil.tex`'s now-stale "extended to `n = 2`" note. No exposition
  entries: the edit is project-side (`notes/BlueprintExposition.md`, *Phase 40a*).
