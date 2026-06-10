# Phase 22h — the corrected `d=3` assembly (work log)

**Status:** in progress (opened 2026-06-09 at the 22g close).

Takes the two producer nodes `lem:case-II-realization` / `lem:case-III` green at `d=3` by building
the corrected remaining-work picture the 22g recon program scoped (GAPs 1–5). **Per-leaf
signatures stay canonical in `notes/Phase22-realization-design.md` §1.48 (T1–T4, the triple-LI
bridge) and §1.49 (G5, G4a–G4e, G0, the (β) branch shape) — point at them, don't duplicate.**
22g's archive (delivered leaves + settled verdicts): `notes/Phase22g.md`.

## Current state

**G5 is DONE (single commit).** `IsProperRigidSubgraph` now requires `2 ≤ V(H).ncard`
(Deficiency.lean; KT p. 659's `1 < |V′|`), with the loopless-from-minimality brick
`loopless_of_isMinimalKDof` (Deficiency.lean, shared with G0) feeding the two circuit sites
(`circuit_splitOff_meets_fiber` / `fundCircuit_inducedSpan_vertexSet_eq`, each now `[G.Loopless]`).
One producer site beyond the §1.49(0) census surfaced and was repaired: `splitOff_isMinimalKDof`
offers the vertex-deleted `Gv` to `hnp` (KT 4.7), so it gained `hV3 : 3 ≤ V(G).ncard` — genuinely
needed (at `|V|=2` the double edge splits to a one-vertex loop graph that is *not* minimal); its
only caller `minimal_kdof_reduction` has `hV3` in the split branch. All other `hnp`-consumer
statements unchanged; blueprint `def:rigid-subgraph` synced (22g caveat removed),
`lem:reduction-step` + Thm 4.9 prose updated.

**Next concrete step: G4b-impl** — `minimal_kdof_reduction_full` (the ~15-line full-IH strong
induction, signature in design §1.49(1)) + the `theorem_55_generic` `hsplit`/`hsplitGP` restate to
the (β) shape, dropping its now-unused `hD`/`hfresh`. Pins the producer signature; 1 commit.

**Build order (design §1.49(6); estimated 13–18 commits):** G5 → **G4b-impl**
(`minimal_kdof_reduction_full` + the `theorem_55_generic` `hsplit`/`hsplitGP` restate to the
full-conditioned-IH (β) shape — pins the producer signature) → in parallel: {G4a-i/ii + G0 ∥ the
`|V|=3` triangle leaves T1–T4 ∥ G4c-i/ii} → G4d-i/ii → the (β)-shaped `hsplit` producer (the
§38-trap concrete-seed assembly with the G4e `M₁/M₂/M₃` dispatch) → Leaf 4 (the
`theorem_55_generic (n:=2) (k:=2)` instance node) → Leaf 5 (the banner flips + the Thm 5.5→5.6
push, unblocking Cor 5.7 at `d=3`).

## Lemma checklist

- [x] **G5** — the `IsProperRigidSubgraph` predicate repair (`2 ≤ V(H).ncard`) + producer-site
  re-proofs (incl. the uncensused `splitOff_isMinimalKDof` site, which gained `hV3`) +
  `loopless_of_isMinimalKDof` brick + blueprint `def:rigid-subgraph` sync (§1.49(0)). Done.
- [ ] **G4b-impl** — `minimal_kdof_reduction_full` (a ~15-line strong induction; the old
  reduction / `theorem_55` / their green blueprint nodes untouched) + the `theorem_55_generic`
  branch restate to the (β) full-IH shape (§1.49(1)).
- [ ] **G4a-i/ii + G0** — the `d=3` adjacent-degree-2-pair chain dichotomy (the cheap `D ≥ 6`
  double count, NOT KT's maximal chains — those are Phase 23's general-`d` form) + the data
  extraction (`b ≠ c`) + `simple_of_isMinimalKDof_of_noRigid` (§1.49(2)). Parallel-safe after
  G4b-impl.
- [ ] **T1–T4** — the `|V|=3` triangle base (§1.48(1)): T1 third-edge/vertex-pin (edge count via
  `rank_add_deficiency_eq`), T2 `theorem_55_triangle` (3-body sibling of `theorem_55_base`), T3
  the cyclically-consistent basis seed, T4 assembly through the GAP-2 upgrade. ~3–4 commits;
  parallel-safe after G4b-impl. (Ledger entry: `notes/BlueprintExposition.md`, writes at this
  phase's close.)
- [ ] **G4c-i/ii** — the fixed-seed `ρ = (a v)` relabel transport (graph iso + `ofNormals`
  framework transport; the existential motive is NOT transported — eq. (6.44) needs the SAME
  seed; genericity free, same coordinate set) (§1.49(3)).
- [ ] **G4d-i/ii** — the (6.43)→(6.44) `a`-column identity + the `M₃` `hcand_mem` (§1.49(4)).
- [ ] **The (β)-shaped `hsplit` producer** (the G4e spine; the §38 trap; §1.49(5)): G4a chain
  dichotomy → `|V|=3 ↦ T4`; chain arm: its own split data + `splitOff_isMinimalKDof` + measure ⟹
  IH at the `v`-split; R3 ⟹ the GP `.1` conjunct ⟹ `q` + `hgab` (via
  `hasGenericRealization_transport_ends`) + the triple-LI-from-alg-indep bridge (§1.48(2));
  GAP-3 good-`t`; the G4e `M₁/M₂/M₃` dispatch (`M₃` via G4c/G4d); compose the GAP-2 upgrade
  `hasGenericFullRankRealization_of_rigidOn_ofNormals` onto the bare candidate, supplying its
  `hne` from the candidate completion.
- [ ] **Leaf 4** — the `theorem_55_generic (n:=2) (k:=2)` instance node over the (β) shape,
  projecting `.2` (R2 verdict (B), §1.41); the `hcontractGP` wiring gains `hVH2` from G5. A small
  green blueprint node, not a standalone `theorem_55_dim3`.
- [ ] **Leaf 5** — the `lem:case-II-realization` / `lem:case-III` flips + the Thm 5.5→5.6 push
  feeding `rigidityMatrix_prop11`'s `hgen`; unblocks Cor 5.7 at `d=3`.

## Blockers / open questions

- **GAP 3 (bounded, folded into the producer):** `hnewtrans : LinearIndependent ![n_a + t•n', n_b]`
  — the bad-`t` set is ≤ 1 value (the affine line `t ↦ n_a + t•n'` meets `span{n_b}` at most once,
  from `hgab`), so a good `t ≠ 0` exists. `Fin(k+2)→ℝ` linear algebra.
- **The `ofNormals`/`withGraph` defeq-timeout trap** (TACTICS-QUIRKS §38) bites every
  carrier-instantiating leaf (the producer body, the T3/T4 seeds). Keep reasoning over abstract
  `F`; instantiate only at the seed.
## Hand-off / next phase

**Smallest next forward commit — G4b-impl** (`minimal_kdof_reduction_full` + the
`theorem_55_generic` (β) restate; design §1.49(1); see *Current state*). After 22h closes (the
molecular conjecture at `d=3`, Cor 5.7 unblocked → Phases 24–26): **Phase 23** = general `d` (KT
Lemma 6.13), scoped with the §1.33 (C) reuse map; open it with its own recon (KT eqs.
(6.46)–(6.67) vs the `d=3` Lean) and add the general-`d` alg-independence row to
`notes/AlgebraicIndependence.md`.

## Decisions made during this phase

- **G5 census correction (one site beyond §1.49(0)):** `splitOff_isMinimalKDof`'s KT-4.7 step
  offers `Gv = G.removeVertex v` to `hnp`, needing `2 ≤ |V(Gv)|` — so the lemma gained
  `hV3 : 3 ≤ V(G).ncard`. Not a formality: at `|V(G)|=2` (double edge, hnp now satisfiable) the
  splitOff is a one-vertex loop graph whose empty base misses the fresh fiber, so the old
  statement is *false* under the corrected predicate. Lesson reinforces §1.49(0)'s: census
  `hnp`-*applications*, not just `exact hnp …` greps — `refine hnp Gv ⟨…⟩` was the missed shape.
- **Loopless route over minimality-hypothesis route for the circuit sites:** the two circuit-site
  lemmas take `[G.Loopless]` (derived by callers via `loopless_of_isMinimalKDof`) rather than a
  full `IsMinimalKDof` hypothesis — (4.10) and the fundCircuit spanning step need only
  looplessness, keeping the statements at their honest strength.
