# Phase 43c — NORMAL and SPRIME: the reduction on structural cases, then Theorem S′ (work log)

**Status:** in progress (opened 2026-11-08 with the PI), the third sub-phase of Phase 43
(PENCIL-NATURAL): layers NORMAL and SPRIME as one sub-phase, at the PI's choice (design doc §1,
2026-11-08). Slice 1 (NORMAL) landed: the reduction on five structural cases, beside its one
caller, and the minimum-degree lemma in a new appendix of further results. SPRIME's pin landed,
with a liveness walk that cuts SPRIME into slices A (two new lemmas), B (S′) and C (the
deletions). Slices A and B landed: Theorem S′ at `d = 3`, its proof citing the maximal-rigid-core
lemma as the PI asked, and the `d = 3` core bound deleted, with the main results unchanged. Next:
slice C, then the sub-phase's last commit. The next concrete commit is SPRIME slice C, item 5.

## Current state

**Next concrete commit: SPRIME slice C, checklist item 5** (pure deletion: 13 declarations, three
files, eight nodes and `sec:main-component-splitoff`; Lean, blueprint and docs). Slice B is in the
tree: `Graph.ChainUsable` on S′'s three conditions, `Graph.X0Reduces` with eleven constructors, and
`Graph.IsX0Graph.exists_additiveCore` on S′'s proof (`CoverageTheoremS.lean`); twelve declarations
and five nodes went. Its orphans are slice C's: the 13 declarations (no Lean user; still compiled)
and `thm:pencil-x0-open-ear-two` and `thm:pencil-x0-splitoff`, which no node uses. Mode:
structural edit, no new chapter and no red target node; each slice reads and restates the nodes it
reaches (`CombinatorialRigidity/CLAUDE.md` *Forward-mode slices*).

**After SPRIME's pin.** `notes/pencil-natural/SprimeSpike.lean` proves NEW-1, NEW-2 and S′ with no
`sorry`, and re-checks every landed consumer in the kernel against S′ and the eleven-clause
`X0Reduces` (a transport): the four main results' types are unchanged, on the standard three
axioms. Its walk and `sprime_walk.py` give items 4–5's deletion sets, orphans and sweep. Rerun
both at slice C: `lake lean notes/pencil-natural/SprimeSpike.lean 2>&1 | python3
notes/pencil-natural/sprime_walk.py`. A landed slice's names show as absent and its sweep is empty,
so the landing commit sweeps its own names (*Decisions made*, slice B).

**After slice 1.** `Graph.pencil_reduction` lives in `Pencil/Grade/Reduction.lean`, with no `n`,
`hD` or finiteness, and its simple two-edge-connected case takes no induction hypothesis;
`Graph.exists_isProperRigidSubgraph_of_three_le_degree` has no Lean user, its node
`lem:pencil-min-degree-rigid` in `blueprint/src/chapter/further-results.tex`
(`sec:further-results`). The four main results' signatures and axioms are unchanged (the
standard three).

## Architectural choices made up front

- **Statements byte-identical:** `pencil_realization_theorem`, `pencilPair_of_nonempty`,
  `Graph.graded_pencil_conditioned_pair`, `Graph.graded_pencil_realization_theorem`. Each Lean
  slice diffs their signature lines and runs `#print axioms` on them in a scratch file
  (`lake lean`): the standard three.
- **Statements that change, by design:** `Graph.pencil_reduction` (slice 1); in SPRIME,
  `Graph.ChainUsable` (two disjuncts fewer), `Graph.X0Reduces` (two constructors fewer), and so
  the hypothesis of `Graph.IsX0Graph.exists_additiveCore`. None is a main result.
- **S′ at `d = 3` only** (the PI, design doc §1): `thm:pencil-d-theorem-s`,
  `def:pencil-d-usable-chain` and their Lean (`exists_additiveCoreAt`, `ChainUsableAt`, the bridge
  `chainUsable_iff_chainUsableAt_three`) fold into the `d = 3` nodes, not restated in every `d`.
- **Slice boundaries from the bodies** (as 43b): SPRIME's slices are the pin's kernel walk.

## Lemma checklist

- [x] **1. Slice 1 — NORMAL: the reduction on five structural cases** (landed 2026-11-08). The
  spike's Lean, unprimed, moved beside its caller; `thm:pencil-reduction` restated, with the glue
  sentence that it plays only the role of KT Theorem 4.9's induction (`pencil.tex`, after the
  `K_4` paragraph); `lem:pencil-min-degree-rigid` moved whole to the new appendix;
  `thm:pencil-d-realization-theorem`'s proof on the five cases. Beyond the list:
  `main-component.tex`'s lead named "the contraction and split cases" of the reduction, now the
  simple two-edge-connected case. The count that finds the bodies of degree two: *Decisions made*.
- [x] **2. SPRIME's pin** (landed 2026-11-08, docs only): the spike and the walk, banked in
  `notes/pencil-natural/` (`SprimeSpike.lean`, `sprime_walk.py`). Verdict: *Decisions made*.
- [x] **3. SPRIME slice A — NEW-1 and NEW-2** (landed 2026-11-08; additive, green; statements
  of existing declarations unchanged, a spike transcription with no deviation).
  - *Lean, `Induction/SparseDeficiency.lean`* (section *The chains of one and two vertices*):
    add, before `deficiencyMerged_two_add_two_le_of_three_le`, NEW-1
    `Graph.exists_deficiency_three_induce_eq_zero_of_deficiency_two_lt [Finite α] [Finite β]
    {G} (hSv : ∀ X ⊆ V(G), 2 ≤ X.ncard → 1 ≤ (G.induce X).partitionDef 2 id) {a b}
    (ha : a ∈ V(G)) (hb : b ∈ V(G)) (hab : a ≠ b) (hnadj : ¬ G.Adj a b)
    (hlt : G.deficiency 2 < G.deficiencyMerged 2 a b + 2) :
    ∃ Z ⊆ V(G), a ∈ Z ∧ b ∈ Z ∧ 3 ≤ Z.ncard ∧ (G.induce Z).deficiency 3 = 0`, the body of
    `…_of_three_le` (the pair case closed by `exfalso`, the tight case returning `Z`); re-prove
    `…_of_three_le` from NEW-1 (with `deficiency_eq_zero_of_deficiency_eq_zero_of_le` and
    `deficiencyMerged_eq_deficiency_of_mem`) and `deficiencyMerged_two_add_two_le` from NEW-1
    directly (the spike's primed form). The header's *Main statements* names NEW-1.
  - *Lean, `Pencil/Grade/TheoremS.lean`* (section *A core at a long chain*): add, before
    `exists_additiveCoreAt_of_partitionDef_nonpos`, NEW-2
    `Graph.IsOpenEar.exists_additiveCoreAt_of_deficiency_induce_eq_zero`: that lemma's signature
    with `(hs : …)` replaced by `{Y : Set α} (hYV₁ : Y ⊆ V₁) (hY2 : 2 ≤ Y.ncard)
    (hYd : (G.induce Y).deficiency n = 0)`, and its body less the first `obtain`; the old lemma
    becomes that `obtain` and NEW-2. The header's *Main results* names NEW-2.
  - *Blueprint.* `lem:deficiency-two-body-chain` in two parts, (1) NEW-1's statement (`a`, `b`
    lie in a rigid set `Z` with `|Z| ≥ 3`) and (2) the current one; `\lean{NEW-1,
    Graph.deficiencyMerged_two_add_two_le}`; proof (1) the current proof less its last sentence,
    (2) by (1) and `lem:deficiency-merge-rigid`; `\uses` loses `lem:deficiency-two-body-chain-d`,
    and its fmlnote goes. `lem:deficiency-two-body-chain-d`'s proof: part (1) of
    `lem:deficiency-two-body-chain`, `lem:deficiency-rigid-higher`, `lem:deficiency-merge-rigid`
    (its `\uses` exactly these). `lem:pencil-d-chain-core` gains the form: (1) a set of at least
    two bodies inside `V₁`, rigid in dimension `d`, gives a core in dimension `d` avoiding `x₁`;
    (2) the current statement, by `lem:deficiency-sparse` and (1); `\lean{NEW-2, …}`.
  - *Gates*: as every Lean slice, and `scripts/check-docstring-labels.py` diffed against the
    parent (two pins move). About +25 Lean lines and +15 TeX.
- [x] **4. SPRIME slice B — S′ at `d = 3`, and what loses its last user with it** (landed
  2026-11-08, as pinned below, the `d = 3` core bound with it; Lean +194/−476, TeX +182/−424).
  Beyond the list: `pencil-d.tex`'s opening paragraph, the split-off subsection's sentence that the
  coverage applies it, the module docstrings of `CoverageCut.lean` and `SparseCount.lean`, the
  ledger's S′ and one-body entries, one FRICTION pointer. Choices: *Decisions made*, slice B. The
  walk: 10 deletions, none with a surviving user; it orphans exactly item 5's 13.
  - *Lean.* `CoverageTheoremS.lean`: `Graph.ChainUsable` is the spike's `ChainUsable'` (`3 ≤ k`;
    `k = 2`, `a`, `b` not adjacent and `def₂(G[V₁]; a, b) + 2 ≤ def₂(G[V₁])`; `k = 1` and
    `def₃(G[V₁]; a, b) = def₃(G[V₁])`); `Graph.IsChain.x0Reduces_of_chainUsable` loses its
    `openEarTwo` and `splitOff` arms; `Graph.IsX0Graph.exists_additiveCore` keeps its signature
    and takes the spike's proof; `x0Reduces_of_sparse` keeps its source. `Coverage.lean`:
    `Graph.X0Reduces` loses `openEarTwo` and `splitOff`, `Graph.X0Reduces.x0Attains` their arms.
    Deleted: `Graph.ChainUsableAt`, `Graph.IsX0Graph.exists_additiveCoreAt`,
    `Graph.chainUsable_iff_chainUsableAt_three`, `Graph.IsOpenEar.isX0Graph_splitOff_one`,
    `Graph.deficiencyMerged_add_bodyBarDim_sub_one_le`, `Graph.deficiencyMerged_three_add_five_le`,
    `Graph.deficiencyMerged_two_add_two_le_of_three_le`, `Graph.deficiencyMerged_two_add_two_le`.
    Docstrings: the walk's slice-B sweep, Coverage.lean's "thirteen constructors", and
    `x0Reduces_of_sparse`'s `θ` sentence, false under S′ (*Decisions made*).
  - *main-component.tex.* Restated: `def:pencil-x0-usable-chain`; `def:pencil-x0-reduces`
    (clause (5) loses "`k = 2` and `def₃(G[V₁]) ≤ def₃(G)`", clause (6) goes, (7) becomes (6),
    cited in the proofs of `thm:pencil-x0-coverage` and `thm:pencil-x0-reduction-attains`, which
    loses `thm:pencil-x0-open-ear-two` and `thm:pencil-x0-splitoff`); `lem:pencil-x0-chain-reduces`'
    proof (the ear clause only); the table less two rows, and the paragraph after it;
    `thm:pencil-x0-theorem-s`' proof on S′'s route **as the Lean runs it** (the PI, *Decisions
    made*, first): every core from `lem:pencil-d-maximal-rigid-core` at `d = 3`, directly or
    through `lem:pencil-d-chain-core` and `lem:pencil-d-core-positive-deficiency`, with no
    route-divergence fmlnote; `\uses` −`lem:deficiency-core-bound`, −`lem:deficiency-one-body-chain`,
    −`def:pencil-d-usable-chain`, −`thm:pencil-d-theorem-s`, + those three, and minus whatever
    else only the old core argument used (re-derive from the rewritten proof); part (2) of
    `lem:deficiency-one-body-chain` (pin, proof, two `\uses`, fmlnote) and of
    `lem:deficiency-two-body-chain` (pin, `\uses` merge-rigid), and that node's fmlnote, which
    slice A rewrote where item 3 said it goes and which part (2)'s removal makes false;
    `rem:pencil-x0-theta`'s second paragraph ("a usable chain, or a core");
    `sec:main-component-sparse`'s lead (:4016–4026).
  - *The `d = 3` core bound (the PI, 2026-11-08; not in the pin's walk).* Delete
    `lem:deficiency-core-bound` (`main-component.tex` :4165–4216, node, proof and fmlnote) and its
    two pins, `Graph.deficiency_three_induce_eq_zero_of_le` and
    `Graph.partitionDef_induce_id_le_of_maximal` (`SparseDeficiency.lean` :643–, :715–; no Lean
    user, grepped at `9fb254e4`), with the module docstring's lines :40–41 and the section header
    :601. Its proof is where the argument of part (2) is written: move that argument into part (2)
    of `lem:deficiency-core-bound-d`'s proof (`pencil-d.tex` :992 now says "the proof of part (2)
    of `lem:deficiency-core-bound` holds …"), read at `def_d` and `D − 1`. Reword
    `lem:pencil-d-maximal-rigid-core`'s proof (:1131, "As in the proof of
    `thm:pencil-x0-theorem-s`", circular once S′ cites it) and `sec:pencil-d-deficiency`'s lead
    (:907). `notes/BlueprintExposition.md` :1555: the entry's exposition now lives in
    `lem:deficiency-core-bound-d`'s proof; repoint it. **Keep:** `lem:deficiency-core-bound-d`,
    `Graph.deficiency_induce_eq_zero_of_le`,
    `Graph.partitionDef_induce_id_le_of_maximal_of_three_le_bodyBarDim`. Grep stems with care:
    `lem:deficiency-core-bound` prefixes the kept `-d` label, and
    `partitionDef_induce_id_le_of_maximal` the kept `…_of_three_le_bodyBarDim`. Add the two
    declarations and the node to `sprime_walk.py`'s slice-B set, or record why the walk needs no
    change.
  - *pencil-d.tex.* Deleted: `def:pencil-d-usable-chain`, `thm:pencil-d-theorem-s`,
    `lem:deficiency-one-body-chain-d`, `lem:deficiency-two-body-chain-d`. Reworded:
    `sec:pencil-d-deficiency`'s lead (:903–915), the core paragraph (:1079–1095, keeping "rigid"
    and "core" in dimension `d`), `sec:pencil-d-chains`' lead (:2174–2180),
    `thm:pencil-d-chain-or-core`'s `d = 3` paragraph, and :4122–4125.
  - About −360 Lean declaration lines and +135 for S′'s proof; TeX −126 lines of nodes.
- [ ] **5. SPRIME slice C — the two steps and what only they use** (pure deletion: 13
  declarations, no surviving user after slice B, no orphan).
  - *Lean.* Delete the files `MainComponent/SplitOff.lean`, `Mathlib/Data/Matrix/Mul.lean` and
    `Mathlib/Algebra/MvPolynomial/Polynomial.lean`, and `Graph.X0Attains.of_openEar_two`
    (Short.lean), `PanelHingeFramework.finite_setOf_finrank_lt_of_curve` (Bridge.lean),
    `Graph.ker_liftingMatrix_congr`, `Graph.ker_liftingMatrix_le_of_le` (Carrier.lean),
    `BodyHingeFramework.finrank_span_rigidityRows_eq_add_of_motions`,
    `Graph.mem_liftingSpace_oneEar` (Ear.lean). Imports: Coverage.lean's (to `Orbit`),
    Bridge.lean's mirror (check what it still needs), three lines of `CombinatorialRigidity.lean`.
    Docstrings: the walk's slice-C sweep (ten Lean files).
  - *Blueprint.* Delete `sec:main-component-splitoff` (six nodes), `thm:pencil-x0-open-ear-two`,
    and `lem:pencil-weighted-lifting-system-local` (its one pin dies; design doc §2 missed it);
    restate `rem:pencil-x0-theta`'s `k = 2` step and the surviving references
    (main-component.tex :137–141, 1175, 1422, 3234, 4022; `sprime_walk.py` (3)–(4)).
  - *Elsewhere.* README (:218) and `home_page/index.md` (:217) list "split-off" among the steps:
    restate. TACTICS-GOLF.md (:464, :1686) cites `SplitOff.lean`; FRICTION.md (:3578, :3600,
    :5694) names deleted declarations; `notes/BlueprintExposition.md` names deleted nodes. The 42f
    record's sense named in the design doc (§2).
  - About −900 Lean declaration lines (the three files 840), TeX −397 lines of nodes and section.
- [ ] **6. The sub-phase's last commit (43c).** `PHASE-BOUNDARIES.md`'s sub-phase checklist: the
  ROADMAP marker, §43's 43c detail compressed, NORMAL and SPRIME to verdicts in the design doc,
  the ledger's 43c section, the main results' axioms, `formalization.yaml`'s route descriptions;
  the design doc's header says no sub-phase is open (`check-phase-note.py --selftest` reads that
  sentence); then EXPO's open, at the PI's word.

## Blockers / open questions

- **The KT Theorem 4.9 remark** itself is EXPO's (design doc §2, EXPO); slice 1 wrote only the glue
  sentence (`pencil.tex`, `sec:pencil-reduction`'s lead), as design doc §1 (a) asks.
- **Where `thm:pencil-reduction` lives** (`pencil.tex`, its only user in `pencil-d.tex`) is EXPO's.

## Hand-off / next phase

The next concrete commit is *Current state*'s: SPRIME slice C, item 5 (deletions only, one
commit; its lists are the walk's slice-C set, sweep and section (4)). Then item 6, the sub-phase's
last commit, and EXPO's open at the PI's word.

## Decisions made during this phase

The open's decisions are `notes/Phase43-design.md` §1 (the PI's answers of 2026-11-08) and the
choices above.

- **S′'s proof cites the maximal-rigid-core lemma, and the `d = 3` core bound goes** (the PI,
  2026-11-08, reviewing the pin's choice taken in the PI's absence, which kept S′'s own `d = 3`
  argument through `lem:deficiency-core-bound`; the PI's words: design doc §1). The PI: "was there
  an opportunity for extra simplification using the maximal-rigid-core lemma? If so, I'd go with
  that." Then, of the `d = 3` node and its two Lean pins: "Would those results be independently
  interesting? If so we could put them in an appendix like we have been for some others, but if
  not then we can lose them." They are the case `d = 3` of the kept `lem:deficiency-core-bound-d`,
  so they go (item 4).
- **Slice B (item 4).** From the Lean, not item 4's paraphrase: S′'s cores come from
  `lem:pencil-d-maximal-rigid-core`, directly or through `lem:pencil-d-chain-core`, or from
  `lem:pencil-d-core-positive-deficiency` (a set of least singleton value, not a maximal one); and
  part (2)'s moved argument reads with `def_d` only, its singleton values planar, so no `D − 1`.
  `rem:pencil-x0-theta` names `θ(1,3,3)`, reached at a core. A landed slice's names are absent from
  the walk, its edits on deleted nodes skipped and its sweep empty, so slice B swept by a
  boundary-checked grep; the orphans also list NEW-1 and NEW-2, an artefact (the after-world reads
  S′ as the spike's primed form). `#sprime_mapped_same` now reports a deleted name.
- **SPRIME's pin (item 2).** S′ holds as Lean at `d = 3` in the folded form, and every consumer
  re-checks in the kernel; §2's route held at every step. The walk confirms §2's deletions and adds
  four declarations and `lem:pencil-weighted-lifting-system-local`; the bounds die with S′ (B), not
  with the steps (C). Under S′ a sparse `θ`-graph may have no usable chain (`θ(1,3,3)`: both long
  paths are chains with adjacent ends), so `x0Reduces_of_sparse`'s docstring and
  `rem:pencil-x0-theta`'s coverage paragraph say "or a core".
- **The count that finds the bodies of degree two** (slice 1, read from the nodes): part (1) of
  `lem:pencil-x0-sparse-count` (no planar-rigid set, so sparse, so at least four bodies of degree
  two; used by Theorem S and its every-`d` form). `lem:pencil-d-chain-count` starts from the
  chains and counts the edges along them, the counterpart of KT Lemma 4.6's count of maximal
  chains, not the count that finds the bodies; `pencil.tex` cites each in that role. The recon's
  "heir of KT Lemmas 4.5–4.6" (`notes/PencilNatural.md` §5) is EXPO's to word.
