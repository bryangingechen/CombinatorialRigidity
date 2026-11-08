# Phase 43c — NORMAL and SPRIME: the reduction on structural cases, then Theorem S′ (work log)

**Status:** in progress (opened 2026-11-08 with the PI), the third sub-phase of Phase 43
(PENCIL-NATURAL): layers NORMAL and SPRIME as one sub-phase, at the PI's choice (design doc §1,
2026-11-08). No Lean has changed yet. In order: slice 1 (NORMAL), SPRIME's pin (a spike and a
liveness walk, docs only), SPRIME's slices as the pin cuts them, and the sub-phase's last commit.
The next concrete commit is slice 1, pinned below: the reduction on five structural cases, the
minimum-degree lemma to a new appendix.

## Current state

**Next concrete commit: slice 1 (NORMAL), checklist item 1.** Its new Lean is the spike's, compiled
at the open; the rest is a move, docstrings and blueprint prose. Mode: structural edit. There is no
new chapter and no red target node, so the red-node consistency gate has nothing to read: each
slice reads and restates the nodes it reaches (`CombinatorialRigidity/CLAUDE.md` *Forward-mode
slices*). Plan and inputs: `notes/Phase43-design.md` §2, NORMAL and SPRIME; the PI's answers of
2026-11-08 are §1 there.

**Verified at the open (HEAD `7880d8f8`).**
- `lake lean notes/pencil-natural/NormalSpike.lean` (banked; invocation in its docstring): exit 0,
  no error or warning; `Graph.pencil_reduction'` and `Graph.graded_pencil_realization_theorem'` on
  the standard three axioms; the second's type is the landed theorem's (an `example … := rfl`).
  The restated reduction needs no `[Finite α] [Finite β]`, `n` or `hD`.
- `Graph.pencil_reduction`'s one caller is `Graph.graded_pencil_realization_theorem`
  (`Grade/Reduction.lean:81`), which passes one `hthree` to the cut, contraction and split arms;
  `Graph.exists_isProperRigidSubgraph_of_three_le_degree` (`Induction/Operations.lean:420`) has
  `pencil_reduction` as its only user. Neither name is on a status surface (`formalization.yaml`,
  README, home page).

## Architectural choices made up front

- **Statements byte-identical:** `pencil_realization_theorem`, `pencilPair_of_nonempty`,
  `Graph.graded_pencil_conditioned_pair`, `Graph.graded_pencil_realization_theorem`. Each Lean
  slice diffs their signature lines and runs `#print axioms` on them in a scratch file
  (`lake lean`): the standard three.
- **Statements that change, by design:** `Graph.pencil_reduction` (slice 1); in SPRIME,
  `Graph.IsX0Graph.exists_additiveCore` (a weaker hypothesis), `Graph.ChainUsable` and
  `Graph.X0Reduces` (two disjuncts, two constructors). None is a main result.
- **S′ at `d = 3` only** (the PI, design doc §1): `thm:pencil-d-theorem-s`,
  `def:pencil-d-usable-chain` and their Lean (`exists_additiveCoreAt`, `ChainUsableAt`, the bridge
  `chainUsable_iff_chainUsableAt_three`) fold into the `d = 3` nodes, not restated in every `d`.
- **Slice boundaries from the bodies** (as 43b): SPRIME's slices are cut by a liveness walk at the
  pin (item 2), not by the 43a line-range sizes.

## Lemma checklist

- [ ] **1. Slice 1 — NORMAL: the reduction on five structural cases** (Lean, blueprint, one
  commit). Line numbers at `7880d8f8`.
  - **Lean, the reduction.** Move `Graph.pencil_reduction` from
    `Induction/ForestSurgery/Reduction.lean` (its section `An induction over all multigraphs`,
    :776–867) into `Pencil/Grade/Reduction.lean`, above its caller, under its own `/-! ## -/`
    header, as the spike's `Graph.pencil_reduction'`, unprimed: hypotheses `hloop`, `hbase`
    unchanged; `hcut` unchanged; `hparallel` (loopless, `3 ≤ |V|`, two-edge-connected,
    `¬ G.Simple`, induction hypothesis at fewer bodies); `hsimple` (`G.Simple`, `3 ≤ |V|`,
    two-edge-connected, **no** induction hypothesis: the main-component induction takes the graph
    whole). No `n`, `hD`, `[Finite α] [Finite β]`. Docstring: the five cases, the lexicographic
    measure (only the loop case keeps `|V(G)|`), no "cf. KT Theorem 4.9"; it plays the role of KT
    Theorem 4.9's outer induction only (design doc §1, 2026-11-08, item 3). Drop the bullet's "and
    an induction over all multigraphs (`thm:pencil-reduction`)" from `ForestSurgery/Reduction.lean`'s
    module docstring (:27–28).
  - **Lean, the caller.** `Graph.graded_pencil_realization_theorem` as the spike's primed form:
    `hthree` dissolves into the cut, parallel and simple arms; the loop and base arms unchanged.
    Docstring and the module docstring (:11–29) read the five cases.
  - **Lean, docstrings.** `Induction/Operations.lean:24–25` and `:410–412`: the lemma has no Lean
    user; it answers for every multigraph what KT Lemmas 4.5–4.6 answer for minimal ones, and its
    node is the appendix's (below). `Pencil/Statement.lean:101` read against the restatement.
    `TACTICS-GOLF.md:1119` (the loop arm holds `|V(G)|`) stays true; check.
  - **Blueprint, `pencil.tex`.** Restate `thm:pencil-reduction` (:504–534) on the five cases, with
    "Cases (i), (iii) and (iv) are handed …; case (v) is handed nothing"; title "Reduction on all
    spanning multigraphs"; statement `\uses` loses `def:rigid-subgraph`,
    `lem:pencil-min-degree-rigid`; the proof (a case split under strong induction) loses
    `lem:two-edge-connected-degree`. Rewrite :454–462 ("Its case analysis still needs a vertex of
    degree two …"): the cases are structural, and a simple two-edge-connected multigraph goes whole
    to the main-component statements, whose own count finds its bodies of degree two. Name that
    count after reading the nodes: `notes/PencilNatural.md` §5 calls `lem:pencil-d-chain-count` the
    heir of KT Lemmas 4.5–4.6, and at `d = 3` `lem:pencil-x0-sparse-count` finds the bodies of
    degree two; cite what the nodes support. One glue sentence there: the reduction plays only the
    role of KT Theorem 4.9's outer induction; its contraction and degree-two steps have their
    counterparts in the main-component induction (verified against
    `sec:main-component-coverage`). Restate :536–549 ("The contraction and split cases, (iv) and
    (v), are settled by one argument …"): case (iv) by `lem:pencil-d-nonsimple-case`, case (v) by
    `lem:pencil-d-distinct-statement`; keep the `lem:pencil-contraction-deficiency` sentence only
    as far as its users bear it out.
  - **Blueprint, the appendix.** New chapter `blueprint/src/chapter/further-results.tex` (title
    e.g. "Further results"), `\input` in `chapter/main.tex` after `\appendix` and **before**
    `retrospective.tex`. A short lead: results proved and formalized that no proof in the
    chapters uses. Move `lem:pencil-min-degree-rigid` (`pencil.tex:481–502`) there whole (label,
    pin, `\leanok`, `\uses`, proof), with one sentence of context in mathematical terms (no route
    history: `AUTHORING.md`). `intro.tex:400` and `:413` say "the appendix"; read them, and make
    each name the one it means. `AUTHORING.md` *Structural placement* says "One appendix chapter":
    add one line that the further-results chapter precedes it.
  - **Blueprint, `pencil-d.tex`.** `thm:pencil-d-realization-theorem`'s proof (:4802–4844): the
    five cases; drop "This argument does not use the proper rigid subgraph … so it settles both";
    keep "does not depend on the dimension", now true of the statement. `sec:pencil-d-reduction`'s
    lead (:4310–4322) read against it. The remark after `thm:pencil-d-generic`'s proof (:6687–):
    "inside the induction of the reduction (\cref{thm:pencil-reduction}) … from the conditioned
    pair at the graphs with fewer bodies" no longer matches case (v), which has no hypothesis; say
    instead an induction on the number of bodies, at a simple two-edge-connected `G`.
  - **Elsewhere.** `intro.tex:301–305` and `:368`, `pencil.tex:28`, `:234`, `:415` read against
    the restatement (they name the induction, not its cases; expected unchanged).
    `notes/BlueprintExposition.md:1167` (the `thm:pencil-reduction` entry): one line, restated in
    43c, the lemma in the appendix.
  - **Gates.** Whole `lake build`, warning-clean, 0 `failed to cache artifact`; `lake lint`;
    `blueprint/lint.sh`; `blueprint/verify.sh` (checkdecls silent);
    `python3 scripts/check-docstring-labels.py` diffed against the parent;
    `python3 notes/check-phase-note.py`; the statement and axioms checks above; the moved name
    grepped tree-wide (`pencil_reduction`, `ForestSurgery/Reduction`).
- [ ] **2. SPRIME's pin** (recon, a docs-only design-pass commit; Opus suggested). A compiler-checked
  spike of S′ at `d = 3` (the fold: `exists_additiveCore`'s blocking hypothesis `¬ ChainUsable`
  without the `k = 2` merged-equality and `k = 1` split-off disjuncts; NEW-1, NEW-2; design doc §2
  SPRIME, whose "the move" was written for the general form) and a kernel liveness walk of the
  deletion set, as 43b's open did with `N1Spike.lean`, banked in `notes/pencil-natural/`. It cuts
  items 3–5 (or re-cuts them) and pins the first to builder precision, with the deleted-name
  list, the dead-docstring sweep (the three files design doc §2 names) and the walk's orphans
  (`lem:deficiency-two-body-chain-d` may lose its only user with `thm:pencil-d-theorem-s`).
- [ ] **3. SPRIME slice A — NEW-1 and NEW-2** (additive, green): `lem:deficiency-two-body-chain`
  restated, `lem:pencil-d-chain-core` gains the form (design doc §2).
- [ ] **4. SPRIME slice B — S′ at `d = 3`**: `exists_additiveCore` on the S′ hypothesis,
  `ChainUsable` and `X0Reduces` less two disjuncts and constructors, the general form and its
  bridge gone; `thm:pencil-x0-theorem-s`, `def:pencil-x0-usable-chain` restated,
  `thm:pencil-d-theorem-s`, `def:pencil-d-usable-chain` and the fmlnote deleted,
  `sec:pencil-d-chains`' lead (`pencil-d.tex:2174–2180`) and the core paragraph (:1079–1095)
  reworded.
- [ ] **5. SPRIME slice C — the deletions**: `SplitOff.lean`, open-ear-two, the two bounds, the
  split-off's own code; `sec:main-component-splitoff`, `thm:pencil-x0-open-ear-two`,
  `lem:deficiency-one-body-chain-d`, two table rows, `rem:pencil-x0-theta`'s `k = 2` step; the 42f
  record's sense named (design doc §2). README (:218) and `home_page/index.md` (:216) list
  "split-off" among the steps: restate.
- [ ] **6. The sub-phase's last commit (43c).** `PHASE-BOUNDARIES.md`'s sub-phase checklist: the
  ROADMAP marker, §43's 43c detail compressed, NORMAL and SPRIME to verdicts in the design doc,
  the ledger's 43c section, the main results' axioms, `formalization.yaml`'s route descriptions;
  the design doc's header says no sub-phase is open (`check-phase-note.py --selftest` reads that
  sentence); then EXPO's open, at the PI's word.

## Blockers / open questions

- **The KT Theorem 4.9 remark** itself is EXPO's (design doc §2, EXPO); slice 1 writes only the
  glue sentence, so the reference stands in the meantime (design doc §1 (a)).
- **Where `thm:pencil-reduction` lives** (`pencil.tex`, its only user in `pencil-d.tex`) is EXPO's.

## Hand-off / next phase

The next concrete commit is *Current state*'s: slice 1, whole. Builder rung: the coordinator's
(Sonnet plausible: the Lean is the spike's; Opus if the four chapters' prose argues for it). After
it, item 2, SPRIME's pin.

## Decisions made during this phase

The open's decisions are `notes/Phase43-design.md` §1 (the PI's answers of 2026-11-08) and the
choices above.
