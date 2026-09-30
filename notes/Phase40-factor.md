# Phase 40 cleanup round 2/5 — `40-factor`, the shared hub normalization (work log)

**Status:** in progress (opened 2026-09-30). Round 2 of the five post-Phase-40 cleanup rounds.
Their order, stops and the PI's decisions are in `notes/Cleanup40.md`, and
`.claude/autopilot/queue.toml` is the authority for which rounds are done. The round extracts the
labeling normalization that the two relative hubs duplicate (`notes/Phase40-design.md` §7) and
rebuilds both hubs on it: three one-commit tasks, none landed. **Next concrete task:** task 1,
E1 — land `Graph.exists_normalized_labeling` in `Molecular/Deficiency.lean` and rebuild the
PanelLayer hub on it (⚠Z, Opus), transcribing the open's spike. Round manual: `CLEANUP.md`.

## Current state

**Opened; no task has landed.** The open settled the extraction's home, visibility and exact
signature (*The extraction, pinned*; *Decisions*). It backed them with a complete
compiler-checked spike: the extraction and both hubs rebuilt on it, with no `sorry`. Tasks 1 and
2 are therefore transcriptions.

**Verified at the open** (the Lean and blueprint trees are `bb333dc4`'s; this commit is docs
only):
- Whole-project `lake build` green, 3003 jobs, 0 `warning:` lines, 0 `failed to cache artifact`.
- `#print axioms` on all **19** `formalization.yaml` main results gives `[propext,
  Classical.choice, Quot.sound]`. The harness is round 1's `scratch/40-cleanup/Axioms.lean`,
  copied to `scratch/40-factor/Axioms.lean` (gitignored) after its 19 names and 14 imports were
  diffed against `formalization.yaml`'s `declaration:` and `file:` fields (identical), and run
  with `lake lean`. Re-run it the same way at the close.
- Both hubs' statements are fingerprinted for the close. `scratch/40-factor/HubStatements.lean`
  prints each statement's structural `Expr.hash`, which was stable across two runs:
  `1841993124` for the PanelLayer hub (`toString` length 14 980) and `3105723357` for the TwoCut
  hub (20 262). Equal output at the close means the round left both statements as they were.
- File sizes: `Deficiency.lean` 4 387 lines, `PanelLayer.lean` 2 299, `TwoCut.lean` 424.

**The spike** (`scratch/40-factor/`, gitignored; each file exits 0 under `lake lean`):
- `Spike.lean` imports `Molecule/Pencil/TwoCut.lean`. Part 1 is the extraction, verbatim as it is
  to land. Part 2 rebuilds both hubs on it under primed names, each in its own file's binder order.
  Part 3 is an `#eval` that checks each primed statement is `==` (the same `Expr`) to the landed
  one: both `true`. `#print axioms` on all three gives `[propext, Classical.choice, Quot.sound]`.
  Its only warnings are two over-long `#print axioms` lines in the harness itself.
- `SpikeDeficiency.lean` is Part 1 alone over `import CombinatorialRigidity.Molecular.Deficiency`,
  so the proof does not lean on a simp lemma or instance that only a downstream import supplies.
  It is warning-free, with the same axioms.
- Sizes: the PanelLayer hub's proof body goes from 101 lines to 22, and the TwoCut hub's from 90
  to 27. The extraction is 34 lines of statement and proof, plus its docstring.

## Scope and standing rules

- **Lean surface.** `Molecular/Deficiency.lean` (the extraction's home),
  `Molecular/AlgebraicInduction/PanelLayer.lean` (the hub, and the orphan pair task 1 retires),
  `Molecular/Molecule/Pencil/TwoCut.lean` (the merged hub). The hub consumers
  (`GenericityDevice.lean:574`, `Pencil/MainComponent/Flat.lean:360`, `TwoCut.lean:319`) are not
  edited: the statements they call do not change.
- **Blueprint.** No edit is planned. The PanelLayer hub's node is
  `lem:relative-deficiency-rank-bound` (`rigidity-matrix.tex`). Its proof narrates the relabelling
  mathematically ("relabelled so that its labels are bodies of $G$ and the outside bodies stay
  separate parts"), and that stays correct. The merged hub has no node (design §7's D5 list).
- **Hygiene only.** Both hubs' statements stay exactly as they are. In each task, `git diff` must
  touch no line from either hub's `theorem` line to its `:= by`; at the close, the fingerprint
  above is the test. A finding that would change a headline or blueprint statement goes to
  *Candidates for `40-simplify`*. It is not acted on, and it is not a stop.
- **Gates, every commit.** As in round 1. For Lean commits: `LAKE_CACHE_DIR` set, one
  whole-project `lake build` in the foreground, no `warning:` or `failed to cache artifact` lines
  in the full output, and `lake lint` green. Every commit also gets a friction review, and this
  log's checklist, *Current state* and *Hand-off* updated. Task 1's deletions also run the deletion
  variant of `CombinatorialRigidity/CLAUDE.md` *Forward-mode slices*.
- **⚠Z marks a fragility-zone task** (`.claude/commands/coordinate-phase.md` *Fragility zone*).
  `PanelLayer.lean` is in `Molecular/AlgebraicInduction/`, so task 1 is Opus: the playbook floor,
  with Phase 38 as the precedent. Task 2 is Opus too, because `notes/Cleanup40.md` §2 *Round 2*
  makes all of the round's builds Opus. On the playbook alone it could be rung-mapped: it edits
  only the labeling combinatorics of a hub typed over `ScrewSpace K k`, and it transcribes a
  compiled spike (the post-recon downgrade).

## The extraction, pinned

Design §7's five properties, in its order and numbering:

```lean
theorem Graph.exists_normalized_labeling [Finite α] (G : Graph α β) (f : α → α) :
    ∃ g : α → α, g '' V(G) ⊆ V(G) ∧ G.numParts g = G.numParts f ∧     -- (i), (ii)
      G.crossingEdges g = G.crossingEdges f ∧                           -- (iii)
      Nat.card (Set.range g) = G.numParts f + V(G)ᶜ.ncard ∧             -- (iv)
      ∀ ⦃x⦄, x ∈ V(G) → ∀ ⦃y⦄, y ∈ V(G) → (g x = g y ↔ f x = f y)      -- (v)
```

(The comments are for this log; the landed statement is `Spike.lean`'s, which has none.) The
proof takes `ι` from `Set.Finite.exists_injOn_of_encard_le` and sets `g x = ι (f x)` on `V(G)` and
`g x = x` off it.

- **No `Nonempty` hypothesis.** The proof treats an empty `α` with `g = f`, so neither hub has to
  supply one.
- **(iv) is in `Nat.card (Set.range g)`,** the form that
  `screwDim_mul_range_card_sub_le_finrank_partitionMotions` takes, so both hubs rewrite with it
  directly.
- **(iv) uses the idiomatic `V(G)ᶜ`.** The hubs' own statements write `.compl`, so each keeps its
  one-line `rfl` bridge `hcompl_eq` (see *Candidates*).
- **Which conjuncts the hubs read.** Both read (iii) and (iv); the merged hub also reads (v), as
  `hguv := (hgf hu hv).2 f₀.2`. (i) and (ii) are kept because design §7 specifies them, and they
  state what "normalized" means.

## Lemma checklist (the round's task list)

One commit per task, in the order given.

- [ ] **1. E1 — the extraction and the PanelLayer hub** (⚠Z, Opus).
  - Land `Graph.exists_normalized_labeling` in `Molecular/Deficiency.lean`, in the
    `## D-deficiency` section right after `deficiency_nonneg`, verbatim from `Spike.lean` Part 1
    (statement, proof and docstring). Add a clause naming it to the module docstring's
    `partitionDef` / `deficiency` bullet.
  - Rebuild the proof of `screwDim_mul_compl_add_deficiency_le_finrank_infinitesimalMotions` on it,
    from `Spike.lean` Part 2, leaving the statement untouched. The rebuilt proof needs neither the
    `open Classical in` above the hub, nor `have : Fintype α`, nor `set VG`, so drop all three.
    The spike's `==` check shows that dropping `open Classical in` leaves the statement unchanged.
    The hub's docstring cites `Set.Finite.exists_injOn_of_encard_le`; make it name the extraction.
  - Retire the orphan pair `crossingEdges_complement_sep` and `range_complement_sep_card`
    (`PanelLayer.lean` 2137–2181, Phase 22i L0c, each with its own `open Classical in`), for the
    reason under *Decisions*. Deletion gate: grep the whole tree for both names, and repoint
    anything found. At the open they occur only at their own declarations.
  - Two more docstrings narrate the normalization; re-point both at the extraction. One is the
    section docstring `### Complement-separated |range f|-form hub bound and B2`, whose step 2
    narrates it. The other is `screwDim_mul_range_card_sub_le_finrank_partitionMotions`'s, whose
    last sentence cites "the complement-separated refinement `f'`".
  - The extraction has no blueprint node. Add a line for it under *Moved to a later round* (round
    3's D5-debt sweep decides whether to pin it), and mirror that line into `notes/Cleanup40.md`
    §2 *Round 3* in the same commit.
- [ ] **2. E2 — the TwoCut merged hub** (⚠Z, Opus; a transcription).
  - Rebuild the proof of `screwDim_mul_compl_add_deficiencyMerged_le_finrank_jointMotions` on the
    extraction, from `Spike.lean` Part 2, leaving the statement untouched. As in task 1, drop
    `open Classical in`, `have : Fintype α` and `set VG … with hVG`.
  - Rewrite the hub's docstring in three places:
    - its normalization narration (the `if x ∈ V(G)` guard and
      `Set.Finite.exists_injOn_of_encard_le`) now names the extraction;
    - "**`hu` and `hv` are load-bearing exactly here**" now reads conjunct (v), which holds only
      on `V(G)`;
    - the last paragraph goes, because the duplication is paid. It calls the ~85 shared lines
      "acknowledged duplication" and points at `notes/Phase39.md` item 6, an entry that moved to
      design §7 at Phase 39's close.
  - Mark design §7's entry *The shared hub normalization — a factoring item* paid, naming the
    lemma and the commits of tasks 1–2. Update §7's closing index of carried items, which lists
    it.
  - Check that `TwoCut.lean`'s module docstring and `partitionMotions_le_jointMotions_bot`'s
    ("reuse the landed hub's counting argument verbatim") still read true. At the open, they do.
- [ ] **3. X — close the round** (`CLEANUP.md` *Workflow* rule 5).
  - Whole-project `lake build` (record the job count) and `lake lint`. `#print axioms` on the 19
    main results the open's way, re-diffing the harness against `formalization.yaml` first.
  - Re-run `scratch/40-factor/HubStatements.lean`; both hashes must equal the open's (*Current
    state*). If the scratch file is gone, rebuild it from that description.
  - Re-measure the three files (`wc -l`) and record the net change.
  - Flip the ROADMAP row to ✓ Complete, and set `40-factor`'s row in
    `.claude/autopilot/queue.toml` to `done = true`.
  - Point the status surfaces at round 3, `40-exposition`: `notes/Cleanup40.md`'s **Status** and
    ROADMAP's cleanup-rounds bullet. Round 3 stops for the PI after its open and one sample
    section.
  - Mirror the *Candidates* into `notes/Cleanup40.md` §2 *Round 4*, one line each, each naming
    this log.

## Candidates for `40-simplify`

Structural findings, and any finding that would change a headline or blueprint statement. They are
recorded here and never acted on in this round (`notes/Cleanup40.md` §2). The close mirrors them
into `notes/Cleanup40.md` §2 *Round 4*.

- **Both hubs' statements write `V(G).compl.ncard` where `V(G)ᶜ.ncard` is idiomatic** (seen at
  the open). Both hubs, and all three of their consumers, carry a one-line `rfl` bridge between
  the two forms (FRICTION *`sᶜ.ncard` vs `s.compl.ncard` notation mismatch for `rw`*). The
  bridges are the hubs' own `hcompl_eq`; `heq` in
  `BodyHingeFramework.finrank_span_rigidityRows_add_deficiency_le` (`GenericityDevice.lean`) and
  in `weldedLoss_nonneg` (`TwoCut.lean`); and the `(V(G).compl.ncard : ℤ) = (V(G)ᶜ.ncard : ℤ)`
  step in `Graph.three_add_deficiency_le_finrank_liftingSpace` (`Flat.lean`). Restating both hubs
  with `ᶜ` should let all five go (read off the proofs, not compiled). It changes no statement's
  strength, but it does change two statements, one of them pinned
  (`lem:relative-deficiency-rank-bound`), and this round keeps both exactly as they are.

## Moved to a later round

Each line: the task, its target round, and a one-line reason. The same line goes into the target
round's plan section in `notes/Cleanup40.md` in the same commit.

- None at the open. Task 1 adds one, for the extraction's missing blueprint node.

## Blockers / open questions

- None.
- Seen at the open, not a task: two of the round's three files are past the ~1500 tripwire
  (`CombinatorialRigidity/CLAUDE.md`). `Molecular/Deficiency.lean` has 4 387 lines and
  `PanelLayer.lean` 2 299, and no round in `notes/Cleanup40.md` plans a split. Task 1 adds about 50
  lines to the first, its definitions' own file (*Decisions*), and nets about −125 on the second.
  `notes/PERFORMANCE.md` is where a split would be ranked.

## Hand-off / next phase

**Next: task 1, E1** (⚠Z, Opus). Transcribe `scratch/40-factor/Spike.lean` Part 1 into
`Molecular/Deficiency.lean` right after `deficiency_nonneg`, rebuild the PanelLayer hub from Part
2, and retire the orphan pair, per the checklist. If the scratch spike is gone, *The extraction,
pinned* gives the statement and construction. The rebuilt hub then consumes it in about 20 lines:
attain the deficiency, normalize, apply `screwDim_mul_range_card_sub_le_finrank_partitionMotions`
at `g`, rewrite by (iii) and (iv), and close with `zify` and `linarith`.

## Decisions made during this round

- **2026-09-30, the open: the extraction is public, in `Molecular/Deficiency.lean`.** Design §7
  says "one private lemma". But these files are not `module` files, so `private` is file-local, and
  the two hubs are in different files (`TwoCut.lean` reaches `PanelLayer.lean` only transitively).
  The lemma is pure labeling combinatorics over `numParts` and `crossingEdges`, with no framework
  in it, and `Deficiency.lean` defines both. So the definitions' file is its home
  (`CombinatorialRigidity/CLAUDE.md` *Engineering conventions*), in the file's `Graph` namespace.
  Both hubs already import that file transitively, and it is outside the fragility zone.
- **The orphan pair is retired, not reused.** `crossingEdges_complement_sep` is the `if`-shaped
  special case of `Deficiency.lean`'s `crossingEdges_congr`. `range_complement_sep_card` is the
  count that the extraction's (iv) now proves for its own `g`. Both landed with the PanelLayer hub
  (Phase 22i, `b755bc14`), whose proof re-derived both facts inline, so neither has ever had a
  caller, and neither is pinned. Moving them next to the extraction would keep two uncalled public
  lemmas alive.
- **The residual shared tail is left.** After the extraction, the two hubs still share about 13
  lines of framework arithmetic (`hCg`, the range bound, `hpdef_eq`, and the `zify`/`linarith`
  close). Extracting that too would need a framework-side lemma in `PanelLayer.lean`, beyond §7's
  specification. For about 13 lines a hub, it is not worth a fragility-zone edit.
