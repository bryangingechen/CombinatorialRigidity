# Phase 40 cleanup round 2/5 — `40-factor`, the shared hub normalization (work log)

**Status:** ✓ closed 2026-09-30 (opened 2026-09-30). Round 2 of the five post-Phase-40 cleanup
rounds. Their order, stops and the PI's decisions are in `notes/Cleanup40.md`, and
`.claude/autopilot/queue.toml` is the authority for which rounds are done. The round extracted the
labeling normalization that the two relative hubs duplicated (`notes/Phase40-design.md` §7) and
rebuilt both hubs on it: three one-commit tasks, all landed. **Next concrete task:** none in this
round; the current round is named in `notes/Cleanup40.md`'s **Status**.
Round manual: `CLEANUP.md`.

## Current state

**Round 2 is closed** (task 3). All three tasks landed, each with one line under *Lemma checklist*
naming its commit. `Graph.exists_normalized_labeling` is in `Molecular/Deficiency.lean`, both hubs
are rebuilt on it with their statements unchanged, and design §7's entry is paid. Nothing is
mid-stream. What carried over: two structural findings to round 4 (*Candidates for `40-simplify`*,
mirrored into `notes/Cleanup40.md` §2 *Round 4*) and one declaration with no blueprint node to
round 3 (*Moved to a later round*, already in §2 *Round 3*).

**Verified at the close** (task 3; the Lean and blueprint trees are `0b260626`'s):
- Whole-project `lake build` green, 3003 jobs (as at the open: the round added no file), 0
  `warning:` lines, 0 `failed to cache artifact`. `lake lint` green.
- `#print axioms` on all **19** `formalization.yaml` main results gives `[propext,
  Classical.choice, Quot.sound]`, as at the open; the output is byte-identical to the open's. The
  harness `scratch/40-factor/Axioms.lean` was re-run with `lake lean` after its 19 names and 14
  imports were diffed against `formalization.yaml`'s `declaration:` and `file:` fields: identical.
- `scratch/40-factor/HubStatements.lean`, re-run with `lake lean`, prints the open's output: hash
  `1841993124` (length 14 980) for the PanelLayer hub and `3105723357` (20 262) for the TwoCut hub.
  Both statements are as they were.
- File sizes: `Deficiency.lean` 4 387 → 4 441 (+54), `PanelLayer.lean` 2 299 → 2 173 (−126),
  `TwoCut.lean` 424 → 358 (−66). Net −138 lines (`git diff --shortstat 8a932535 0b260626`: +93,
  −231).

**Verified at the open** (`8a932535`, a docs-only commit; its Lean and blueprint trees are
`bb333dc4`'s):
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

- [x] **1. E1 — the extraction and the PanelLayer hub** (⚠Z, Opus; `080be6a4`).
  `Graph.exists_normalized_labeling` landed in `Deficiency.lean` after `deficiency_nonneg`,
  verbatim from the spike, with a module-docstring clause. The PanelLayer hub's proof went from 101
  lines to 22, statement untouched (no diff line between its `theorem` line and `:= by`), dropping
  `open Classical in`, `Fintype α` and `set VG`. The orphan pair is retired (the tree-wide grep
  finds the two names only in this log), and both normalization docstrings are re-pointed. The
  no-node line is under *Moved to a later round* and mirrored into `notes/Cleanup40.md` §2
  *Round 3*. Gates: `lake build` green (3003 jobs, 0 warnings, 0 cache failures), `lake lint`
  green; both hub fingerprints still equal the open's, and all 19 main results stay at the three
  standard axioms.
- [x] **2. E2 — the TwoCut merged hub** (⚠Z, Opus; a transcription; `0b260626`).
  `screwDim_mul_compl_add_deficiencyMerged_le_finrank_jointMotions`'s proof is `Spike.lean` Part
  2's, verbatim: 90 lines to 27, statement untouched (no diff line between its `theorem` line and
  `:= by`), dropping `open Classical in`, `have : Fintype α` and `set VG … with hVG`. Its docstring
  is rewritten in the three places: the normalization narration names the extraction; "**`hu` and
  `hv` are load-bearing exactly here**" reads conjunct (v), which holds only on `V(G)`; the
  duplication paragraph is gone. Design §7's entry is marked paid and its closing index updated.
  The module docstring and `partitionMotions_le_jointMotions_bot`'s still read true (the latter's
  "merged hull" typo is now "hub"). Gates: `lake build` green (3003 jobs, 0 warnings, 0 cache
  failures), `lake lint` green; both hub fingerprints still equal the open's, and the merged hub
  and `weldedLoss_nonneg` are at the three standard axioms. `TwoCut.lean` 424 → 358.
- [x] **3. X — close the round** (`CLEANUP.md` *Workflow* rule 5; Opus; this commit). Docs only.
  - **Gates and axioms.** Whole-project `lake build` green, 3003 jobs, and `lake lint` green. The
    harness was re-diffed against `formalization.yaml` (identical) and re-run with `lake lean`: 19
    of 19 main results at `[propext, Classical.choice, Quot.sound]` (*Current state*).
  - **Fingerprints.** `HubStatements.lean` re-run (the scratch file was still there): both hashes
    equal the open's.
  - **Sizes.** Re-measured with `wc -l`: net −138 lines over the three files (*Current state*).
  - **ROADMAP row and `done = true`.** The row reads ✓ Complete, and `40-factor`'s row in
    `.claude/autopilot/queue.toml` has `done = true` (nothing else there changed).
  - **Status surfaces at round 3.** `notes/Cleanup40.md`'s **Status** and ROADMAP's
    cleanup-rounds bullet name opening round 3, `40-exposition`, as next, and say it stops for the
    PI after its open and one sample section.
  - **Candidates to round 4.** Both are mirrored into `notes/Cleanup40.md` §2 *Round 4*, one line
    each, naming this log.
  - **The sha backfill.** Task 2's "this commit" reads `0b260626`, here and in design §7's paid
    entry.

## Candidates for `40-simplify`

Structural findings, and any finding that would change a headline or blueprint statement. They are
recorded here and never acted on in this round (`notes/Cleanup40.md` §2). The close (task 3)
mirrored them, one line each, into `notes/Cleanup40.md` §2 *Round 4*.

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
- **The merged hub's `hne : V(F.graph).Nonempty` is redundant** (task 2, compiled). It follows
  from `hu`, and its one consumer, `weldedLoss_nonneg`, passes `⟨u, hu⟩`. In the proof it feeds
  only `have : Nonempty α`, which the merged hub does not need: it supplies the subtype's
  `Nonempty` directly, as `⟨⟨fun _ => u, rfl⟩⟩`. Deleting that `have` leaves `hne` unused (the
  `unusedVariables` warning, seen with the LSP), so dropping it means changing the statement. The
  merged hub has no blueprint node. (The PanelLayer hub is different: its
  `exists_eq_ciSup_of_finite` over `α → α` needs `Nonempty α`, which it can only get from `hne`.)

## Moved to a later round

Each line: the task, its target round, and a one-line reason. The same line goes into the target
round's plan section in `notes/Cleanup40.md` in the same commit.

- **`Graph.exists_normalized_labeling` (`Molecular/Deficiency.lean`) has no blueprint node**
  (task 1), round 3 (`40-exposition`). It is the relabelling both relative hubs share. It cites no
  nonexistent blueprint label, so no node is minted here (this round's rule), and
  `lem:relative-deficiency-rank-bound`'s proof already narrates the relabelling mathematically.
  Round 3's D5-blueprint-debt sweep decides whether to pin it or name it in that proof.

## Blockers / open questions

- None.
- Seen at the open, not a task: two of the round's three files are past the ~1500 tripwire
  (`CombinatorialRigidity/CLAUDE.md`). `Molecular/Deficiency.lean` has 4 387 lines and
  `PanelLayer.lean` 2 299 at the open, and no round in `notes/Cleanup40.md` plans a split. Task 1
  took the first to 4 441 (+54: the extraction, in its definitions' own file, *Decisions*) and the
  second to 2 173 (−126); both sizes stand at the close. `notes/PERFORMANCE.md` is where a split
  would be ranked.

## Hand-off / next phase

**Round 2 is closed; there is no next step in it.** Round 3, `40-exposition`, opened 2026-09-30
(`notes/Phase40-exposition.md`); `notes/Cleanup40.md`'s **Status** names the current round. What
carried over: the two *Candidates for `40-simplify`*, which are round 4's inputs (mirrored into
`notes/Cleanup40.md` §2 *Round 4*), and the one *Moved to a later round* entry, which is round 3's
(already in §2 *Round 3*). No task of this round is left open.

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
