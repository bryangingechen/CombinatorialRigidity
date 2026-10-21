# Toolchain bump to Lean v4.36.0-rc1 (work log)

**Status:** closed (opened and closed 2026-10-21). Queue item `bump-4.36`, done: Lean `v4.34.0-rc2`
→ `v4.36.0-rc1`, mathlib `8b36e867` → `930ae145`, `Matroid` `2b92ee39` → `8ece6307`, in five commits
on `master`, not yet pushed. Every gate is green on the final tree, and all 19 main results' axioms
are unchanged. The record (the pins, why, what broke, the gate table, the lessons) is
`notes/ToolchainBumps.md` *Bump record: v4.34.0-rc2 → v4.36.0-rc1*; its *Where this stands* has the
PI's actions after the push. **Next:** the queue's next item, RECONCILE 3/3, resumes at task 34.1
(`notes/Reconcile-lean-cleanup.md`).

## Current state

**Closed.** The commits: `8936b312` (the pins, the first build RED), `e91a16ad` (G1 and G2, and
the whole tree's taxonomy), `1fac0646` (G3 and G4), `6fbfe605` (W1 to W6), and the close (a
docstring reflowed, the remaining gates, the record, shape B lifted).

**The builds** (logs under `scratch/bump-4.36/`, gitignored). Every log has 0 `failed to cache
artifact` lines, no mathlib module was built from source, and every count agrees with the import
graph. The default target's closure is 154 modules: the root and 153.

| log | tree | exit | built / failed / blocked | result |
|---|---|---|---|---|
| `build1` | the pins (`8936b312`) | 1 | 57 / 2 / 95 | stops at G1, G2 |
| `build2`, `build2b` | + G1, G2 | 1 | 69 / 1 / 84 | stops at G3 |
| `build3-probe`…`8` | + G3, G4 (working tree) | 0 at `8` | 154 / 0 / 0 | each G4 site in turn |
| `build9` | + G3, G4 (`1fac0646`) | 0 | 154 / 0 / 0 | 0 `error`, 87 warnings, the probe's set exactly |
| `build10` | + W1 to W6 (`6fbfe605`) | 0 | 154 / 0 / 0 | 0 `error`, 0 `warning`, 6151 jobs |
| `build11` | the close | 0 | 66 rebuilt, 1 replayed | 0 `error`, 0 `warning`, 6151 jobs |

**The fragility zone** (`Molecular/AlgebraicInduction/`, `Molecular/RigidityMatrix/` and the 43
files naming `ScrewSpace`) compiled with no error; its 17 warning sites were renames or imports.

**The close checklist's other items don't apply** (`PHASE-BOUNDARIES.md`): there is no blueprint
chapter (so no end-to-end re-read and no exposition ledger), no ROADMAP §N section, no design doc
and no new main result, and no user-facing surface names the toolchain; the dispatch log is the
coordinator's.

## Checklist (the fix tasks, in order)

Sites deduplicated by (file, line, col); each group's root cause and fix shape are the record's
table.

- [x] **G1**: mathlib's `MvPolynomial/Funext` imports its polynomial layer privately; one `public
  import` in our mirror.
- [x] **G2**: `Set` shape A, a set where a predicate is expected; `(· ∈ S)` at `Jacobs.lean`.
- [x] **G3**: `Equiv.setCongr` changed meaning with no deprecation; `Set.equivOfEq` at 9 lines in 3
  files.
- [x] **G4**: `Set` shape B, 6 sites in 5 files; name the set. **Promoted to `TACTICS-QUIRKS.md`
  § 117.**
- [x] **W1 to W6**: 33 deprecated names (one sweep), 6 deprecated imports, 2 no-op `push Not`, 22
  module-system pairs, 1 type-changed deprecation, 1 deprecated `rwa`.
- [x] **The close**: `exists_independent_perp_pair_gen`'s docstring (`Claim612.lean`) reflowed to
  100 columns with no word changed; the gate set run on the final tree; the record and *Where this
  stands* in `notes/ToolchainBumps.md`, its "122" corrected to 154; § 117; the ROADMAP row; the
  queue's `done = true`.

## Blockers / open questions

None. **Candidate for the PI** (a later round, not a queue item): converting the 90 non-`module`
files (89 in this log before the close, whose scan missed `Carrier.lean`) to `module`, which would
retire `allowNonModules`; the record's last lesson.

## Hand-off / next phase

**The queue's next item, `reconcile-lean`**: RECONCILE 3/3 resumes at task 34.1
(`notes/Reconcile-lean-cleanup.md` *Hand-off*). **PI actions after the push** (none taken here: no
push, no `gh` writes): check the push's CI run, then close PR #1 and issue #2, which this bump
supersedes (`notes/ToolchainBumps.md` *Where this stands*).

## Decisions made during this bump

- **The pins** are the PI's (2026-10-21): mathlib at the rev `Matroid`'s tip is tested against.
- **One group of fixes per commit**, the opening committed RED; **probe, then revert** sized the
  blocked modules (the record's first lesson).
- **G3 and G4 landed as the probe's patch** unchanged; `Nonvacuity.lean` uses the named lemma
  `edgesIn_subset_edgeSet _`.
- **W4, W5, W2's mirror** (coordinator, 2026-10-21): `allowNonModules = true` on the lib;
  `+typeChanged` on the narrative-bridge shim, the pattern amended in
  `CombinatorialRigidity/CLAUDE.md` and `blueprint/AUTHORING.md`; the `Countable` mirror moved with
  its upstream file.
- **W3 and W6 forms**: `contrapose!` → `contrapose`; `rw [h'] at h0 ⊢; assumption`.
- **The phase-note gate covers this log**: `notes/check-phase-note.py` matches `Bump-<version>.md`.
- **Promoted:** shape B to `TACTICS-QUIRKS.md` § 117; the record to `notes/ToolchainBumps.md`.
