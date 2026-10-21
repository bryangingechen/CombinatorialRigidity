# Toolchain bump to Lean v4.36.0-rc1 (work log)

**Status:** in progress, and the build is RED on purpose. The pins are applied (Lean
`v4.36.0-rc1`, mathlib `930ae14`, `Matroid` `8ece630`) and `lake exe cache get` hit every file.
The first `lake build` stops at two blocking errors: 57 of the default target's 154 modules
compiled, 2 failed and 95 were never reached. This tree is a documented intermediate state of a
multi-commit bump on `master`, which the PI reviews before any push. **Next concrete task:** fix
G1 and G2, the two blockers (*Checklist*), rebuild, and extend the taxonomy over the 95 modules
they unblock. Queue item `bump-4.36`; plan and playbook `notes/ToolchainBumps.md`; why:
`notes/Reconcile-lean-cleanup.md` *Autopilot: for the PI*.

## Current state

**Next:** G1 and G2 in one commit (*Hand-off*). **The build is RED**: the pins and their checks
are done, and the rest of the breakage is unknown until the 95 blocked modules compile, the
fragility zone included.

| | before | after |
|---|---|---|
| `lean-toolchain` | `v4.34.0-rc2` | `v4.36.0-rc1` |
| mathlib | `8b36e867` (2026-08-24) | `930ae145` (1 476 commits on, 115 past `v4.36.0-rc1`) |
| `Matroid` | `2b92ee39` | `8ece6307` (`main`'s tip, 2026-10-20) |

**Verified at the open (2026-10-21):**
- **No baseline build.** v4.34.0-rc2's `lake` aborts on macOS 27 (exit 133), so the pre-edit tree
  cannot build here. Its Lean is unchanged since `f8a6f8ec` (RECONCILE 3/3's task 34), whose gates
  ran green under v4.34.0-rc2: 2 998 jobs, 0 warnings, `lake lint` passed.
- **The pins.** `scripts/bump-mathlib.sh 930ae14 --apply` resolved `930ae145516d…`, moved mathlib,
  the 8 transitive revs and Cli's `inputRev` (`v4.34.0-rc2` → `v4.36.0-rc1`). `Matroid` is a
  hand-edit: its `rev` and the "v4.34.0-rc2 one" comment in `lakefile.toml`, its `rev`/`inputRev`
  in `lake-manifest.json`; `require mathlib` stays last. Re-checked rather than assumed:
  `git ls-remote` gives `main` = `8ece630`, whose `lean-toolchain` is `v4.36.0-rc1` and whose
  manifest pins the script's 9 revs, plus `loogle` `9f11169aaebf`, which is ours (unchanged).
- `lake env lean --version`: "Lean (version 4.36.0-rc1, …, commit c9afcddf514a…, Release)", exit
  0, after fetching every dep; `git status` shows only the three pin files.
- `lake exe cache get`: "Attempting to download 9058 file(s)", 9058/9058 downloaded and
  decompressed, exit 0: a full hit, so no transitive pin is stale.
- **The first build** (`scratch/bump-4.36/build1.log`, gitignored): exit 1; 0 `failed to cache
  artifact`; 0 mathlib modules built, 143 `Matroid` modules built from source. Our modules: the
  default target's import closure is **154** (the root and 153 `CombinatorialRigidity.*`; the
  *gate set*'s "122" dates from 2026-08). 57 built, 2 failed, 95 blocked, and the import graph
  agrees exactly: every module importing neither failed one built, and none importing one did.
  42 are blocked by G1 alone, 3 by G2 alone, 50 by both.

**The fragility zone is unseen.** `Molecular/AlgebraicInduction/` (17 files, `CaseIII/` and
`Theorem55.lean` among them) and `Molecular/RigidityMatrix/` (4 files; `Basic.lean` defines the
`ScrewSpace` carrier) compiled 0 files; of the 43 files naming `ScrewSpace`, none compiled. No
site below is in the zone but W4's two header-only ones (`PanelLayer.lean`, `Coupling.lean`).
Proof repairs in the zone are dispatched at Opus.

## Checklist (the fix tasks, in order)

The taxonomy of the first build. Sites are deduplicated by (file, line, col), deprecations by
`scripts/sweep-deprecations.py`; paths are under `CombinatorialRigidity/`.

**Errors, by root cause.** Both are blockers; fix them first.

- [ ] **G1: mathlib's `Mathlib.Algebra.MvPolynomial.Funext` now imports its polynomial layer
  privately** (one `public import` of `…MvPolynomial.Rename`; plain `import`s of `…Polynomial.Roots`
  and two more). Our mirror `Mathlib/Algebra/MvPolynomial/Funext.lean` imports only it, so `![…]`
  and the `Polynomial` namespace are gone: 9 errors at 9 positions (79, 88, 97: `![p₁, …]` parses
  as Bool `!` of a list; 123–125: unknown `Polynomial`, `Polynomial.C`, `Polynomial.X`; 120: the
  goal left unsolved), plus a cascaded `unusedSectionVars` warning at 118. Fix: public imports for
  what the file uses (`Polynomial.funext` is in `Mathlib.Algebra.Polynomial.Roots`, `![…]` in
  `Mathlib.Data.Fin.VecNotation`). 1 file, ~2 lines. 92 modules wait on it (42 on it alone).
- [ ] **G2: `Set` is now a one-field structure** (`Mathlib/Data/Set/Defs.lean`: `ofPred ::
  protected Mem : α → Prop`), so a `Set V` no longer elaborates as a predicate `V → Prop`. 1 site:
  `Jacobs.lean:132:56`, `Function.Embedding.subtype S` (its cascade at 133:34 goes with it). Fix:
  pass the predicate (`(· ∈ S)`). 1 file, 1 line. 53 modules wait on it (3 on it alone). Expect
  this class again among the 95 blocked modules, wherever a set is used as a function.
- [ ] **The second build's taxonomy**: rebuild after G1 and G2 and add the 95 modules' groups here,
  ordered, each with its files, a size and the fragility zone marked.

**Warnings, by class** (from the 57 compiled modules; W4 from Lake's header check, which runs on
blocked modules too).

- [ ] **W1: deprecated names, 10 sites in 6 files**: `Henneberg.lean` 2, `HennebergRigidity.lean`
  1, `Mathlib/Algebra/Module/Submodule/Union.lean` 2,
  `Mathlib/Combinatorics/SimpleGraph/Connectivity/Connected.lean` 2,
  `Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean` 1, `Molecular/Extensor.lean` 2. Six
  renames, no "different type" note; `SetLike.not_le_iff_exists` → `IsConcreteLE.…` changes
  namespace, so check its dot notation. Mechanical: one `--apply` of the sweep over the full
  build's log.
- [ ] **W2: deprecated imports, 3 sites in 2 files**: `Mathlib/Data/Countable/Defs.lean:8`
  (`Mathlib.Data.Countable.Defs` → `Mathlib.Basic.Countable.Defs`: the mirror's own upstream path
  moved, so the mirror may move with it), `PebbleGame/Exec.lean:9, 10` (→ `Mathlib.Order.Sym2`,
  `Mathlib.Order.Prod.Lex.Basic`). By hand, small.
- [ ] **W3: `push Not` made no progress, 2 sites**: `Matroid/Constructions/Submodular.lean:166,
  378` (ported from `apnelson1/Matroid`). Drop the no-op, small.
- [ ] **W4: Lake's module-system warning, 22 (file, import) pairs in 13 files** ("imports … from
  package `mathlib`, which is designed for use with the module system"), new in this Lake: mathlib
  sets `requiresModuleSystem`. Complete already: exactly 13 of our 89 non-`module` files import
  mathlib directly. `BodyBar/` 8 pairs (6 files), `Matroid/Constructions/` 7 (2), `Molecular/` 6
  (4), `Nonvacuity.lean` 1. One decision (*Blockers*), then 1 line or a conversion.

**At the close:** the gate set in `notes/ToolchainBumps.md`, the "122" there corrected to the
closure's count; the bump record; the ROADMAP row flipped; `done = true` in the queue.

## Blockers / open questions

- **W4's fix, to decide at W4.** Lake's documented opt-out is `allowNonModules = true` on our
  `[[lean_lib]]` (one line: we mix non-`module` files with module dependencies, knowingly). The
  fix at the source is converting files to `module`, newly possible: `Matroid` at `8ece630` has a
  `module` header in 362 of its 365 files, which retires `LEAN-OPS.md`'s stated reason for the
  holdouts. That is a round of its own over up to 89 files. Leaning: the one line for the bump,
  the conversion filed as a later candidate.

## Hand-off / next phase

**Smallest next commit: G1 and G2.** Add the public imports that
`Mathlib/Algebra/MvPolynomial/Funext.lean` needs (~2 lines) and pass a predicate at
`Jacobs.lean:132` (1 line); rebuild to `scratch/bump-4.36/build2.log`; then add the 95 unblocked
modules' breakage to *Checklist*, as above. If that breakage is large, the commit lands G1, G2 and
the taxonomy with the build still RED, and the groups follow one per commit, in order. Neither
site is in the fragility zone.

**PI action, after the push** (none taken here: no push, no `gh` writes): close PR #1 and issue
#2, which this bump supersedes (`notes/ToolchainBumps.md` *Where this stands*).

## Decisions made during this bump

- **The pins** are the PI's (2026-10-21, `notes/ToolchainBumps.md` *Where this stands*): mathlib
  at the rev `Matroid`'s tip is tested against, not the tag, the rule of the v4.34 bumps.
- **The build is committed RED.** The visible breakage is already over ~10 sites (3 error sites,
  37 warning sites) with 95 modules unseen, so no partial fix rides in the opening commit.
- **The phase-note gate covers this log**: `notes/check-phase-note.py` now matches
  `Bump-<version>.md` (its *Which files*).
