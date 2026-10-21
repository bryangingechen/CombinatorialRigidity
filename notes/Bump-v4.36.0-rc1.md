# Toolchain bump to Lean v4.36.0-rc1 (work log)

**Status:** in progress. The build is green but not yet warning-clean. The pins are applied (Lean
`v4.36.0-rc1`, mathlib `930ae14`, `Matroid` `8ece630`) and every error group, G1 to G4, is fixed:
`build9` is exit 0, 0 `error`, "Build completed successfully (6159 jobs)", all 154 default-target
modules compiled. What remains is warnings: 43 positioned sites plus Lake's 22 module-system
pairs (W1 to W6). This tree is a documented intermediate state of a multi-commit bump on `master`,
which the PI reviews before any push. **Next concrete task:** W1 + W3 + W6, the mechanical warning
classes (*Hand-off*). Queue item `bump-4.36`; plan and playbook `notes/ToolchainBumps.md`; why:
`notes/Reconcile-lean-cleanup.md` *Autopilot: for the PI*.

## Current state

**Next:** W1 + W3 + W6 (*Hand-off*). **The build is green** (`build9`, G1 to G4 fixed) but not
warning-clean: 43 positioned warning sites plus W4's 22 Lake pairs remain.

| | before | after |
|---|---|---|
| `lean-toolchain` | `v4.34.0-rc2` | `v4.36.0-rc1` |
| mathlib | `8b36e867` (2026-08-24) | `930ae145` (1 476 commits on, 115 past `v4.36.0-rc1`) |
| `Matroid` | `2b92ee39` | `8ece6307` (`main`'s tip, 2026-10-20) |

**The builds** (logs under `scratch/bump-4.36/`, gitignored). Every log has 0 `failed to cache
artifact` lines, no mathlib module is ever built from source, and every count agrees with the
import graph: each module importing no failed module built, and none importing one did.

| log | tree | exit | built / failed / blocked | stops at |
|---|---|---|---|---|
| `build1` | the pins (`8936b312`) | 1 | 57 / 2 / 95 | G1, G2 |
| `build2`, `build2b` | + G1, G2 (this commit) | 1 | 69 / 1 / 84 | G3 |
| `build3-probe`…`8` | + G3, G4 (working tree) | 0 at `8` | 154 / 0 / 0 | each G4 site in turn |
| `build9` | + G3, G4 (this commit, committed) | 0 | 154 / 0 / 0 | done: 0 `error`, warnings only |

`build8-probe`: "Build completed successfully (6159 jobs)", 0 `error`. The probe's fixes are kept
as `scratch/bump-4.36/probe-g3-g8.patch` (gitignored) and spelled out under *Checklist*.
`build9` (the patch applied unchanged) has the same 87 `warning:` lines as
`build8-probe` (the diff of the sorted sets is empty), none outside W1 to W6, and the 6 cascaded
unused-simp-argument warnings at `KFrame.lean` are gone.

**Verified at the open** (2026-10-21, `8936b312`'s message has the detail): no baseline build, as
v4.34.0-rc2's `lake` exits 133 on macOS 27 (the Lean was unchanged since `f8a6f8ec`, green under
rc2); `scripts/bump-mathlib.sh 930ae14 --apply` plus the `Matroid` hand-edit, `require mathlib`
last, `loogle` unchanged; `lake env lean --version` exit 0; `lake exe cache get` 9058/9058 files.

**The fragility zone** (`Molecular/AlgebraicInduction/`, 17 files with `CaseIII/` and
`Theorem55.lean`; `Molecular/RigidityMatrix/`, 4, whose `Basic.lean` defines `ScrewSpace`; and the
43 files naming `ScrewSpace`) compiled in the probe **with no error**. Its share of the breakage is
17 warning sites in 9 files, all renames or imports (W1, W2, W6). Proof repairs in the zone are
dispatched at Opus, and there are none.

## Checklist (the fix tasks, in order)

Sites are deduplicated by (file, line, col), deprecations by `scripts/sweep-deprecations.py`;
paths are under `CombinatorialRigidity/`.

**Errors, by root cause.** 17 lines in 10 files in all, none in the fragility zone.

- [x] **G1** (mathlib's `MvPolynomial/Funext` imports its polynomial layer privately now): one
  `public import Mathlib.Algebra.Polynomial.Roots` in `Mathlib/Algebra/MvPolynomial/Funext.lean`.
  `![…]` comes with it; a second import of `Mathlib.Data.Fin.VecNotation` was tested and dropped.
- [x] **G2** (`Set` shape A, below): `(· ∈ S)` for `S` at `Jacobs.lean:132`.
- [x] **G3, the third blocker (84 modules behind it): `Equiv.setCongr` changed meaning.** It is now
  `α ≃ β → Set α ≃ Set β` (`Mathlib/Logic/Equiv/Set.lean:177`); the equivalence of equal sets'
  subtypes is `Set.equivOfEq` (`:50`, simp lemma `Set.equivOfEq_apply`). The old name still
  exists, so no deprecation fires. 9 lines in 3 files: `BodyBar/KFrame.lean:439, 457, 475` (its 3
  errors and 6 cascaded unused-simp-argument warnings), `BodyBar/TayTheorem.lean:297, 299, 354,
  355, 357`, `JacobsZeroExtension.lean:184` (the last 6 sit behind KFrame; the probe fixed them
  before they compiled). Fix: `Equiv.setCongr h` → `Set.equivOfEq h`, `Equiv.setCongr_apply` →
  `Set.equivOfEq_apply`. Mechanical, ~9 lines; outside the zone.
- [x] **G4 (`Set` shape B, below), 6 sites in 5 files**, each a blocker in turn:
  `Molecular/Deficiency.lean:2389` (75 modules behind it), then
  `Molecular/Molecule/Pencil/MainComponent/Chain.lean:327` (10), `…/CoverageCut.lean:273, 283`
  (6), `…/GenericBase.lean:195` (3), `Nonvacuity.lean:413` (1). Mechanical, ~6 lines; outside the
  zone. The probe's fix per site is listed under shape B.

**The `Set` cascade, by shape** (`Mathlib/Data/Set/Defs.lean`: `structure Set (α) where ofPred ::
protected Mem : α → Prop`). Small: two shapes, 7 sites in 6 files across the whole tree.

- **Shape A, a set where a predicate is expected.** `Function.Embedding.subtype S`, `S : Set V`
  (G2, the only site). Fix: pass `(· ∈ S)`.
- **Shape B, an anonymous projection on a membership proof whose set is still a metavariable.** A
  binder `fun x hx => hx.1` given as the subset or non-membership argument of a lemma whose sets
  are fixed only by later unification (`union_eq_left.mpr`, `Set.ncard_le_ncard`,
  `Set.ncard_insert_of_notMem`, a local `hsv _`). Error: "Invalid projection … `hx` has type
  `?m.N.1 x`". Fix: name the set. Ascribe the binder (`fun g' (hg' : g' ∈ G.crossingEdges id) =>
  hg'.1` at Chain:327, the same at Deficiency:2389, `(h : w ∈ N(G, y) \ {v})` at CoverageCut:273,
  its `u` twin at 283); pass the set argument (`hsv {x ∈ V(G) | f x = f u} …`, GenericBase:195);
  or use the named lemma (`edgesIn_subset_edgeSet _`, Nonvacuity:413). G4's six sites.
- **Not seen anywhere in the tree:** `Set.ext`/`funext` across the old defeq, `setOf` unfolding,
  `show`/`change` through it, simp-lemma drift. No shape needs a new mirror lemma or a wrapper.

**Warnings, by class** (the whole tree, from `build8-probe`: G3 and G4 add or remove none, and
shift no warned line). 43 positioned sites, plus W4's 22.

- [ ] **W1: deprecated names, 33 sites in 20 files** (14 in the zone, in `Molecular/`:
  `Molecule/Pencil/{Arms,Chart}.lean`, `Molecule/Pencil/MainComponent/{Configuration,Cut,Flat,
  Lines}.lean`, `Molecule/ScrewVelocity.lean`, `RigidityMatrix/Claim612.lean`).
  17 × `Matrix.linearIndependent_rows_iff_isUnit` → `…_row_…`; 7 × `SetLike.not_le_iff_exists`
  and 3 × `SetLike.exists_of_lt` → `IsConcreteLE.…` (a namespace change: check dot notation); 6
  others; no "different type" note. One `--apply` of the sweep on a full build's log, then a
  build for line lengths.
- [ ] **W2: deprecated imports, 6 sites in 5 files** (2 in the zone): `Mathlib.Data.Real.Basic` →
  `Mathlib.Basic.Real.Basic` at `Mathlib/LinearAlgebra/Matrix/Rank.lean:17`,
  `Molecular/AlgebraicInduction/PanelLayer.lean:8`, `Molecular/Molecule/ScrewVelocity.lean:9`;
  `PebbleGame/Exec.lean:9, 10` (→ `Mathlib.Order.Sym2`, `Mathlib.Order.Prod.Lex.Basic`);
  `Mathlib/Data/Countable/Defs.lean:8`, the mirror whose upstream file moved (*Blockers*).
- [ ] **W3: `push Not` made no progress, 2 sites**: `Matroid/Constructions/Submodular.lean:166,
  378` (ported from `apnelson1/Matroid`). Drop the no-op.
- [ ] **W4: Lake's module-system warning, 22 (file, import) pairs in 13 files** ("imports … from
  package `mathlib`, which is designed for use with the module system"): exactly the 13 of our 89
  non-`module` files that import mathlib directly. `BodyBar/` 8 pairs (6 files),
  `Matroid/Constructions/` 7 (2), `Molecular/` 6 (4), `Nonvacuity.lean` 1. A choice (*Blockers*).
- [ ] **W5: a deprecation whose target has another type, 1 site**: the narrative-bridge shim
  `SimpleGraph.IsLaman.exists_rowIndependent_placement` (`MatroidIdentification.lean:945`). Lean
  now checks the types; the shim's differ by design. Lean's fix is `+typeChanged` (*Blockers*).
- [ ] **W6: deprecated syntax, 1 site**: `rwa [h'] at h0 ⊢`
  (`Molecular/Molecule/Pencil/MainComponent/Flat.lean:202`, in the zone), "use `rw [...] at ...
  <;> assumption`". Mechanical.

**At the close:** the gate set in `notes/ToolchainBumps.md`, its "122" corrected to the closure's
count; shape B lifted to `TACTICS-QUIRKS.md` as a rescue pattern (symptom "Invalid projection …
`?m.N.1 x`"); the bump record; the ROADMAP row flipped; `done = true` in the queue.

## Blockers / open questions

Choices, for the coordinator or the PI; none blocks G3 or G4.

- **W4.** Lake's documented opt-out is `allowNonModules = true` on our `[[lean_lib]]` (one line:
  we mix non-`module` files with module dependencies, knowingly). The fix at the source is
  converting files to `module`, newly possible: `Matroid` at `8ece630` has a `module` header in
  362 of its 365 files, which retires `LEAN-OPS.md`'s stated reason for the holdouts. That is a
  round of its own over up to 89 files. Leaning: the one line for the bump, the conversion filed
  as a later candidate.
- **W5.** `+typeChanged` on the shim changes the documented shim pattern, so the same commit would
  update `CombinatorialRigidity/CLAUDE.md` *Engineering conventions* and `blueprint/AUTHORING.md`
  *Narrative-bridge corollaries*.
- **W2's mirror.** `Mathlib/Data/Countable/Defs.lean` mirrors an upstream file that moved to
  `Mathlib/Basic/Countable/Defs.lean`. `DESIGN.md` *Mirror directory* would move the mirror too (5
  importers, 3 mentions in docs); the alternative keeps the path and changes only the import.

## Hand-off / next phase

**Smallest next commit: W1 + W3 + W6**, the mechanical warning classes (*Checklist*): one
`scripts/sweep-deprecations.py --apply` for W1's 33 deprecated-name sites (then a build for line
lengths), drop W3's two no-op `push Not` calls, and rewrite W6's `rwa`. The coordinator will pass a
shaping block for W2, W4 and W5's choices (*Blockers*), which stay open. Then the close gates
(`notes/ToolchainBumps.md` *The gate set*).

**PI action, after the push** (none taken here: no push, no `gh` writes): close PR #1 and issue
#2, which this bump supersedes (`notes/ToolchainBumps.md` *Where this stands*).

## Decisions made during this bump

- **The pins** are the PI's (2026-10-21, `notes/ToolchainBumps.md` *Where this stands*): mathlib
  at the rev `Matroid`'s tip is tested against, not the tag, the rule of the v4.34 bumps.
- **Committed RED, one group of fixes per commit**: the opening (`8936b312`) carried no fix, and
  this commit only G1 and G2 (the coordinator's scope); the remaining breakage is over ~10 sites.
- **G3 and G4 landed as the probe's patch**, unchanged: the `Nonvacuity.lean:413` site uses
  the named lemma `edgesIn_subset_edgeSet _` instead of a named binder (shape B's tighter form).
- **Probe, then revert**: G3 and G4 were applied in the working tree, rebuilt to a green tree and
  reverted, so the taxonomy covers every module while each commit stays one group.
- **The phase-note gate covers this log**: `notes/check-phase-note.py` matches `Bump-<version>.md`.
