# LEAN-OPS.md — rarely-needed Lean-source operations

**Read-on-demand reference, not session-start orientation.** Two
infrastructure procedures needed only occasionally — the module-system
conversion how-to (the conversion is already done across all 28 files)
and the `apnelson1/Matroid` fork-editing protocol — were extracted here
from `CLAUDE.md` to keep the per-`.lean`-session manual lean (the same
discipline behind `../PHASE-BOUNDARIES.md` / `../REFS.md`).
`CombinatorialRigidity/CLAUDE.md` keeps a one-line pointer + the critical
nub of each; this file is the full procedure. Read it when converting a
file to the module system or when patching the fork.

## Module-system conversion

Project files use Lean's module system (`module` + `public import` +
`@[expose] public section`) so downstream files see only an imported
module's public interface, not its full elaboration state (as mathlib
does). Landed in the Phase 8-perf pass across all 28 files; reference
shape: `Mathlib/Analysis/InnerProductSpace/PiL2.lean`.

**Converting a file:** (1) blank line then bare `module` after the
copyright block (the keyword *is* the marker — no `import`); (2) every
`import X` → `public import X`; (3) an unnamed `@[expose] public section`
between the `/-! … -/` doc block and the first declaration (closes
implicitly at EOF; existing `namespace/end` pairs unchanged).

**Constraints:**
- A `module` file can only `import` (or `public import`) other `module`
  files — build error *"cannot import non-`module` X"*. Mathlib is
  ~98.6% converted; the holdout that matters is
  `Matroid.Representation.Map` (`apnelson1/Matroid`), which keeps
  `LinearRigidityMatroid.lean` non-`module`. Non-`module` files import
  `module` files freely, so the rest of the project is unaffected.
- `public section` hides `def` bodies for defeq *intra*-module too
  (≈ `@[irreducible]`). Symptom: *"Not a definitional equality"* on a
  `:= rfl` projection, or *"definitions were not unfolded … not
  exposed"*. Fix: promote that `def` to `@[expose] def`. Default a new
  file to `public section`; reach for `@[expose] public section` only
  when most defs need exposure (cf. `Framework.lean`).
- `set_option backward.privateInPublic` is debt: the project carries
  **zero** opt-ins — do not add one. It's only needed when a `private`
  decl sits in an *exposed* (`@[expose]`) body or is an attribute-tagged
  (`@[simp]`/`@[fun_prop]`) helper resolved by name cross-module; the
  cleaner fix is demoting the helper from `private`. (`theorem`/`lemma`
  proof bodies are private scope regardless, so a private helper used
  only there needs nothing.)

Per-file `@[expose]`/`public` dispositions, the conversion audit, and
the eliminated opt-ins: `notes/PERFORMANCE.md` *Module system* / *F3.4–F3.5*.

## Editing the `apnelson1/Matroid` fork

The project's `Matroid` dependency is **the user's fork**
(`github.com/bryangingechen/Matroid`, pinned by `lake-manifest.json` +
`lakefile.toml`, checked out at `.lake/packages/Matroid/`) — *not* upstream
`apnelson1/Matroid` — maintained precisely so the project can patch it. **You
are authorized to edit it** when a proof genuinely needs a `cycleMatroid` /
`Matroid.Graph` / union API that does not yet exist there. (This is distinct
from the *local* vendored mirror under `CombinatorialRigidity/Matroid/`, which
is plain project source — see top-level `CLAUDE.md` *Vendored provenance*.)

- **Prefer the project-side route first.** A new lemma in
  `CombinatorialRigidity/Matroid/` or a `Mathlib/<exact path>` mirror travels
  with the project and needs no cross-repo step. Reach into the fork only when
  the project-side route genuinely can't reach the internals you need. (Often
  it can: Phase 22's N4b looked like it needed a fork-side `cycleMatroid`-under-
  collapse lemma, but the vendored `cycleMatroid_contract` applied directly.)
- **Mechanics — it is a separate git repo.** Edit + commit under
  `.lake/packages/Matroid/` in *that* repo's own history. Do **not** push the
  fork or bump its `rev`/`inputRev` in `lake-manifest.json` / `lakefile.toml`
  unprompted — both are outward-facing, cross-repo steps; surface them to the
  user as a follow-up. **Flag any pending fork edit** in the commit summary and
  the active `notes/PhaseN.md`: a local-only fork edit will not travel with a
  `git push` of this repo until the pin is bumped, so an unflagged one silently
  breaks the build for the next checkout.
