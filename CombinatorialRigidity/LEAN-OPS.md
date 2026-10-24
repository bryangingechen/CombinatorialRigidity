# LEAN-OPS.md — rarely-needed Lean-source operations

**Read-on-demand reference, not session-start orientation.** Two
infrastructure procedures needed only occasionally — the module-system
conversion how-to (every project file is a `module` since Phase 41a's item
P5) and the `apnelson1/Matroid` fork-editing protocol — were extracted here
from `CLAUDE.md` to keep the per-`.lean`-session manual lean (the same
discipline behind `../PHASE-BOUNDARIES.md` / `../REFS.md`).
`CombinatorialRigidity/CLAUDE.md` keeps a one-line pointer + the critical
nub of each; this file is the full procedure. Read it when a `module`
file fails in a way the module system explains, when converting a script
or scratch file, or when patching the fork.

## Module-system conversion

Project files use Lean's module system (`module` + `public import` +
`@[expose] public section`) so downstream files see only an imported
module's public interface, not its full elaboration state (as mathlib
does), and a proof-only edit rebuilds no importer. The first files
converted in the Phase 8-perf pass, the last 90 in Phase 41a's items
P3–P5 (2026-10-24), so every file of the library is one; a new file is
authored as one. Reference shape:
`Mathlib/Analysis/InnerProductSpace/PiL2.lean`.

**Converting a file:** (1) blank line then bare `module` after the
copyright block (the keyword *is* the marker — no `import`); (2) every
`import X` → `public import X`; (3) an unnamed `@[expose] public section`
between the `/-! … -/` doc block and the first declaration (closes
implicitly at EOF; existing `namespace/end` pairs unchanged).
From the repository root, `python3 scripts/module-conversion-plan.py --convert
<file>…` applies the three steps (to a file with a module docstring; the root,
which has none, was converted by hand); with no flag it lists the files left
(none since P5), in an order that keeps each commit building (`--layers`), and
what to check in each (`--hazards`).

**What a conversion breaks** (Phase 41a's items P3–P5, the last 90 files: nine failed their
first build; `../notes/PERFORMANCE.md` *The conversion, layers 0–8* and the two after it):
- **The import closure narrows.** A `module` file sees only what its imports
  re-export, so a tactic or lemma reached through an upstream file's private
  `import` is gone: `unknown tactic` (`ring`, via `Mathlib.Tactic.Linarith`) or
  `Unknown constant` (`Nat.cast_sum`). Import it directly, with a plain
  `import` when only proofs use it.
- **Bodies hidden upstream stop unfolding.** An `rfl`, `rw [f]` or `unfold f`
  through a definition that an already-`module` file does not expose (19
  project files use `public section`, and mathlib exposes little) fails, and
  so does a bare `exact h` that held by unfolding: *"Type mismatch"*, with a
  note naming the definition *"not unfolded because [its] definition is not
  exposed"* (P4: mathlib's `Graph.deleteVerts`, under `removeVertex`, at
  three sites the `--hazards` scan cannot see). Destructuring a membership
  that holds by unfolding fails the same way: *"Invalid `⟨...⟩` notation:
  The expected type … is not an inductive type"*, or `rcases` *"is not an
  inductive datatype"* (P5: `rintro ⟨S, hS, rfl⟩` on `relScrews`, in the
  `public section` file `RigidityMatrix/Bricks`). Add `@[expose]` to the
  project definition, or use a lemma about it.
- **A private name is unknown in public scope.** A `private` declaration
  named in a public statement or an exposed body (under the file-wide
  `@[expose]`, any `def`'s body) is `Unknown identifier`, with a note that it
  would need to be public. A proof inside the body counts, a `have` in its
  tactic block included; only a `by` block given as a term, such as a proof
  argument, is private scope (`../scripts/ModulePrivateScope.lean`; P5:
  `flatScrewEquiv`'s surjectivity `have`). Drop `private`, also from its
  `@[simp]` lemmas, which importers' `simp` would otherwise lose. A
  theorem's proof is private scope and needs nothing.
- **A name can resolve elsewhere.** When a public declaration has the
  private one's name in an enclosing namespace (the root included), the
  exposed body resolves to it instead, silently or with a deprecation
  warning (`Submodular`'s private `Matroid.setOf_minimal_antichain` became
  mathlib's deprecated root alias). Use the public declaration, or rename the
  private one.

**Constraints:**
- A `module` file can only `import` (or `public import`) other `module`
  files — build error *"cannot import non-`module` X"*. Mathlib is
  ~98.6% converted. The holdout that kept
  `LinearRigidityMatroid.lean` non-`module`, `Matroid.Representation.Map`
  (`apnelson1/Matroid`), is itself a `module` since the `Matroid` pin `8ece630`,
  so that reason lapsed, and the file converted in Phase 41a's item P3 (see
  `../notes/Bump-v4.36.0-rc1.md`). Non-`module` files import `module` files
  freely, so a script or scratch file need not convert.
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

## Patching the `Matroid` dependency

⚠️ **As of the v4.34.0-rc1 bump (2026-08-20) the `Matroid` dependency is plain
upstream `apnelson1/Matroid`** (pinned by `lake-manifest.json` +
`lakefile.toml`, checked out at `.lake/packages/Matroid/`). The user's fork
`github.com/bryangingechen/Matroid` is **retired** — see
`notes/ToolchainBumps.md` *The `Matroid` fork is retired* for why, and
`lakefile.toml`'s require comment for the short version.

So the default answer to "can I patch the dependency?" is now **no**: there is
no fork to carry the patch, and a local edit under `.lake/packages/` would be
silently lost on the next checkout (git-pinned package traces are rev-keyed —
see TACTICS-QUIRKS § 48's note on why such an edit is not an honest gate).
Take the project-side route below. If a patch is genuinely unavoidable, raise
it with the user: the options are an upstream PR to `apnelson1/Matroid` or
re-standing-up a fork, and both are the user's call, not a mid-session one.

(All of this is distinct from the *local* vendored mirror under
`CombinatorialRigidity/Matroid/`, which is plain project source and freely
editable — see `../DESIGN.md` *Project history* → **Vendored provenance**.)

- **Prefer the project-side route first.** A new lemma in
  `CombinatorialRigidity/Matroid/` or a `Mathlib/<exact path>` mirror travels
  with the project and needs no cross-repo step. Reach into the fork only when
  the project-side route genuinely can't reach the internals you need. (Often
  it can: Phase 22's N4b looked like it needed a fork-side `cycleMatroid`-under-
  collapse lemma, but the vendored `cycleMatroid_contract` applied directly.)
- **Never bump the pin unprompted.** Changing `rev`/`inputRev` in
  `lake-manifest.json` / `lakefile.toml` is a dependency bump — a human
  decision, and gated by the same discipline as a toolchain bump (`CLAUDE.md`
  *Build discipline*, playbook in `notes/ToolchainBumps.md`).
- **Historical note (fork era, 2026-06 → 2026-08).** While the pin pointed at
  the user's fork, editing `.lake/packages/Matroid/` in *that* repo's own
  history was authorized, and the standing rule was to flag any pending fork
  edit in the commit summary + active `notes/PhaseN.md`, since a local-only
  fork edit does not travel with a `git push` of this repo until the pin is
  bumped. Retained for reading older phase notes; not a live workflow.
