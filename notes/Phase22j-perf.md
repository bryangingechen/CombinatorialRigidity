# Perf pass (post-Phase-22j) — `CaseI.lean` file split (work log)

**Status:** in progress (opened 2026-06-15 at the 22j close; the agreed pre-22k internal step).
**Round type:** structural-edit perf pass (file split), driven like a `coordinate-phase` loop — one
file carved off per slice, build-verified between. **No new math, no decl renamed.**

## Current state

**Next: a structural-edit round splitting `Molecular/AlgebraicInduction/CaseI.lean` (10,346 lines) into a
5-file `AlgebraicInduction/` chain.** The ranked plan — target files, the verified intra-file
dependency DAG, the cut-line map, the leverage analysis, and the rename-free / blueprint-pin-safe
argument — is the **canonical** recon output in `notes/PERFORMANCE.md` *Molecular `CaseI.lean` perf
recon (2026-06-15)* plan (B). This log carries only the slice state + hand-off; do not duplicate the
plan.

Why this round: `CaseI.lean` is 6.9× the ~1500-line soft cap and is the *active* realization-layer file
(every per-edit incremental rebuild churns 10k lines of unrelated KT cases), so factor-2/3/4 leverage is
the strongest in the project's history. Factor-1 (downstream-import) benefit is **nil** — it's the
terminal leaf of the `AlgebraicInduction/` chain — so the win is build-incrementality + navigability,
not transitive-import surface. 22j's A0–A2 already shrank the L6b producer's budget (3.2M→600000) and
dropped its longLine suppression, de-risking the producer's move.

## Target (canonical: `notes/PERFORMANCE.md` plan B)

Replace the one file with a linear chain matching the verified DAG (foundations → Case I → Case II →
Case III → base producers/dispatch); import chain `GenericityDevice ← Coupling ← CaseI ← CaseII ←
CaseIII ← Theorem55`, top-level aggregator imports `…Theorem55` (drop the `…CaseI` import line):

| New file | ~LoC | block |
|---|---|---|
| `AlgebraicInduction/Coupling.lean` | ~1300 | foundations (coupling + `extProj`) |
| `AlgebraicInduction/CaseI.lean` | ~2150 | Case I + rank-polynomial suite |
| `AlgebraicInduction/CaseII.lean` | ~1150 | Case II (the L6b producer) |
| `AlgebraicInduction/CaseIII.lean` | ~3850 | Claim 6.11 + Case III (still ~2.5× cap — sub-split a later round) |
| `AlgebraicInduction/Theorem55.lean` | ~1850 | base producers + cut-edge + dispatch |

The cut-line *line numbers* in the recon predate 22j's A0/A1/A2 (the producer shifted) — **re-derive
the exact cut points against the current file**, not the recon's numbers.

## Layer plan / slices (structural-edit; build-verify each)

Recommended slicing — **carve dependency-latest blocks first**, so each new file imports the *shrinking*
monolith and every intermediate state builds (the monolith keeps the name `CaseI.lean` until the final
slice, when its head splits into `Coupling.lean` + the trimmed `CaseI.lean`):

- [ ] **P1 — carve `Theorem55.lean`** (the tail block: base producers + cut-edge + dispatch) into a new
  file importing the monolith; aggregator imports `…Theorem55`. Build + lint warning-clean.
- [ ] **P2 — carve `CaseIII.lean`** (Claim 6.11 + Case III); rewire `Theorem55` to import it. Build.
- [ ] **P3 — carve `CaseII.lean`** (the L6b producer block); rewire `CaseIII` to import it. Build.
- [ ] **P4 — split the head**: carve `Coupling.lean` (foundations) off the monolith, leaving the
  trimmed `CaseI.lean` (Case I + rank-poly) importing it. Build. (Confirms the final 5-file chain.)

Each slice: pure semantics-preserving move + per-file boilerplate (`namespace` / `variable {k}` /
`open scoped Graph` / `variable {α β}` — cf. the F1 `SparsityIComponents` `variable {V}` gotcha,
`notes/PERFORMANCE.md` — **plus the three `local` notation re-assertions** for any file importing a
poisoned `CaseI`-or-later file, see *Blockers* "Notation-poison blocker"); gate = `lake build` +
`lake lint` **warning-clean** + axiom-clean on the touched modules. The new files inherit **non-`module`** status (the molecular chain is non-`module`,
PERFORMANCE.md *Module system*). A slice may be split finer if a single carve is too large for one
sitting.

## Blockers / open questions

- **Rename-free is load-bearing.** No decl moves namespace or changes name, so all **50** blueprint
  `\lean{…}` pins into `CaseI.lean`'s decls stay valid by name and `checkdecls` is unaffected (recon-
  verified; the pre-Phase-22b structure pass established exactly this). If any slice is tempted to
  rename/re-namespace a decl, STOP — that breaks the pin and is out of scope for a pure file split.
- **First-dispatch shape.** The first slice may warrant a short read-only design-settle confirming the
  exact cut lines + the slicing order against the *current* file before the first carve (the recon's
  cut map is at the block level; line numbers shifted). The coordinator decides per the
  `coordinate-phase` step-1 research-shape trigger.
- **Notation-poison blocker — REAL; proven per-file fix (2026-06-15).** A new file that `import`s
  `CaseI` (or any later file in the chain that does) cannot parse the `V(`/`E(`/`↾` notations: a
  **body decl inside `CaseI`** serializes an olean parser-priority effect that lets the
  `apnelson1/Matroid` package's *global* two-arg `V(" G ", " e ")"` / `E(" G ", " e ")"` and *scoped*
  `↾` (`Graph.restrict`) win over mathlib's *scoped* one-arg `V(`/`E(`. `import CaseI` + `open scoped
  Graph` → `V(G)` fails with `unexpected token ')'; expected ','`; `import GenericityDevice` + the same
  preamble parses fine, and `CaseI`'s 4 imports with an **empty body** parse fine — so it is a body
  decl, not the imports. (An earlier coordinator "probe-artifact" dismissal was wrong: a `tail -30`
  truncation had hidden the parse error; full-output re-test confirms it. The dispatch-1 `binop%`/cast
  claim was a confounded cascade off the parse failure, not a separate issue — once the notation parses,
  `(screwDim k - 1)` elaborates correctly.) **Proven fix (coordinator scratch-build-verified):** each
  carved file that imports a poisoned file adds, right after `open scoped Graph`:
  ```
  local notation "V(" G ")" => Graph.vertexSet G
  local notation "E(" G ")" => Graph.edgeSet G
  local infixl:65 " ↾ " => Graph.restrict
  ```
  These re-assert the intended one-arg/graph notations verbatim from their source `=>` RHS; they are
  **pin-safe** (no decl renamed/re-namespaced), elaborate identically to the scoped originals, and are
  per-file boilerplate (same category as `open scoped Graph`). If any *other* shadowed notation
  surfaces in a slice, re-assert it the same way from its source definition. The trimmed `CaseI` head
  imports `GenericityDevice` (clean) → it needs no re-assertion; only files importing `CaseI`-or-later do.
- **SECOND poison — `binop%` coercion (NOT per-file-fixable); breaks the "pure move" premise
  (2026-06-15).** After the notation fix, the carved `Theorem55` still fails: `import CaseI` also flips
  `binop%`'s leaf-coercion decision, so bare-ℕ `(screwDim k - 1)` inside a ℤ context elaborates as
  ℤ-subtraction (`Int.subNatNat`) instead of the ℕ-sub-then-cast (`↑(screwDim k - 1)`) the monolith
  produces — so the 4 cut-edge `hbrickZ` `have` statements (`case_cut_edge_realization{,_gp}`) fail their
  `exact_mod_cast hbrick`. Confirmed via `lean_run_code` on the **unmodified** tree (the snippet succeeds
  under `import GenericityDevice` and even under all 4 of CaseI's imports together, fails under `import
  CaseI`) — same CaseI-body-decl mechanism, but the elaboration-state does **not** transfer through the
  import, and there is no `local`-style per-file fix (unlike the notation poison). CaseI has **no**
  `instance`/`Coe`/`OfNat`/`default_instance`/`notation`/`macro` construct (only one `@[simp]`), so the
  mechanism is opaque. Only the bare `(screwDim k - 1)` pattern is at risk; the many `screwDim k * ((… :
  ℤ) - 1)` sites have explicit ℤ ascriptions and are safe. **This means importing CaseI is not
  semantics-transparent — the split cannot be the guaranteed pure pin-safe move it was scoped as.**
  Surfaced to the user as a strategic fork (2026-06-15): (a) allow minimal cast-ascription proof-body
  touch-ups at affected sites; (c) root-cause-investigate/neutralize the poison decl first; (d) defer the
  split (its only leverage is build-incrementality — import-surface benefit is nil — and 22k is the math
  frontier). Awaiting the user's call before any further P1 dispatch.

## Hand-off / next phase

**BLOCKED pending a user decision (2026-06-15).** P1 (carve `Theorem55.lean`) was attempted three times;
the carve mechanics are clean (cut line re-derived, zero backward edges, trimmed `CaseI` builds), but
`import CaseI` poisons downstream elaboration in two ways — notation (fixed per-file) and `binop%`
coercion (NOT per-file-fixable) — so the split is **not** the guaranteed pure semantics-preserving
move it was scoped as. See *Blockers* "SECOND poison" for the strategic fork (a/c/d) surfaced to the
user. **Do not re-dispatch P1 until that fork is resolved.**

Once resolved, the original plan: **P1 — carve `Theorem55.lean`** (the base-producer + cut-edge +
dispatch tail of `CaseI.lean`) into a new file importing the monolith (with the 3 `local` notation
re-assertions per *Blockers*), point the aggregator (`CombinatorialRigidity.lean`) at
`…AlgebraicInduction.Theorem55` instead of `…AlgebraicInduction.CaseI`, re-derive the cut line. Gate:
`lake build` + `lake lint` warning-clean + axiom-clean. Then P2→P3→P4 per the *Layer plan*. The full target + DAG + cut map + leverage is in
`notes/PERFORMANCE.md` *Molecular `CaseI.lean` perf recon* plan (B).

After this round closes: open **Phase 22k** (completing the honest all-`k` Theorem 5.5 — Case III +
the zero-carry spine; the L7–L10 layer plan in `notes/Phase22i.md` *Hand-off*, consuming Brick A), then
Phase 23 (general `d`). The other ranked split candidates (recon plan C — `RigidityMatrix.lean` 3380 with
a possible downstream-import benefit; `ForestSurgery.lean` 3783 in the stable Induction subtree; the
three other `CaseI` raised budgets) are **assessed, not scheduled** — surface them to the user as a
possible later round, not part of this one.

### coordinate-phase note (`coordinate-phase 22j-perf` or similar)

Scaffolded by the 22j coordinator at the 22j close (2026-06-15, user-approved option a). Drive this
round one slice at a time per the *Layer plan*; each slice is a structural-edit build dispatch (file
move + import rewire + per-file boilerplate; gate = build/lint warning-clean + axiom-clean; **no
`verify.sh`** unless a `\lean{}` pin moves — and it must not, the split is rename-free). The
model-experiment is **running**; re-run the session-start availability check and record any
substitution/override in `notes/model-experiment.md` before the first dispatch. Rate each slice S/P/B
(a file carve is typically S=1/P=1/B=2 — bounded import rewire — → sonnet per the map, absent an
override).
