# Perf pass (post-Phase-22j) — `CaseI.lean` file split (work log)

**Status:** in progress (opened 2026-06-15 at the 22j close; the agreed pre-22k internal step).
**Round type:** structural-edit perf pass (file split), driven like a `coordinate-phase` loop — one
file carved off per slice, build-verified between. **No new math, no decl renamed.**

## Current state

**Next: P2 — carve `CaseIII.lean`** (Claim 6.11 + Case III). **P1 landed** — the
`Theorem55.lean` tail block (base producers + cut-edge + dispatch) is carved into its own file
importing the monolith; the aggregator now imports `…AlgebraicInduction.Theorem55` (drop the
`…CaseI` line). CaseI shrank 10,366 → 8,504 lines; the new chain head is `…CaseI ← Theorem55`. Build
+ lint warning-clean, the moved producers axiom-clean (`propext, Classical.choice, Quot.sound`), all
50 blueprint name-only pins unaffected. The round splits `Molecular/AlgebraicInduction/CaseI.lean`
into a 5-file `AlgebraicInduction/` chain. The ranked plan — target files, the verified intra-file
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

- [x] **P1 — carve `Theorem55.lean`** (the tail block: base producers + cut-edge + dispatch) into a new
  file importing the monolith; aggregator imports `…Theorem55`. Build + lint warning-clean. **Done** —
  cut at CaseI's old :8503/:8504 (after `case_III_realization`, before `theorem_55_base_producer_parallel_pair`);
  1862 decl-lines moved verbatim (head→tail, `case_III_realization` is the last head decl);
  Theorem55 = 1899 LoC, CaseI now 8504. Axiom-clean, lint-clean, 50 pins intact.
- [ ] **P2 — carve `CaseIII.lean`** (Claim 6.11 + Case III); rewire `Theorem55` to import it. Build.
- [ ] **P3 — carve `CaseII.lean`** (the L6b producer block); rewire `CaseIII` to import it. Build.
- [ ] **P4 — split the head**: carve `Coupling.lean` (foundations) off the monolith, leaving the
  trimmed `CaseI.lean` (Case I + rank-poly) importing it. Build. (Confirms the final 5-file chain.)

Each slice: pure semantics-preserving move + per-file boilerplate (`namespace` / `variable {k}` /
`open scoped Graph` / `variable {α β}` — cf. the F1 `SparsityIComponents` `variable {V}` gotcha,
`notes/PERFORMANCE.md`); gate = `lake build` + `lake lint` **warning-clean** + axiom-clean on the
touched modules. The new files inherit **non-`module`** status (the molecular chain is non-`module`,
PERFORMANCE.md *Module system*). A slice may be split finer if a single carve is too large for one
sitting. **No special notation/cast boilerplate is needed** — the import-poison blocker was
root-caused and fixed in the monolith (see *Blockers*); standard `open scoped Graph` is transparent.

## Blockers / open questions

- **Rename-free is load-bearing.** No decl moves namespace or changes name, so all **50** blueprint
  `\lean{…}` pins into `CaseI.lean`'s decls stay valid by name and `checkdecls` is unaffected (recon-
  verified; the pre-Phase-22b structure pass established exactly this). If any slice is tempted to
  rename/re-namespace a decl, STOP — that breaks the pin and is out of scope for a pure file split.
- **First-dispatch shape.** The first slice may warrant a short read-only design-settle confirming the
  exact cut lines + the slicing order against the *current* file before the first carve (the recon's
  cut map is at the block level; line numbers shifted). The coordinator decides per the
  `coordinate-phase` step-1 research-shape trigger.
- **Import-poison blocker — ROOT-CAUSED and FIXED in the monolith (2026-06-15).** Both reported
  poisons (notation: a downstream `import CaseI` file could not parse `V(`/`E(`/`↾`; and `binop%`:
  bare-ℕ `screwDim k - 1` in a ℤ context elaborated as `Int.subNatNat` not `↑(screwDim k - 1)`, so the
  4 cut-edge `hbrickZ` `exact_mod_cast`s failed) share **one** cause and **one** fix. The cause: the
  lemma at `CaseI.lean:1909` was declared `theorem Graph.rigidContract_vertexSet_inter_eq_singleton`
  **inside** `namespace CombinatorialRigidity.Molecular`, so its bare `Graph.` prefix made it land in
  a *sub-namespace* `CombinatorialRigidity.Molecular.Graph` (verified: `#check
  @CombinatorialRigidity.Molecular.Graph.rigidContract_…` resolved). A downstream `namespace
  CombinatorialRigidity.Molecular` + `open scoped Graph` then resolves `Graph` to that **nearest**
  sub-namespace, so mathlib's *root*-`Graph` scoped notations (`V(`/`E(`/`↾`/the `-` deleteVerts infix)
  never activate — which both leaves only the Matroid *global* two-arg `V(G, e)` (parse failure) and
  changes the `-`-notation environment that drives `binop%`'s leaf-coercion (cast flip). The monolith
  escaped both because its file-head `open scoped Graph` ran *before* this decl created the sub-namespace.
  `open CombinatorialRigidity.Molecular` (vs `namespace …`) sidesteps it; `open scoped _root_.Graph`
  forces the root scope — both confirm the diagnosis. **Fix (landed):** pin the decl to
  `_root_.Graph.rigidContract_vertexSet_inter_eq_singleton` (its rightful project-`Graph`-API home,
  matching every sibling `Graph.foo` rigidity lemma). It has no blueprint pin and is referenced only
  inside `CaseI` by the relative name `Graph.rigidContract_…` (now resolving to root `Graph`); no
  external caller — self-contained. Scratch-verified: a downstream `namespace … Molecular` +
  **standard** `open scoped Graph` file now parses `V(`/`E(`/`↾` and elaborates the cut-edge
  `exact_mod_cast`s, with no `local notation`/`_root_` per-file boilerplate. Monolith + full library
  build warning-clean, lint-clean, axiom-clean (the cut-edge producers `#print axioms` show only
  `propext, Classical.choice, Quot.sound`). The split is again a guaranteed pure semantics-preserving
  move. See TACTICS-QUIRKS § 56 + FRICTION [resolved] *Bare `Graph.`-prefix in the `Molecular` namespace*.

## Hand-off / next phase

**P1 landed (2026-06-15).** `Theorem55.lean` carved off; aggregator rewired; build/lint/axioms clean
(detail in *Current state* + the P1 checklist item). The import-poison that stalled three P1 attempts
stays fixed and transparent — slice boilerplate is just `namespace`/`variable`/`open scoped Graph`
(no `local notation` / `_root_`); mechanism in *Blockers*.

**Next concrete commit: P2 — carve `CaseIII.lean`** (the Claim 6.11 + Case III block: from the head of
the trimmed `CaseI.lean`, the `case_III_*` / `caseIIICandidate` / Claim-6.11 decls down to and
including `case_III_realization`, currently CaseI's last decl ending at :8502). New file imports the
monolith (`…CaseI`); rewire `Theorem55` to import `…CaseIII` instead of `…CaseI`; re-derive the cut
line against the current file. Watch the forward edge `case_III_*` → `case_II_placement_eq612` (a
Case-II decl earlier in CaseI), which keeps CaseIII importing the monolith. Gate: `lake build` +
`lake lint` warning-clean + axiom-clean. Then P3→P4 per the *Layer plan*. Full target + DAG + cut map
+ leverage: `notes/PERFORMANCE.md` *Molecular `CaseI.lean` perf recon* plan (B).

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
