# Toolchain + dependency bumps — running log and playbook

Durable log for Lean-toolchain / mathlib / `Matroid` bumps. Not a phase note:
bumps are maintenance and cut across whatever phase is active. Read this
**before** attempting a bump; the *Playbook* section is the how-to and the
*Scheduled cleanup* section is the standing debt queue.

Pointers: `CombinatorialRigidity/CLAUDE.md` *Build discipline* (the
never-`lake update` rule and its escape hatch) and *Automated mathlib bumps*
(the hopscotch workflow).

---

## Playbook — how to run a bump here

**The blocker to know about first.** `lake update` is denied by a PreToolUse
hook (`.claude/hooks/block-lake-update.sh`), added after an OOM incident. That
hook is right to exist, but it has no built-in escape hatch, so a *deliberate,
requested* bump needs one of:

1. **`scripts/bump-mathlib.sh <rev>`** — dry by default, `--apply` to write.
   Deterministic, reviewable in the diff, no hook bypass. This automates by
   script what the v4.34.0-rc1 bump did by hand:
   - Resolve `<rev>` (SHA, branch, or tag) against mathlib's GitHub API, then
     read mathlib's own `lake-manifest.json` and `lean-toolchain` at it.
   - Copy **its** transitive pins (`batteries`, `aesop`, `Qq`, `Cli`,
     `proofwidgets`, `importGraph`, `plausible`, `LeanSearchClient`) verbatim
     into ours — rev *and* `inputRev`.
   - Set our `mathlib` rev to the target, and `lean-toolchain` to mathlib's.
   - Non-mathlib deps (`Matroid`, `checkdecls`, and `loogle` which comes in
     transitively via `Matroid`) keep their own pins — it skips any package
     mathlib's manifest doesn't mention.
   - Warn if mathlib has grown a transitive dep we don't carry (that one needs
     a hand-edit; the script won't invent a `require`).
   - Then verify with `lake env lean --version`: it materializes every dep and
     fails loudly if the manifest is inconsistent with the lakefile.
2. **Human runs `lake update`** — `! lake update` in the Claude Code prompt, or
   a normal shell. Simplest when a human is present, and the only route that
   also re-resolves the non-mathlib deps.

**Copying mathlib's transitive pins is the whole trick, and it is what
hopscotch gets wrong** — see *The hopscotch false positive* below. Running
`scripts/bump-mathlib.sh` against the pin we already have is a cheap check that
the invariant still holds: it prints `already in sync` when it does, and names
the drifted packages when it doesn't.

### Environment: `LAKE_CACHE_DIR` is mandatory on this machine

Lean 4.34 routes build artifacts through a new Lake cache that defaults to
`<elan toolchain dir>/lake/cache`. On this machine that directory is not
writable by the agent harness (macOS returns `EPERM` even with the sandbox
disabled), and **Lake reports the failed cache write as a build failure**,
not a warning:

```
✖ [1145/1188] Building Matroid.ForMathlib.Data.Set.Subsingleton
error: failed to cache artifact: operation not permitted (error code: 1)
  file: <elan toolchain dir>/lake
```

The Lean code compiled fine in every one of those cases. The danger is that
the "failed" targets block their reverse-dependencies, so a build can look
like it covered the tree when it silently stopped: the first v4.34.0-rc1 build
compiled **36 of 122** of our modules and reported a correspondingly flattering
error count.

Fix: point `LAKE_CACHE_DIR` at a writable directory (the user cache dir
works) for every build — `LAKE_CACHE_DIR=<writable-dir> lake build`.
(`lake build --no-cache` does **not** help — it disables cache *downloads*,
not the local write. `LAKE_CACHE_DIR=""` disables the cache entirely.)

Sanity check after any build: `grep -c 'failed to cache artifact' <log>`
should be `0`, and the `Built` + `Replayed` `CombinatorialRigidity.` lines
together should account for all 122 files.

### Two verification traps

- ~~**Cached modules do not re-emit warnings.**~~ **Superseded — the cache
  replays them.** The trap as originally recorded (a warning count off an
  incremental build is a *delta*, not a total; the v4.34.0-rc1 bump's per-build
  figures read 337 → 389 → 543 while the real surface never changed) was
  observed *without* `LAKE_CACHE_DIR`. With it set, a cache hit prints
  `⚠ Replayed <module>` and re-emits that module's stored warnings, so a
  whole-tree count off a fully-cached build is honest — the 2026-08-20 cleanup
  session read 1441 warnings off a build that compiled nothing. No `touch`
  needed. (This cuts the other way too: the *first* v4.34.0-rc1 build's
  flattering error count above was a no-cache-dir build, and a build with no
  writable cache dir under-reports errors as well as warnings.)
- **`lake env lean <file>` does not apply the lakefile's `leanOptions`.** It is
  a ~10s-per-file iteration loop (vs minutes for a targeted `lake build`) and
  its *errors* are trustworthy, but it silently skips the whole mathlib style
  linter set — it reported clean on three lines that were over the
  100-character limit. Lint cleanliness is only established by `lake build`.

---

## Bump record: v4.30.0-rc2 → v4.34.0-rc1 (2026-08-20)

| | before | after |
|---|---|---|
| `lean-toolchain` | `v4.30.0-rc2` | `v4.34.0-rc1` |
| mathlib | `21b745fd` (2026-05-13) | `653c36f0` (2026-08-14) |
| `Matroid` | `bryangingechen` fork `cb3be62` | `apnelson1` `f44939f` |

mathlib is pinned to a master commit rather than the `v4.34.0-rc1` tag
(`de5ce8a9`, 2026-08-11) because `653c36f0` is the exact revision
`apnelson1/Matroid` HEAD is tested against — same Lean version, less risk in
the dependency. Both choices are defensible; if a future bump prefers the tag,
check the `Matroid` pin's own mathlib rev first.

### The `Matroid` fork is retired

The `bryangingechen/Matroid` fork carried two patches. They diverged in status:

- **`unifOn_rankPos_iff` simp drift** (Phase 13, `08d517f`) — **obsolete.**
  Upstream re-greened it independently with a different simp set.
- **`deleteVerts` notation precedence** (Phase 23g, `cb3be62`) — **still
  absent upstream.** `scoped notation:51 G:100 " - " S:100` is unchanged in
  `apnelson1/Matroid` HEAD, so the `-`-continuation parse poisoning of
  TACTICS-QUIRKS § 48 is live again in this repo.

The decision was to **retire the fork anyway** and pin bare upstream, because
the measured cost turned out to be small: the notation poisoning bites at
exactly **4 sites**, each with a cheap local workaround already documented in
§ 48 (one added paren; three `Nat.sub_add_cancel` rewrites). Retiring buys a
plain upstream pin with green CI and nothing to maintain or rebase.

Consequence to keep in mind: **§ 48's workarounds are load-bearing again.**
New `-`-then-`+` or chained-`-` arithmetic written in a file with a
`Graph`/`WList`-typed variable in scope will fail to parse, with the error
surfacing lines away from the cause.

Still worth doing eventually: propose the precedence fix upstream
(`notation:65`, operands left at 100 — widen only the *result* level, never the
operands; the 65/66 variant broke a coercion-sensitive rewrite). § 48 carries
the analysis to cite. That would let future code drop the workarounds.

### What actually broke, by root cause

~39 fixes across 28 files. Grouped, because the groups are what generalize:

| root cause | sites | fix shape |
|---|---|---|
| `simp`/`simpa` no longer unfolds `set`/`let`-bound locals | 13 | add the defining equation to the simp set |
| `convert … using N` / `simpa … using h` where plain `exact` works | 13 | delete the tactic |
| `Std.Symm` / `Std.Irrefl` structure fields | 6 | wrap the field body in `⟨…⟩` |
| simp not bridging coercion / beta / `Subtype.mk` gaps | 6 | explicit `congrArg Subtype.val`, `Function.comp_def` |
| `deleteVerts` notation poisoning (§ 48) | 4 | paren, or `Nat.sub_add_cancel` |
| `Finset.le_eq_subset` now a syntactic equality | 3 | drop the no-op `simp only` |
| misc simp-set drift | 5 | add the missing unfolding lemma |

A third, smaller pattern worth naming: **an explicit-proof simp lemma like
`if_pos rfl` can stop applying because simp normalizes the *condition* first.**
In `Relabel/ChainColumn.lean` the scrutinee `0 = 0` became `True` before
`if_pos rfl` could fire, so the fix was to drop `if_pos rfl` and list
`ite_true` instead. Worth remembering because the deprecation table also
renames `if_pos` → `ite_eq_left`, and blindly applying that rename here would
have kept a broken proof looking merely deprecated.

Two of these are worth internalizing as *rescue patterns*. They are **not yet
in `TACTICS-QUIRKS.md`** — transcribing them is scheduled (item 4b below):

1. **The zeta-delta change** (joint-largest with the `exact` group below, at
   13 sites each). Mathlib/Lean tightened simp's
   default unfolding of `set x := … with hx` and `let` bindings. Every `simp`
   that saw through such a binding now needs `hx` (or the local's name) passed
   explicitly. All 8 `GenericityDevice.lean` failures were a single
   `set F := … with hF`; adding `[hF]` fixed every one.
2. **Reach for `exact` before debugging a `convert`.** Thirteen sites were
   definitionally true all along; the tactic was performing matching that
   mathlib's unifier no longer does. `convert X using N` → `exact X` (or, in
   term mode, dropping a `by simpa … using` wrapper entirely) was the whole
   fix each time. The gaps `exact` closed for free included `Matrix.of`,
   `Matrix.row`, `LinearIndepOn` vs its unfolding, eta-expansion of a
   `∘`, and `(b :: rest)[s + 1]` vs `rest[s]`.

Notably **nothing was a mathematical break** — no statement changed truth
value, no proof needed a new idea, and `#print axioms` on the headline results
is unchanged.

### The hopscotch false positive (why 3 months accumulated)

`.github/workflows/hopscotch.yml` runs daily and had been reporting a
regression since **2026-05-15** (issue #2: *"Bumping mathlib to `0fb2045`
would break the build"*). It was never a code break. The log says:

```
Warning: your project pins different versions of some dependencies than Mathlib.
This will cause `lake exe cache get` to compute wrong hashes.
  batteries:  project: 5c57f3857ba8   mathlib: 48ff08a0e30a
error: mathlib: failed to fetch cache
```

`lake update mathlib` bumps **only** mathlib, leaving `batteries` (and the
rest) at the revisions mathlib *used to* want. `lake exe cache get` hashes
over the whole dependency set, so the hash misses, the cache fetch fails, and
mathlib would have to build from source — which the runner cannot do.

Every mathlib commit from `0fb2045` onward fails identically, so hopscotch
bisected to it and stopped. The project therefore sat at 2026-05-13 mathlib
for three months with no signal about *real* code compatibility.

**The fix is to sync the transitive pins, not to reorder the requires.** The
mathlib warning suggests putting `require mathlib` last; that is a red herring
for this failure. Evidence: the v4.34.0-rc1 bump left the require order
untouched (mathlib is still first) and only rewrote the transitive pins to
match mathlib's manifest — and the mismatch warning disappeared.

---

## Scheduled cleanup (next session)

All of the below is **mechanical and separable** from the bump itself: no
statement changes, no new proofs. Ordered by value.

### 0. `lake lint` — ✓ DONE (green; two linters, seven false positives, three cascade rounds)

**Landed 2026-08-20.** `lake lint` (batteries `runLinter`) had 64 errors. Two
corrections to how this section originally recorded them, both worth keeping
because both were wrong in a way a reader would have relied on:

- **It was two linters, not one.** 59 `unusedArguments` **plus 5
  `defsWithUnderscore`** — the second went unmentioned, so a reader planning
  the fix would have under-scoped it.
- **"The 32 lint-failing files and the 31 files this bump edited are *disjoint*
  — zero overlap" is false.** Eleven files are in both. The *conclusion*
  ("pre-existing code meeting a changed linter") survives, but only on the
  stronger check the claim should have made in the first place: per
  **declaration**, not per file. Of the 64 flagged declarations exactly **one**
  was edited by the bump — `trivialMotionFamily_linearIndependent`, whose
  `simpa` gained `trivialMotionFamily` (a zeta-delta fix). The other 63 were
  untouched. **Lesson: file-level overlap is the wrong granularity for a
  "not our edits" claim**; a file can be edited in one proof and carry a
  vestigial binder forty lines away.

#### `unusedArguments` (59 declarations, 65 binders)

Disposition, per user adjudication: **drop the binder**, then let the build
find the exceptions. `DESIGN.md`'s *Typeclass shape for finiteness on `V`*
resolution is **not** in conflict — see the amendment there; its rule is "state
at the weakest typeclass the *statement* uses", and dropping is that rule
applied, not a reversal of it. Prep worth reusing: all 65 binders were declared
**inline on their own declaration** (no `variable` block anywhere), so no
`omit [...] in` was needed.

**Seven turned out to be linter FALSE POSITIVES**, and this is the finding to
carry forward. `unusedArguments` reads the *proof term*; the project's standard
`haveI : Fintype X := Fintype.ofFinite X` bridge idiom needs `Finite X` to
**elaborate** but does not leave it in the term. So the linter reports a binder
the declaration cannot be stated without:

| declaration | binder |
|---|---|
| `Matrix.rank_ge_of_isUnit_mul_reindex_fromBlocks` | `[Finite p]` |
| `Graph.BodyBarFramework.finrank_realBlockPiSpanOn` | `[Finite α]` |
| `…BodyHingeFramework.le_finrank_span_rigidityRows_of_cut` | `[Finite β]` |
| `…BodyHingeFramework.le_finrank_span_rigidityRows_of_splice` | `[Finite β]` |
| `…BodyHingeFramework.exists_independent_panelRow_subfamily_of_le_finrank` | `[Finite α]` |
| `…Molecular.edgeRowSplit_corner_card` | `[Finite β]` |
| `SimpleGraph.trivialMotionFamily_linearIndependent` | `[Finite V]` |

Each keeps its binder under `@[nolint unusedArguments]` with a two-line comment
naming the bridge — precedence rule 2 in `CombinatorialRigidity/CLAUDE.md`
*Fix warnings at the source* (a construct semantically required but invisible
to the linter), and the same disposition the tree already used at 4 pre-existing
sites (`Framework.lean`'s `IsInfinitesimallyRigid`, `RigidityMatrix/Basic.lean`,
`BodyBar/Framework.lean`). `[_inst : …]` was the adjudicated fallback but reads
as *deliberately unused*, which is the wrong story for a false positive.

**`unusedArguments` CASCADES — iterate `lake lint` to a fixed point.** This is
the single most important thing to know before starting. Dropping a binder from
a lemma removes it from that lemma's proof term, which removes it from its
**callers'** proof terms too — so a caller whose only use of `Finite α` was
passing it down becomes newly unused. It took **three rounds** to converge here:
**64 → 9 → 2 → 0** errors. Budget for that, and do not read
the first report as the size of the job. The tell is unmistakable: round 2's
`Theorem55.lean` hits were exactly the four non-`_gen` callers of the four
`_gen` producers round 1 had just generalized, and round 3's two hits were
callers of round 2's `splitOff_reroute_packing`. Each round costs a full build
plus a `lake lint` (~10 and ~15 min here), so the cost is in the iteration, not
the edits.

**Screening heuristic for next time, and its limit.** Grepping each flagged
declaration's body for `Fintype.ofFinite` predicted **15** at-risk of 59 — a
useful pre-filter (every one of the seven was in it), but it over-predicts by 8, because the bridge often converts
a *different* type variable than the dropped one. It also cannot tell you which
8: `Fintype.ofFinite _` with an underscore hides the dependency
(`edgeRowSplit_corner_card` needs `Finite β` only to reach
`Finite {e // e ∈ E(G)}`). Cheapest reliable loop, once the tree is otherwise
green: drop everything, then `lake env lean <file>` on the at-risk files — its
errors are trustworthy and it is ~1 min/file against ~10 min for a full build.

Net across all three rounds: **63 declarations became strictly more general** (52 in round 1, 9 in round 2, 2 in round 3) (weaker hypotheses, and no
call site changed since instance arguments are inferred).

#### `defsWithUnderscore` (5 declarations)

Four renames and one deletion, the naming settled with the user:

- `typeI_iso_of_two_neighbors` → **`isoTypeIOfTwoNeighbors`**, and
  `typeII_iso_of_three_neighbors` → **`isoTypeIIOfThreeNeighbors`**. Leading
  with `iso` is what makes these work: the direct camelCase-ification gives
  `typeIIsoOfTwoNeighbors` and `typeIIIsoOfThreeNeighbors`, where `typeIIso` /
  `IIIso` is genuinely ambiguous against the sibling `typeI` / `typeII` defs.
  It also matches the file's existing `isoOfOptionSubtypeNe`. 23 occurrences,
  including prose back-ticks in ROADMAP / DESIGN / TACTICS-GOLF / five notes
  files — repointed in the same commit per the retirement rule.
- `Matroid.PartialTransversal.of_fun` → **`ofFun`** (19 sites: the def, its
  `@[simps]` projection lemma, and the hand-written `of_fun_*` family). Matches
  the upstream `Matroid.ofFun` the project already imports.
- `Matroid.N_singleton` → **`nbhd`**, *and its sibling `def N` deleted* — `N`
  had zero references anywhere in the tree or blueprint, was mentioned only in
  its own docstring, and was **shadowed** by a `set N := …` inside the one
  proof that docstring points at. Both vendored, so both are recorded in the
  file's Modifications note.
- `Matroid.instDecidablePredProdMatch_84PropMemFinsetOfDecidableEq` — **deleted
  outright, no rename needed.** It was an *anonymous* `instance` (the whole
  underscore, `Match_84` and all, is Lean's auto-generated name, not something
  an author wrote), and it existed only because `PartialTransversal.move`
  filtered with a **pattern** lambda `fun ⟨i, x⟩ ↦ x ∈ B i`, which elaborates
  to a `match` instance synthesis cannot see through. Its body was a no-op
  rewrap of `decidableMem`. Switching `move` to the **projection** lambda
  `fun e ↦ e.2 ∈ B e.1` — the form the very next lemma, `move_edges`, already
  states and proves by `rfl` — makes synthesis fire and the instance
  unnecessary. **General shape worth remembering: an "anonymous instance with a
  mangled name" is usually a signal that a nearby pattern lambda should be a
  projection lambda.**

### 1. Deprecation rename sweep — ✓ DONE (846 renames, 70 files)

**Landed 2026-08-20.** The bump commit deliberately left mathlib's deprecated
*aliases* in place; they still elaborated, so the build was green, but each use
emitted a warning and the project gate wants warning-clean builds. The sweep
took the tree from **920 deprecation warnings to 0** (total warnings 1441 →
approx. 515), and needed three things beyond running the script:

- **8 hand sites** the script correctly refused (below).
- **The 5 `le_eq_subset` sites**, which have no replacement name — dropped from
  their simp sets, since the linter separately reported each as an unused simp
  argument.
- **13 lines rewrapped.** `if_neg` → `ite_eq_right` is *six* characters longer,
  and `Set.diff_*` → `Set.sdiff_*` / `*setOf*` → `*ofPred*` one; thirteen lines
  crossed mathlib's 100-character limit. Worth expecting on any future
  rename sweep: the style linter, not the sweep, is what tells you.

A vetted sweep script lives at **`scripts/sweep-deprecations.py`**. It applies
only **pure renames** — every pair where mathlib emitted no *"the updated
constant has a different type"* note. Usage:
`python3 scripts/sweep-deprecations.py <build-log>` for a dry run, `--apply` to
write.

**It is driven by the build log's `file:line:col` positions, not by a regex over
the tree**, and that is a correctness point rather than a style one. Lean's
warning names the *fully qualified* old constant (`Set.mem_setOf_eq`) while its
position points at the identifier **as written**, which here is very often the
unqualified suffix under an `open Set` — for `Set.mem_setOf_eq` that was **all
154** sites. A regex on the qualified name would have silently swept none of
them; the boundary-regex design this section originally specced would have
reported success while leaving the largest single family untouched. Editing at
the reported position also removes the need for boundary heuristics
(`if_pos` inside `dif_pos` can't arise) and preserves the author's
qualification depth (`mem_setOf_eq` → `mem_ofPred_eq`, not the fully qualified
form).

Three renames are **excluded** because their types changed; how each resolved:

- `SimpleGraph.isClique_iff_induce_eq` → `SimpleGraph.induce_eq_top` (1 site) —
  the iff is *flipped* (`induce s G = ⊤ ↔ G.IsClique s`) **and** every argument
  became implicit, so `(isClique_iff_induce_eq G).mp h` became
  `induce_eq_top.mpr h`. A prose back-tick reference in the same docstring had
  to be repointed in the same commit (nothing gates a docstring reference).
- `cond_true`/`cond_false` → `Bool.cond_*` (6 sites) — the type change is
  argument *explicitness*, which is irrelevant to a **simp argument**, so all
  six were plain renames after all. Worth knowing: an explicitness-only change
  is safe wherever the name is used as a simp/rw lemma rather than applied.

Plus one **skip**, which is the interesting one: at `Henneberg.lean:445` the
deprecated name sat inside a `grind only [!a, !b, …]` list, and Lean reported
the warning at the position of the **`grind` token**, not the identifier (which
was on the next line). A position-driven sweep cannot fix that; it reported the
skip and the site was fixed by hand. Expect roughly one of these per sweep.

Two lemmas have no replacement at all and needed the simp *call* reconsidered:
`Finset.le_eq_subset` and `Set.le_eq_subset` are now syntactic equalities, so
`simp only [le_eq_subset]` is a no-op. Three sites were fixed in the bump; the
remaining **5** were dropped in the sweep commit (they were also reported by
`linter.unusedSimpArgs`, which is the reliable way to find them).

Highest-volume renames, measured (the figures this section carried before the
sweep — 34 / 30 / 36 / 20 / 16 — were **low by a factor of ~5**; they had come
from an early partial build, which is the "cached modules do not re-emit
warnings" trap the *Two verification traps* section above now records as
superseded):

| rename | sites |
|---|---|
| `if_neg` → `ite_eq_right` | 181 |
| `if_pos` → `ite_eq_left` | 167 |
| `Set.mem_setOf_eq` → `Set.mem_ofPred_eq` | 154 |
| `dif_pos` → `dite_eq_left` | 48 |
| `Set.diff_subset` → `Set.sdiff_subset` | 45 |
| `Set.ncard_diff_singleton_of_mem` → `…_sdiff_…` | 32 |
| `Set.mem_diff` → `Set.mem_sdiff` | 29 |
| `dif_neg` → `dite_eq_right` | 28 |

The rest of the `Set.diff_*` → `Set.sdiff_*` and `*setOf*` → `*ofPred*` families
are the long tail (≤ 14 each, 50-odd distinct pairs).

Those are **site** counts, cross-checked against the diff. Count sites, not
warning *lines*: one source position can be reported several times in a build
log (`if_true` shows 39 warning lines at 12 distinct positions), so a raw
`grep -c` over-counts. The script dedupes by `(file, line, col)`.

It **was** done as its own commit with a full build after, which is what caught
the 13 over-long lines. Nothing surfaced `simp made no progress`, the failure
mode this section had warned about.

### 2. `haveI`/`letI` style-linter sweep — 475 sites (468 `haveI`, 7 `letI`)

Mathlib's `linter.style.haveILetI` now fires on `haveI`/`letI` where the goal
is a `Prop`. Each hit is a `Try this:` suggestion with an exact line/column,
so this is scriptable off a full-build log rather than by hand. The linter
only fires where the change is safe (Prop goals), so it is a pure rename of
`haveI` → `have` / `letI` → `let` at the reported positions. (The "155+"
figure this section used to carry was another partial-build undercount — see
item 1's table.) The suggestion payload is literally the token with a
combining strikethrough on the `I`, so the edit is: delete one character at the
reported column + 5.

Do **not** blanket-sed `haveI` → `have`: the two differ for genuine instance
bindings, and only the flagged sites are known-safe.

### 3. Unused-simp-argument cleanup — ~15-20 sites

`linter.unusedSimpArgs` reports each with the exact suggested replacement
list. Mostly fallout from the same drift: a simp arg that used to be
load-bearing is now redundant (or is one of the syntactic-equality lemmas
above).

### 4. `flexible` linter polish in `Claim612.lean`

The bump's fix for `Fin.snoc`/`Fin.castPred` there ends a `simp` with a rigid
`rfl` / `exact one_ne_zero`, which `linter.flexible` flags. The edited sites
are currently warning-free, so this is latent rather than open — but if it
resurfaces, the linter emits the exact `simp only [...]` list to substitute.
Recorded because the underlying nuisance is real: `![0, 0, 0] (Fin.castPred 2 ⋯)`
does not reduce under simp any more, and neither `Fin.castPred` (max recursion)
nor `Fin.castPred_mk` (does not match an `OfNat` literal index) fixes it.

### 4b. Three general fixes deferred from the bump session — ✓ DONE

All three came out of diagnosing *this* bump and are what make the next one
cheap. Landed 2026-08-20.

1. ~~**`scripts/bump-mathlib.sh`**~~ — **done.** Resolves a rev (SHA / branch /
   tag) via mathlib's GitHub API, copies its transitive pins and
   `lean-toolchain` into ours, skips any package mathlib's manifest doesn't
   mention (so `Matroid`, `checkdecls`, `loogle` keep their pins), warns about a
   new mathlib transitive dep we don't carry, and is dry-run by default. Run
   against the pin we already have it prints `already in sync`, which is how the
   bump commit's invariant is now checkable in one command. *Playbook* above is
   rewritten around it.
2. ~~**`scripts/sweep-deprecations.py`**~~ — **done**, and *not* the specced
   regex: see item 1 for why the log-position design is the correct one and
   what the regex would have missed.
3. ~~**A `lake update` escape hatch**~~ — **done**, in
   `CombinatorialRigidity/CLAUDE.md` *Build discipline*, on the
   never-`lake update` bullet itself (both routes, script first). That section
   also gained the **`LAKE_CACHE_DIR` mandate**, which had been recorded only
   here — an operational requirement that belongs in the file every
   Lean-touching session auto-loads.

**Still open:** the two `TACTICS-QUIRKS.md` rescue entries the *What actually
broke* section above says are "written up" — the **zeta-delta / `set`-binding**
entry and the **reach-for-`exact`-before-`convert`** entry. Both are described
in full there; they need transcribing into the symptom-indexed format with a
section number.

### 5. Unstick hopscotch — the highest-leverage item

Without this, the next bump is another multi-version jump. Options, cheapest
first:

- Add a workflow step that runs a **full** `lake update` (or the pin-sync in
  the *Playbook* above) after hopscotch rewrites the mathlib pin, so the
  transitive pins never go stale.
- Report the single-package-update behaviour upstream to
  `leanprover-community/hopscotch-action` — the diagnosis above is precise
  enough to file as-is.
- Failing both, bump manually on a cadence (weekly) using the *Playbook*;
  one-commit bumps are vastly cheaper to debug than four-version jumps.

Also worth closing out: issue #2 and PR #1 in this repo are both stale
artifacts of the false positive and should be closed/superseded once the
bump lands.

### 6. Optional: audit the remaining `convert` sites

25 `convert … using N` plus 7 bare `convert` remain; 3 of them broke on this
jump (~10%). Not worth a speculative sweep — but if a future bump breaks
several again, converting the survivors to `exact`/`simpa only` where they are
definitionally true would reduce the recurring cost. Note the diagnostic:
`convert` failing with leftover *instance-path* goals (`Real.instRing.toSemiring
= Real.semiring`) is the tell that the statement is defeq and `exact` will work.
