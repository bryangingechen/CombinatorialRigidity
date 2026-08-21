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

**Copying mathlib's transitive pins is the whole trick** — and since
2026-08-21 `lake update mathlib` does it *for us*, because `require mathlib` now
sits **last** in `lakefile.toml` (see *The hopscotch false positive* below; that
ordering is load-bearing and the require carries a comment saying so). The
script remains the deterministic route to a *specific* rev without a full
re-resolve. Running
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

**Root cause: our own `require` order — not hopscotch, and not `lake`.**
`lake update mathlib` re-resolves mathlib's transitive deps *by design*:
`reuseManifest` re-pins an old entry only `unless entry.inherited ||
toUpdate.contains entry.name`, and every transitive entry in our manifest is
`inherited=true`. It then runs `addDependencyEntries` on each materialized dep,
adopting that dep's **own** `lake-manifest.json` pins — but only for names *not
already stored*. **First writer wins.** And Lake visits a package's requires in
**reverse** order (`Lake/Load/Resolve.lean`: *"later requires should shadow
earlier definitions"*), so `require mathlib` sitting **first** meant it was read
**last**: `Matroid` — pinned to a fixed rev, hence carrying a frozen manifest —
planted `batteries`/`proofwidgets` first and mathlib's own pins were silently
dropped. `lake exe cache get` then hashes over a dependency set mathlib never
tested, the hash misses, the cache fetch fails, and mathlib would have to build
from source — which the runner cannot do.

Every mathlib commit from `0fb2045` onward fails identically, so hopscotch
bisected to it and stopped. The project therefore sat at 2026-05-13 mathlib
for three months with no signal about *real* code compatibility.

**The fix is to move `require mathlib` LAST — mathlib's own warning was
right all along.** This section previously asserted the opposite ("sync the
transitive pins, not the require order; the warning's advice is a red herring"),
on the evidence that the v4.34.0-rc1 bump left the order untouched and the
mismatch warning still disappeared. That evidence is **confounded**:
`bump-mathlib.sh` had already hand-synced every pin, so all sources agreed and
order stopped mattering. It never tested order.

**Measured both ways (2026-08-21).** Two copy-on-write clones of the post-bump
tree, identical but for the position of the mathlib require, each running
`MATHLIB_NO_CACHE_ON_UPDATE=1 lake update mathlib` against mathlib `51458cb7`
(chosen because it carries our toolchain, so no elan restart, and moves two
packages):

| package | mathlib require FIRST | mathlib require LAST | mathlib@`51458cb7` pins |
|---|---|---|---|
| `batteries` | `f207b55c` (stale) | **`36cc05ca`** | `36cc05ca` |
| `proofwidgets` | `99e8adee` (stale) | **`ebeca04e`** | `ebeca04e` |

Every other package identical in both arms, and `Matroid` / `checkdecls` /
`loogle` kept their own pins either way — a selective update does not disturb
them. So the reorder makes every `lake update mathlib` (ours, a human's, or
hopscotch's) adopt mathlib's tested pins, and the drift cannot form.

**Reproduction recipe, worth keeping.** `MATHLIB_NO_CACHE_ON_UPDATE=1` is the
guard in mathlib's `post_update` hook that skips `lake exe cache get`, so a
probe costs a `git fetch` instead of a multi-GB olean download — and the
manifest is still written either way (Lake's `writeManifest` runs *before* the
hooks), which is the only thing the test needs to read. Clone the tree with
`cp -Rc` (APFS copy-on-write: instant, no disk cost) so the verified working
tree is never at risk.

---

## Scheduled cleanup

**State of play (2026-08-21).** Items 0, 1, 2, 3, 4, 4a, 4b, 4c **and 5** are
**DONE**; both gates are **green** (`lake build` 2948 jobs, 0 errors; `lake lint`
"Linting passed"), and warnings are **1441 → 0**. Item 5 (unstick hopscotch) was
**not** the multi-option strategy call this note had it queued as: the root cause
was our own `require` order, and it closed with a one-line `lakefile.toml`
reorder — measured both ways, see *The hopscotch false positive*. Item 6 is
optional and untouched.

**All three of the last-five warning sites resisted the fix this note predicted
for them, and in each case the cheaper route was the right one.** Worth reading
before scoping the next bump's cleanup, because the miss has one shape: each
prediction was scoped off the *linter's report* rather than off the mechanism
producing it, so it over-sized the job (twice) and reached for a new mirror
lemma the tree did not need (once).

| site | predicted here | what actually worked |
|---|---|---|
| 1 × `linter.flexible`, `Claim612.lean` (item 4) | a mirror lemma for `![a,b,c] (Fin.castPred 2 ⋯)` under `CombinatorialRigidity/Mathlib/`; "four other routes tried and dead" | **one more simp argument** — `Fin.castLT` — on the existing call. No new lemma, and it retired three sibling bullets' trailing `rfl`s too |
| 1 × overlapping instances, `Search/DFS.lean` (item 4c) | drop the `variable`-line instances, re-add them inline on "the ~4 downstream `_sound`/`_complete` lemmas" (really **11** declarations) | **move the `variable` line to *below* the one def that carries inline binders** — two lines, zero signature changes anywhere |
| 3 × overlapping instances, `Induction/Operations.lean` (item 4c) | `section`-scope the `omit`/re-`variable` dance, then "re-derive which of the four `omit … in` clauses are still needed" | the `section` scoping, as predicted — and the four `omit … in` clauses needed **no** change at all |

**Where this stands (2026-08-21).** The 10-commit stack is **merged into local
`master`** (fast-forward from `bump/lean-4.34.0-rc1`, which still exists as a
ref) and is **still unpushed**: `origin/master` sits at `0920772` (Phase-38
close, 2026-07-23), leaving local master **281 commits ahead**. So **CI has
still never validated this stack** — and note the consequence for item 5: the
hopscotch workflow runs against `origin/master`, i.e. the *pre-fix* lakefile, so
it will keep re-stamping issue #2 until master is pushed. Both gates are
verified locally
*after* the require-order reorder (`lake build` 2948 jobs — the same job count as
the pre-reorder run — 0 errors, 0 warnings, 0 cache failures; `lake lint`
"Linting passed"), as are the two bump-specific checks: all 17
`formalization.yaml` headline declarations at
`[propext, Classical.choice, Quot.sound]` with no `sorryAx`, and all 11
`PebbleGame/Examples.lean` `#eval`s reproducing their documented values (the
2026-08-20 run; nothing since has touched an `#eval` or a headline declaration's
axioms — the reorder changed no Lean source and left `lake-manifest.json`
byte-identical, since our pins were already synced).

**Next concrete task: get CI onto this stack, then push `master`.** Nothing in
the queue blocks it — everything mechanical is done and item 5 closed with the
reorder. Two routes, and the ordering is a real choice rather than a formality:

- **CI first (safer).** Push `bump/lean-4.34.0-rc1` and open a PR against
  `master`; PRs build + lint but **skip** the Pages deploy. The diff is large
  (281 commits, since `origin/master` is at Phase-38 close) but the point is the
  build, not the review.
- **Push `master` directly.** Simplest, and the local gates are green — but
  every green `master` push **publishes** (blueprint, docs, upstreaming
  dashboard via `docgen-action`). There is no "deploy later" knob, so this is
  the first CI run *and* the deploy in one step.

Then the post-merge tidying: close issue #2 / PR #1 (both stale false-positive
artifacts), and the optional upstream report the user is still weighing
(item 5).

All of the below is **mechanical and separable** from the bump itself: no new
proofs, and the only statement changes are item 0's 63 declarations, all in the
*generalizing* direction (dropped unused hypotheses). Item 4c's scoping fixes
changed **no** signature at all — verified by `#check` on both sides.
Ordered by value.

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

### 2. `haveI`/`letI` style-linter sweep — ✓ DONE (475 sites: 468 `haveI`, 7 `letI`)

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

**Landed 2026-08-20**, position-driven off the build log exactly like the
deprecation sweep (same reason: the reported column is authoritative and a
whole-tree text match is not). Zero skips, zero errors, and warnings fell
**515 → 40**. Two things worth knowing next time: the seven `letI` hits become
*anonymous* `let : DecidableEq α := Classical.decEq α`, which is fine — the
`haveI`/`letI` vs `have`/`let` difference is value *inlining*, not instance
visibility, and a local binder of class type is an instance candidate either
way; and `haveI` → `have` only shortens lines, so unlike the rename sweep it
cannot push anything past the 100-character limit.

### 3. Unused-simp-argument cleanup — ✓ DONE (folded into item 2's sweep)

`linter.unusedSimpArgs` reports each with the exact suggested replacement
list. Mostly fallout from the same drift: a simp arg that used to be
load-bearing is now redundant (or is one of the syntactic-equality lemmas
above).

### 4. `flexible` linter in `Claim612.lean` — ✓ DONE (one simp argument; it was never a mirror-lemma job)

**Landed 2026-08-21**, by adding **`Fin.castLT` to the existing simp set** —
attempt 5 below. The four attempts before it are kept because each looks like it
should work, and because attempt 3's conclusion ("the existing proof is right,
surface rather than silence") was the wrong call: it diagnosed the *residual*
correctly and then stopped, instead of asking why `simp` produced a residual at
all.

One warning, the tree's last. This section previously called the site "latent
rather than open" because "the edited sites are currently warning-free". **That
was wrong — it fires.** Three attempts, all recorded because each looks like it
should work:

1. **Substitute the linter's suggested `simp only [...]`.** It *makes no
   progress at all* — `lean_goal` shows all three goals of the `<;>` unchanged,
   because the suggested list omits `homogenize`, `Fin.snoc`, `dotProduct`,
   `Fin.sum_univ_succ`, the very lemmas doing the work. **Diagnosis worth
   keeping: `simp?`'s suggestion was captured against a different branch than
   the `<;>` produces**, so `refine ⟨?_, ?_, ?_⟩ <;> simp` is exactly where the
   flexible linter's advice is least trustworthy.
2. **`simp only` with the original argument list**, or `norm_num`. Leaves the
   residual goal unclosed.
3. **Fold the closer into the simp set** (`simp [..., one_ne_zero]`). `simp`
   leaves `¬![0, 0, 1] (Fin.castPred 2 ⋯) = 0` — the documented non-reduction —
   so `one_ne_zero` never fires and is itself then reported unused.

4. **Just add `only`** (same argument list — `simp only` is not a flexible
   tactic, so this would be a one-word fix). Dead: under `simp only` that list
   unfolds into a `dite`/`Fin.succ`/`cast` thicket
   (`if h : ↑(Fin.succ 0).succ < 3 then cast ⋯ … else cast ⋯ 1`, and an unexpanded
   `∑ i, …`). **Only the *default* simp set reaches the tidy residual**, which is
   precisely why the tactic here is flexible and why it cannot simply be pinned.

**The reading attempt 3 produced — and why it was wrong.** `exact one_ne_zero`
does close that residual **by defeq** (`![0,0,1] (Fin.castPred 2 ⋯)` is defeq to
`1`) where the simp sets tried so far do not reduce it syntactically, and that
looked like the *reach for `exact`* pattern (TACTICS-QUIRKS § 106) rather than a
defect — so the site was **surfaced rather than silenced** per
`CombinatorialRigidity/CLAUDE.md` precedence rule 3. Every clause of that is
still true except the conclusion: § 106 is about goals that are *irreducible*,
and this one was merely **one unfolding short**. The question the analysis never
asked is *why* `simp` stopped where it did.

5. **Add `Fin.castLT` to the *existing* simp set** — **this is the fix.**
   `simp [homogenize, Fin.snoc, dotProduct, Fin.sum_univ_succ, Fin.castLT]`
   closes all three conjuncts, so the rigid `exact one_ne_zero` disappears and
   the flexible warning goes with it, at the source and with no new lemma.

**Why it works, and why attempts 1–4 all missed it.** The residual
`¬![0, 0, 1] (Fin.castPred 2 ⋯) = 0` is not an *irreducible* goal — it is a goal
whose index is stuck one unfolding short of a `Fin.mk` literal. `simp` normalizes
`homogenize`'s `Fin.snoc` index to `Fin.castPred 2 ⋯`; unfolding *that* to
`⟨2, _⟩` is what lets the `Fin` numeral simprocs evaluate `![0, 0, 1] 2 = 1`.
Attempts 1–4 all tried to reach the residual and then close it; the fix is to
not produce it. Two details worth keeping:

- **`Fin.castPred` in the simp set is *unused*** — `linter.unusedSimpArgs` says
  so, and only `Fin.castLT` is needed. `simp [Fin.castPred_mk]` makes no
  progress and plain `simp [Fin.castPred]` hits max recursion, which is what
  sent the earlier attempts looking for a mirror lemma; `Fin.castLT` is the
  argument that actually unblocks the chain.
- **The same argument retired the three sibling bullets' trailing `rfl`s.** All
  four incidence bullets of `exists_affineIndependent_panel_incidence` had the
  same shape — flexible `simp`, then a rigid defeq closer (`exact one_ne_zero`
  once, `rfl` three times). Only the `exact` was reported, because the linter
  treats `rfl` as flexible-safe; but the three `rfl`s were the *same latent
  defect*, one bump away from being reported too. All four bullets are now the
  identical single `simp` call.

**Generalized as TACTICS-QUIRKS § 107** (`simp` stalls on a `Matrix.cons`/`![…]`
applied to a `Fin.castPred`/`Fin.castLT` index). The mirror lemma this section
used to recommend — a `Matrix.cons`-of-`Fin.castPred` reduction under
`CombinatorialRigidity/Mathlib/` — is **not needed**, and is filed in
`notes/FRICTION.md` as a deliberately-unmirrored candidate: one simp argument
covers every site in the tree today, so write the mirror only if a second file
needs the same unfolding.

### 4a. Warning classes this queue never enumerated — ✓ DONE (18 of 22 sites)

Found by reading the build log's warning *taxonomy* rather than this note. None
came from the deprecation drift, which is why the note missed them — worth a
taxonomy pass on the next bump rather than working only from the queue:

- **17 no-op tactics** (`linter.unusedTactic`): nine multi-line `change` blocks
  in `Molecule/Pencil/Engine.lean`, four single-line ones in
  `CaseIII/Relabel/Basic.lean`, one in `Matrix/Rank.lean`, two `push_cast`, and
  one `(first | rfl | simp)` whose `simp` branch is never executed — its sibling
  two lines up genuinely needs it, so fix only the flagged site. The Engine
  blocks share one shape (`· change …` over exactly three lines, then a `have`),
  so the transform is "delete three lines, hoist the `have` onto the bullet" —
  and that hoist preserves the following continuation lines' indentation
  exactly, since `· ` is two characters and the `have` sat two deeper.
- **1 redundant `@[expose]`** (`Jacobs.lean`'s `IsLaman3`) — exposed by default.

### 4c. `linter.overlappingInstances` — ✓ DONE (4 sites; fixed by *scoping*, never by deleting a binder)

**Landed 2026-08-21.** Both duplications are **real**, and in both cases the
obvious removal **breaks the build** — the two trap analyses below are kept in
full because each failure is worth knowing, and because someone will otherwise
"fix" these again. The working fixes are *scoping* moves in both cases, recorded
after each trap. Generalized as **TACTICS-QUIRKS § 108**.

**`Search/DFS.lean`'s `reachableFindingAux`** (2 × `[Fintype V]`,
2 × `[DecidableEq V]`) restates its section's `variable [Fintype V]
[DecidableEq V]` inline. Deleting the inline pair produces:

```
error: failed to synthesize instance of type class Fintype V
error: MVar does not look like a recursive call:
  {V : Type u} → [DecidableEq V] → (V → List V) → (V → Bool) → Finset V → V → Fintype V
error: Unknown constant `…reachableFindingAux.induct`
```

**Why: a section `variable` instance is inserted where it is first
*referenced*, not where the binder list would put it.** `Fintype V` is first
referenced inside the body's termination measure, so it lands at the **end** of
the telescope (visible in that error), which changes the recursive-call shape
and takes the well-founded-recursion machinery — and the generated `.induct`
principle two proofs use — down with it. The inline binders are load-bearing
*for the recursion*, not decoration. (Neighbouring quirk: TACTICS-QUIRKS § 16 on
`termination_by`/`decreasing_by`.) A deletion also *adds* four new
`unusedFintypeInType`-style warnings on the downstream `_sound`/`_complete`
lemmas — a net loss.

**`Induction/Operations.lean`'s three `candidate*` defs** (2 × `[DecidableEq α]`).
This is **not** a naive duplicate `variable` — it is an `omit`/re-introduce
interaction across one 1,550-line namespace (`ChainData`, lines 1634–3183):

```
1882  variable [DecidableEq α]                    ← introduce
2087  omit [DecidableEq α]                        ← turn off for the rest
2402  omit [DecidableEq α]                        ← redundant (already off)
2472  variable [DecidableEq β]
2636  variable [DecidableEq α]                    ← re-introduce: ADDS A SECOND BINDER
3141  omit [DecidableEq α] [DecidableEq β] in     ← ×4, each omits one of the two
3183  end ChainData
```

**The key fact: a bare `omit [C]` does not remove the variable from the
section's list, so a later `variable [C]` puts a *second copy in scope* rather
than un-omitting the first.** Hence two copies downstream of 2636, and the four
`omit … in` statements at 3141+ each drop one and keep the other. Deleting the
2636 line therefore gives `cannot omit referenced section variable inst✝¹` ×4:
each `omit` now targets the only copy, which *is* referenced.

**Fix as landed (Operations.lean) — the `section` scoping, and it was cheaper
than specced.** Wrap the `DecidableEq α`-needing region in its own
`section ShiftPerm`/`end` (the `end` placed at the `/-! ###` header boundary
rather than mid-subsection where the old `omit` sat), delete **both** bare
`omit [DecidableEq α]` lines, keep the later `variable [DecidableEq α]` as the
single introduction for the tail. Three edit sites, not five. **The four
`omit … in` clauses at the tail needed no change at all** — this section
predicted they would need re-deriving; they did not, so do not budget a build
for that step.

**What the linter is actually counting — check this before pricing any
`overlappingInstances` fix.** It counts duplicated instances **in scope for the
declaration**, not duplicated arguments in the resulting signature. Lean only
abstracts the section variables a declaration *references*, so the duplicate
copies were never reaching the telescope in the first place. `#check` on the
pre-fix and post-fix trees gives **byte-identical** signatures for all three
defs — and shows that even before the fix each carried at most one copy:

| def | signature, unchanged by the fix | linter said |
|---|---|---|
| `candidateVtx` | **no `DecidableEq` binder at all** (it uses none) | 2 × `[DecidableEq α]` |
| `candidateSeed` | 1 × `[DecidableEq α]` | 2 × `[DecidableEq α]` |
| `candidateEnds` | 1 × `[DecidableEq β]`, 1 × `[DecidableEq α]` | 2 × `[DecidableEq α]` |

So this is a **scoping-hygiene** warning, not a signature defect: nothing was
over-hypothesised, and nothing got generalized by fixing it (contrast item 0,
where the fix genuinely weakened 63 statements). That is the reassuring reading —
the fix cannot break a call site — but it is also the reason the warning is worth
clearing rather than suppressing: with two copies in scope a reader cannot tell
which one a declaration uses, and the four downstream `omit … in` clauses were
silently dropping the spare.

**Fix as landed (DFS.lean) — two lines, and *not* the one specced here.** The
specced fix ("drop the instances from the `variable` line … then add them inline
to the ~4 downstream `_sound`/`_complete` lemmas") was mis-sized: **11**
declarations sit under that `variable` line, not 4. What works instead is to
leave the line's content alone and **move it to *below* `reachableFindingAux`**
— the one def whose inline binders the recursion needs. The def then has only
its inline pair (warning gone), and all 11 downstream declarations pick the
instances up from the section exactly as before. **No signature changes
anywhere** — `#check` on all five load-bearing declarations gives byte-identical
telescopes before and after, `reachableFindingAux` included (it already carried
just one `[Fintype V]` / `[DecidableEq V]` despite the linter reporting two, per
the scoping-vs-signature note above). Both the def and the moved `variable` line
carry a comment saying why the line is out of order.

**Dead end worth not repeating:** `omit [Fintype V] [DecidableEq V] in` on the
def. It must sit *above* the docstring — between docstring and `def` it is a
parse error (*"unexpected token 'omit'; expected 'lemma'"*) — and even placed
correctly the linter still fires.

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

~~**Still open:** the two `TACTICS-QUIRKS.md` rescue entries…~~ — **done.**
The **zeta-delta / `set`-binding** entry is now **§ 105** and the
**reach-for-`exact`-before-`convert`** entry **§ 106**, both with *Symptom
index* lines. § 105 cross-references the three neighbouring `set` entries it is
easy to confuse it with (§ 1 `omega`/`grind` atoms, § 6 `set` of a lambda,
§ 98 `rw [heq]` motive failures), since the distinguishing feature is that
nothing was wrong with the proof — only simp's default unfolding moved.

### 5. Unstick hopscotch — ✓ DONE (2026-08-21, a one-line `lakefile.toml` reorder)

**Fixed by moving `require mathlib` LAST.** The root cause was our own require
order, measured both ways — see *The hopscotch false positive* above for the
mechanism and the numbers. The three priced options this section used to carry
(own bump workflow / hand-bump cadence / a mix) are **moot**: hopscotch now
works as designed, so there is no new workflow to write, no `open-issue: false`
to set, and nothing to route around.

Kept because it still bears on the upstream report: **the action cannot be
configured around this.** `hopscotch` runs `lake update <dependency-name>` for
the single dependency under test (documented behaviour), and neither `hopscotch`
nor `hopscotch-action` exposes a flag to sync transitive pins or to address a
`lake exe cache get` hash mismatch; `extra-args` forwards to `hopscotch dep`,
which has no such option. The action is monolithic (bump, build, PR/issue in one
step), so there is nowhere to inject a fix-up step. That was never the fix — but
it is why a downstream with the losing require order has no escape short of
editing its lakefile.

**Blast radius, measured.** Only three repos run the action: this one,
`bryangingechen/autoformaltemplate` (mathlib + `checkdecls`, whose manifest is
empty), and `chrisflav/proetale` (mathlib + `upstreamer`, likewise empty). So
neither of the others has a second pin-writer to lose to, and proetale's own
hopscotch issue (#116) is a **genuine** break — duplicate declarations after
mathlib upstreamed them. That is why three months of this went unreported.

**Still open, and no longer blocked by a strategy decision:**

- **Close issue #2 and PR #1.** Both are stale artifacts of the false positive,
  and closing them is now sayable on the merits: a false positive caused by our
  require order, fixed by the reorder. (PR #1 bumps to `888dee7`, long
  superseded.)
- **Optional: report upstream** — user deciding as of 2026-08-21. Two defects
  survive the local fix, and they are the action's rather than ours: (i) a
  **bump**-phase failure is presented as a build incompatibility, under a
  *"Build failure log"* heading, with no Lean having compiled — even though
  hopscotch's own README says the two phases are recorded distinguishably;
  (ii) such a failure reproduces on every later commit, so bisect latches onto
  it permanently and the tracking issue can never self-close, leaving a daily
  workflow silently wedged. Context for the report: **zero** issues have ever
  been filed on either repo, and the closest PR
  (`leanprover-community/hopscotch#2`, adding `--cache`, open since 2026-04-20)
  is *not* this fix — it prepends `lake cache get` to the **verify** array and
  logs failure as a warning, whereas our failure is fatal in the **bump** step
  and never reaches verify.

### 6. Optional: audit the remaining `convert` sites

25 `convert … using N` plus 7 bare `convert` remain; 3 of them broke on this
jump (~10%). Not worth a speculative sweep — but if a future bump breaks
several again, converting the survivors to `exact`/`simpa only` where they are
definitionally true would reduce the recurring cost. Note the diagnostic:
`convert` failing with leftover *instance-path* goals (`Real.instRing.toSemiring
= Real.semiring`) is the tell that the statement is defeq and `exact` will work.
