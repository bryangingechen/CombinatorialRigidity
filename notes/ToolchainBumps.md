# Toolchain + dependency bumps — running log and playbook

Durable log for Lean-toolchain / mathlib / `Matroid` bumps. Not a phase note:
bumps are maintenance and cut across whatever phase is active. Read this
**before** attempting a bump — *Where this stands* is the hand-off, *Playbook*
is the how-to, and the per-bump records below carry what broke and why.

Pointers: `CombinatorialRigidity/CLAUDE.md` *Build discipline* (the
never-`lake update` rule and its escape hatch) and *Automated mathlib bumps*
(the hopscotch workflow).

---

## Where this stands — and the next concrete task

**Current pins (2026-08-24):** Lean `v4.34.0-rc2`, mathlib `8b36e867`,
`Matroid` `2b92ee39`. Every gate green locally (the rc2 record's table).

The rc1 stack (10 commits) is **merged into local `master`** — fast-forward
from `bump/lean-4.34.0-rc1`, which still exists as a ref — and the **rc2 bump
sits on top of it**, on `bump/lean-4.34.0-rc2`. The whole thing is **still
unpushed**: `origin/master` sits at `0920772` (Phase-38 close, 2026-07-23),
leaving local master **284 commits ahead**. So **CI has never validated any of
it**, and the hopscotch workflow runs against `origin/master` — i.e. the
*pre-fix* lakefile — so it will keep re-stamping issue #2 until master is
pushed.

**Next concrete task: get CI onto this stack, then push `master`.** Nothing
blocks it; the two routes differ in a way that is a real choice, not a
formality:

- **CI first (safer).** Push `bump/lean-4.34.0-rc2` and open a PR against
  `master`; PRs build + lint but **skip** the Pages deploy. The diff is large
  (284 commits) but the point is the build, not the review.
- **Push `master` directly.** Simplest, and the local gates are green — but
  every green `master` push **publishes** (blueprint, docs, upstreaming
  dashboard via `docgen-action`). There is no "deploy later" knob, so this is
  the first CI run *and* the deploy in one step.

Then the post-merge tidying: close issue #2 / PR #1 (both stale false-positive
artifacts), and the optional upstream hopscotch report the user is still
weighing (see *The hopscotch false positive*).

---

## Playbook — how to run a bump here

**The blocker to know about first.** `lake update` is denied by a PreToolUse
hook (`.claude/hooks/block-lake-update.sh`), added after an OOM incident. That
hook is right to exist, but it has no built-in escape hatch, so a *deliberate,
requested* bump needs one of:

1. **`scripts/bump-mathlib.sh <rev>`** — dry by default, `--apply` to write.
   Deterministic, reviewable in the diff, no hook bypass.
   - Resolve `<rev>` (SHA, branch, or tag) against mathlib's GitHub API, then
     read mathlib's own `lake-manifest.json` and `lean-toolchain` at it.
   - Copy **its** transitive pins (`batteries`, `aesop`, `Qq`, `Cli`,
     `proofwidgets`, `importGraph`, `plausible`, `LeanSearchClient`) verbatim
     into ours — rev *and* `inputRev`.
   - Set our `mathlib` rev to the target, and `lean-toolchain` to mathlib's.
   - Non-mathlib deps (`Matroid`, `checkdecls`, and `loogle` which comes in
     transitively via `Matroid`) keep their own pins — it skips any package
     mathlib's manifest doesn't mention, so **bumping `Matroid` is always a
     hand-edit** of `lakefile.toml` plus that package's `rev`/`inputRev` in
     `lake-manifest.json`.
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
re-resolve. Running `scripts/bump-mathlib.sh` against the pin we already have is
a cheap check that the invariant still holds: it prints `already in sync` when
it does, and names the drifted packages when it doesn't.

**Check whether the two deps already agree before reconciling anything.** One
`curl` of `apnelson1/Matroid`'s `lake-manifest.json` against mathlib's own at
the target rev says whether their transitive pins are identical. At the
v4.34.0-rc2 bump they were, which reduced the pin work to a single script run.

**`lake exe cache get` doubles as a pin check — run it before the build.** Read
the *total*, not just the exit code: a full hit (all 8779 files at the
v4.34.0-rc2 bump, zero misses) means the whole dependency set hashes to exactly
what mathlib CI built, so no transitive pin is stale. A partial or failed fetch
is the very signal *The hopscotch false positive* is about — the fix is to
correct the pins, never to let it build mathlib from source.

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

Fix: point `LAKE_CACHE_DIR` at a writable directory (a user cache dir works;
`~/Library/Caches` is *not* writable by the harness on macOS) for every build —
`LAKE_CACHE_DIR=<writable-dir> lake build`. (`lake build --no-cache` does
**not** help — it disables cache *downloads*, not the local write.
`LAKE_CACHE_DIR=""` disables the cache entirely.)

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
  whole-tree count off a fully-cached build is honest. No `touch` needed. (This
  cuts the other way too: a build with no writable cache dir under-reports
  errors as well as warnings — that is the flattering count above.)
- **`lake env lean <file>` does not apply the lakefile's `leanOptions`.** It is
  a ~10s-per-file iteration loop (vs minutes for a targeted `lake build`) and
  its *errors* are trustworthy, but it silently skips the whole mathlib style
  linter set — it reported clean on three lines that were over the
  100-character limit. Lint cleanliness is only established by `lake build`.

### The gate set to re-run after any bump

| check | notes |
|---|---|
| `LAKE_CACHE_DIR=<dir> lake build` | 0 errors, 0 warnings, 0 `failed to cache artifact`, 122/122 modules accounted for |
| `LAKE_CACHE_DIR=<dir> lake lint` | batteries `runLinter`; separate from the in-build style linters |
| `lake build pebble-game` | the exe is **not** in `defaultTargets`, so a plain `lake build` skips it |
| `lake exe checkdecls blueprint/lean_decls` | silence + exit 0 = all 758 pinned blueprint declarations resolve |
| `#print axioms` on the 17 `formalization.yaml` headline decls | expect `[propext, Classical.choice, Quot.sound]`, no `sorryAx` |
| the 11 `PebbleGame/Examples.lean` `#eval`s | printed by the build itself as `info:` lines; each has its expected value in a comment |
| the 4 `examples/*.txt` via `lake exe pebble-game` | each file carries its expected output in its own header |

The last row is the only gate that exercises **codegen** rather than
elaboration, which is why it is worth the seconds it costs on a *toolchain*
bump. One trap: read the whole output, not `tail -1` — the verdict line
(`LAMAN` / `SPARSE_NOT_TIGHT` / `NOT_SPARSE`) comes **first**, ahead of the
`ARCS`/`VERTEX`/`BLOCKING` witness lines, so tailing shows a witness line and
reads as a wrong answer.

### What the cleanup after a big bump costs

Distilled from the rc1 queue (closed; details in *Cleanup queue* below). A
one-rc bump may need none of this — rc2 needed nothing — but a multi-version
jump will:

- **`unusedArguments` CASCADES — iterate `lake lint` to a fixed point.** The
  single most important thing to know before starting. Dropping a binder
  removes it from that lemma's proof term, hence from its **callers'** terms
  too, so a caller whose only use of `Finite α` was passing it down becomes
  newly unused. rc1 took **three rounds: 64 → 9 → 2 → 0**. Do not read the
  first report as the size of the job; each round costs a full build plus a
  lint (~10 and ~15 min here), so the cost is in the iteration, not the edits.
- **Expect `unusedArguments` false positives on the `Fintype.ofFinite` bridge.**
  The linter reads the *proof term*; the project's standard
  `haveI : Fintype X := Fintype.ofFinite X` idiom needs `Finite X` to
  **elaborate** but leaves it out of the term. rc1 had **7 of 59**, each now
  carrying `@[nolint unusedArguments]` with a comment naming the bridge (11
  such sites in the tree today — `grep -rn "nolint unusedArguments"`).
  Screening heuristic and its limit: grepping each flagged declaration's body
  for `Fintype.ofFinite` caught all 7 but flagged 15 of 59, and cannot tell you
  which 8 are spurious (`Fintype.ofFinite _` hides which variable it converts).
  Cheapest reliable loop: drop everything, then `lake env lean <file>` on the
  at-risk files.
- **Work from the build log's warning *taxonomy*, not from a queue.** rc1's
  item 4a found 22 sites in classes this note had never enumerated, none of
  them from the deprecation drift. A taxonomy pass is how you find them.
- **Count *sites*, not warning lines.** One source position can be reported
  several times in one log (`if_true`: 39 lines at 12 positions), so a raw
  `grep -c` over-counts. `scripts/sweep-deprecations.py` dedupes by
  `(file, line, col)`.
- **A rename sweep can push lines past the 100-character limit.** rc1 rewrapped
  13 lines (`if_neg` → `ite_eq_right` is six characters longer). The style
  linter, not the sweep, is what tells you — so budget a full build after.
- **File-level overlap is the wrong granularity for a "not our edits" claim.**
  rc1's original write-up claimed the lint-failing files and the bump-edited
  files were disjoint; eleven were in both. The conclusion (pre-existing code
  meeting a changed linter) survived only on the *per-declaration* check: 63 of
  64 flagged declarations were untouched by the bump. A file can be edited in
  one proof and carry a vestigial binder forty lines away.

**And the methodology lesson, which is the one that generalizes past linters.**
All three of rc1's last-five warning sites resisted the fix this note had
predicted for them, and the miss has one shape every time: **the prediction was
scoped off the linter's *report* rather than the *mechanism* producing it**, so
it over-sized the job twice and reached for a new mirror lemma the tree did not
need once.

| site | predicted | what actually worked |
|---|---|---|
| 1 × `linter.flexible`, `Claim612.lean` | a new mirror lemma under `CombinatorialRigidity/Mathlib/`; "four other routes tried and dead" | **one more simp argument** (`Fin.castLT`). No lemma, and it retired three sibling bullets' trailing `rfl`s too |
| 1 × overlapping instances, `Search/DFS.lean` | drop the `variable`-line instances, re-add inline on "the ~4 downstream lemmas" (really **11**) | **move the `variable` line *below* the one def with inline binders** — two lines, zero signature changes |
| 3 × overlapping instances, `Induction/Operations.lean` | `section`-scope the `omit` dance, then re-derive which `omit … in` clauses survive | the `section` scoping, as predicted — and the four `omit … in` clauses needed **no** change |

---

## Bump record: v4.34.0-rc1 → v4.34.0-rc2 (2026-08-24)

| | before | after |
|---|---|---|
| `lean-toolchain` | `v4.34.0-rc1` | `v4.34.0-rc2` |
| mathlib | `653c36f0` (2026-08-14) | `8b36e867` (2026-08-24) |
| `Matroid` | `f44939ff` | `2b92ee39` |

**Nothing broke — zero source fixes.** The first `lake build` after the pin
edit was green: 2964 jobs, 0 errors, 0 warnings, 0 `failed to cache artifact`,
and all **122** of our modules genuinely recompiled (`Built`, not `Replayed`,
so the clean warning count is not a cache-replay artifact). `lake lint` passed
first run, and every gate in the table above was re-run green. The contrast
with the four-version rc1 jump (~39 fixes across 28 files plus a six-item
cleanup queue) is the durable lesson: a **one-rc bump taken promptly costs a
build, not a session** — the argument for tracking rc's as they land rather
than letting them pile up.

**Pin choice, same rule as rc1:** mathlib at **the exact revision
`apnelson1/Matroid` HEAD is tested against** (`8b36e867`), not the
`v4.34.0-rc2` tag (`85e3a25e`, 54 commits behind). Both pre-build checks in the
*Playbook* passed — Matroid's manifest and mathlib's own at `8b36e867` carry
identical transitive pins, and `cache get` hit all 8779 files — so there was no
pin set to reconcile and no build-from-source risk. `Matroid`'s default branch
is **`main`**, not `master`: `git ls-remote refs/heads/master` returns nothing
there and reads alarmingly like a deleted branch.

**Two claims re-checked rather than assumed.** The `Matroid` churn **missed us
by luck, not design**: its 6 new commits touch 80 files, none of them one of
our 8 imported modules — but ~30 sit in their transitive closure, and the set
includes a `Graph/Hom.lean` rename and four *removed* `Graph/Iso/*` files. Only
the green build settled that; the changed-file list could not. And **§ 48 is
still load-bearing**: `scoped notation:51 G:100 " - " S:100` is unchanged at
`Matroid/Graph/Subgraph/Defs.lean:66` in the new rev, so the `deleteVerts`
parse poisoning and its four local workarounds stand, and `lakefile.toml`'s
comment asserting this is still accurate.

---

## Bump record: v4.30.0-rc2 → v4.34.0-rc1 (2026-08-20)

| | before | after |
|---|---|---|
| `lean-toolchain` | `v4.30.0-rc2` | `v4.34.0-rc1` |
| mathlib | `21b745fd` (2026-05-13) | `653c36f0` (2026-08-14) |
| `Matroid` | `bryangingechen` fork `cb3be62` | `apnelson1` `f44939f` |

mathlib pinned to a master commit rather than the `v4.34.0-rc1` tag
(`de5ce8a9`) because `653c36f0` is the revision `apnelson1/Matroid` HEAD was
tested against — the rule the rc2 bump then reused.

### The `Matroid` fork is retired

The `bryangingechen/Matroid` fork carried two patches, which diverged in
status:

- **`unifOn_rankPos_iff` simp drift** (Phase 13, `08d517f`) — **obsolete.**
  Upstream re-greened it independently with a different simp set.
- **`deleteVerts` notation precedence** (Phase 23g, `cb3be62`) — **still
  absent upstream** (re-checked at the rc2 bump). `scoped notation:51 G:100
  " - " S:100` is unchanged in `apnelson1/Matroid`, so the `-`-continuation
  parse poisoning of TACTICS-QUIRKS § 48 is live in this repo.

The decision was to **retire the fork anyway** and pin bare upstream, because
the measured cost is small: the poisoning bites at exactly **4 sites**, each
with a cheap local workaround already documented in § 48 (one added paren;
three `Nat.sub_add_cancel` rewrites). Retiring buys a plain upstream pin with
green CI and nothing to maintain or rebase.

Consequence to keep in mind: **§ 48's workarounds are load-bearing.** New
`-`-then-`+` or chained-`-` arithmetic written in a file with a
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
| `simp`/`simpa` no longer unfolds `set`/`let`-bound locals (§ 105) | 13 | add the defining equation to the simp set |
| `convert … using N` / `simpa … using h` where plain `exact` works (§ 106) | 13 | delete the tactic |
| `Std.Symm` / `Std.Irrefl` structure fields | 6 | wrap the field body in `⟨…⟩` |
| simp not bridging coercion / beta / `Subtype.mk` gaps | 6 | explicit `congrArg Subtype.val`, `Function.comp_def` |
| `deleteVerts` notation poisoning (§ 48) | 4 | paren, or `Nat.sub_add_cancel` |
| `Finset.le_eq_subset` now a syntactic equality | 3 | drop the no-op `simp only` |
| misc simp-set drift | 5 | add the missing unfolding lemma |

The two joint-largest groups are now rescue patterns: **TACTICS-QUIRKS § 105**
(zeta-delta — pass `hx` from `set x := … with hx`; all 8
`GenericityDevice.lean` failures were one `set`) and **§ 106** (reach for
`exact` before debugging a `convert`).

A third, smaller pattern worth naming: **an explicit-proof simp lemma like
`if_pos rfl` can stop applying because simp normalizes the *condition*
first.** In `Relabel/ChainColumn.lean` the scrutinee `0 = 0` became `True`
before `if_pos rfl` could fire, so the fix was to drop it and list `ite_true`.
Worth remembering because the deprecation table *also* renames `if_pos` →
`ite_eq_left`, and blindly applying that rename would have kept a broken proof
looking merely deprecated.

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

**The fix is to move `require mathlib` LAST — mathlib's own warning was right
all along.** This section long asserted the opposite, on the evidence that the
rc1 bump left the order untouched and the warning still disappeared; that
evidence was **confounded** (`bump-mathlib.sh` had already hand-synced every
pin, so all sources agreed and order stopped mattering — it never tested
order).

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

**The action cannot be configured around this**, which is what bears on the
still-open upstream report. `hopscotch` runs `lake update <dependency-name>`
for the single dependency under test (documented behaviour), and neither
`hopscotch` nor `hopscotch-action` exposes a flag to sync transitive pins or to
address a `cache get` hash mismatch; `extra-args` forwards to `hopscotch dep`,
which has no such option. The action is monolithic (bump, build, PR/issue in
one step), so there is nowhere to inject a fix-up step.

**Blast radius, measured.** Only three repos run the action: this one,
`bryangingechen/autoformaltemplate` and `chrisflav/proetale` (both
mathlib + one dep with an empty manifest). So neither of the others has a
second pin-writer to lose to, and proetale's own hopscotch issue (#116) is a
**genuine** break. That is why three months of this went unreported.

**Optional upstream report — user deciding as of 2026-08-21.** Two defects
survive the local fix, and they are the action's rather than ours: (i) a
**bump**-phase failure is presented as a build incompatibility, under a
*"Build failure log"* heading, with no Lean having compiled — even though
hopscotch's own README says the two phases are recorded distinguishably;
(ii) such a failure reproduces on every later commit, so bisect latches onto it
permanently and the tracking issue can never self-close, leaving a daily
workflow silently wedged. Context: **zero** issues have ever been filed on
either repo, and the closest PR (`leanprover-community/hopscotch#2`, adding
`--cache`, open since 2026-04-20) is *not* this fix — it prepends
`lake cache get` to the **verify** array and logs failure as a warning, whereas
our failure is fatal in the **bump** step and never reaches verify.

### Cleanup queue — closed 2026-08-21

Items 0–5 **DONE**, item 6 optional and untouched; warnings **1441 → 0** and
both gates green on the rc1 tree (`lake build` 2948 jobs, `lake lint` "Linting
passed"). The forward-looking content is lifted into *What the cleanup after a
big bump costs* above; what each item produced, and where its detail now lives:

| item | outcome | detail now lives in |
|---|---|---|
| **0.** `lake lint` green | 64 errors → 0 over three cascade rounds — 59 `unusedArguments` + 5 `defsWithUnderscore`. **63 declarations became strictly more general** (dropped unused hypotheses; no call site changed, since instance arguments are inferred), 7 kept under `@[nolint]` as bridge false positives, 4 renames + 2 deletions | `DESIGN.md` *Typeclass shape for finiteness on `V`* (the amendment); the `@[nolint unusedArguments]` comments in the tree |
| **1.** Deprecation rename sweep | 846 renames over 70 files, 920 deprecation warnings → 0; 8 hand sites, 5 `le_eq_subset` sites dropped (no replacement name), 13 lines rewrapped | `scripts/sweep-deprecations.py` — its header carries the log-position design and the `EXCLUDED` type-changed renames with reasons |
| **2.** `haveI`/`letI` style sweep | 475 sites (468 `haveI`, 7 `letI`), warnings 515 → 40. Position-driven like item 1; do **not** blanket-sed, the two differ for genuine instance bindings and only flagged Prop-goal sites are safe | this row |
| **3.** Unused simp arguments | folded into item 2's sweep | this row |
| **4.** `linter.flexible` in `Claim612.lean` | one simp argument (`Fin.castLT`), after four plausible attempts failed | **TACTICS-QUIRKS § 107**; the declined mirror lemma is filed in `notes/FRICTION.md` as a deliberately-unmirrored candidate |
| **4a.** Unenumerated warning classes | 22 sites found by a taxonomy pass: 17 no-op tactics, 1 redundant `@[expose]` | this row |
| **4b.** General fixes | both bump scripts, and the `lake update` escape hatch | `scripts/`, `CombinatorialRigidity/CLAUDE.md` *Build discipline* |
| **4c.** `linter.overlappingInstances` | 4 sites, fixed by **scoping** in both files — never by deleting a binder, which breaks the build two different ways | **TACTICS-QUIRKS § 108**, which carries both mechanisms, both errors, both fixes, the scoping-vs-signature analysis, and the `omit` dead end, and names these two files as its worked cases |
| **5.** Unstick hopscotch | a one-line `lakefile.toml` require reorder | *The hopscotch false positive* above |

The `4b` rescue-pattern transcriptions closed as **TACTICS-QUIRKS § 105** and
**§ 106** (see *What actually broke*). § 105 cross-references the three
neighbouring `set` entries it is easy to confuse it with (§ 1 `omega`/`grind`
atoms, § 6 `set` of a lambda, § 98 `rw [heq]` motive failures), since its
distinguishing feature is that nothing was wrong with the proof — only simp's
default unfolding moved.

### 6. Optional: audit the remaining `convert` sites — still open

25 `convert … using N` plus 7 bare `convert` remain; 3 of them broke on the rc1
jump (~10%), and none on rc2. Not worth a speculative sweep — but if a future
bump breaks several again, converting the survivors to `exact`/`simpa only`
where they are definitionally true would reduce the recurring cost. The
diagnostic is § 106's: a `convert` failing with leftover *instance-path* goals
(`Real.instRing.toSemiring = Real.semiring`) is the tell that the statement is
defeq and `exact` will work.
