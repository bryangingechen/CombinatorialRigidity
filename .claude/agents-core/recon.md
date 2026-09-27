# recon core discipline

This is the **shared core** for the `recon` agent family
(`.claude/agents/recon*.md` — the rung-pinned variants and the
unpinned base). Those definitions are thin: role, return contract, and
a pointer here. This file carries the recon discipline they share;
edit it once, and every variant follows. A dispatched agent reads this
file as its FIRST action and follows it as if it were part of its
system prompt.

Three clauses bind every recon / design-pass (each earned its place —
the same rung pinned a route *wrong* unprimed and *right* primed with
these):

1. **Verify every load-bearing claim against the landed source** —
   open the actual `def`/`theorem`, not the prior pin's prose or a
   docstring. Docstrings are not evidence; derive claims from the
   definition body, and check a surprise with a small compiler witness
   (`lean_run_code` / `lake lean`) before writing it into a
   verdict. This includes confirming that a pinned object **is** the
   construction the pin names (open every graph/algebra construction
   the pin references), not merely that the cited API names exist.
2. **Flag, don't force.** If the corrected route needs a motive/
   IH-level change or genuinely-new math, say so and stop; a verdict
   that honestly names an open decision beats a confident wrong one
   (confident wrong pins have cost reverted builds). Frame source
   checks adversarially — "try to *refute* the proposed reading; a
   refutation is more valuable than a confirmation."
3. **Trace structural invariants to ground, not just API existence.**
   When a step matches two index families, confirm a stated contract
   fact makes their cardinalities coincide; a contract recording two
   known-linked quantities without the linking hypothesis is a latent
   gap. When a route hangs on a deferred gate/side-condition, trace
   the gate to its *producer* and confirm the producer emits that
   exact object — do not accept "the gate is sourceable from X" on
   prose alone.

**Match your method to the question.** A *prose* analysis is right for
faithfulness / decomposition questions ("does this match the source?",
"what are the buildable sub-leaves?"). For a **route-composition**
question — "do these specific Lean objects compose to produce goal
X?" — in a defeq-fragile zone, prose is the wrong tool: write a
**compiler-checked spike** instead — a scratch `.lean` that BUILDS the
candidate composition, `sorry`s the gaps, and reports the **exact
kernel-checked residual goal(s)**, not a prose verdict. The spike
mechanics (trial, 2026-09-27 incident):

- **Location: `scratch/<phase>/`** in the repo (gitignored, so the tree
  stays clean). Not `/tmp` or a session scratchpad: the lean-lsp MCP
  refuses a file with no `lean-toolchain` ancestor.
- **Iterate with the MCP.** Load its tools once with ToolSearch
  (`select:mcp__lean-lsp__lean_goal,mcp__lean-lsp__lean_multi_attempt,mcp__lean-lsp__lean_diagnostic_messages,mcp__lean-lsp__lean_loogle,mcp__lean-lsp__lean_local_search`),
  then read goals with `lean_goal` rather than inserting a `sorry` and
  recompiling, and try tactics with `lean_multi_attempt`. The server
  loads the imports once and re-elaborates only from the edit onward.
- **Attest with `lake lean <file>`, never `lake env lean <file>`.**
  `lake lean` applies the lakefile's `[leanOptions]` (`autoImplicit =
  false`, the mathlib linter set, `warn.sorry`); `lake env lean` runs
  with Lean's defaults and hides errors as well as warnings. Report the
  `lake lean` counts.
- **Keep the files** when the coordinator may hand the spike to a
  builder (a complete spike is the build, step 3 *Resume and land*);
  otherwise delete them.

Commit nothing from `scratch/` unless the invocation prompt authorized
banking complete, gate-clean pieces (a finished leaf, a design entry)
directly.

For a **design-pass commit** (when the invocation prompt commissions
one): commit as a docs commit under the project's usual per-commit
checklists and author/trailer rules. Run any gate (`lake build`,
`blueprint/verify.sh`, …) as a blocking Bash call **with an explicit
`timeout` parameter (600000)**, and **never `run_in_background`/Monitor
a gate** — without the explicit timeout the harness auto-backgrounds a
long call, and a gate you background and wait on via Monitor strands the
same way; an ended turn leaves the work uncommitted (dispatch-log F6). (Your `Co-Authored-By:` trailer
name is pinned in your agent definition; if your own environment block
identifies a different model, your environment wins — use its name and
flag the mismatch in your return.)

A follow-up coordinator message may lift the read-only constraint and
authorize committing your sorry-free work under the user's standing
`/coordinate-phase` invocation — expect that as a normal continuation,
not a contradiction of these instructions.
