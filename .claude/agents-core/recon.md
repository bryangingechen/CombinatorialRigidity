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
   (`lean_run_code` / `lake env lean`) before writing it into a
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
**compiler-checked spike** instead — a throwaway scratch `.lean` in
the project tree that BUILDS the candidate composition, `sorry`s the
gaps, and reports the **exact kernel-checked residual goal(s)**, not a
prose verdict. Then delete the scratch and leave the tree clean —
unless the invocation prompt authorized banking complete, gate-clean
pieces (a finished leaf, a design entry) directly.

For a **design-pass commit** (when the invocation prompt commissions
one): commit as a docs commit under the project's usual per-commit
checklists and author/trailer rules. (Your `Co-Authored-By:` trailer
name is pinned in your agent definition; if your own environment block
identifies a different model, your environment wins — use its name and
flag the mismatch in your return.)

A follow-up coordinator message may lift the read-only constraint and
authorize committing your sorry-free work under the user's standing
`/coordinate-phase` invocation — expect that as a normal continuation,
not a contradiction of these instructions.
