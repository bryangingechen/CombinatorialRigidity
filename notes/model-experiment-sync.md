# Model-tier experiment — cross-repo protocol-sync tracker

Repo-local tracker for propagating **protocol** amendments
(`notes/model-experiment-protocol.md`) to the other participating repos.
The protocol file is byte-identical across repos by design; when an
amendment lands here it must be copied to the siblings.

**Discipline (this is what keeps the list short).** The amendment's *full
text* lives in the protocol file — its canonical home. This tracker carries
only a **one-line pointer** per pending item (date · tag · where in the
protocol). When you amend the protocol: edit the protocol file, add a
pointer line here, and **delete the line once it is synced** to the
siblings. Do not restate amendment content here (that duplication is what
bloated the main log's header for a month).

**Participating repos:** `autoformaltemplate`, `enharmonic`.

**Last full sync:** 2026-06-10 evening (template `1e441ae`).

## Pending propagation (landed locally, not yet synced)

Each line: `date — tag → protocol §`. `(repo-local)` = no protocol change to
propagate (a companion lives in `.claude/commands/coordinate-phase.md` or
`notes/coordinate-phase-rescue.md`); listed only so the audit trail is complete.

- 2026-06-11 — `killed` Outcome value → *Per-dispatch record* (Outcome)
- 2026-06-11 — boundary-pair worktree-build caveat (`cache get` before any fresh-worktree build) → *Boundary pairs*
- 2026-06-11 — 22h-close: P ≥ 2 for unbuilt-argument prose; Mode `recon` + stakes-based recon rungs → *Task rating* (P), *Model assignment map*
- 2026-06-11 — resume amendments: Mode `resume`; resume-first rule in `killed` → *Per-dispatch record* (Mode/Outcome)
- 2026-06-12 — boundary-pair procedure expansion (confidence language, task pinning, sequential builds, worktree gate limit, fixed duplicate prologue) → *Boundary pairs*
- 2026-06-12 — no-nested-subagents (fixed-prompt clause; companion `block-nested-agent.sh` hook is repo-local) → *Constant factors* / dispatch prompt
- 2026-06-12 — boundary-pair parallel-dispatch + harvest-before-discard → *Boundary pairs*
- 2026-06-12 — worktree-seeding (APFS `cp -Rc .lake`) → *Boundary pairs* (worktree build caveat)
- 2026-06-12 — model-availability fallback (substitute nearest rung; fable→opus) → *Model assignment map*
- 2026-06-13 — session-start availability check → *Model assignment map*
- 2026-06-13 — Notes discipline: signal-only, not a recap → *Per-dispatch record* (Notes discipline)
- 2026-06-13 — boundary-pair-as-pin-audit → *Boundary pairs*
- 2026-06-13 — Notes-discipline episode-lesson + ~4-line/~600-char cue → *Per-dispatch record* (Notes discipline)
- 2026-06-13 — P-axis variant-flag calibration (companion step-1 trigger is repo-local) → *Task rating* (P)
- 2026-06-13 — boundary-pair consumer-fitness caveat (companion step-4 clause is repo-local) → *Boundary pairs*
- 2026-06-16 — `salvaged` Outcome value → *Per-dispatch record* (Outcome)
- 2026-06-16 — supersession-deletion check **(repo-local** to coordinate-phase.md step-4)
- 2026-06-17 — write-each-row-to-the-discipline-not-its-neighbors → *Per-dispatch record* (Notes discipline)
- 2026-06-18 — `resume`-Mode widening: user-interrupted agents + agentId-from-logs recovery (companion rescue §3 is repo-local) → *Per-dispatch record* (Mode)
- 2026-06-18 — Notes length **gate + reframe**: commit msg = recap, Notes = experiment-meta delta; ~600-char cap now *enforced* (repo-local `notes/check-log-rows.py`, wired into coordinate-phase per-commit step) → *Per-dispatch record* (Notes discipline)
- 2026-06-20 — P-axis "instantiation-into-a-consumer's-slot" level-match calibration: "wire landed brick B into slot C" is P=1 only if B's conclusion is at C's slot's same object/framework level (B *existing* ≠ level-match); a level mismatch is a hidden P=3 leaf (companion step-1 trigger is repo-local) → *Task rating* (P)
- 2026-06-22 — diverse-lens RECON pair for a recurring-mis-pin DESIGN seam (read-only, no worktree; constructive + adversarial-refute lenses, the refute member adjudicates the constructive's open flags) → *Boundary pairs*
- 2026-06-22 — satisfiability-check on deferred-hypothesis leaves: a LANDED+axiom-clean leaf can be mis-targeted if its hypothesis is undischargeable for the consumer **(repo-local** to coordinate-phase.md step-4; companion `DESIGN.md` *Constructibility recon …*)
- 2026-06-22 — un-named-dispatch default (a `name` routes to the async mailbox, no synchronous return) **(repo-local** to coordinate-phase.md step-3; companion rescue §2)
- 2026-07-01 — un-named-dispatch return-mechanism clarification: an un-named dispatch may run in the **background** yet still delivers LANDED/BLOCKED + cost in its completion notification (`<result>`/`<usage>`); only *naming* drops the return — the "synchronous" framing was imprecise **(repo-local** to coordinate-phase.md step-3 + rescue §2; refines the 2026-06-22 entry)
- 2026-07-01 — `resume`-Mode widening: the **spike→resume-to-build** pattern — a *completed* read-only recon/spike agent continued via SendMessage to run the build it de-risked (reuse sorry-free work, don't re-derive); log the spike as a `recon` row, rate the resume row by the build's S/P/B → *Per-dispatch record* (Mode)
- 2026-07-01 — **map v2**: S=1/P=3/B≤2 sonnet boundary cell (pair-priority) + repo-local fragility-zone modifier (producer builds in the zone → opus minimum; replaces phase-wide standing overrides) + raising-S-as-cost-lever → *Model assignment map*
- 2026-07-01 — **versioned rung addenda** (prompt shaping as a logged, versioned, discipline-layer-only treatment; `haiku-a1`/`sonnet-a1`; task-content sharpening stays a committed hand-off edit) → *Constant factors + prompt shaping*
- 2026-07-01 — fable-vs-opus design-pass comparison: route re-route/adjudication recons to fable when reachable + occasional opus-vs-fable diverse-lens recon pairs → *Model assignment map* (recon bullet)
