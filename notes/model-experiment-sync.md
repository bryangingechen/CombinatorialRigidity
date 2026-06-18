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
