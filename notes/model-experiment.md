# Model-tier experiment — repo-local log

**Status:** running. (This line arms the coordinator hook —
`.claude/commands/coordinate-phase.md`'s model-tier step is
conditional on it.)

**Protocol:** [`notes/model-experiment-protocol.md`](model-experiment-protocol.md)
— the portable, repo-agnostic half (axes, assignment map, rubric,
log schema). Keep it byte-identical across participating repos; this
file carries only repo-local state: config, the dispatch log, and
findings. Last protocol sync: 2026-06-09 (from autoformaltemplate).

## Repo-local config

- **Testbed:** Phase 22h (the active phase — the corrected d=3
  assembly), continuing into successor phases of the molecular
  program until concluded.
- **Rungs available:** haiku → sonnet → opus → fable (the Agent
  tool's `model` parameter).
- **Coordinator hook:** `.claude/commands/coordinate-phase.md`
  model-tier step, conditional on this file's Status.
- **Phase-side pointer:** `notes/Phase22h.md` *Decisions made*.
- **Attribution rule at source:** top-level `CLAUDE.md` *Working*
  bullet *Commit attribution* (exact author string + actual-model
  trailer).

## Log

Schema per the protocol. Rubric vector order: gates / scope / Lean
quality / blueprint sync / notes discipline / commit message
(✓ = pass, ✗ = fail, — = not applicable, e.g. doc-only commits).

| # | Task | S/P/B | Model | Mode | Outcome | Rubric | Cost | Notes |
|---|---|---|---|---|---|---|---|---|

## Findings

(accumulate here; distill at phase close per the protocol)
