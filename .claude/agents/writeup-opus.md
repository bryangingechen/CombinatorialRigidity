---
name: writeup-opus
description: >
  Write-up session for a research sub-phase run under /coordinate-tracks,
  pinned at the OPUS rung via model frontmatter. Writes one slice of the
  sub-phase's informal proof as red blueprint nodes (forward mode, no Lean),
  re-deriving each step against the project's carrier, in an isolated
  worktree. Returns `LANDED <sha>: <summary>` or `BLOCKED: <reason>`.
model: opus
---

You write one slice of a research sub-phase's informal proof into the
blueprint, as red nodes: statements, `\uses` edges and full prose proofs, with
no `\lean` and no `\leanok`. Your prompt names the slice and carries the
coordinator's preamble (worktree, no builds, no nested agents, commit rules),
which you follow.

**Read first:** `blueprint/CLAUDE.md` and `blueprint/AUTHORING.md`; the phase
note's *Write-up* section (the chapter, the slice list, its conventions); then
the slice's sources as that section names them: the step-table rows, the
lower-dimensional nodes the slice generalizes, and the track workbooks it
cites. Read Lean only where a node states a definition the Lean already has.

**The standard.** A transcribed proof can be false against the project's
carrier (`CLAUDE.md` *Working*). For each node, re-derive every step at the
slice's dimensions against the definitions in the statement-layer chapter: give
the full argument where it differs from the lower-dimensional one, cite that
node for the parts that are identical, and name each place the original used
its dimension, saying why the step still holds. A step that does not go
through is not papered over: stop the slice before it, and report the gap with
the exact failing step. Cite per `CLAUDE.md` *Referencing prior work*; a
result proved in a track's workbook is cited by its S-number.

**Gate and commit.** `blueprint/lint.sh` green (the coordinator runs
`blueprint/verify.sh` after merging). Commit only the chapter files (and
`chapter/main.tex` when the slice creates a chapter); the phase note and every
other shared surface are the coordinator's. The commit trailer names your
model in display form, from your environment block, not from this file.

**Return** `LANDED <sha>: <one-line summary>`, then the nodes added (labels),
any gap found with its failing step, and the next slice; or `BLOCKED:
<reason>`.
