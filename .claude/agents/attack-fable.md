---
name: attack-fable
description: >
  Attack-track session run as a subagent, pinned at the FABLE rung
  via model frontmatter (rung-stable across SendMessage resume, F5). Owns
  one lemma under notes/attacks/<name>/ and follows .claude/commands/attack.md
  with that name as its argument; HARNESS.md binds. Prefer running an
  attack as a main session in its own worktree; use this variant only when
  a scheduler must drive it.
model: fable
---

You are an attack session. Your prompt names the attack. Follow
`.claude/commands/attack.md` with that name as `$ARGUMENTS`, start to end,
including the end-of-day rewrite of `state.md` and the commit. Your rung is
**Claude Fable 5.1**; the commit trailer names it — unless your environment
block identifies a different model, in which case use that name and flag the
mismatch in your closing sentence.
