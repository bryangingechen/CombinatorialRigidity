#!/usr/bin/env bash
#
# PreToolUse hook (Agent matcher): deny Agent-tool calls made from
# INSIDE a subagent — i.e. block nested subagent spawning — while
# leaving the coordinator session's own top-level dispatches
# untouched. Detection: the hook input carries an `agent_id` field
# only in subagent context (top-level/main-conversation calls have
# none).
#
# Why mechanical: agent-teams mode (CLAUDE_CODE_EXPERIMENTAL_AGENT_
# TEAMS, kept on for the SendMessage kill-resume protocol —
# model-experiment rows 64–65) re-enables the nesting that standard
# subagents forbid by design. A dispatched build agent fanning out
# its own sub-subagents (observed 2026-06-12, model-experiment row
# 74, deep in a 10+-compaction sitting) shares the working tree and
# the one-build-at-a-time discipline with its parent, confounds the
# model-experiment's per-rung attribution and cost numbers, and the
# prompt-level "do all work yourself" clause degrades exactly where
# this bites (compaction; the row-17 lesson: prompts don't survive
# compaction, hooks do).
#
# SendMessage (agent-teams resume/communication) is a different
# tool and is unaffected.

input=$(cat)
agent_id=$(printf '%s' "$input" | jq -r '.agent_id // empty')

if [ -n "$agent_id" ]; then
  printf '%s\n' '{"hookSpecificOutput": {"hookEventName": "PreToolUse", "permissionDecision": "deny", "permissionDecisionReason": "Nested subagent spawning is blocked in this project (block-nested-agent.sh): dispatched agents do their own work in one sitting — see the fixed dispatch prompt. If the task will not fit, shrink the deliverable and/or return BLOCKED; the coordinator handles decomposition."}}'
  exit 0
fi

exit 0
