# Model-tier experiment — repo-local log

**Status:** running. (This line arms the coordinator hook —
`.claude/commands/coordinate-phase.md`'s model-tier step is
conditional on it.)

**Protocol:** [`notes/model-experiment-protocol.md`](model-experiment-protocol.md)
— the portable, repo-agnostic half (axes, assignment map, rubric,
log schema). Keep it byte-identical across participating repos; this
file carries only repo-local state: config, the dispatch log, and
findings. Last protocol sync: 2026-06-09 (from autoformaltemplate).
**Local protocol amendment 2026-06-10** (log-row timing rule +
softened change-propagation framing) — propagate to
autoformaltemplate and other participating repos at next sync.

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
| 1 | G4b-impl `minimal_kdof_reduction_full` + (β) restate, 624b585 | 1/2/2 | sonnet | normal | clean | ✓✓✓✓✗✓ | 163k tok / 81 tools / 906s | full-diff read clean; matched §1.49(1) interface exactly. Notes ✗: Hand-off section left stale (still named G4b-impl); coordinator repaired (2-line edit) |
| 2 | G4a-i + G0 `exists_adjacent_degree_two_pair` + `simple_of_isMinimalKDof_of_noRigid`, 6a0346d | 1/2/1 | sonnet | normal | clean | ✓✓✓✓✓✓ | 118k tok / 301 tools / 3529s | bundled G0 + K₂ brick with G4a-i (the checklist's own grouping; G4a-ii needs G0) — scope pass; hand-off updated correctly this time |
| 3 | G4a-ii `exists_chain_data_of_noRigid` (no commit) | 1/2/1 | haiku | probe | BLOCKED | —————— | 143k tok / 69 tools / 1050s | probe one rung below map (sonnet). Hit the real ReducibleVertex→…→ForestSurgery import chain but mis-concluded "needs module restructuring"; correct resolution (place the lemma in ForestSurgery.lean — design §1.49(2) pins the signature, not the file) was its own dismissed option 2. Reverted cleanly, no tree damage. Also returned without the LANDED/BLOCKED-only format. Escalating to sonnet with corrected hand-off |
| 4 | G4a-ii `exists_chain_data_of_noRigid`, d1eef6d | 1/2/1 | sonnet | escalation-retry | clean | ✓✓✓✓✓✓ | 125k tok / 134 tools / 2190s | escalation pair with #3. Signature matches §1.49(2) verbatim; ForestSurgery.lean placement per corrected hand-off; 4-way case split verbose but sound. Pair lesson: haiku failed on a file-placement judgment call, not the proof |
| 5 | T1 `exists_isLink_of_isMinimalKDof_card_three`, 2257053 | 1/2/1 | sonnet | normal | clean | ✓✓✓✓✓✓ | 52k tok / 137 tools / 1905s | compact (71-line) idiomatic proof; rank-formula edge count per §1.48(1); blueprint node + hand-off both correct |
| 6 | T2 `theorem_55_triangle`, b3abd57 | 1/2/1 | sonnet | normal | clean | ✓✓✓✓✓✓ | 141k tok / 84 tools / 786s | 50-line brick reusing the cycle-telescoping infra; good reuse judgment (no Fin m transport) |
| 7 | T3 `exists_triangle_normals`, b6761d1 | 1/2/1 | sonnet | normal | clean | ✓✓✓✓✓✓ | 118k tok / 313 tools / 6702s | hardest leaf so far (the §38 trap zone): 4 private helpers vs whnf explosion; surfaced + documented a NEW quirk (§42 proof-term mismatch, `let`-bound statement params) with FRICTION entry + quirks-index line — exemplary friction review. Same (1/2/1) profile as #5–6 but 3.5× the wall time: the S/P/B axes don't capture defeq-fragility of the target area |

## Findings

(accumulate here; distill at phase close per the protocol)
