# Model-tier experiment — repo-local log (CONCLUDED)

**Status:** concluded (2026-07-09).

The two-repo model-tier dispatch experiment (CombinatorialRigidity +
enharmonic, ~890 rated dispatches) is **concluded**. Its findings are
promoted into the standing **Dispatch playbook** section of
`.claude/commands/coordinate-phase.md` (the S/P/B rating, the rung map,
the fragility-zone floor, raising-S-as-cost-lever, the verification
tiers). New coordinator **exceptions** — escalations, probes,
BLOCKED/killed dispatches, gate-invisible defects caught in
verification — go to `notes/dispatch-log.md` (exception-only; routine
clean dispatches are not logged). This file is a **thin archival
pointer**; the detail below is history, not live process.

**This is a repo-local sync of template HEAD `7b6eab8`**, which
concluded the experiment upstream and rebuilt the coordinator command
around the promoted playbook.

## Archive (frozen audit trail)

The full per-dispatch log — the grandfathered **rows 1–189**, the
**Phase 23a–23h rows 190–670**, the post-Phase-23 cleanup-round rows
**671–717**, **Phase 24 rows 718–723**, **Phase 25 rows 724–739**,
**Phase 26 rows 740–745**, and the post-Phase-26 program-closing
cleanup-round rows **746–754**, each with its session-close config
notes and *Findings* close-outs — lives in
[`notes/model-experiment-archive.md`](model-experiment-archive.md)
(search-target, not read on load). The portable protocol (axes,
assignment map, rubric, log schema) is
[`notes/model-experiment-protocol.md`](model-experiment-protocol.md),
retained as an archival reference.

## Config history (archival)

Preserved for the audit trail; not live process. The molecular program
(Phases 17–26) was the testbed and closed 2026-07-07; the experiment
ran paused-and-armed through the post-Phase-26 cleanup round, then
concluded here at the 2026-07-09 template sync.

- **Rungs:** haiku → sonnet → opus → fable (the Agent tool's `model`
  param). The rung map now lives in the coordinator command's *Dispatch
  playbook*.
- **Fragility-zone list** (now carried live in the coordinator
  command's fragility-zone bullet): `Molecular/AlgebraicInduction/`
  (esp. `CaseIII/` + `Theorem55.lean`), `Molecular/RigidityMatrix/`,
  and any ScrewSpace-carrier-touching edit — the §38 / heavy-`whnf`
  defeq-fragile zone. Producer builds there → opus minimum; mechanical
  refactors / doc edits there stay mapped. The combinatorial side
  (`Molecular/Induction/`, incl. `ForestSurgery/`) is NOT in the zone.
- **map v2** (2026-07-01): the S=1/P=3 sonnet boundary cell, the
  fragility-zone modifier, and the versioned rung addenda replaced the
  Phase-23 blanket OPUS-ONLY override — all now folded into the
  *Dispatch playbook*.
- **Availability check** (user-confirmed from 2026-07-02): no probe
  dispatches; the session-start check-in asks the user which rungs are
  available and blocks until answered. Retained in the rebuilt command.
- **Log-row length gate:** `notes/check-log-rows.py` enforced the
  protocol's ~600-char Notes cap on the (now archived) live table; it
  can be adapted to audit `notes/dispatch-log.md` Notes cells (see that
  file's header).
- **Attribution:** top-level `CLAUDE.md` *Working → Commit attribution*
  (exact author string + actual-model trailer).
