# PENCIL kernel (K-bare) numerics-gate scripts

Exact-ℚ (`fractions.Fraction`, no floating point; rank certification via a
GF(p) lower bound confirmed by an exact-ℚ recheck) numerics scripts backing
the Phase 39 PENCIL "kernel (K-bare)" numerics gate — the audit trail for the
verdicts cited in `notes/Phase39-design.md` §"W5-L7 research recon", residue
(ii) ("(K-bare) numerics gate PASSED 2026-07-30"). Moved here from a session
scratchpad (`scratchpad/kbare/`) 2026-07-30 for reproducibility, per the
project's *Never commit local machine paths* discipline (checked: none
present). A **parallel** model layer to the `notes/scripts/escape/` scripts,
which back kernel (K) instead (see that directory's own README); the two
carriers' samplers and rigidity-matrix builders genuinely differ — see
`notes/scripts/README.md` *Divergences*.

**Start from `notes/scripts/README.md`** — the harness-wide primitive index,
layering map, invocation table, and conventions. This file is the per-driver
description list for this directory.

**The 2026-08-06 re-baselining round did not reach this directory, and that is
a fact about the closures, not an oversight.** All four harness-debt items were
cleared by slices S1–S3 (`../README.md` *Harness debt* → the **CLOSED** block);
`kbare/` sits outside every one of their import closures, so no driver here was
edited and no figure here moved. The round's standing rules still apply to
**new** work: a new sampler or battery asserts the composite genericity guard
`repin.star_generic` rather than a star-rank test alone, and a new guard owes
an adversarial witness it must reject (§4 conventions 1 and 6). Note this
directory's own `kbare_common.plane_basis` is the third member of the
degenerate `plane_basis` family (*Divergences*) — untouched by the round, and
new work uses `repin.robust_plane_basis`.

Every script is stdlib-only Python (no third-party dependencies). Run from the
**repo root** as `python3 notes/scripts/kbare/<script>.py`; the canonical
`scriptpath` bootstrap (2026-08-05) makes the working directory irrelevant, so
the in-script docstrings' `cd scratchpad/kbare && …` reproduce notes are
historical only. The exact-ℚ linear algebra and Plücker primitives
`kbare_common` used to define now live in `notes/scripts/exactcore.py` and are
re-exported from `kbare_common` under their original names (`rank_exact` is
`exactcore.rank`), so `from kbare_common import *` is unchanged.

| script | role | backs |
|---|---|---|
| `kbare_common.py` | Core library: exact-ℚ / GF(p) linear algebra (rref, rank, nullspace), the Plücker/rigidity-matrix model, exact partition-deficiency computation, habitat predicates (`closed_hub_nbhds`, 2EC, no-proper-rigid certification via `f(W) < 0`), the `spider`/`dangerous_gadget`/`split_off` graph constructors, and the pencil-witness sampler primitives. No `__main__`; a pure library. | shared by gate1/gate2/stress_extra |
| `gate1.py` | Gate (1) — bare pencil rank at every infeasible gadget tried: `theta(6,6,6)+center` (19v), its safe split `G'` (18v), `spider(5,5,5)+center` = `G'_dang` (16v), and the 17-vertex dangerous gadget (feasible baseline). Certifies GF(p) rank == target then exact-ℚ-confirms the attaining sample. | "(K-bare) numerics gate PASSED" — the four target-attainment figures (105/105, 100/100, 90/90, 95/95) |
| `gate2.py` | Gate (2) — extension probes from forced-degenerate target-rank `G'`-seeds: re-insert the split vertex `v` at several candidate points (random, midpoint, on-line, center-plane) and check whether the extension attains `G`'s target, for both the `theta(6,6,6)` and `spider(5,5,5)` safe splits, plus a context probe on the *dangerous*-direction 17-vertex gadget. | "(K-bare) numerics gate PASSED" — the "extension from a forced-degenerate seed works in both deficiency branches" finding |
| `stress_extra.py` | Supplementary stress probes (run after gate1/gate2 pass): explains the one gate-2 "on line(a0,b0)" failure as a witness-checker artifact (a coincident-point degeneracy, not a rank failure); a `spider(4,5,5)` deficiency cross-check against the generic baseline; a `theta(7,7,7)/(6,6,7)/(6,7,7)` family sweep; and deeper-degenerate (collinear-hub) `G'` seeds for both safe splits. | "(K-bare) numerics gate PASSED" — the family-sweep figures (120/110/115) and the def-equal-branch genericity caveat |
| `danger.py` | The (K-bare) extension-route recon's danger-zone probe (added 2026-07-30, after the gate; NOT byte-faithful scratch — authored in place): audits the count status of every gate gadget (all count-INDEPENDENT — the gate never sampled the stressed stratum), constructs the count-DEPENDENT infeasible habitat gadget DZ (subdivided `K3,3` + apex hub, 20v/23e, index 1, def 0, spanning circuit), certifies its bare target attainment (114/114), and probes extension from its corank-**2** target-rank `G'` seeds, for both a non-hub-ends split and the KT-faithful hub-end split. | design doc §"(K-bare) extension-route recon" — the dependent-stratum existence + corank-2 extension findings |
| `optc.py` | The user-adjudicated ("C: cheap numerics extensions + A") option-C probes (added 2026-07-30, authored in place; `python3 optc.py c1\|c2\|c3`): C1 adversarial deeper-degenerate corank-2 `G'` seeds at DZ (chain-local degenerations fall below `target(G')` — excluded by the rank antecedent; hub-coplanar stratum target-compatible, picture unchanged); C2 the index-2 danger-gadget search over subdivided cubic skeletons + apex (`K3,3` arithmetically excluded; cube `Q3`/Wagner `V8` 24v hits certified exactly, Petersen skeleton-level) with a mini-gate showing bare attainment 138/138 and the same extension picture from corank-**3** `G'` seeds; C3 the corank-2 failure-locus map (every sampled on-`line(a,b)` point fails by exactly 1, 0/179 exact-ℚ-confirmed off-line failures — the failure set looks exactly like the line). | design doc §"(K-bare) extension-route recon" — the "Option-C results" block |

Reproduce commands cited in the design doc, e.g. `python3 notes/scripts/kbare/gate1.py`, assume the repo root as the working directory.
