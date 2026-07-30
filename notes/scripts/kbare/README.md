# PENCIL kernel (K-bare) numerics-gate scripts

Exact-ℚ (`fractions.Fraction`, no floating point; rank certification via a
GF(p) lower bound confirmed by an exact-ℚ recheck) numerics scripts backing
the Phase 39 PENCIL "kernel (K-bare)" numerics gate — the audit trail for the
verdicts cited in `notes/Phase39-design.md` §"W5-L7 research recon", residue
(ii) ("(K-bare) numerics gate PASSED 2026-07-30"). Moved here from a session
scratchpad (`scratchpad/kbare/`) 2026-07-30 for reproducibility, per the
project's *Never commit local machine paths* discipline (checked: none
present) — kept byte-faithful to their original scratch form, not refactored.
Independent of the `notes/scripts/escape/` scripts, which back kernel (K)
instead (see that directory's own README).

Every script is standalone stdlib Python (no third-party dependencies).
`gate1.py`/`gate2.py`/`stress_extra.py` import `kbare_common` (and, for
`gate2.py`/`stress_extra.py`, `gate1.sample_spider_pencil`) as local siblings,
so run with `python3 <script>.py` from this directory (the in-script
docstrings say `cd scratchpad/kbare && python3 <script>.py` — that is the
scripts' original scratch-relative reproduce note, left byte-faithful; from
the repo root, `cd notes/scripts/kbare && python3 <script>.py` is the
equivalent).

| script | role | backs |
|---|---|---|
| `kbare_common.py` | Core library: exact-ℚ / GF(p) linear algebra (rref, rank, nullspace), the Plücker/rigidity-matrix model, exact partition-deficiency computation, habitat predicates (`closed_hub_nbhds`, 2EC, no-proper-rigid certification via `f(W) < 0`), the `spider`/`dangerous_gadget`/`split_off` graph constructors, and the pencil-witness sampler primitives. No `__main__`; a pure library. | shared by gate1/gate2/stress_extra |
| `gate1.py` | Gate (1) — bare pencil rank at every infeasible gadget tried: `theta(6,6,6)+center` (19v), its safe split `G'` (18v), `spider(5,5,5)+center` = `G'_dang` (16v), and the 17-vertex dangerous gadget (feasible baseline). Certifies GF(p) rank == target then exact-ℚ-confirms the attaining sample. | "(K-bare) numerics gate PASSED" — the four target-attainment figures (105/105, 100/100, 90/90, 95/95) |
| `gate2.py` | Gate (2) — extension probes from forced-degenerate target-rank `G'`-seeds: re-insert the split vertex `v` at several candidate points (random, midpoint, on-line, center-plane) and check whether the extension attains `G`'s target, for both the `theta(6,6,6)` and `spider(5,5,5)` safe splits, plus a context probe on the *dangerous*-direction 17-vertex gadget. | "(K-bare) numerics gate PASSED" — the "extension from a forced-degenerate seed works in both deficiency branches" finding |
| `stress_extra.py` | Supplementary stress probes (run after gate1/gate2 pass): explains the one gate-2 "on line(a0,b0)" failure as a witness-checker artifact (a coincident-point degeneracy, not a rank failure); a `spider(4,5,5)` deficiency cross-check against the generic baseline; a `theta(7,7,7)/(6,6,7)/(6,7,7)` family sweep; and deeper-degenerate (collinear-hub) `G'` seeds for both safe splits. | "(K-bare) numerics gate PASSED" — the family-sweep figures (120/110/115) and the def-equal-branch genericity caveat |
| `danger.py` | The (K-bare) extension-route recon's danger-zone probe (added 2026-07-30, after the gate; NOT byte-faithful scratch — authored in place): audits the count status of every gate gadget (all count-INDEPENDENT — the gate never sampled the stressed stratum), constructs the count-DEPENDENT infeasible habitat gadget DZ (subdivided `K3,3` + apex hub, 20v/23e, index 1, def 0, spanning circuit), certifies its bare target attainment (114/114), and probes extension from its corank-**2** target-rank `G'` seeds, for both a non-hub-ends split and the KT-faithful hub-end split. | design doc §"(K-bare) extension-route recon" — the dependent-stratum existence + corank-2 extension findings |

Reproduce commands cited in the design doc, e.g. `python3 notes/scripts/kbare/gate1.py`, assume the repo root as the working directory.
