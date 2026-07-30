# PENCIL escape-certificate numerics scripts

Exact-ℚ (`fractions.Fraction`, no floating point) numerics scripts backing the Phase 39
PENCIL "kernel (K)" research — the audit trail for the numeric verdicts cited in
`notes/Phase39-design.md` §"W5-L7 research recon" and its "(K) route-1 gate" / "(K)
non-constancy recon" subsections, plus the earlier §R2/N2 escape-certificate reproduce.
Moved here from a session scratchpad (`scratchpad/escape/`) 2026-07-30 for reproducibility,
per the project's *Never commit local machine paths* discipline (checked: none present) —
kept byte-faithful to their original scratch form, not refactored.

Every script is standalone stdlib Python (no third-party dependencies); run with
`python3 <script>.py` from this directory. `pencil_escape.py` and `localtest.py` are
imported as local siblings by the scripts that build on them.

| script | experiment | backs (design doc section) |
|---|---|---|
| `pencil_escape.py` | Core exact-ℚ model: Plücker rigidity-matrix construction (double-subdivision graphs, pencil-generic exact-ℚ sampling, rank/nullspace, escape-test primitives). Also the original §R2/N2 single-habitat escape-certificate reproduce (dbl-subdiv K4). | §R2/N2; imported by every other script here |
| `run_habitats.py` | N7 — escape `M₁` across five structurally distinct chain habitats (H1–H5, chain-end degree pairs (3,3)/(4,3)/(5,3)/(4,4)) | "W5-L7 research recon", Numerics N7 |
| `probe_zero.py` | Finding 1 — parametric sweep of the escape value `E(t) = r·(b̂∧ĉ)` along the meet line `Π(b)∩Π(c)`; shows a genuine in-stratum sign change | "W5-L7 research recon", Finding 1 |
| `localize_zero.py` | Finding 1 continuation — bisects the sign change to an exact interior zero `t* ≈ −2.5311710127`, confirming it sits at a valid rank-84/nullity-1 pencil realization (not a rank-drop degeneracy) | "W5-L7 research recon", Finding 1 |
| `probe_disjunction.py` | Finding 2 — searches for the "all three candidates fail" locus (`r ∈ S^⊥`); confirms the KT disjunction `r ∉ S^⊥` is robust even where `M₁` alone fails | "W5-L7 research recon", Finding 2 |
| `localtest.py` | N8 — the (K) route-1 locality gate: fixes an identical radius-1 local chain block and varies only the far graph (within-habitat and cross-habitat), comparing the normalized escape direction `[r]` and the zero-crossing `t*` | "(K) route-1 gate" |
| `localtest_zeros.py` | N8 companion — faster zero-bisection sweep reusing `localtest.py`'s fixed local block, for the same-local/different-far comparison | "(K) route-1 gate" |
| `n9.py` | N9a/N9b — corank stratification witness (θ(4,4,3), an index-1 minimal-rigid non-cycle habitat) plus canonical-move completeness (every far-vertex move on habitat H1 changes `[r]`) | "(K) non-constancy recon" |

Reproduce commands cited in the design doc, e.g. `python3 notes/scripts/escape/run_habitats.py`
or `python3 notes/scripts/escape/n9.py`, assume the repo root as the working directory.
