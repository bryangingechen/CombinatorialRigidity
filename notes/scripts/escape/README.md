# PENCIL escape-certificate numerics scripts

Exact-ℚ (`fractions.Fraction`, no floating point) numerics scripts backing the Phase 39
PENCIL "kernel (K)" research — the audit trail for the numeric verdicts cited in
`notes/Phase39-design.md` §"W5-L7 research recon" and its "(K) route-1 gate" / "(K)
non-constancy recon" subsections, plus the earlier §R2/N2 escape-certificate reproduce.
Moved here from a session scratchpad (`scratchpad/escape/`) 2026-07-30 for reproducibility,
per the project's *Never commit local machine paths* discipline (checked: none present).

**Start from `notes/scripts/README.md`** — the harness-wide primitive index, layering
map, invocation table, and conventions. This file is the per-driver description list
for this directory.

Every script is stdlib-only Python (no third-party dependencies). Run from the **repo
root** as `python3 notes/scripts/escape/<script>.py`; the canonical `scriptpath`
bootstrap (2026-08-05) makes the working directory irrelevant. `pencil_escape.py` and
`localtest.py` are the modules the other scripts here build on; the exact-ℚ linear
algebra and Plücker primitives they used to define now live in
`notes/scripts/exactcore.py` and are re-exported from `pencil_escape`.

| script | experiment | backs (design doc section) |
|---|---|---|
| `pencil_escape.py` | Core exact-ℚ model **library** (no `__main__` — running it produces no output): Plücker rigidity-matrix construction, double-subdivision graphs, base graphs `K4`/`K5_minus_matching`, pencil-generic exact-ℚ sampling, escape-test primitives. | §R2/N2; imported by every other script here |
| `run_habitats.py` | N7 — escape `M₁` across five structurally distinct chain habitats (H1–H5, chain-end degree pairs (3,3)/(4,3)/(5,3)/(4,4)) | "W5-L7 research recon", Numerics N7 |
| `probe_zero.py` | Finding 1 — parametric sweep of the escape value `E(t) = r·(b̂∧ĉ)` along the meet line `Π(b)∩Π(c)`; shows a genuine in-stratum sign change | "W5-L7 research recon", Finding 1 |
| `localize_zero.py` | Finding 1 continuation — bisects the sign change to an exact interior zero `t* ≈ −2.5311710127`, confirming it sits at a valid rank-84/nullity-1 pencil realization (not a rank-drop degeneracy) | "W5-L7 research recon", Finding 1 |
| `probe_disjunction.py` | Finding 2 — searches for the "all three candidates fail" locus (`r ∈ S^⊥`); confirms the KT disjunction `r ∉ S^⊥` is robust even where `M₁` alone fails | "W5-L7 research recon", Finding 2 |
| `localtest.py` | N8 — the (K) route-1 locality gate: fixes an identical radius-1 local chain block and varies only the far graph (within-habitat and cross-habitat), comparing the normalized escape direction `[r]` and the zero-crossing `t*`. Also the home of **`meet_line`**, which the whole `w4/` stack imports; since 2026-08-06 it **signals** a parallel-normal pair with a zero direction instead of raising `UnboundLocalError` (`../README.md` *Harness debt* item 1), so **every caller must test `d`** | "(K) route-1 gate" |
| `localtest_zeros.py` | N8 companion — faster zero-bisection sweep reusing `localtest.py`'s fixed local block, for the same-local/different-far comparison | "(K) route-1 gate" |
| `n9.py` | N9a/N9b — corank stratification witness (θ(4,4,3), an index-1 minimal-rigid non-cycle habitat) plus canonical-move completeness (every far-vertex move on habitat H1 changes `[r]`) | "(K) non-constancy recon" |

Reproduce commands cited in the design doc, e.g. `python3 notes/scripts/escape/run_habitats.py`
or `python3 notes/scripts/escape/n9.py`, assume the repo root as the working directory.
