# Phase 39 W4 (`hcontract`) recon — contraction-arm hybrid gates

Exact-ℚ numerics for the W4 decomposition recon (2026-07-30); results and
the decomposition they feed are in `notes/Phase39-design.md`
§"W4 decomposition recon". Shared infrastructure imported from
`../kbare/kbare_common.py` (model-to-Lean dictionary in its docstring).

- `hybrid_gates.py [nsamples]` — the four gates:
  - **N8** K4 via triangle contraction (the bare-kernel `(K-bare-c)` shape:
    coincident-cluster contracted realization, specialization-glued hybrid);
  - **N9** C4+x,y via vertex removal (the branch-(2b) 6.5-mirror at the W4
    discriminating instance, plus the first direct truth sample of the
    conjecture's target on its forced all-coplanar stratum), with a
    deliberate collinear control exhibiting the rank-29 in-stratum failure
    locus the output motive's fourth conjunct excludes;
  - **N10** C4+x+y+xy via C4 contraction (the `(K-c)` kernel shape: simple
    + feasible contraction, generic-triangle IH, two distinct-anchor
    boundary panels — the first sample beyond N3's single-cluster boundary
    pattern);
  - **N10b** C4+x~1,y~1,xy — the forced-boundary-panel pattern (boundary
    body with two outside anchors; no panel genericity survives there).

Reproduce: `python3 notes/scripts/w4/hybrid_gates.py 6` (seed fixed,
~1 min). All gates assert their targets; the run prints `ALL GATES PASSED`.

- `no_good_search.py [nrandom]` — the W4-L4 residual-branch inhabitant
  search (§"W4-L4 identification recon"): classifies structured families
  (cycle + hub gadgets, cycle + anchored pair, two-hub multi-path) and
  random sparse graphs against the residual habitat (simple, 2EC,
  provably feasible, ∃ proper rigid, no co-1 rigid subgraph, no provably
  Simple∧Feasible contraction), with a three-way feasibility proxy
  (landed-lemma-backed provably-good / provably-bad / middle-zone) and
  the `B#351` coarse-proxy regression check. Result (2026-07-30, two
  runs): **0 candidates** (strong or middle). ~10 min per run.
  **Superseded as evidence** by `nogood_subdiv.py` below — its `|V| ≤ 13`
  cap and `≤ 3`-interior gadget paths both sit below the Ear-Lemma
  threshold, so the habitat it swept was empty for structural reasons.

- `nogood_subdiv.py [--validate | --witness | --min]` — the follow-up
  search over **subdivision** families with arbitrarily long branches
  (2026-08-02). Replaces the `2^|V|` subset sweep by a branch-subset
  enumeration (a rigid `W` is its own 2-core, so it is a union of whole
  branches), and the deficiency oracle by the Lee–Streinu `(6,6)` pebble
  game (`def = 6(|V|−1) − rank_{(6,6)}(5G)`). Result: the `hnoGood'`
  **vacuity conjecture is REFUTED** — 96 inhabitants, smallest `|V| = 19`.
  - `--validate` (~4 min): pebble game vs `kbare_common.exact_deficiency`,
    400/400; `C_k` rigid iff `k ≤ 6`; the Ear-Lemma threshold; branch
    enumeration vs brute force on 120 random 2EC graphs.
  - `--witness` (~1 min): the canonical `|V| = 19` inhabitant, re-checked
    over all `2^19` subsets with both oracles, plus the two deficient
    variants.
  - `--min` (~3 min): 21455-instance minimality sweep + the short-branch
    probe behind the open (SAFE-RES) conjecture.
  - no flag (~4 min): families D/E/F.

  Argument state and consequences: `notes/Pencil-informal.md`
  §"`hnoGood'` vacuity".
