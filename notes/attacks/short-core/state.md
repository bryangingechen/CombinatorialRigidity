# Attack short-core — state

Sessions so far: 6 · last session: 2026-10-30 · baseline HEAD: 38f41bf9 · review 1: 2026-10-30 (S25) · review 2: 2026-10-30 (S50)

## Statement <!-- budget 10 -->
SHORT-CORE (brief §3, restated at review 1 on the PI's word) for the `Pᵈ` analogue of
`Graph.X0Attains.of_openEar_three` / `-four`, concluding `Graph.X0AttainsGrade K (d − 2) G` (on master; S39, S44, S51).
Hypotheses: `hG`; the open ear on `V₁` (`hcover hinj hxV₁ ha hb hab hpath hsep`); `h₁`, `h₂` read in `Pᵈ`;
`ρ = relScrews a b` of `G[V₁]`. Conclusion: at general ear data, `W ⊇ star(y₁) + star(y₃)` implies `W = Λ²V`.
At a danger cell this is the step's conclusion itself: it fails exactly when `G` does not attain (S41).
- `k ≥ 4`: every `ρ`, every base datum, every `d` (S35).
- `k = 3`: base data general in S21's sense; at `d ≥ 5` also S31's and S33's factors. Every-`ρ` iff `κ < 7 − d` (S32).
Unused: `hG` (only S20's main-picture polynomial); the danger numbers outside S31's path-length step and S45.

## Current route and proof sketch <!-- budget 30 -->
**`d = 4`: claimed proved by hand (S1–S21), read by three readers (S12, S24, S25).** Also S35 (`k = 4, 5`) and
S31–S33 (`k = 3`).

**Secondary target, every `d`** (brief §6):
- `k ≥ 4`: S35. `k = 3`, `d ≤ 6`: S28–S33. Read by S38.
- `k = 3`, `d ≥ 7` (G1): partial, S40–S48 (`d = 7`: bridges, runs of free bodies, `G[V₁]` a cycle). **Parked**: see N.

**N, the need question (brief §6): answered no by hand, S52–S53, controlled by S54.**
- S52: for any `D ≥ 3`, a sparse `G` with an open ear of `k ≥ 2` bodies and `s_D(V₁) ≤ 0` has a core at `D` (row 9):
  Theorem S's branch `X₀ = {x₁}` read at `D`, the maximal `D`-rigid set avoiding `x₁`; `x₂ ∉ W` keeps `x₁` to one
  neighbour in `W`; `lem:deficiency-core-bound` (2) and `-additive-core` (2) carry over (planar counts, plus
  `v_D = (D/3)v₃ − (D/3 − 1)d_G`).
- S53: with every chain at most four edges, `s_D(V₁) ≤ e(4 − D/3) − 4 < 0` at `D ≥ 12`. So from `d = 5` on, a graph
  past rows 1–5 with a three-body chain has a chain with `k ≥ 4` (free: CERT, S35) or a core at `D` (free: row 9,
  formal). No graph needs the `k = 3` row; 42c's range and the tier below are not used.
- S54: on T5's ten cores, paths of 1–4 and 1–5 edges, `d = 3..8`, every assertion holds (caps in S54).
- Read by S55: every step confirmed, two repairs made in place (2-edge-connectivity, the `D = 6` Lean pins).

**By brief §6's *Outcome*, G1 has no consumer in the coverage and is parked as an obligation of the every-`d` tier.**
Its last state (for whoever resumes it): G1a `d = 7` cells with no `a`–`b` cut of S46 bridges or S47 runs (thetas,
necklaces); G1b `d ≥ 8`, S47's identity restricted to motions with `S_b − S_a ∈ H∧V` first.

Open obligations consumed by the `Pᵈ` step (PD-STEPS): 0 by piece. G1a, G1b are parked (no consumer, S53), not proved.

## Where it breaks <!-- budget 10 -->
Nowhere on a consumed obligation: `d = 4` is claimed proved, and N's answer removes `k = 3`, `d ≥ 7` from the coverage.
The parked G1 breaks where it did at session 5: at `d = 7`, S47 (ii)'s no-coloop hypothesis on a run lying on a cycle
of `F/P` (`r_e = dim ρ(F/P − e; u, v) ∈ {D − 1, D}`; on a theta, `span(P₁ − e) + (U₂ ∩ U₃) = Λ²V`); a
2-edge-connected route without free bodies (necklaces), where heights inside a part must move (`δΛ ∈ Z_{ab}⊗E`); and
at `d ≥ 8`, S47's extra term `⟨ω_H∧η̇, S_b − S_a⟩`. N itself would break if S52 (iv)'s transfer of
`lem:deficiency-core-bound` to `D`-rigidity failed, or if row 9 at `D` needed more than S52's core (its second read
found no gap, design doc §2.1).

## Tried on this route, and what each rules out <!-- budget 10 -->
- The every-`ρ` form at `k = 3`, `κ ≥ 7 − d` (S2, S5, S26): `ρ = H∧V` refutes it; the proof must use `F`'s `ρ`.
- T5's first branch for N (`def_D(G) > 0` ⇒ no `D`-rigid set): not needed; S52's set avoids `x₁` in either case.
- S52 at `k = 1`: fails at step (iii) (`b` may lie in `W`); the `k = 1` rows at `d ≥ 5` are ONE-EAR's, outside N.

## Next steps <!-- budget 5 -->
1. Stop for the PI (brief §6 *Outcome*): N answered no at `d ≥ 5`, G1 parked. A review is due (S53 ends the track's
   consumed scope).
2. If the PI keeps the track: the PI's call between closing it (deliverable met at `d = 4`) and resuming G1 for the
   every-`d` tier, which would start at G1b's restricted identity.

## Worries <!-- budget 5 -->
- S52–S53 are one session's hand proof with one reader (S55); S35, S41, S45–S48 one reader each. S52 (iv) reads
  `-core-bound` at `D`; its Lean is at `D = 6` only (S55).
- N's "no" is conditional on CERT's open ears at `d` (rows 11–12 for chains with `k ≥ 4`; unsettled at `d ≥ 7`),
  S35 with S20's factoring for `short` rows at `k ≥ 4`, and row 9's formal work at `D` (CARRIER).
- S47's "free" excludes `N[a] ∪ N[b]`; at a single-neighbour `a` the plane `Π_a` is base data (S9), not a point span.

## Signals <!-- budget 2 -->
- Sessions since "Where it breaks" last changed: 1 (G1's break unchanged since session 5, now parked)
- Open obligations: 0 consumed (G1a, G1b parked by S53, not proved; 2 → 0, a removed consumer, not a moved break)
