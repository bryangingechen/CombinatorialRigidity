# Attack short-core — state

Sessions so far: 6 · last session: 2026-10-30 · baseline HEAD: 38f41bf9 · reviews: 1 (S25), 2 (S50), 3 (S56) · **closed 2026-10-30 on the PI's word (S56)**

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
**Closed.** What the track delivers, each claimed proved by hand and read as noted:
- **`d = 4`, `k = 3, 4, 5`** (the brief's deliverable): S1–S21, with S35 for `k = 4, 5`; read by S12, S24, S25
  (review 1). The `P⁴` step: S20's factoring, S19's inputs, base data with (P) and (B) (S21).
- **`k ≥ 4`, every `d`, every `ρ`:** S35, read by S38 and review 2. The every-`ρ` `hins` of `of_openEar_splitOff`
  transcribes there, `D` for 6 (S20 writes it out at `d = 4` only).
- **`k = 3`, `d = 5, 6`:** S28–S33, read by S38.
- **N, the need question** (brief §6): answered no by hand, S52–S53, controlled by S54, read by S55 and review 3.
  From `d = 5` on, a graph past rows 1–5 with a two- or three-body chain has a chain with `k ≥ 4` (free given
  CERT's open ears, or by S35) or a core at `D` (row 9). So the coverage never needs the `k = 3` row there.

**Parked, not proved: G1** (`k = 3`, `d ≥ 7`), no consumer in the coverage by S53. Its last state: G1a, the `d = 7`
cells with no `a`–`b` cut of S46 bridges or S47 runs (thetas, necklaces); G1b, `d ≥ 8`, to start at S47's identity
restricted to motions with `S_b − S_a ∈ H∧V`. **Revival trigger:** CERT's open ears fail at some `d ≥ 7` (S56).

Handed on (S56): the `Pᵈ` short-ear step and `lem:deficiency-core-bound` at every `D` to PD-STEPS; S53 to
PD-COVERAGE; pointers in `notes/Phase42-design.md` §2.3 SHORT and §3.

Open obligations consumed by the `Pᵈ` step (PD-STEPS): 0. G1a, G1b are parked (no consumer, S53), not proved.

## Where it breaks <!-- budget 10 -->
Nowhere on a consumed obligation. N would break if S52 (iv)'s transfer of `lem:deficiency-core-bound` to
`D`-rigidity failed, or if row 9 at `D` needed more than S52's core (its second read found no gap, design doc §2.1).
The parked G1 breaks where it did at session 5: at `d = 7`, S47 (ii)'s no-coloop hypothesis on a run lying on a cycle
of `F/P` (`r_e = dim ρ(F/P − e; u, v) ∈ {D − 1, D}`; on a theta, `span(P₁ − e) + (U₂ ∩ U₃) = Λ²V`); a
2-edge-connected route without free bodies (necklaces), where heights inside a part must move (`δΛ ∈ Z_{ab}⊗E`); and
at `d ≥ 8`, S47's extra term `⟨ω_H∧η̇, S_b − S_a⟩`.

## Tried on this route, and what each rules out <!-- budget 10 -->
- The every-`ρ` form at `k = 3`, `κ ≥ 7 − d` (S2, S5, S26): `ρ = H∧V` refutes it; the proof must use `F`'s `ρ`.
- T5's first branch for N (`def_D(G) > 0` ⇒ no `D`-rigid set): not needed; S52's set avoids `x₁` in either case.
- S52 at `k = 1`: fails at step (iii) (`b` may lie in `W`); the `k = 1` rows at `d ≥ 5` are ONE-EAR's, outside N.

## Next steps <!-- budget 5 -->
None on this track. Resume only on the revival trigger above, at G1b's restricted identity, after a new brief from
the PI. Phase 42's next step is in `notes/Phase42-design.md` (header and §3).

## Worries <!-- budget 5 -->
- S52–S53 are one session's hand proof with two readers (S55, review 3); S35, S41, S45–S48 with one or two each.
- N's "no" is conditional on CERT's open ears at `d` (rows 11–12 for chains with `k ≥ 4`; unsettled at `d ≥ 7`),
  S35 with S20's factoring for `short` rows at `k ≥ 4`, and row 9's formal work at `D` (CARRIER).
- S47's "free" excludes `N[a] ∪ N[b]`; at a single-neighbour `a` the plane `Π_a` is base data (S9), not a point span.

## Signals <!-- budget 2 -->
- Sessions since "Where it breaks" last changed: 1 (G1's break unchanged since session 5, now parked; track closed)
- Open obligations: 0 consumed (G1a, G1b parked by S53, not proved; 2 → 0, a removed consumer, not a moved break)
