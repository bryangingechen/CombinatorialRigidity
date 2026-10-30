# Attack short-core — state

Sessions so far: 2 · last session: 2026-10-30 · baseline HEAD: 3b6dd7e9 · review 1: 2026-10-30 (S25)

## Statement <!-- budget 10 -->
SHORT-CORE (brief §3, as restated at review 1 on the PI's word), for the `P⁴` analogue of
`Graph.X0Attains.of_openEar_three` / `-four` (`k = 5` has no `P³` model). It concludes PD-STATE's
`def:pencil-d-x0-attains` at `d = 4` (planned `X0AttainsGrade K 2`). `V = K⁵`, `3 ≤ k ≤ 5`. Hypotheses:
`hG`; the open ear on `V₁` (`hcover hinj hxV₁ ha hb hab hpath hsep`, edge `ab` allowed); `h₁`, `h₂` read
in `P⁴`; `ρ = relScrews a b` of `G[V₁]`; base data general in S21's sense ((P) `p_a ∦ p_b`, (B) `la ≠ lb`
or `ρ ⊆ Λ²Π_a`), which the step's own choice meets. Conclusion: at general ear data,
`W ⊇ star(y₁) + star(y₃)` implies `W = Λ²V`. The every-`ρ` form is false (S2); the form at every
attaining base datum is open and unused. Unused hypotheses:
- `hG`: it enters only S20's main-picture polynomial.
- the danger numbers: S20 proves the implication at every base datum with (P) and (B).

## Current route and proof sketch <!-- budget 30 -->
**`d = 4`: claimed proved by hand (S1–S21), read by three readers: S6–S8 (S12), S14–S16 (S24),
S19–S21 (S25).** Annihilator form first (S1), then per cell:
- `k = 4, 5`: tangent lemma, every `ρ`, every `κ` (S7, S8).
- `k = 3`, `κ ≤ 2`: tangent lemma, every `ρ` (S6, existence corrected in S12).
- `k = 3`, `κ = 3`: at general base data `ρ ⊆ Λ²Π_a`, so `dim W ≤ 3` (S16, by S9, S14, S15).
- The step (S20): `of_openEar_splitOff` at `D = 10`, the insertion by hand in `Λ²K⁵` (S19), and `hins`
  restricted to (P) and (B), which the base data supply (S21).
- Controls: `p2_path.py` (S17); `t3_kappa.py` (S18: no `κ = 3` among T3's 72 capped cells).
- Formal ports, PD-STATE's and PD-STEPS': `earConfig` and the polynomial lemmas at grade 3, the `P⁴`
  base-data producer with S21's additions, and S15 by `thm:pencil-jj-equality` (S25).

**Secondary target: every `d`, `3 ≤ k ≤ C(d − 1, 2) + 2`** (brief §6). Write `r = dim ρ⁽²⁾` for the
`P²` relative motions of `a, b`. At general base data and `d ≥ 5`, `κ = 3 − r` (S26 (iii)). At `k = 3`
the every-`ρ` form fails wherever `κ ≥ 7 − d`, that is `r ≤ d − 4` (S26 (i)). There the proof must use
the actual `ρ`, starting from `Λ²P(ρ) ⊆ ρ⁽²⁾` (S26 (ii), S10 at every `d`).

Open obligations (3), each consumed by the `Pᵈ` step's `hins` at `d ≥ 5` (PD-STEPS, brief §6):
- **G1** `k = 3`, `d ≥ 5`, `1 ≤ r ≤ 3`. Curves (S22) where `r ≥ d − 3`: at `d = 5`, `r = 3` closes by
  S22's third curve (a sketch), and `r = 2` does when `p_b ∉ Π_a`. Provenance where `r ≤ d − 4`:
  `d = 5`, `r = 1`; `d = 6`, `r ≤ 2`; `d ≥ 7`, every `r`.
- **G2** `4 ≤ k ≤ C(d − 1, 2) + 2`, `d ≥ 5`: S7 and S8's curves through S22's divisibility.
- **G3** `r = 0` (`κ = 3`) at every `d`: S14–S16 with `d − 2` heights give `ρ ⊆ Λ²Π`.

## Where it breaks <!-- budget 10 -->
At `d = 4`, nowhere known (three readings: S12, S24, S25). The first open step of the secondary
target is `d = 5`, `k = 3`, `r = 1` (`κ = 2`). There S22's curves leave `y₁∧y₃∧p_a∧p_b ∈ R`, and no
curve can finish: `ρ = (Π_a + Π_b)∧V` holds both stars with `W` proper (S26 (i)). The actual `ρ` has
`Λ²P(ρ) ⊆ ρ⁽²⁾`, a line in `Λ²K³` (S26 (ii)). That rules out S26's `ρ` but not the cell. The open
step: from `Λ²P(ρ) ⊆ ρ⁽²⁾` and failure `0 ≠ R ∩ J° ⊆ T` (S1 read at `d = 5`), reach a contradiction.
Or find S16's analogue: a partition argument, as in S14, for a `P²` framework in which the relative
motions of `a, b` form a line. T3 holds no such cell in range (S23).

## Tried on this route, and what each rules out <!-- budget 10 -->
- The every-`ρ` form at `κ = 3`, `k = 3`, `d = 4` (S2, S5). It rules out `ρ = Π∧V`, and any `ρ` with
  `ρ + Λ²Π = Π∧V`. This is why `hins` at `k = 3` takes (B) (S20).
- Arguments valid for every `ρ` at `k = 3`, `κ ≥ 7 − d` (S26, review 1). `ρ = (Π_a + Π_b)∧V` fails,
  which rules out S22's third curve, and any curve moving `y₃`, at `d = 5`, `κ = 2` (`log.md`).
- The tangent lemma alone at `κ = 3`, `k = 3`, `d = 4`: retired to `log.md`. S16 closes the cell.

## Next steps <!-- budget 5 -->
1. Existence first. Build, exactly, a `d = 5`, `k = 3` danger cell with `r = 1`, or show that no such
   cell is a danger cell (a partition argument, as in S14). T3's search holds none (S23, `SHORT_PER = 2`).
2. G1 at `d = 5`, `r = 1` by provenance from S26 (ii). Write S22's third curve as a result (`r ≥ 2`).
3. G2 at `d = 5`, `k = 4`: S7's curves read through S22, checked on T3's `d = 5` cells.

## Worries <!-- budget 5 -->
- `d ≥ 7`, `r = 3`: S26 (ii) says nothing there, so S26's `ρ` is not excluded; the input needed is unnamed.
- S9 (iii) at `d − 2` heights (`κ = 3 − r` for `d ≥ 5`) is S9's proof read at more heights, not written
  out as its own result. S26 (iii) uses it.
- S15 by `thm:pencil-jj-equality` still needs a label for the edge `ab` (S24, S25).

## Signals <!-- budget 2 -->
- Sessions since "Where it breaks" last changed: 0 (session 2 moved it to `d = 5`, `k = 3`, `κ = 2`; review 1 struck its curve candidate, S26)
- Open obligations: 3 (trend: 6 → 3 over sessions 1–2, `d = 4`'s six closed; review 1 re-split G1 by `r`, count unchanged)
