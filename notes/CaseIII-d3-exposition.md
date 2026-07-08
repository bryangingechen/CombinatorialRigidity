# Case III at d=3 — worked-case exposition (plan)

**Status: DONE (landed at Phase-27 close, 2026-07-08).** The A2-x worked-case
exposition landed per the 5-step plan below: the `sec:…-claim612` section lead
reframed as the d=3 worked case, the capstone node
`lem:case-III-candidate-dispatch-d3` pinning `case_III_candidate_dispatch`, and
a navigational `\cref` (not a `\uses` edge) from `lem:case-III`. Ledger entry
recorded (`notes/BlueprintExposition.md`, flavor (b)). Retained as the plan
doc / audit trail. Originally a blueprint exposition-writing task spun out of
the Phase-26 cleanup round's A2 (`notes/Phase26-cleanup.md`, item A2-x); sibling
to `notes/FormalizationRetrospective.md` (both exposition deliverables, not
cleanup hygiene). Owner-adjudicated 2026-07-07.

## Purpose

Present Katoh–Tanigawa's Case III at `d = 3` (Lemma 6.10, the three-panel candidate
dispatch of §6.4.1) as an explicit **worked concrete case** in the blueprint, framed
as the accessible on-ramp to the general Lemma 6.13 (`lem:case-III`, §6.4.2) that the
actual proof runs on. This mirrors KT's own concrete-first pedagogy.

## Why it's worth doing — the d=3 case is *genuinely* simpler

Not a mechanical specialization of the general proof. The general form carries three
substantial pieces of machinery the d=3 case does not need at all, so the general
form does **not** supersede the d=3 case on the clarity axis:

| Axis | d=3 (Lemma 6.10, §6.4.1) | general-`k` (Lemma 6.13, §6.4.2) |
|---|---|---|
| Dispatch | fixed `fin_cases u : Fin 3` over three candidates M₁/M₂/M₃ | discriminator over an index `i ∈ {0..d}` on a **length-`d` chain** `v₀…v_d` |
| Transport | M₃ needs **one** relabel (`Equiv.swap a v`) | iterated transport of `ρ₀` along the chain, a column op at **each** interior vertex |
| Extraction | none — the base triangle gives the three panels | the **chain-vs-short-cycle dichotomy** (Lemma 4.6/4.8) + the cycle family (Lemma 5.4); *present in the general proof, vacuous at d=3* |
| Rank cert | direct three-arm certification | the `fromBlocks A 0 C D` certificate with the moving-member bookkeeping (the "member-mapping wall") |
| Carrier | six joins of four points in `⋀²ℝ⁴` (6-dim, visualizable; Lemma 2.1 concrete) | `(k+2 choose 2)` joins in `⋀^k(ℝ^{k+2})` |

The concrete case carries the core idea — three candidate placements, one full-rank by
the six-join span — without the chain / dichotomy / block scaffolding a reader would
otherwise have to absorb all at once.

## Decision: KEEP the d=3 dispatch + write it up

- **KEEP** `case_III_candidate_dispatch` and its d=3-only helper chain: `exists_complementIso…`
  (d=3), `exists_line_data_of_homogeneousIncidence` (d=3),
  `exists_homogeneousIncidence_of_normals` (d=3), `omitTwoExtensor_eq_extensor_kept` (d=3),
  `exists_independent_perp_pair` (d=3), and the arm producers
  `case_III_arm_realization{,_M2,_M3}` (the arms are also used generally). It is
  **not** dead-code-to-retire — it is a worked case with real pedagogical value.
  (It is unpinned and has zero Lean callers, but that is correct for a
  worked-example / illustration node — a demonstration, not a proof step.)
- The `sec:…-claim612` blueprint prose is the base and is largely written already
  (the p1/p2/p3 candidate narrative, the block-full-rank↔perp criterion, the six-join
  span). The task is to **reframe + strengthen the connective tissue** to the general
  case and to **ground the concrete dispatch**, not to write from scratch.

## Execution steps (for a future agent / `/coordinate-phase`)

1. **Ground the concrete dispatch.** Add a blueprint node pinning
   `case_III_candidate_dispatch` (the concrete three-panel dispatch) as the worked-case
   capstone. Honestly green (proven); a dep-graph leaf (worked example) — which is
   correct, not a defect. Consider also pinning `case_III_arm_realization{,_M2,_M3}` for
   the three arms.
2. **Reframe the section lead.** `sec:…-claim612` gets a lead paragraph: "the concrete
   `d=3` case (KT §6.4.1); the general proof (`lem:case-III`, Lemma 6.13) threads the
   same three-candidate idea along a length-`d` chain; presented here as the accessible
   worked case." State the simplicity gains (the table above, in prose).
3. **Cross-link general ↔ concrete.** `lem:case-III`'s prose points to the worked case
   for intuition via a **prose `\cref`**, *not* a `\uses` edge — the general proof does
   not depend on the d=3 dispatch. (Keep this distinction crisp: `\uses` = logical
   dependency; `\cref` in prose = navigational pointer.)
4. **Keep the existing green nodes** (block-iff-perp, eq644, p2/p3-placement, r-nonzero,
   the `splitOff-*-relabel` lemmas, `claim612`→`_gen`) — they ground the concrete
   narrative and stay.
5. **Gates:** `blueprint/verify.sh` (checkdecls) + `blueprint/lint.sh` + `lake lint`.
   Vocabulary gate applies — no `brick/motive/producer/stratum/green-modulo`, no phase
   codes, in the prose (`blueprint/CLAUDE.md`).

## Do NOT confuse with the general-path wiring fix

Independent task: the *general* Claim 6.12 (`case_III_claim612_gen`) is **live** and
needs its missing `\uses` edge — that is `notes/Phase26-cleanup.md` **A2-w**, a small
honesty fix, and is **not** part of this exposition write-up.

## Pointers

- Lean: `CombinatorialRigidity/Molecular/AlgebraicInduction/CaseIII/Realization.lean`
  (`case_III_candidate_dispatch`, ~324–655); `CaseIII/Arms.lean`
  (`case_III_arm_realization{,_M2}`); `CaseIII/Relabel/Arm.lean`
  (`case_III_arm_realization_M3`); `RigidityMatrix/Claim612.lean` (the d=3 helpers).
- Blueprint: `blueprint/src/chapter/algebraic-induction/case-iii.tex`, `sec:…-claim612`
  (~595–1118), and `lem:case-III` (1312).
- Related: `notes/BlueprintExposition.md` (the source-side exposition ledger — this is a
  sibling worked-case task; consider adding a ledger entry when it lands).
