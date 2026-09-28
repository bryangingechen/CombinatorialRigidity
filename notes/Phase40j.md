# Phase 40j — PENCIL-X0 / SPLITOFF: splitting off a body of degree two at non-adjacent neighbours (work log)

**Status:** ✓ complete (opened design-first, built and closed 2026-09-28). SPLITOFF, STEPS' sixth
group (`notes/Phase40-design.md` §3 STEPS), proved the split-off step at a body `x` of degree two
whose neighbours `a ≁ b`, the one-body ear `a − x − b` on `V₁`: if `X₀` attains at
`G″ = G.splitOff (x 0) a b (e 0)` (`G` with `x` suppressed) and
`deficiencyMerged₃(G[V₁]; a, b) + 5 ≤ def₃(G[V₁])` (Step MC11's `δ ≥ 5`), then `X₀(G)` attains
((MC-31)). No new mathematics. **Next: STEPS' CONTRACT-A group, not yet opened** — see *Hand-off*.

## Current state

**Closed.** Two build commits (B1 `0fdf5d5a`, B2 `2fc2c02c`) and the close landed. The five nodes of
`main-component.tex` §`sec:main-component-splitoff` are green: `lem:pencil-curve-limit`,
`lem:pencil-splitoff-special-rank`, `lem:pencil-splitoff-flexes`, `lem:pencil-splitoff-curve` and
`thm:pencil-x0-splitoff`, with two unpinned remarks after the theorem (the exposition-ledger entry,
and (MC-31)'s bound within one for `δ ≤ 4`, not formalized).

The Lean is `Molecule/Pencil/MainComponent/SplitOff.lean` (its module docstring lists the
statements), importing `Orbit.lean` only, with the general pieces in `Bridge.lean`, `Ear.lean`,
`Cut.lean`, `Carrier.lean` and the mirror `Mathlib/Algebra/MvPolynomial/Polynomial.lean`
(`MvPolynomial.polynomial_eval_aeval`, upstream-eligible). The spikes (`scratch/40j/`, gitignored
and local to this checkout) are consumed.

**Headline axioms, re-verified at the close** on 26 declarations: the eighteen `formalization.yaml`
main results and the eight pins of the five nodes. All 26 are exactly
`[propext, Classical.choice, Quot.sound]`; none uses `sorryAx`. *Measured, script not retained*:
one `#print axioms` line per declaration under `import CombinatorialRigidity`, run with `lake lean`
on the fully built tree (a full `lake build` first: 2 985 jobs, 0 warnings).

- **Satisfiability (not landed).** `C₇` with ear `6 − 0 − 1` (`V₁ = V ∖ {0}`): (H) and every
  structural hypothesis, `¬ Adj 6 1` included, kernel-checked in the recon's instance spike. `hδ` is
  measured (script not retained): `def₃(P₆) = 5` with merged value `0`, so `δ = 5`. A non-cycle
  instance, θ(1,1,6) at the middle body of its long path, also has `δ = 5` (measured only).
- **Faithfulness** (against (MC-31)): `of_splitOff` is its `δ ≥ 5` conclusion; `hδ` is literally
  Step MC11's `δ ≥ 5`. `ℓ₀(G″) = 3 + def₂(G″)` is discharged inside the step by BRIDGE. (H) is
  asked at `G` only, as in 40g–40i; nothing at `G″` beyond attainment, nothing at `G′`.

## Architectural choices made up front

- **The route** (the recon's verdict; as landed, the *SPLITOFF done* paragraph of
  `notes/Phase40-design.md` §3 STEPS): (MC-28) as a count of motion spaces, (MC-29) as two landed
  deficiency lemmas composed, (MC-30)(i) as a dimension count on the lifting system's kernel, then a
  polynomial line of pictures and flexes back to a main picture and the curve-limit lemma.
- **Three carrier-forced, proof-level deviations** (recorded in the blueprint proofs and the remark
  after the theorem): the flexes of `G′` are the lifting system's kernel, not `L_{G′}` (`G′` may
  have bodies of degree 1); the special point is not admissible, so the curve is necessary; the
  workbook's rational `P(t)` is a polynomial line, and main-ness along it is `G`'s main-picture
  polynomial on the picture line, nonzero at `t = 1`.
- **The coordinator's calls** (2026-09-28, under the PI's session-start "follow precedent"; not PI
  decisions, so not in `notes/pencil/adjudications.md`):
  1. no new mathematics, so 40j opened directly (the 40f/40g/40i precedent);
  2. `hδ` in the merged form, by 40i's `hδ₂` precedent;
  3. placement by the recon's table (the steps in a new `SplitOff.lean`, the general pieces in
     `Bridge.lean`, `Ear.lean`, `Cut.lean`, `Carrier.lean`), a reading of PI decision 5's convention
     the PI may reverse;
  4. pins by PI decision 4(b)'s first-consumer rule: SPLITOFF pays none of the D5 pin debt, which
     passes to COVERAGE;
  5. only (MC-31)'s `δ ≥ 5` conclusion is formalized, with a remark;
  6. `hinj` and `hab` kept, for ear-data parity with `of_openEar_one`;
  7. two COVERAGE tracked items (`hδ`'s supplier; (H) at the split-off antecedents);
  8. the mirror `MvPolynomial.polynomial_eval_aeval`;
  9. a cleanup-round item (*Hand-off*);
  10. two builds: the general pieces, then the step.
- **Blueprint placement.** The general lemmas before the step; the curve-limit lemma first, as the
  only one not about the split-off graph.

## Lemma checklist

All landed with the standard axioms (*Current state*); pins in **bold**, the other names unpinned
helpers.

- [x] **B1** (`0fdf5d5a`) — **`PanelHingeFramework.finite_setOf_finrank_lt_of_curve`** →
  `lem:pencil-curve-limit` (`Bridge.lean`, pinned fully qualified), with the mirror
  `MvPolynomial.polynomial_eval_aeval`; `BodyHingeFramework.finrank_span_rigidityRows_eq_add_of_motions`
  and `Graph.mem_liftingSpace_oneEar` (`Ear.lean`), `span_supportExtensor_ofNormals_eq`
  (`Cut.lean`), `Graph.ker_liftingMatrix_congr` and `Graph.ker_liftingMatrix_le_of_le`
  (`Carrier.lean`), unpinned until B2.
- [x] **B2** (`2fc2c02c`) — new `SplitOff.lean`: **`Graph.finrank_span_rigidityRows_splitOff_special`**
  with **`BodyHingeFramework.finrank_span_rigidityRows_eq_add_of_motions`** →
  `lem:pencil-splitoff-special-rank`; **`Graph.planeDiff_eq_zero_of_splitOff`** →
  `lem:pencil-splitoff-flexes`; **`exists_mem_forall_add_smul_eq_zero`**,
  **`Graph.mem_liftingSpace_oneEar`** and **`Graph.ker_liftingMatrix_congr`** →
  `lem:pencil-splitoff-curve`; **`Graph.X0Attains.of_splitOff`** → `thm:pencil-x0-splitoff`.
- [x] **The close** (docs and blueprint, with one Lean docstring chore): the end-to-end re-read, the
  exposition ledger, the headline axioms, the design doc, ROADMAP and `MolecularConjecture.md`; the
  public surfaces left unchanged (the PI's standing call, recorded at 40f's close).

## Blockers / open questions

- **None for 40j.**

## Hand-off / next phase

**40j is closed. Next: STEPS' CONTRACT-A group, not yet opened.** It is the next group in the
design doc's list order, and the last of STEPS' groups: contraction at an additive core,
(MC-67)–(MC-71). The next concrete step is **CONTRACT-A's design recon** (opus,
compiler-checked), by the 40f–40j precedent; the group opens as 40k after it. Its inputs are the
design doc's §3 STEPS CONTRACT-A entry and the landed CONTRACT-R step (`Contract.lean`,
`notes/Phase40f.md`). It factors out the shared part of CONTRACT-R's assembly (PI decision 4,
2026-09-26) and splits `Contract.lean` (1 496 lines, at the ~1500-line tripwire) along that line: the
general pieces to a shared file, the flat-core pieces and CONTRACT-R's assembly left behind. The
split waits for CONTRACT-A because the factoring decides the cut.

**Cleanup-round item** (call 9; the design doc's SPLITOFF entry): `span_supportExtensor_ofNormals_eq`
could replace the orientation split inlined in
`PanelHingeFramework.finrank_span_rigidityRows_ofNormals_congr` (`Cut.lean`). 40j's files are
under the ~1500-line tripwire (`SplitOff.lean` 744, `Ear.lean` 1 228, `Carrier.lean` 1 062,
`Cut.lean` 1 053, `Bridge.lean` 472).

## Decisions made during this phase

- **2026-09-28 — the close.** The re-read added the remark after the theorem (the exposition-ledger
  entry: the curve ends at the general picture, so no geometry of the main component is used) and
  dropped the proof's now-redundant aside. One Lean chore: `SplitOff.lean`'s module docstring states
  (MC-30)(i) and the line lemma correctly, and its four declaration docstrings say what each proves.
- **B2** — `SplitOff.lean` imports only `Orbit.lean`; two coordinator-reviewed docstring fixes in
  `Ear.lean` and the mirror.
- **B1** — `checkdecls` needs the fully qualified
  `CombinatorialRigidity.Molecular.PanelHingeFramework.…` for a declaration with no `_root_.`
  prefix; the mirror is stated at general `[CommSemiring R]`.
- **At the open** — the Jackson–Jordán attribution (Claim 6.5, Case 1, EGRES TR-2006-06,
  pp. 15–16) read in `.refs/`; the blueprint cites the journal paper without a claim number.
