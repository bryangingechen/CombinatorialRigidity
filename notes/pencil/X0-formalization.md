# The `X₀` formalization — planning note

**Status: PLANNING (2026-09-25).** This is the input for opening the formalization of the pencil
conjecture along the `X₀` route. **The architecture is decided** (PI, 2026-09-25, verbatim in
`adjudications.md`): the Lean target moves to the simpler route below, over **every infinite field**
(no `CharZero`). A fresh session opens the phase from this note. First it settles the open calls in
§5, then it follows `PHASE-BOUNDARIES.md` *When this commit opens a phase*.

**Read §2 before doing any mathematics.** Nearly everything the route needs already exists in
written, second-read form. The job now is transcription and formalization, not re-derivation.

## 1. The target

- **Headline shape.** The recon's `spike_pencil_conjecture_of_X0` (its source is verbatim in
  `notes/Phase39-design.md` § *X₀ architecture recon (2026-09-25)*). It is
  `pencil_conjecture_of_arms_pair` with one arm, `spike_pair_arm`, serving as both `hcontract` and
  `hsplit`:
  - not 2EC: the landed `pencilPair_of_not_twoEdgeConnected`;
  - 2EC and simple: `X0Dist` (the distinct motive) and `X0Gen` (the generic motive under
    `PencilNondegFeasible`);
  - 2EC and non-simple: W4-A (W4-L1), the bare motive.
- **Carried until discharged:** `X0Dist`, `X0Gen` and W4-A. The spike states them in consumer shape
  (simple, 2EC, `3 ≤ |V|`). Nothing else is needed: no `hK`, `hbareSplit`, `hcard` or `hfresh`.
- **Field:** `[Infinite K]`. `X0Dist`/`X0Gen` are proved informally in characteristic 0 modulo
  Jackson–Jordán, and over any infinite field modulo (MC-33)(i). Hence the Jackson–Jordán layer (§3,
  L3) must be field-general.
- **Protected:** `hK`, `hbareSplit`, `pencilPair_of_splitOff_of_habitat` and the landed headline
  `pencil_conjecture_of_hcontract_hK_hbareSplit_of_card` are not edited. The new headline sits
  beside them.

## 2. What is already done — the index (use it; do not redo it)

| what | where | state |
|---|---|---|
| the informal mathematics, (MC-1)–(MC-168) | `workbook/K-main.md` §(K-main); query with `python3 notes/ledger.py --label '(MC-89)'` / `--brief …`; the section header summarizes every step | written; second-reading coverage in `W4-reopen.md`'s table |
| **the proof tree of (MC-89)** | K-main Step MC20, *Part I — the dependency tree of (MC-89)* (steps CUT/BRIDGE, BASE, FLAT, CONTRACT, THETA, 𝒮, coverage ⟹ attainment) | audited complete by Step MC20's second reader: every computation it consumes is replaced by a hand proof |
| **every argument leaf of (MC-89)** | (MC-166)'s *Scope* list (K-main Step MC20) | the blueprint's node list for (MC-89); audited characteristic-free |
| the generic and distinct motives | K-main Step MC19: (MC-123)–(MC-130), (MC-133), (MC-157); nondegeneracy (MC-13)(c), (MC-14) (Step MC8) | second-read 2026-09-25 |
| the certificate leaves as hand proofs over every field | K-main Step MC20, (MC-134)–(MC-139) | second-read; characteristic-2/3/5 certificates (MC-168) |
| the consumer map and the spike | `notes/Phase39-design.md` § *X₀ architecture recon (2026-09-25)*, spike verbatim at its end | re-elaborated by the coordinator: two `sorry`s |
| Jackson–Jordán beyond ℝ | K-main *Jackson–Jordán beyond ℝ*, (MC-33): the step table, repairs R0/R1, bypass R2 | `[INFORMAL]`; a full write-up is in flight (§6) |
| the `n = 2` alternative to Jackson–Jordán | the recon above, *Jackson–Jordán: the options* (a); `notes/Prospect.md`, the G2 entries (dropped 2026-07-10 by rule, not by proof) | a sizing recon is in flight (§6) |
| W4-A | `notes/Phase39-design.md` § *W4 decomposition recon*, "W4-A — the non-simple bare producer" (KT Lemma 6.2 mirror; the motions-collapse rank brick) | sketch; bricks landed; about 2–3 commits |
| drivers behind every figure | `notes/scripts/w4/README.md`, the *Step MCnn's drivers* bullets; commands in `notes/scripts/README.md`'s invocation table | the unguarded ones are listed in *Harness debt* (the 2026-09-25 item) |
| Lean bricks to reuse | the recon's *Cost sketch*, by declaration name | — |
| the PI's calls | `adjudications.md` §§ 2026-09-23 onward; the architecture call is 2026-09-25 | — |
| the superseded split/contract route | `W4-reopen-archive.md`; `workbook/W4.md`; the kernels (K-res), (K-c), (K-bare-c) | fallback only; do not resume without a PI call |

**Not needed on this route, whatever their state:** the open ear cell (MC-154) (Case II-cyclic);
the second proof (MC-148); the relative-dof conjecture (MC-23); the census (MC-7)–(MC-9) except as
a sanity check; the kernels above; smark's O7e programme.

## 3. Proposed blueprint layers

The layers are listed in dependency order. Each carries its informal source, what it reuses in the
Lean, and whether it waits on the Jackson–Jordán route.

- **L0 — consumer wrapper, and W4-A.** The new headline with `X0Dist`/`X0Gen` carried as
  hypotheses: the spike minus its `sorry`s. Then W4-A discharges its `sorry`. Small, and independent
  of everything below. Reuses `pencil_conjecture_of_arms_pair`, `pencilPair_of_not_twoEdgeConnected`,
  `hasPencilRealization_of_distinct`, and for W4-A `isKDof_zero_of_parallel_pair`, `rigidContract`,
  `rigidContract_deficiency_eq` and the `case_I_realization_nonsimple_gen` pattern.
- **L1 — carrier.** Planar pictures, admissibility, the lifting space `L(q)` and `X₀`'s rational
  parametrization ((MC-1)–(MC-3)). "The generic point attains" becomes a nonzero rank polynomial.
  Reuses `MvPolynomial.exists_eval_ne_zero` and its variants, and the
  `PanelHingeFramework.exists_rankPolynomial_of_*` family.
- **L2 — the flat rank.** (MC-4), (MC-5). The inequality is landed at grade 1
  (`screwDim_mul_compl_add_deficiency_le_finrank_infinitesimalMotions`). New: `F(q) ≅ L(q)`, and the
  split `Λ²K⁴ = W_Π ⊕ W′` against the opaque `ScrewSpace` carrier.
- **L3 — Jackson–Jordán's equality**, field-general. It is consumed at FLAT (`G`), CONTRACT (`H`,
  `G/H`), `G′ + ab` and SPLITOFF (`G″`) ((MC-141)'s list), all at simple graphs. Two options, per
  §5: the landed KT spine extended to `n = 2`, or the TR (bar-joint 2D, extensions, vertex split,
  bricks). **This is the only layer that waits on the route call.**
- **L4 — the local steps.**
  - cut and bridge fibre products (MC-52), (MC-53), (MC-55), (MC-56);
  - the ear step (MC-16)–(MC-22), (MC-24)–(MC-26), with the chain spans (MC-134) and the
    intersections (MC-135)–(MC-137);
  - short ears (MC-45), (MC-46) (orbit table (MC-138)) and (MC-54);
  - split-off (MC-28)–(MC-31);
  - contraction (MC-34)–(MC-39) and (MC-59);
  - THETA (MC-21), (MC-139).

  Deficiency bookkeeping reuses the landed laws: `rigidContract_deficiency_eq`,
  `deficiency_eq_of_cutEdges_ncard_le_one`, `removeVertex_deficiency_ge`, and item 6's Layers A–C.
  There is no landed cut-vertex deficiency law.
- **L5 — the structural half and the assembly.** (MC-62), (MC-63), (MC-67)–(MC-71),
  (MC-75)–(MC-80), (MC-87), then (MC-89) itself by strong induction (MC-55)(i), (MC-56). This is pure
  combinatorics on `def₂`, `def₃`. Reuses `exists_maximal_induced_isProperRigidSubgraph`,
  `triangle_isProperRigidSubgraph`, `c4_isProperRigidSubgraph`.
- **L6 — the motives.** (MC-157) from (MC-89). (MC-133)(ii) from (MC-130) (the reduction, via the
  hub-plane chart (MC-124)–(MC-129)) and (MC-14) (nondegeneracy on `X₀`). Discharging
  `X0Dist`/`X0Gen` closes L0's carried hypotheses. Partly reuses `pencilChartFramework`/`PencilSeed`,
  `exists_pencilSeed_of_nondeg`, L6b, and
  `hasGenericPencilRealization_of_independent_pencilRow_target`.

**Before transcription:** consider splitting `K-main.md` by step (`W4-reopen.md` *PI calls pending*,
the structural chore, which records the design and its open convention question).

**What can start before the Jackson–Jordán call:** L0, L1, L2's inequality, L4's combinatorics,
and all of L5. L3's consumers can carry its equality as a hypothesis meanwhile. That uses the
carried-hypothesis idiom, which is a sequencing device and not a citation (`DESIGN.md`
*Formalize everything the argument uses*).

## 4. Where formalization may expose mathematics

- **Genericity.** The induction argues about generic points throughout; (MC-157) alone needs only
  one. The delicate places are dominance (MC-18)(b), the two-scale and flat limits in contraction
  ((MC-37), (MC-66), (MC-69)), and the semicontinuity at chord points. Each must become an explicit
  nonzero-polynomial or rational-parametrization statement.
- **Fresh edge labels.** `G′ + ab` and split-off add edges inside a fixed `β`. That calls for either
  a `β`-headroom hypothesis like `hcard`, or a type-changing induction; the informal proof never
  sees the issue.
- **Non-spanning uses** of the rank theorem at `H` and `G/H`. The landed
  `rankHypothesis_of_theorem_55_gen` is stated for spanning `G` with `hcard` headroom.
- **(H) versus 2EC.** The proof needs all of (H), since CUT and BRIDGE pass through non-2EC graphs,
  while the consumer uses only the 2EC form.
- `supportExtensor e ≠ 0` for **every** `e : β`, not only the edges of `G`. This is trivial, but it is
  easy to miss.

## 5. Open calls (the PI's), in the order they gate work

1. **Phase structure.** `notes/Phase39.md` sits at its 580-line cap, and the programme is
   multi-phase. The molecular programme's pattern would suggest a new phase number, sub-lettered as
   layers open (codes until open), with its own `notes/PhaseNN-design.md`. Phase 39 would then close
   on the reduction plus the carried headline. The alternative is new checklist items inside
   Phase 39. *Agent's suggestion: the new phase.*
2. **The W4-L1 (W4-A) hold lift.** W4-A is on the adopted route. The lift is recorded per item
   (`notes/Phase39.md` *Blockers*). So is L0's wrapper; G0's 2026-09-23 lift covers "a new
   declaration carrying … any other unsettled piece as hypotheses", which arguably includes it, but
   confirm.
3. **The Jackson–Jordán route**, (a) or (b) of the recon, once the two in-flight dispatches (§6)
   report.
4. **The kernels and smark:** cancel or hold. The recon reads *hold* until L6 lands.

## 6. Dispatches in flight at the end of the 2026-09-25 session

*(Readers E and F, Steps MC17–MC18 and MC1–MC6/MC10, landed the same session: nothing on (MC-89)'s path refuted.)*

If the session ended before they landed, their results are lost. Re-dispatch from these one-line
briefs with the appendix's reusable brief.
- **Recon H** — sizing the KT spine at `n = 2`. Which `6 ≤ bodyBarDim n` sites are essential; KT
  Lemma 4.6 and Case III (Lemma 6.13, p. 686's remark) at `d = 2`; `ChainData`'s real floor; the
  wrappers; a commit count against option (b).
- **Writer I** — (MC-33)(i) as a full proof: bypass R2 written out construction by construction;
  the field-general induction for TR Thm 6.1/7.1; the brick lemmas 3.2, 3.3 re-proved.

## Appendix — the reusable second-reader brief (as used 2026-09-25)

Dispatch a `recon-opus` agent, read-only. The brief says:
- **The role.** A fresh second reader, adversarial: try to refute; a located gap beats a
  confirmation.
- **Hygiene.** Leave `git status` clean. Cite by label, never by line number, since other commits
  land meanwhile. Every foreground command gets an explicit timeout.
- **The return.** The harness refuses subagent report files, so the report comes back as the final
  message. Scratch holds scripts and raw outputs only.
- **Reading.** Read K-main's header, which ends with the standing hypotheses (H). Retrieve claims
  with `ledger.py --label` / `--brief`, not grep. Obey `HARNESS.md` § *Evidence*.
- **Scope.** The claims, in priority order. For Lean-facing claims, open the definition bodies
  (not the docstrings).
- **Method.** Re-derive each proof. Check every citation's hypotheses. Re-run every cited driver
  command. Any new script must be seeded and exact.
- **Deliverable.**
  - a verdict per claim: CONFIRMED / CONFIRMED-WITH-REPAIR / GAP / REFUTED;
  - each repair as exact replacement text keyed by label;
  - new claims under placeholder labels (the coordinator mints the `MC-` labels);
  - the commands re-run, with timings.

**Landing a report** is covered by `W4-reopen.md` *Standing constraints*: repairs go in place,
marked; new labels get a row in `labels.md`; new drivers are ported with the canonical bootstrap,
seeds unchanged, and re-run to confirm they reproduce.
