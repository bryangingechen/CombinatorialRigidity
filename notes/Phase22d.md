# Phase 22d — Claim 6.11's first green-machinery prerequisite (the matroid-base 4.3(ii) leaf) (work log)

**Status:** in progress. Opened 2026-06-05 design-pass-first; re-scoped 2026-06-05 to
attack KT Claim 6.11 **bottom-up** (build its leaf-most missing-green prerequisite, not
an axiomatized claim). Gap-2 leaf landed green 2026-06-06; the Gap-3 + footnote-6 recons
(2026-06-06) settled the analytic kernel's shape; the kernel-route decision (2026-06-06,
user) is to build the algebraic-independence route directly. Recon detail lives in the
design doc (§1.30/§1.31); this note carries the forward plan + a compressed verdict log.

## Current state

Gap-2 landed green + axiom-clean: `Graph.splitOff_exists_base_inter_fiber_lt`
(`ForestSurgery.lean`), the matroid-base form of **KT Lemma 4.3(ii) at `k=0`** — a base
`B'` of `M(G̃_v^{ab})` with `|ãb ∩ B'| < D−1` (a redundant `ãb`-copy exists). Blueprint
node `lem:case-III-claim-6-11-base` green; `lem:case-III` / `lem:case-II-realization` red.

**Next concrete commit:** the **Gap-3 combinatorial shell**
`Graph.splitOff_removeVertex_minimalKDof` — `G_v = removeVertex v` minimal `k'`-dof with
`0 ≤ k' ≤ D−2`, from the Gap-2 base + the green def-count chain. Pure `M(G̃)` matroid
theory, no rigidity matrix, **buildable** (inputs all green, in the checklist). New green
node `lem:case-III-gap3-minimalKDof`.

After that the work is the **analytic kernel** — content pinned by the recons, route
fixed by the user (see *Deferred sub-phases*): genuinely-new
(`non-root-from-algebraic-independence`), built directly, not carried as a hypothesis.

## Claim 6.11 discharge — the Gap 2 → 3 → 1 map

Claim 6.11 (KT p. 684, eq. (6.23)): `R(G_v^{ab}, q)` has a redundant row among its `D−1`
`ab`-rows — the `+1` that lifts 22c's stratum-1 `D(|V|−1)−1` brick to full `D(|V|−1)`.
KT's proof (pp. 684–685) factors, in dependency order:

1. **Gap 2 — matroid-base 4.3(ii)** (✓ landed): a base `B'` of `M(G̃_v^{ab})` with
   `h := |ãb ∩ B'| < D−1`. Pure combinatorial `M(G̃)`; all inputs green.
2. **Gap 3 — the nested IH-at-restriction.** `G_v := G_v^{ab} − ab = removeVertex v`;
   `B' ∖ ãb` independent in `M(G̃_v)` ⟹ `def(G̃_v) ≤ h ≤ D−2` ⟹ `G_v` minimal `k'`-dof.
   Apply the geometric IH (6.1) to `G_v` at the restricted seed `q|_{E_v}` ⟹
   `rank R(G_v, q|_{E_v}) = D(|V∖v|−1) − k'` (eq. (6.22)). **SPLITS:** a green
   combinatorial shell (the `minimal k'-dof` step, next build) + the analytic kernel
   (the eq. (6.22) rank-at-the-given-seed).
3. **Gap 1 — the `M(G̃)`↔row bridge.** With `rank R(G_v^{ab},q) = D(|V∖v|−1)` (eq. (6.18))
   and Gap 3's eq. (6.22), the `k' ≤ D−2 < D−1` corank over the `D−1` `ab`-rows forces one
   redundant (pigeonhole). Step ③ is pure LA *given* (6.18)+(6.22).

The kernels of Gaps 3 and 1 **likely merge into one node** — "the rigidity matrix at the
inductively-fixed seed `q` attains the rank `M(G̃)` predicts" — bottoming on the
`non-root-from-algebraic-independence` brick (open: confirm one-vs-two, *Blockers*).
eq. (6.18) is *not* separately in hand: 22c's `case_II_placement_eq612` gives the `−1`,
Claim 6.11 supplies the `+1` — the same missing content.

## Lemma checklist

- [x] `Graph.forest_surgery_count` — strengthened with the `|ãb ∩ ⋃ Fs'i| < D−1` conjunct
  (KT Lemma 4.1's second conclusion). Caller `forest_surgery_split` re-destructures.
- [x] `Graph.splitOff_exists_base_inter_fiber_lt` — Gap-2 leaf (above), green +
  axiom-clean. Node `lem:case-III-claim-6-11-base`.
- [ ] **(next) `Graph.splitOff_removeVertex_minimalKDof`** — Gap-3 combinatorial shell:
  `G_v = removeVertex v` minimal `k'`-dof, `0 ≤ k' ≤ D−2` (confirm exact statement shape
  at build open). Inputs (all green, by signature): the Gap-2 leaf, `subgraph_minimality`
  (`Deficiency.lean:400`), `removeVertex_le` (mathlib), `matroidMG_restrict_mulTilde`
  (`Deficiency.lean:212`), `mulTilde_removeVertex_le_splitOff` (`ForestSurgery.lean:91`),
  `rank_add_deficiency_eq` (`Deficiency.lean:994`), `removeVertex_deficiency_ge`
  (`SplitOffDeficiency.lean:405`). Count: `def(G̃_v) = D(|V∖v|−1) − rank M(G̃_v) ≤ h ≤ D−2`.
  Node `lem:case-III-gap3-minimalKDof`; `lem:case-III` stays red.
- [ ] (deferred, the kernel) the eq. (6.22) generic-rank transfer / Gap-1 row bridge — see
  *Deferred sub-phases*. Red; built directly, not carried.

## Deferred sub-phases (future work in the phase)

Parked until the leaf's shape is clear; a sub-letter is minted when its turn comes.

- **The analytic kernel (Gap-3 kernel ⊕ Gap-1 row bridge — likely ONE node).** Payload:
  `corank R(ofNormals G_v ends q|_{E_v}) = def(G̃_v)` at the inductively-fixed seed `q`,
  then the redundant-row conversion (eq. (6.23)). The footnote-6 recon (design doc §1.30)
  pinned the content: the device *consumer*
  `isInfinitesimallyRigidOn_ofNormals_of_rankPolynomial_ne_zero` already runs the
  given-point direction, so the only gap is certifying `eval q Q ≠ 0` for the specific
  device-built `Q` — which KT gets from `q` being **algebraically independent over ℚ**
  (footnote 6). The project has **zero** `AlgebraicIndependent` machinery. Leaf-most-first
  cut (do not pre-commit the finer cut): **(i)** mirrorable
  `MvPolynomial.eval_ne_zero_of_algebraicIndependent` (alg.-indep. tuple ⟹ off every
  nonzero ℚ-poly's zero locus); **(ii)** the seed-alg-indep invariant threaded through the
  induction (may need a *third* motive form, paralleling 22b's GP / link-recording
  strengthenings); **(iii)** the kernel `lem:case-III-seed-rank-bridge` composing (i)+(ii)
  with the consumer + `rigidityMatrix_prop11` + `rank_add_deficiency_eq`. **Route (user,
  2026-06-06, design doc §1.31): build this DIRECTLY to green**, not as a permanent
  hypothesis. The product-route *relaxation* candidate (pick `q` as a non-root of the
  finite product of the nested IH rank polynomials, avoiding alg-independence at `d=3`;
  ~70% confidence) is the deferred TODO in the standing tracker
  `notes/AlgebraicIndependence.md`.
- **Candidate-completion + Claim 6.12 disjunction.** With the redundant `ab`-row, lift
  22c's `case_II_placement_eq612` `≥ D(|V|−1)−1` to `= D(|V|−1)` on one candidate (eq.
  (6.24)–(6.29) row-op), then the Claim-6.12 extensor-span contradiction via the **green**
  Lemma 2.1 (`omitTwoExtensor_linearIndependent`) + the eq. (6.44) degree-2 forcing picks
  the full-rank candidate. Claim 6.12 **de-risked** (Lemma 2.1 green). Candidate normal
  form: **abstract one per-candidate lemma, instantiate ×3** (`p₂=p₁` with `a↔b`;
  `p₃=p₁∘ρ`); `case_II_placement_eq612` is already this shape (22c recon, design doc §1.26).
- **The `d=3` assembly** — `prop:rigidity-matrix-prop11` `hub` brick + `thm:theorem-55`
  flip + wiring the green `case_I_realization`. Unlettered.
- **General `d`** (Lemma 6.13) → Thm 5.5 → Thm 5.6 → Conjecture 1.2 — Phase 23.

## Blockers / open questions

- **Do the Gap-3 kernel and Gap-1 row bridge merge into one node?** Both bottom on "the
  seed attains the rank `M(G̃)` predicts" / the `non-root-from-alg-indep` brick. Confirm
  one-vs-two at the kernel sub-phase's open; do not pre-commit now.
- **Claim 6.12 — de-risked** (bottoms on the green Lemma 2.1).
- **Recurring Lean traps** (carry from 22a–c, FRICTION): heavy `IsInfinitesimallyRigidOn`
  defeq across `ofNormals`/`withGraph` graph-swaps can `isDefEq`-timeout — make the two
  frameworks *syntactically* equal before `convert`; transfer rigidity via a
  `mem_infinitesimalMotions` round-trip. (Bites once Gap 1 lands, not the matroid-only shell.)

## Hand-off / next phase

**Next concrete commit:** the Gap-3 shell `Graph.splitOff_removeVertex_minimalKDof`
(`ForestSurgery.lean`, beside the Gap-2 leaf) — statement + green inputs in the checklist.
Pure matroid theory, buildable; `lem:case-III` stays red.

After it, the **kernel sub-phase** (its own dedicated math-first recon at open): build the
`non-root-from-algebraic-independence` brick directly (the (i)/(ii)/(iii) cut under
*Deferred sub-phases*). Then the candidate-completion + Claim-6.12 disjunction, the `d=3`
assembly, and general-`d` (Phase 23).

KT math: KT §6.4.1 (Lemma 6.10, Claims 6.11/6.12, eqs. (6.22)–(6.45)), §4 (Lemmas
4.3(ii)/4.4/4.7/4.8). Recon detail: design doc §1.30 (footnote-6 kernel) + §1.31
(kernel-route) + §1.26 (candidate structure); also `notes/Phase20.md`
(`splitOff_isMinimalKDof`), `notes/Phase21b.md` *Finding A/B*, `notes/Phase22c.md`,
`notes/AlgebraicIndependence.md` (the alg-independence tracker).

## Decisions & recon log (compressed)

The finished-work tail — one-line verdicts; the blow-by-blow is in the cited commits /
design-doc arcs (per `notes/CLAUDE.md` *Forward-weighted note*).

- **Re-scope (2026-06-05).** User overrode the opening "axiomatize Claim 6.11" verdict
  (commit 4e6a7bb): build Claim 6.11's leaf-most missing prerequisite bottom-up rather
  than deferring onto Claim 6.12.
- **Green substrate richer than the opening recon credited.** Gap 2 is buildable from green
  Phase-20 infra — `splitOff_isMinimalKDof`'s proof already builds the `ãb`-base count (and
  discarded it); `isBase_vfiber_ncard_ge` is a near-verbatim template. (Detail in the Gap-2
  leaf's proof + commit 13d2464.)
- **Gap-2 leaf (commit 13d2464).** Two bricks: (1) strengthen `forest_surgery_count` with
  the `< D−1` conjunct (the inserted `r i` are the only `e₀`-copies, `h' ≤ D−2`); (2) the
  `k=0` base assembly (`def = 0` ⟹ a full-rank independent set is a base,
  `Indep.isBase_of_ncard`). KT 4.3(ii) is an **existence** statement (a base with `<D−1`),
  not "every base" — matching the Claim-6.11 use.
- **Gap-3 recon (commit 0f7ef2a).** Gap 3 **splits**: green combinatorial shell (next build)
  + research-shaped analytic kernel; the combinatorial glue (`def(G̃_v) ≤ h` ⟹ `G_v`
  minimal `k'`-dof) is all green Phase-19/20.
- **Footnote-6 kernel recon (commit 892f44c; design doc §1.30).** eq. (6.22) is NOT a green
  re-exposure of 21b/22b machinery. Confirmed two of the user's three structural claims
  (matroid↔row link = the IH `rigidityMatrix_prop11`, green-modulo; step ③ pure LA);
  refuted the bottom line — the motive is existence-only (`∃ Q`), `IsGeneralPosition` is
  only pairwise transversality, not non-root-ness of `Q`. Named the missing brick:
  `non-root-from-algebraic-independence`.
- **Kernel-route decision (commit 3f0ea8e; design doc §1.31).** Build the alg-independence
  route directly to green (the certain path); product-route relaxation tracked in
  `notes/AlgebraicIndependence.md`.
- **22c left off** at `case_II_placement_eq612` (`CaseI.lean:2331`) = the `≥ D(|V|−1)−1`
  brick; its `e_a=va` link is carried as `_hG_ea`. 22d supplies the `+1`.
