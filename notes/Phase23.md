# Phase 23 — Case III general `d` (KT Lemma 6.13) → Thm 5.5 → Thm 5.6 → Conjecture 1.2 (work log)

**Status:** in progress (opened 2026-06-17 with a general, layer-level
design recon — docs only, no Lean).

## Current state

Phase 23 is **open via its general design recon** — the sub-phase division
is sketched at the layer level in `notes/Phase23-design.md` (the
authoritative recon). No Lean yet. The next concrete commit is **the 23a
detailed, leaf-level design recon** (not a build): read the realization
spine end-to-end, enumerate the `screwDim 2`/`Fin 4`/`ScrewSpace 2`
reach-ins along the import spine, run an opacity-readiness probe at symbolic
`k`, and cut 23a into buildable leaves.

The recon's single most consequential finding: the §1.33(C) sketch's
*"theorem_55 skeleton + Cases I & II — general & GREEN — the spine is
`k`-free"* is **wrong about the spine**. The graph-side combinatorics is
`n`-parametric, but the realization spine (`theorem_55_all_k`,
`case_III_realization*`, `case_III_nested_rank_lower`,
`case_III_candidate_dispatch`) carries `screwDim 2`/`ScrewSpace 2`/`Fin 4`
literally. Two distinct lifts are bundled: a *mechanical carrier lift* of
the spine (23a) and a *genuinely new* general-`d` chain dispatch +
`⋀^{d−1}(ℝ^{d+1})` duality (23b). The cut runs along that fault line.

## Architectural choices made up front

- **Sub-lettering 23a/23b/… (not integer phases)** to keep the integer
  phases 24–26 stable, exactly as Phase 22 did. The division (recon
  §2): 23a carrier lift, 23b chain dispatch + duality, 23c chain-entry
  ingredients (4.6/5.4/4.8), 23d assembly + Thm 5.6 + Conjecture 1.2.
- **23a is first** (recon §3): everything downstream is stated over the
  carrier, so the new mathematics of 23b must be written at general grade,
  which presupposes the spine is general grade; and the symbolic-`k`
  carrier transport (ScrewSpaceCarrier §6) is the most likely blocker — best
  surfaced before the hard new work builds on it.
- **The general-`d` carrier API (ScrewSpaceCarrier §6, the deferred 22l
  "part 2") folds into 23a**, not a standalone sub-phase — the migration
  surface *is* the carrier-lift surface.
- **Reuse verbatim (source-verified general & GREEN):** Lemma 2.1
  (`omitTwoExtensor_linearIndependent_of_li`), Claim 6.11
  (`exists_redundant_panelRow_ab_of_finrank_eq`),
  `linearIndependent_sum_augment_candidateRow`, the
  `complementIso`/`topEquiv`/`pairingDualEquiv` meet API.

## Sub-phase plan

The layer-level division, with hard cores and dependency order, is in
`notes/Phase23-design.md` §2–§3 (authoritative). Summary:

- [ ] **23a — general-`d` carrier lift of the spine** (FIRST). Lift the
      `screwDim 2`-pinned realization spine to symbolic `screwDim k` and
      complete the ScrewSpaceCarrier §6 general-`d` consumer migration. Hard
      core: symbolic-`k` `screwBasis`/`annihRow` transport (OD-5).
- [ ] **23b — general-`d` Case-III chain dispatch + `⋀^{d−1}` duality**.
      Replace the fixed-3-candidate `case_III_candidate_dispatch` with the
      `d`-chain dispatch (eqs. 6.46–6.64) + the `⋀^{d−1}(ℝ^{d+1})` duality
      finish (eq. 6.67, the N3b analog; re-state the `Fin 4`-pinned 22f
      `extensor_mem_range_map_subtype_of_mem` route at general grade). May
      split on contact (OD-6).
- [ ] **23c — chain-entry ingredients**: Lemma 4.6 dichotomy, Lemma 5.4
      short-cycle base, Lemma 4.8 split-off. Standalone-vs-folded is open
      (OD-1/2/3). Lemma 5.4 (if load-bearing) is its own panel-content leaf
      (risk #4).
- [ ] **23d — assembly**: Theorem 5.5 (general `d`) → re-green
      `prop:rigidity-matrix-prop11` + `hub` → Theorem 5.6 (§5.2 strip +
      re-add) → state Conjecture 1.2 as a theorem. Gates Cor 5.7 (Phase 26);
      Phases 24–25 can proceed in parallel.

## Blockers / open questions

The clause-(ii) flags the recon could not settle from the source live in
`notes/Phase23-design.md` §4 (OD-1…OD-6). The load-bearing ones for the
*next* cut:
- **OD-1** — is Lemma 5.4 genuinely on the Lean-load-bearing path at general
  `d`, or dodgeable as the `d=3` assembly dodged it?
- **OD-2/OD-3** — does the general-`d` chain entry (Lemma 4.6) reduce to the
  green Phase-20 `minimal_kdof_reduction`, and do 4.6/4.8 already exist
  subsumed there? (First detailed-recon task for 23c.)
- **OD-4** — does the general-`d` N3a (the `d+1` points, eq. 6.67) take the
  existence/Zariski route like `d=3`, or force the alg-independence hammer?
  (Tracked in `AlgebraicIndependence.md`; see *Decisions made*.)
- **OD-5** — does the symbolic-`k` carrier transport port verbatim or force
  an API addition? (The 23a opacity-readiness probe settles it.)

## Hand-off / next phase

**Next concrete commit: the 23a detailed, leaf-level design recon** (docs
only, not a build) — decompose 23a into buildable leaves per
`notes/Phase23-design.md` §3. It reads the spine files end-to-end, enumerates
the `screwDim 2`/`Fin 4`/`ScrewSpace 2` reach-ins along the import spine
(RigidityMatrix → … → Theorem55), runs the ScrewSpaceCarrier §6
opacity-probe at symbolic `k` (settling OD-5), and resolves OD-2/OD-3 by
`lean_local_search` for the chain dichotomy / split-off-minimality lemmas.

**Tracked follow-up (deferred from this commit, not Phase-23 math):**
- **Compress `notes/Phase22-realization-design.md`** (≈8.5k lines, now
  back-references-only). Per `notes/CLAUDE.md` *One canonical home per
  content type*, its closed arcs compress to ≤3-line verdicts now that
  Phase 22 has closed. This commit lifted §1.33(C)–(E)'s reuse map into
  `notes/MolecularConjecture.md`'s *Reuse map* (the recon needed it), so the
  Phase22-design doc can now be compressed/archived without losing the
  Phase-23 starting material. **Do this as a tightly-scoped doc-hygiene
  commit, not a blind delete** — a self-contained follow-up, off the
  Phase-23 critical path.

## Decisions made during this phase

### Phase-local choices and proof techniques

- **The §1.33(C) "spine is `k`-free" cell is wrong; corrected in the recon.**
  Source-verified the spine decls are `screwDim 2`/`ScrewSpace 2`/`Fin 4`-
  pinned (`Theorem55.lean:2248/2266`, `CaseIII/Realization.lean:181/518/561/665`).
  The carrier lift (23a) is mechanical-but-large; the chain dispatch (23b) is
  the new argument. Full grade table: `notes/Phase23-design.md` §1.
- **The 22f `⋀²ℝ⁴` duality "happy accident" is a TEMPLATE, not a verbatim
  reuse.** `extensor_mem_range_map_subtype_of_mem` /
  `exists_smul_eq_of_mem_range_map_subtype` (`Meet.lean:648/676`) are
  `Fin 4`/`⋀²`-pinned; the *route* generalizes (general mathlib +
  `topEquiv`/`pairingDualEquiv` mirrors) but the lemmas re-state at
  `⋀^{d−1}(ℝ^{d+1})`. Corrects §1.33(D)'s "ALREADY PARTLY LANDED." Build the
  duality LAZILY at concrete grade; do **not** build a general Hodge star.
- **General-`d` alg-independence: a tracker row was added.** Per the standing
  instruction (MolecularConjecture risk #8). The `d=3` seed-rank kernel
  already consumes `AlgebraicIndependent ℚ q` (`case_III_nested_rank_lower`),
  so the machinery is live; the open question (OD-4) is whether the eq. 6.67
  N3a *points* step is a new alg-independence site or takes the existence
  route as `d=3`'s N3a did. → `notes/AlgebraicIndependence.md`.

### Promoted to TACTICS-GOLF / TACTICS-QUIRKS / FRICTION / DESIGN

- (none this commit — design recon only.)
