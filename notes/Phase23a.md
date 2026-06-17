# Phase 23a — General-`d` carrier lift of the spine [CARRIER] (work log)

**Status:** in progress (opened 2026-06-17; Phase 23 opened with a general,
layer-level design recon, then this 23a leaf-level recon — both docs only, no
Lean yet).

**Orientation.** This is the **23a (CARRIER layer)** sub-phase work log — the
*rolling* state + hand-off for the active sub-phase only. The cross-phase
**plan/guidance** (sub-phase division, sequence, open decisions, sources) is
the canonical job of `notes/Phase23-design.md`; the program map is
`notes/MolecularConjecture.md`. **Sub-phase naming convention** (set
2026-06-17): the layers are tracked by stable **codes** — `CARRIER`, `CHAIN`,
`ENTRY`, `ASSEMBLY` (see the design doc §2) — and a **letter (23a, 23b, …) plus
a `notes/Phase23X.md` work log are minted only when a layer is about to open**,
so a later split (e.g. `CHAIN` into two) does not renumber-churn the rest.
`23a` is the minted letter for the opening `CARRIER` layer; the other three
stay code-only until their turn.

## Current state

Phase 23 is **open with both recon stages landed**, **Leaf 0 (the `screwDim`
arithmetic kit) green**, **Leaf 1 fully landed** (1a rank-nullity core; 1b
grade-`k` extensor bricks), and **Leaf 2 landed (re-scoped — see below)**: the
N1 spanning brick `span_omitTwoExtensor_eq_top` lifted to general `k`, on a new
upstream mirror `Fintype.card_subtype_fst_lt_snd`. The next concrete commit is
**Leaf 2b** — lift the shared-spine LI brick
`linearIndependent_normals_of_algebraicIndependent` that the Leaf-2 re-scope
mis-dropped to CHAIN (it is consumed by the KT-6.5 cut arm
`case_I_realization_h65`, a genuine general-`k` spine decl) — then **Leaf 3**
(the CaseII rank-arithmetic numeral pass — `case_II_realization_all_k` and its
lemmas to `screwDim k` / `HasGenericFullRankRealization k`) — see *Hand-off*.
The general sub-phase division (§2–§3) and the 23a leaf recon (§"23a") live in
`notes/Phase23-design.md` (the authoritative recon).

**Leaf 2 re-scope (recon correction — itself corrected by the coordinator).**
The Leaf-2 recon listed five decls to lift. A build-time consumer trace
correctly found **three** of them — `omitTwoExtensor_eq_extensor_kept`,
`omitTwoExtensor_homogenize_eq_extensor_kept`, `exists_independent_perp_pair` —
**dispatch-internal**: each is consumed only inside the `⋀²ℝ⁴` duality decls
`exists_line_data_of_homogeneousIncidence` (Claim612:522) /
`exists_hduality_witness_of_panel_incidence` (Claim612:1075), which feed only
`case_III_candidate_dispatch` and which CHAIN replaces wholesale; and they are
`k=2`/`d=3`-inherent in *shape* (the 2-element kept-complement tabulation; the
fixed 3-normal `3×3` det). They move to CHAIN, lifted at the grade CHAIN needs.
**But the trace mis-classified the fourth**, `linearIndependent_normals_of_algebraicIndependent`
(Realization:99): it is consumed **not only** inside the dispatch
(Realization:350, CHAIN) **but also** by `case_I_realization_h65` (Theorem55:678),
the KT-Lemma-6.5 degree-2-cut arm producer the dof induction
`theorem_55_minimalKDof_k` calls at Theorem55:2143. That arm is a genuine
reduction case of the spine — **not** the Case-III candidate dispatch — and
Leaf 5 lifts it to general `k`, so the brick must be available at `Fin (k+2)`.
This matches the authoritative recon (`notes/Phase23-design.md` §"23a"(a),
ll.471–476: a "shared brick 23a must lift"). So the brick is **re-instated as
Leaf 2b** (next); the actual content of the landed Leaf-2 commit was only the
genuine N1 brick `span_omitTwoExtensor_eq_top` (KT Lemma 2.1's spanning result;
23a-OD-B `(k+2)×(k+2)` squareness confirmed clean) + its supporting card count.

**OD-5 settled (ports verbatim, no API addition, no spike).** The 23a recon
verified against the landed source that the `screwBasis`/`annihRow` coordinate
transport (hard-part (d)) is **already written at symbolic `k` and already
compiles** (`PanelLayer` coordinate layer + `GenericityDevice.exists_good_realization_ofParam`
are `(k:ℕ)` in HEAD). ScrewSpaceCarrier §6's "exercised symbolically for the
first time in Phase 23" worry is false in the source — the coordinate layer
was authored general; the `d=3` usage only specialized the numerals around it.
The genuinely-new symbolic surface is the **`screwDim k` numeric arithmetic**
(`2 ≤ screwDim k` etc. that `d=3` discharged by `decide`) — handled by Leaf 0.

The recon's single most consequential finding: the §1.33(C) sketch's
*"theorem_55 skeleton + Cases I & II — general & GREEN — the spine is
`k`-free"* is **wrong about the spine**. The graph-side combinatorics is
`n`-parametric, but the realization spine (`theorem_55_all_k`,
`case_III_realization*`, `case_III_nested_rank_lower`,
`case_III_candidate_dispatch`) carries `screwDim 2`/`ScrewSpace 2`/`Fin 4`
literally. Two distinct lifts are bundled: a *mechanical carrier lift* of
the spine (23a) and a *genuinely new* general-`d` chain dispatch +
`⋀^{d−1}(ℝ^{d+1})` duality (CHAIN). The cut runs along that fault line.

## Architectural choices made up front

- **Sub-lettering (not integer phases)** to keep the integer phases 24–26
  stable, exactly as Phase 22 did — but tracked by **stable codes** until
  open (see the *Orientation* convention above). The division (recon §2):
  `CARRIER` carrier lift (= the minted **23a**), `CHAIN` chain dispatch +
  duality, `ENTRY` chain-entry ingredients (4.6/5.4/4.8), `ASSEMBLY`
  assembly + Thm 5.6 + Conjecture 1.2. Letters for `CHAIN`/`ENTRY`/`ASSEMBLY`
  are minted when they open (a `CHAIN` split then costs no renumber-churn).
- **23a is first** (recon §3): everything downstream is stated over the
  carrier, so the new mathematics of CHAIN must be written at general grade,
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

- [ ] **23a [CARRIER] — general-`d` carrier lift of the spine** (FIRST, the
      one minted letter). Lift the
      `screwDim 2`-pinned realization spine to symbolic `screwDim k`. OD-5
      settled (transport already general). **6-leaf sequence**
      (`notes/Phase23-design.md` §"23a"(c)): Leaf 0 `screwDim` arithmetic kit
      (Basic ✓) → Leaf 1 `Fin 4` panel-incidence geometry (PanelLayer; **split
      at build**: 1a duality-free rank-nullity core ✓, 1b grade-`k` extensor
      bricks ✓; `exists_extensor_eq_panelSupportExtensor` dropped to CHAIN)
      → Leaf 2 N1 spanning brick `span_omitTwoExtensor_eq_top` ✓ (the three
      other Claim612 incidence bricks are dispatch-only → CHAIN) → **Leaf 2b**
      the shared LI brick `linearIndependent_normals_of_algebraicIndependent`
      (Realization l.99; spine-consumed via `case_I_realization_h65`)
      → Leaf 3 CaseII rank-arithmetic numeral pass → Leaf 4 Case-III spine,
      dispatch left explicit → Leaf 5 Theorem55 spine, dispatch threaded up
      (closes 23a). Carrier files (RigidityMatrix/Basic, PanelHinge,
      Pinning, GenericityDevice, Coupling, CaseI) need **no lift** — already
      general. Green-modulo boundary: the Case-III dispatch becomes an
      explicit `hcand` hypothesis for CHAIN (§"23a"(d)).
- [ ] **CHAIN — general-`d` Case-III chain dispatch + `⋀^{d−1}` duality**
      (code; letter minted at open). Replace the fixed-3-candidate
      `case_III_candidate_dispatch` with the
      `d`-chain dispatch (eqs. 6.46–6.64) + the `⋀^{d−1}(ℝ^{d+1})` duality
      finish (eq. 6.67, the N3b analog; re-state the `Fin 4`-pinned 22f
      `extensor_mem_range_map_subtype_of_mem` route at general grade). May
      split on contact (OD-6).
- [ ] **ENTRY — chain-entry ingredients** (code; letter minted at open):
      Lemma 4.6 dichotomy, Lemma 5.4 short-cycle base, Lemma 4.8 split-off.
      Standalone-vs-folded is open (OD-1/2/3). Lemma 5.4 (if load-bearing) is
      its own panel-content leaf (risk #4).
- [ ] **ASSEMBLY — assembly** (code; letter minted at open): Theorem 5.5
      (general `d`) → re-green
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
  subsumed there? (First detailed-recon task for ENTRY.)
- **OD-4** — does the general-`d` N3a (the `d+1` points, eq. 6.67) take the
  existence/Zariski route like `d=3`, or force the alg-independence hammer?
  (Tracked in `AlgebraicIndependence.md`; see *Decisions made*.)
- **OD-5** — **RESOLVED: ports verbatim, no API addition, no spike** (23a
  recon, `notes/Phase23-design.md` §"23a"(b)). The coordinate transport is
  already general in HEAD; the new symbolic surface is `screwDim k` arithmetic
  (Leaf 0), not the carrier. Residual 23a-OD-C: cap regressions under the
  numeral substitution are local `maxHeartbeats` bumps (standing idiom), not
  an OD-5 reopening.

## Hand-off / next phase

**Next concrete commit: Leaf 2b** — lift the shared-spine LI brick
`linearIndependent_normals_of_algebraicIndependent` (`CaseIII/Realization.lean:99`)
from `Fin 4` to `Fin (k+2)`: the "any `k+1` distinct-body normals are LI from
`AlgebraicIndependent ℚ q`" fact (a Vandermonde/projection argument, no `d=3`
content — recon `notes/Phase23-design.md` §"23a"(a) ll.471–476). The Leaf-2
re-scope wrongly dropped this to CHAIN; it is consumed by the KT-6.5 cut arm
`case_I_realization_h65` (Theorem55:678), a genuine general-`k` spine decl, not
just by `case_III_candidate_dispatch` (see *Current state*). Its still-`k=2`
consumers (`case_I_realization_h65`; the Realization:350 dispatch) should unify
at `k:=2` by defeq (`Fin 4` = `Fin (2+2)`, as `span_omitTwoExtensor_eq_top`'s
consumer did); add a `k=2` wrapper only if a consumer's elaboration needs the
literal signature. Re-green Realization (+ Theorem55 if a consumer touches).

**Then Leaf 3** (`notes/Phase23-design.md` §"23a"(c)) — the CaseII
rank-arithmetic numeral pass (`AlgebraicInduction/CaseII.lean`): restate
`case_II_realization_all_k` and its lemmas at `screwDim k` /
`HasGenericFullRankRealization k`, routing the eq.-(6.12) ℤ/ℕ cast plumbing
through the already-`{D V N:ℕ}`-parametric Basic helpers and the Leaf-0 kit for
the `≥2` facts. Re-green CaseII. **The three genuinely dispatch-internal Leaf-2
bricks** (`omitTwoExtensor_eq_extensor_kept`, `…_homogenize_…`,
`exists_independent_perp_pair`) stay at `Fin 4` and move to CHAIN — do **not**
re-attempt those as part of 23a's spine lift.

**Earlier commits (settled).** Leaf 0 — the `screwDim`-arithmetic kit in
`RigidityMatrix/Basic.lean`. Leaf 1a — `exists_linearIndependent_perp_of_normals`
(general rank-nullity perp-space brick; the three `d=3` helpers reduce to it).
Leaf 1b — `exists_linearIndependent_extensor_pair_perp_grade` /
`exists_extensor_in_two_panels_grade` (grade-`k` extensor bricks, with `k=2`
wrappers keeping the `Theorem55` spine green). Leaf 2 (this commit) —
`span_omitTwoExtensor_eq_top` lifted to general `k` (the N1 Lemma-2.1 spanning
fact; 23a-OD-B squareness confirmed clean), on the new mirror
`Fintype.card_subtype_fst_lt_snd` (`Mathlib/Data/Fintype/Card.lean`,
FRICTION-logged). Three of the four other recon-listed bricks correctly
re-scoped to CHAIN; the fourth (`linearIndependent_normals_of_algebraicIndependent`)
is shared-spine and re-instated as Leaf 2b (see *Current state*). The
detailed 23a recon settled OD-5 (ports verbatim) and resolved OD-2/OD-3 (4.6/4.8
exist only in fixed-tuple `d=3` form). See §"23a".

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
  The carrier lift (23a) is mechanical-but-large; the chain dispatch (CHAIN) is
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
- **23a recon: the carrier + most bricks are ALREADY general-`k`; the `2`-pins
  are call-site numerals.** Source-verified: `ScrewSpace`/`screwBasis`/
  `annihRow`/`panelSupportExtensor`/`HasGenericFullRankRealization`/`PanelHingeFramework`
  + all of Coupling/CaseI/Pinning/PanelHinge/GenericityDevice are `(k:ℕ)`. So
  23a is a **mechanical numeral-replacement + a `Fin 4` panel-incidence lift +
  a `screwDim k` arithmetic kit**, not a structure redefine. The `Fin 4`
  cluster is the `d=3` panel-geometry band (PanelLayer ll.357–838) + the
  dispatch-only `⋀²ℝ⁴` duality (Claim612, CHAIN). Full per-file map +
  6-leaf plan: `notes/Phase23-design.md` §"23a"(a),(c).
- **OD-5 = ports verbatim (no API addition, no spike).** Hard-part (d) is
  already symbolic in HEAD (`PanelLayer` coordinate layer +
  `GenericityDevice.exists_good_realization_ofParam`). The new symbolic surface
  is `screwDim k` arithmetic (`2 ≤ screwDim k` etc. that `d=3` `decide`d) — and
  `2 ≤ screwDim k` is **false at `k=0`** (`screwDim 0=1`), so the spine threads
  a `k≥1` floor. → Leaf 0 kit. Detail: §"23a"(b).
- **OD-2/OD-3 = 4.6/4.8 exist only in fixed-tuple `d=3` form.**
  `exists_chain_data_of_noRigid` (`ForestSurgery/Reduction.lean:383`) yields a
  fixed `v,a,b,c` 4-tuple, not a length-`d` chain; `splitOff_removeVertex_minimalKDof`
  (:1492) = Lemma 4.8(i). The general-`d` length-`d` chain producer is a **new
  ENTRY leaf** (not subsumed). No Lemma-5.4 short-cycle decl exists (the `d=3`
  Case III dodged it via the triangle base, corroborating OD-1).

- **Leaf 0 landed: the `screwDim`-arithmetic kit, with two recon corrections.**
  `one_le_screwDim` / `two_le_screwDim (hk : 1 ≤ k)` / `screwDim_sub_two_le_mul`
  in `RigidityMatrix/Basic.lean` (the `decide`-replacement facts for the
  symbolic-`k` spine). Two deltas from the recon spec (`§"23a"(c)`):
  `screwDim_sub_two_le_mul` takes **`2 ≤ m`**, not the recon's `1 ≤ m` — the
  latter is *false* at `m = 1` (RHS `= D·0 = 0 < D-2 = 1` at `k = 1`); the call
  site (`case_III_nested_rank_lower` l.642) has `2 ≤ |V'|` (`hGab2`) in scope.
  And the recon's `(hk)` on `screwDim_sub_two_le_mul` is **unused** (`D-2 ≤ D =
  D·1 ≤ D·(m-1)` needs nothing about `k`), so dropped. `two_le_screwDim` keeps
  its `k ≥ 1` floor (false at `k = 0`, `screwDim 0 = 1`). No consumers yet
  (Leaf 3–5 wire them); banks the one genuinely-new symbolic obligation first.

- **Leaf 1a — rank-nullity perp-space brick.** `exists_linearIndependent_perp_of_normals
  {r m} (N : Fin r → Fin (k+2) → ℝ) (hmr : m + r ≤ k + 2)` (PanelLayer): `m` LI
  vectors in `⋂ⱼ Nⱼ^⊥` (`mulVecLin` kernel + `finrank_range_add_finrank_ker`); the
  three `d=3` helpers reduce to it as `r`/`m`-instances (triplicated proof deleted).
  Two recon-scope corrections settled here: **23a-OD-A wrong** —
  `ExtensorInPanel`'s `p : Fin k → …` makes the perp arity the extensor grade `k`,
  not `Fin 2`, so the extensor bricks need `Fin k`/`Fin (k+1)` tuples (Leaf 1b);
  and **`exists_extensor_eq_panelSupportExtensor` is CHAIN** (routes through the
  `⋀²ℝ⁴` point-join↔panel-meet duality), dropped from Leaf 1.
- **Leaf 1b — grade-`k` extensor bricks.** `exists_linearIndependent_extensor_pair_perp_grade
  (hk : 1 ≤ k) (n : Fin (k+2) → ℝ)` (two LI `ScrewSpace k` extensors of `Fin k`-tuples
  in one panel: `k+1` LI panel vectors → two distinct `k`-subsets' extensors are LI by
  `exteriorPower.ιMulti_family_linearIndependent_field`, the principled replacement for
  the `k=2`-only `linearIndependent_pair_extensor_of_li3` isolation argument; needs `1≤k`
  so the two subsets differ) and `exists_extensor_in_two_panels_grade` (one nonzero
  `ScrewSpace k` extensor in two panels, `r=2,m=k`, no transversality). Each keeps a `k=2`
  wrapper (`exists_linearIndependent_extensor_pair_perp` / `exists_extensor_in_two_panels`,
  unchanged signatures) so the still-`k=2` `Theorem55` spine stays green until Leaf 4/5.
- **Leaf 2 — `span_omitTwoExtensor_eq_top` to general `k`, re-scoped.** Lifted the
  N1 spanning brick (KT Lemma 2.1: the `(k+2 choose 2)` panel-support `k`-extensors
  of `k+2` LI vectors span `ScrewSpace k`) `{pbar : Fin (k+2) → Fin (k+2) → ℝ}`;
  its only consumer `case_III_claim612` stays `k=2` and unifies at `k:=2` with no
  wrapper (`Fin 4` defeq `Fin (2+2)`). 23a-OD-B confirmed: the `decide`d card
  `Fintype.card {q // q.1<q.2} = 6` generalizes to the new mirror
  `Fintype.card_subtype_fst_lt_snd` (`(card α).choose 2` via the `{s.card=2}`
  bijection). **Recon correction (coordinator-corrected):** of the other four
  recon-listed Leaf-2 bricks, **three** (`omitTwoExtensor_eq_extensor_kept`,
  `…_homogenize_…`, `exists_independent_perp_pair`) are genuinely dispatch-internal
  (consumed only by the `⋀²ℝ⁴` duality decls `exists_line_data_of_homogeneousIncidence`
  / `exists_hduality_witness_of_panel_incidence`, CHAIN) and `k=2`-inherent in shape
  → moved to CHAIN. The fourth, `linearIndependent_normals_of_algebraicIndependent`,
  is **shared-spine, not dispatch-only** (also consumed by `case_I_realization_h65`,
  the KT-6.5 cut arm at Theorem55:678, lifted general-`k` in Leaf 5) → re-instated
  as Leaf 2b. Landed Leaf 2 = the one clean N1 brick `span_omitTwoExtensor_eq_top`.

### Promoted to TACTICS-GOLF / TACTICS-QUIRKS / FRICTION / DESIGN

- *`2 ≤ screwDim k` — `omega` can't see through `Nat.choose 2`; `Nat.choose_mono`
  route + the `k ≥ 1` floor (false at `k=0`)* → FRICTION [idiom] *`2 ≤ screwDim k`
  (and the rest of the general-`d` `screwDim`-arithmetic kit)*.
- *LI of two grade-`k` extensors of overlapping `Fin k`-tuples — restrict
  `ιMulti_family_linearIndependent_field` to the two subsets, don't isolate* →
  TACTICS-GOLF § 18 / FRICTION [idiom].
- *`Fintype.card {q : α × α // q.1 < q.2} = (card α).choose 2` (off-diagonal ordered
  pairs); the subtype-Fintype instance needs `Mathlib.Data.Fintype.Prod`* → FRICTION
  [mirrored] *`Fintype.card_subtype_fst_lt_snd`* (`Mathlib/Data/Fintype/Card.lean`).
