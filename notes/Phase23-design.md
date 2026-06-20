# Phase 23 — Case III general `d` (KT Lemma 6.13): general design recon

**Status:** live design recon (decision-support doc). This is the *general,
layer-level* sub-phase-division recon for Phase 23 — the first stage of a
two-stage recon (a later dispatch does the leaf-level recon of the FIRST
sub-phase before any build). It sketches the cut-points, their dependency
order, hard cores, and the reuse/replace/add map; it does **not** attempt
full leaf-level signatures for every sub-phase. Authoritative recon for
Phase 23; `notes/Phase23a.md` / `notes/Phase23b.md` are the per-layer work logs
and point here. **Detailed leaf-level recons done so far:** §"23a" (CARRIER,
closed) and §"CHAIN — detailed leaf-level recon" (the minted **23b**, open
2026-06-17 — decides OD-6/OD-7, flags OD-4 + the producer-shape mismatch (b)).

**Audience:** the agent opening the first Phase-23 sub-phase (and the
detailed-recon dispatch that decomposes it into buildable leaves).

**Source-verified, 2026-06-17.** Every load-bearing claim below was checked
against (i) the KT paper directly — §6.4.2 Lemma 6.13, eqs. (6.46)–(6.67),
cross-read against §6.4.1 (the `d=3` Lemma 6.10 it generalizes), §4 (Lemmas
4.6/4.8/4.9), §5.1–5.2 (Lemmas 5.1–5.4, Theorems 5.5/5.6) — and (ii) the
actual landed `def`/`theorem` in tree (grade, conclusion shape). The KT
read corrected several §1.33(C) sketch cells; the corrections are flagged
inline and in *Open decisions*.

---

## 0. What Phase 23 is, in one paragraph

KT prove Theorem 5.5 (every minimal `k`-dof-graph has a panel-hinge
realization at rank `D(|V|−1)−k`) by induction on `|V|`, four cases. Three
cases (base, not-2-edge-connected, proper-rigid-subgraph = Case I, `k>0`
split = Case II) are dimension-general and already green in the
**`screwDim 2` / `ScrewSpace 2` / `Fin 4`-pinned** `d=3` spine. The fourth,
**Case III** (`k=0`, 2-edge-connected, no proper rigid subgraph; KT §6.4),
is the crux, and is the only case whose **argument** is currently written
`d=3`-specific: KT §6.4.1 (Lemma 6.10) does it with a *fixed* 3-candidate
dispatch (vertices `v,a,b,c`), and §6.4.2 (Lemma 6.13) generalizes it to a
length-`d` chain `v₀v₁…v_d` with `d` candidate frameworks `(G,pᵢ)` and
isomorphisms `ρᵢ`. KT, p. 692: *"The proof strategy is exactly the same as
`d = 3`."* The mathematical heart of Phase 23 is **two things**: (a) lift
the whole `screwDim 2`-pinned spine to general `screwDim k`, and (b) replace
the `d=3` Case-III dispatch with the general-`d` chain dispatch + the
`⋀^{d−1}(ℝ^{d+1})` duality finish. Then complete Theorem 5.5 (general `d`),
derive Theorem 5.6 (KT §5.2 strip + projective-move-free re-add), and state
Conjecture 1.2 as a theorem.

KT's general-`d` proof, **verbatim from p. 692** (the load-bearing claim
this recon rests on): *"By Lemma 4.6, either `G` is a cycle of length at
most `d` or `G` has a chain of length `d`. If `G` is a cycle of length at
most `d`, then we are done by Lemma 5.4. Hence, let us consider the case
where `G` has a chain `v₀v₁v₂…v_d` of length `d` (where `d_G(vᵢ)=2` for
`1≤i≤d−1`)."* So the **chain entry is a genuine new dichotomy** (Lemma 4.6),
the **short-cycle base is genuinely needed** (Lemma 5.4), and the chain
interior split is **Lemma 4.8**. None of these three appear `d=3` because
`d=3` runs a fixed 3-chain `v→a→b→c` and never invokes 4.6/4.8/5.4 on the
load-bearing path (see Open decision OD-1, OD-2).

---

## 1. The carrier-grade fault line — the single biggest scoping fact

§1.33(C)'s row *"genericity device, prop:rigidity-matrix-prop11,
theorem_55 skeleton, Cases I & II — general & GREEN — the spine is `k`-free"*
is **wrong about the spine**, and this is the recon's most consequential
correction. The graph-side combinatorics is `n`-parametric, but the
**realization spine carries `screwDim 2` / `ScrewSpace 2` / `Fin 4`
literally**. Source-verified grades of the spine decls (the table names
them at general grade; the tree pins them at `d=3`):

| Decl | File | Grade as landed | Phase-23 action |
|---|---|---|---|
| `theorem_55_all_k`, `theorem_55_d3` | `AlgebraicInduction/Theorem55.lean:2248/2266` | `HasGenericFullRankRealization 2 n`, `hn : bodyBarDim n = screwDim 2` — **`d=3`-pinned** | re-state at `screwDim k` motive |
| `case_III_realization`, `case_III_realization_0dof` | `CaseIII/Realization.lean:665/518` | `HasGenericFullRankRealization 2 n`, `screwDim 2` — **`d=3`-pinned** | re-state at `screwDim k` |
| `case_III_nested_rank_lower` | `CaseIII/Realization.lean:561` | `q : α × Fin 4 → ℝ`, `screwDim 2` — **`d=3`-pinned**; *already consumes* `AlgebraicIndependent ℚ q` | re-state at `Fin (k+2)` / `screwDim k` |
| `case_III_candidate_dispatch` | `CaseIII/Realization.lean:181` | `q : α × Fin 4 → ℝ`, fixed `v,a,b,c` 3-candidate, `screwDim 2`, `h622lb` over `Fin 4` — **`d=3`-pinned AND structurally fixed-3-candidate** | **REPLACE** by the chain dispatch |
| `case_II_placement_eq612` | `AlgebraicInduction/CaseII.lean:71` | `screwDim k`-stated already? (check) | confirm grade in detailed recon |

**Two distinct lifts are bundled in the table's one "spine" row.** (i) A
*mechanical carrier lift* — re-state the `screwDim 2`-pinned spine decls
(`theorem_55_*`, `case_III_realization*`) at `screwDim k`; their *proofs*
compose general-grade bricks, so this is plumbing once the carrier API is
general. (ii) A *genuinely new argument* — `case_III_candidate_dispatch`
is not merely `d=3`-graded but **structurally a fixed 3-candidate dispatch**
(`v,a,b,c`, `e_a,e_b,e_c`), which is exactly KT's §6.4.1; the general-`d`
Lemma 6.13 replaces it with the `d`-candidate chain dispatch (eqs.
6.46–6.67). The recon's sub-phase cut runs **along this fault line**.

**The general-`d` carrier API (ScrewSpaceCarrier §6) is a prerequisite for
both.** The opaque `ScrewSpace k` `def` landed (22l) with a general-`k`
`mk`/`val`/`equivExteriorPower`/instance API (`RigidityMatrix/Basic.lean`),
but every *consumer* in the spine was migrated at `k=2` only. The
general-`d` "part 2" (ScrewSpaceCarrier-design.md §6) is the migration of
those consumers to symbolic `k` — and §6 flags the real unknown: at `k=2`,
`screwDim 2 = 6` is concrete and many proofs lean on `fin_cases`/`decide`;
at general `k`, `screwDim k = (k+2).choose 2` is symbolic and the
`screwBasis`/`annihRow` coordinate machinery (hard-part (d)) gets exercised
symbolically for the first time. **This recon folds the general-`d`
carrier-API work into sub-phase 23a (below), not a standalone sub-phase** —
the migration surface *is* the carrier-lift surface, and §6's whole point
was to shape the API against the general-`d` usage rather than freeze it
speculatively.

---

## 2. The sub-phase division

Four layers, dependency-ordered, tracked by **stable codes** —
**`CARRIER`**, **`CHAIN`**, **`ENTRY`**, **`ASSEMBLY`**. The cut isolates the
**mechanical carrier lift** (`CARRIER`) from the **new chain argument**
(`CHAIN`), puts the **base ingredients** the chain entry needs (`ENTRY`) where
they actually block, and ends with **assembly + Thm 5.6 + Conjecture 1.2**
(`ASSEMBLY`). The first layer is `CARRIER`; rationale in §3.

> **Naming convention (set 2026-06-17).** Layers are referred to by these
> codes until they open; a **letter (23a, 23b, …) plus a `notes/Phase23X.md`
> work log are minted only when a layer is about to open**, so a later split
> (e.g. `CHAIN` into two) does not renumber-churn the rest. **`CARRIER` is the
> opening layer = the minted `23a`** (its leaf-level recon is §"23a" below, its
> work log is `notes/Phase23a.md`); `CHAIN`/`ENTRY`/`ASSEMBLY` stay code-only
> until their turn. This is the project's standing "mint a sub-letter only when
> its turn comes" discipline (`notes/MolecularConjecture.md`; top-level
> `CLAUDE.md` *When this commit opens a phase*), refined to use codes meanwhile.

### `CARRIER` (the opening layer = sub-phase 23a) — General-`d` carrier lift of the spine

**Scope.** Lift the `screwDim 2`/`ScrewSpace 2`/`Fin 4`-pinned realization
spine to symbolic `screwDim k`, and complete the ScrewSpaceCarrier §6
general-`d` consumer migration in step. This is the carrier-API "part 2"
the 22l refactor unblocked but deferred. Concretely: re-state
`theorem_55_all_k` / `theorem_55_d3` (→ a general `theorem_55` at the
`screwDim k` motive), `case_III_realization` / `_0dof` /
`case_III_nested_rank_lower`, the `case_II_*` placement bricks, and the
GenericityDevice / Coupling / CaseI consumers, replacing `Fin 4` →
`Fin (k+2)`, `screwDim 2` → `screwDim k`, `HasGenericFullRankRealization 2`
→ `… k`, and re-greening each file along the import spine
(RigidityMatrix → PanelLayer → Pinning → PanelHinge → GenericityDevice →
Coupling → CaseI → CaseII → CaseIII → Theorem55). The Case-III *graph
dispatch* (`case_III_candidate_dispatch`) is **out of 23a scope** — it is
replaced wholesale in CHAIN, so 23a leaves the Case-III `hsplit` arm carrying
the `d=3` dispatch as an explicit hypothesis (green-modulo, the project's
standing idiom) and lifts everything else.

**Hard core.** The symbolic-`k` stress on the `screwBasis`/`annihRow`
coordinate machinery (ScrewSpaceCarrier §6, hard-part (d)) and on the
`screwDim k = (k+2).choose 2` arithmetic that `d=3` discharged by `decide`.
Not deep mathematics — but the *largest* mechanical surface in Phase 23, and
the one most likely to surface a needs-thought transport (per §6, the
general-`k` coordinate transport is unproven at symbolic grade; the d=3
probe found it defeq-free at `k=2` only).

**Dependency position.** First — everything downstream is stated over the
carrier, so the chain dispatch (CHAIN) and the duality (also CHAIN) must be
written at general grade, which presupposes the spine is general grade.

**Reuse/replace/add map** (keyed to §1.33(C), source-corrected):
- *Reuse verbatim, already general & GREEN:* Lemma 2.1
  `omitTwoExtensor_linearIndependent_of_li` (`Extensor.lean:563`, `{e:ℕ}`),
  Claim 6.11 `exists_redundant_panelRow_ab_of_finrank_eq`
  (`CaseIII/Candidate.lean:126`, `screwDim k`/`ScrewSpace k`/`Fin (k+2)` —
  **verified general**), `linearIndependent_sum_augment_candidateRow`
  (`RigidityMatrix/Basic.lean:1231`, `ScrewSpace k`, graph-free), the
  `complementIso`/`topEquiv`/`pairingDualEquiv` meet API (`Meet.lean`,
  `{j:ℕ} (hj : j ≤ k+2)` — dimension-parametric).
- *Re-state at general grade (lift, this sub-phase):* the spine table in §1.
- *Add:* the general-`k` consumer migration (ScrewSpaceCarrier §6).

### CHAIN — The general-`d` Case-III chain dispatch + the `⋀^{d−1}` duality

**Scope.** Replace the fixed-3-candidate `case_III_candidate_dispatch` with
the general-`d` chain dispatch of Lemma 6.13: given the base framework
`(G₁,q₁)` on the chain-split `G₁` and the isos `ρᵢ` (eq. 6.54), build the
`d` candidate frameworks `(G,p₀),…,(G,p_{d−1})` (eqs. 6.47/6.48/6.57/6.59),
do the matrix bookkeeping (eqs. 6.49–6.64) that embeds `R(G₁,q₁)` as a
submatrix and reduces each `R(G,pᵢ)` to a top-left `D×D` block `Mᵢ` plus
`R(G₁∖(v₀v₂)_{i*}, q₁)`, establish the "±r chain" (eq. 6.66) so each `Mᵢ`
fails full rank iff `r ⊥ C(Lᵢ)`, and finish via the `⋀^{d−1}(ℝ^{d+1})`
duality + Lemma 2.1 (eq. 6.67): take `d+1` points `p₀…p_d` (one per panel
incidence pattern), whose `(d−1)`-extensors of `d−1`-subsets span a
`(d+1 choose d−1) = D`-dimensional space, forcing some `Mᵢ` to have full
rank.

**Scope expansion (23a Leaf-5 build-contact finding — corrects §"23a"(a)/(d)
and §1).** The recon assumed the realization spine was "general & GREEN" modulo
*only* this chain dispatch. False: lifting the spine (23a Leaf 5,
`theorem_55_minimalKDof_k_all_k`) found that the **base / cut / Case-I / M4-
forgetful-map** realization producers — `theorem_55_base_producer`,
`case_cut_edge_realization{,_gp}`, `case_I_dispatch` (+ `case_I_realization_h65`),
and `hasPanelRealization_of_generic` — are **also `d=3`-pinned**: each bottoms
out in `Fin 4` panel geometry and the `⋀²ℝ⁴` duality
`exists_extensor_eq_panelSupportExtensor` (the forget map provably calls it,
`GenericityDevice.lean:1936/1945`; every conditioned-pair producer routes
through the forget map for its bare `HasPanelRealization` half). They are **not**
liftable by 23a's numeral pass (unlike the inductive CaseII/CaseIII arms, which
transport the IH realization additively). 23a therefore carries them as four
further explicit `h…` hypotheses (`hbase_k`/`hcut_k`/`hcontract_k`/`hforget_k`,
all green-modulo, never `sorry`; the `d=3` wrapper fills them zero-carry). **So
CHAIN's `⋀^{d−1}(ℝ^{d+1})` duality is the prerequisite to lift these four
producers off `Fin 4`** — that lift is added to CHAIN's deliverables (**OD-7
decided 2026-06-17: fold into CHAIN's tail after the duality CHAIN-3, not a
dedicated successor — they are a direct corollary of the duality lift; caveat
flagged in §"CHAIN — detailed leaf-level recon" (e)**), on top of the chain
dispatch below. Detail: `notes/Phase23a.md` *Hand-off* + Leaf-5 *Decisions*
entry; the leaf plan + the producer-shape flag (b) are §"CHAIN — detailed
leaf-level recon".

**Hard core.** Two parts, both genuinely new:
1. **The `d`-fold chain bookkeeping (eqs. 6.59–6.64).** Index-heavy but
   KT calls it "exactly the same as `d=3`." The reusable graph-free
   `linearIndependent_sum_augment_candidateRow` augments by **one** Unit
   candidate; the chain needs `d` candidates indexed `0…d−1`, so this is
   the augment generalized to a `d`-fold `Sum`/`Fin d`-indexed family +
   the row-correspondence eq. (6.62)/(6.66) along the chain. The
   `case_III_candidate_dispatch` body (a fixed `v,a,b,c` term, ~hundreds of
   lines) is the `d=3` template to generalize.
2. **The `⋀^{d−1}(ℝ^{d+1})` duality (the N3b analog).** Replaces the
   bespoke `⋀²ℝ⁴` route. Per §1.33(D) (source-confirmed): do **NOT** build
   a general Hodge-star / regressive-product / star-operator API — KT never
   needs it; the whole content is "the join of `d−1` points spanning a
   `(d−2)`-flat = the meet of the panels containing it, as the same Plücker
   line," which is the **top-power-is-1-dimensional** fact. The route that
   generalizes is the 22f "happy accident":
   `extensor_mem_range_map_subtype_of_mem` +
   `exists_smul_eq_of_mem_range_map_subtype` (`Meet.lean:648/676`) — place
   both members in `range(exteriorPower.map (d−1) W.subtype)`, which is
   `(W choose d−1)`-dim. **Source-verified nuance / correction to (D):**
   those two lemmas as landed are **`Fin 4`/`⋀²`-PINNED**
   (`W : Submodule ℝ (Fin 4 → ℝ)`, `⋀[ℝ]^2`, `finrank_exteriorPower_two_eq_one`).
   The *route* generalizes (it rests on general mathlib —
   `exteriorPower.finrank_eq`, `exteriorPower.map_injective_field`,
   `map_apply_ιMulti` + the general `topEquiv`/`pairingDualEquiv` mirrors),
   but the lemmas themselves must be **re-stated** at `⋀^{d−1}(ℝ^{d+1})`
   with the general `finrank (⋀^{d−1} W) = (dim W choose d−1)`. This is
   "modest, mostly-mathlib API at concrete grade," not a verbatim reuse —
   the (D) cell "ALREADY PARTLY LANDED" is true only as a *template*.

**Dependency position.** After 23a (needs the general-grade carrier + spine
to state its conclusion `HasGenericFullRankRealization k n G`). **OD-6 decided
at the CHAIN open (23b, 2026-06-17): five leaves within ONE sub-phase** (the
arm-realization engine they feed is already general-`k`, so neither hard core
stands alone as a deliverable; split at contact only if the chain bookkeeping
proves larger than estimated). The detailed leaf plan + the load-bearing
producer-shape flag are §"CHAIN — detailed leaf-level recon" below.

**Reuse/replace/add map:**
- *Reuse verbatim:* Claim 6.11 (the chain's redundant `(v₀v₂)_{i*}` row is
  "always exists by Claim 6.11," KT p. 693), Lemma 2.1 (the eq. 6.67
  span-`D` finish, KT p. 698).
- *Replace:* `case_III_candidate_dispatch` (fixed-3 → `d`-chain); the
  `⋀²ℝ⁴` N3b leaf (`complementIso_smul_eq_extensor_join`,
  `exteriorPower_basis_toDual_eq_pairingDual_comp_map`, both `Fin 4`-pinned
  in `Meet.lean`) → `⋀^{d−1}(ℝ^{d+1})`.
- *Add:* the `d`-fold candidate augment; the chain row-correspondence
  (eq. 6.62), the ±r chain (eq. 6.66); the `d+1`-points-in-general-position
  construction (eq. 6.67) — a **new algebraic-independence site** (the
  panel coefficients are alg-indep over ℚ so any `j` hyperplanes meet in a
  `(d−j)`-flat; AlgebraicIndependence.md row, see OD-4).

### ENTRY — Chain-entry ingredients: Lemma 4.6 dichotomy + Lemma 5.4 short-cycle base + Lemma 4.8 split-off

**Scope.** The three ingredients KT's general-`d` Case III invokes *to
enter* the chain argument, which `d=3` did not need on the load-bearing
path: (4.6) the chain-or-short-cycle dichotomy (a degree-2 minimal-0-dof
graph with no proper rigid subgraph is a short cycle or has a length-`d`
chain), (5.4) the short-cycle base (a cycle of length `3≤|V|≤D` realizes as
an infinitesimally rigid nonparallel panel-hinge framework — Crapo–Whiteley
[4]/[34]), and (4.8) the chain-interior split-off minimality (`Gᵢ = splitOff
at vᵢ` is minimal 0-dof). **Whether this is a standalone sub-phase or folds
into CHAIN is an open decision (OD-1/OD-2/OD-3)** — it hinges on whether 4.6/
4.8 already exist subsumed in the green Phase-20 `minimal_kdof_reduction`
machinery and whether 5.4 is genuinely on the Lean-load-bearing path or a
KT-narrative dependency (the `d=3` Case III dodged 5.4 entirely — §1.33(B.1)).

**Hard core.** Lemma 5.4 (the cycle realization) if it is genuinely
load-bearing: it is its own deferred sub-phase per risk #4 (the
panel-realization of a cycle with independent hinge extensors = the
Crapo–Whiteley projective fact), the one piece here that is real new panel
content rather than a Phase-20 graph fact. 4.6/4.8 are combinatorial and may
already be in tree.

**Dependency position.** Feeds CHAIN's chain entry (the dispatch needs to know
it is in the chain case, with a valid length-`d` chain and the base
framework on `G₁`). Could land *before* CHAIN if 5.4 is the bottleneck, or
*concurrently* if 4.6/4.8 are subsumed and 5.4 is narrative-only — see OD.

**Reuse/replace/add map:**
- *Check Phase-20 status:* Lemma 4.6 / Lemma 4.8 — no explicit blueprint
  node found at recon time; may be subsumed in `minimal_kdof_reduction`
  (`Molecular/Induction/`). The detailed recon must `lean_local_search`
  these before scoping. (OD-3.)
- *Add (if load-bearing):* Lemma 5.4 cycle base — its own leaf/sub-phase
  (risk #4; the project decided 2026-06-03 to *formalize, not cite* it as
  genuine panel content).

### ASSEMBLY — Assembly: Theorem 5.5 (general `d`) → Theorem 5.6 → Conjecture 1.2

**Scope.** With `CARRIER`–`ENTRY` green, compose: complete `theorem_55` at general `d`
(the Case-III arm now discharged by the CHAIN chain dispatch + ENTRY entry),
re-green `prop:rigidity-matrix-prop11` + its `hub` at general grade, derive
**Theorem 5.6** (KT §5.2: strip `G` to a minimal `k`-dof spanning subgraph,
realize via Thm 5.5, re-add the deleted edges — the rank only grows, using
projective invariance to arrange `Π(u)∩Π(v) ≠ ∅`), and **state Conjecture
1.2 as a theorem** (the panel-hinge ⇔ body-hinge realizability equivalence,
which combined with Phase 16's Prop 1.1 is the conjecture). The `d=3`
versions of the Thm 5.5→5.6 push (`rankHypothesis_of_theorem_55_d3`,
`theorem_55_6_d3`) are the templates — mostly carrier-lift + dropping the
`hn : bodyBarDim n = screwDim 2` specialization.

**Hard core.** Mostly composition once `CARRIER`–`ENTRY` land; the genuine content is
the general-`d` `hub` partition brick of `prop:rigidity-matrix-prop11` (a
Phase-19-partition obligation, **Track-independent**, already noted
multi-commit in the `d=3` case) and the projective-invariance step of
Thm 5.6 at general `d` (the `d=3` re-add was "projective-move-free" because
two distinct hyperplanes through the origin always meet — confirm that holds
at general `d`; KT §5.2 uses projective invariance [4, §3.6] explicitly).

**Dependency position.** Last; gates Cor 5.7 (Phase 26). Phases 24–25 (the
`d=3` bar-joint matroid, projective duality) can proceed in parallel — they
don't gate on the rank theorem until Cor 5.7.

**Reuse/replace/add map:**
- *Reuse / lift:* `rankHypothesis_of_theorem_55_d3` (`Theorem55.lean:2312`),
  `theorem_55_6_d3`, the strip `exists_isMinimalKDof_spanning_subgraph`, the
  re-aim `reaimSub`, the monotonicity `finrank_infinitesimalMotions_le_of_graph_le`.
- *Add:* the general-`d` `hub` partition; the Conjecture 1.2 statement node;
  the general-`d` projective-invariance arrangement (if not free).

---

## 3. Recommended sequence — and why 23a is first

**Sequence: 23a → {CHAIN, ENTRY interleaved} → ASSEMBLY.** ENTRY may lead CHAIN if
Lemma 5.4 turns out to be the long pole; CHAIN may split on contact.

**Why 23a (the carrier lift) is first, not CHAIN (the chain argument):**
1. *Everything downstream is stated over the carrier.* The chain dispatch
   (CHAIN) concludes `HasGenericFullRankRealization k n G` and consumes
   `screwDim k` rank bounds; the `⋀^{d−1}` duality is stated over
   `Fin (k+2) → ℝ`. Both must be *written* at general grade, which is only
   coherent once the spine they plug into is general grade. Building CHAIN
   first would force every new lemma to carry a private `screwDim 2`→`k`
   bridge, exactly the friction the carrier lift removes once.
2. *It is the largest mechanical surface and the one most likely to surface
   a blocking transport.* ScrewSpaceCarrier §6 explicitly flags the
   symbolic-`k` `screwBasis`/`annihRow` transport as unconfirmed at general
   grade (the d=3 probe found it defeq-free only at `k=2`). Doing 23a first
   surfaces any such blocker before the hard *new* mathematics of CHAIN is
   built on top — the project's design-pass-first discipline (don't grind
   research-shaped work over an unverified foundation).
3. *It is the natural home for the deferred carrier "part 2."* 22l deferred
   the general-`d` API migration to this boundary precisely so it lands
   against the now-known general-`d` usage; 23a is that landing.

**FIRST sub-phase = 23a.** The next dispatch is the **23a detailed,
leaf-level recon** (read the spine files end-to-end, enumerate the
`screwDim 2`/`Fin 4`/`ScrewSpace 2` reach-ins along the import spine, run
the ScrewSpaceCarrier §6 opacity-probe-style per-layer readiness check at
symbolic `k`, and cut 23a into buildable leaves). Not a build.

---

## 4. Open decisions (clause-(ii) flags — honest unknowns this recon could
not settle from the source)

- **OD-1. Is Lemma 5.4 (short-cycle base) genuinely on the Lean-load-bearing
  path at general `d`?** KT p. 692 invokes it explicitly: *"If `G` is a
  cycle of length at most `d`, then we are done by Lemma 5.4."* So at
  general `d` the short-cycle base is a **real branch of the Case-III case
  split** — unlike `d=3`, where Case III's `|V|=3` floor was the triangle
  handled inline (the `d=3` assembly dodged 5.4, §1.33(B.1)). *Unsettled:*
  whether the general-`d` formalization can likewise dodge it (e.g. if the
  chain dichotomy can be arranged so the cycle branch is vacuous or folded
  into the base case) or must formalize 5.4 as KT does. If load-bearing,
  5.4 is its own leaf/sub-phase (risk #4: genuine panel content, the
  Crapo–Whiteley cycle realization). **Present as an open branch; do not
  pre-commit a cut that assumes 5.4 is free.**

- **OD-2. Does the general-`d` chain entry (Lemma 4.6 dichotomy) reduce to
  Phase-20 machinery, or is it a new combinatorial prerequisite?** KT's
  4.6 says a 2-edge-connected minimal-0-dof graph with no proper rigid
  subgraph either is a short cycle or has a length-`d` chain. The `d=3`
  assembly entered Case III with a degree-2 vertex `v` and its two
  neighbours `a,b` (the `splitOff v a b` shape) — it never needed the full
  4.6 dichotomy because the 3-candidate dispatch only needed *one* degree-2
  vertex plus its `a`-neighbour's `c`. The general chain needs the *whole*
  length-`d` chain `v₀…v_d`. *Unsettled:* whether `minimal_kdof_reduction`
  (Phase 20) already produces a chain of the needed length, or only the
  single degree-2 split. **The detailed recon must check this in tree
  before scoping ENTRY.**

- **OD-3. Do Lemmas 4.6 / 4.8 already exist (subsumed) in the green
  Phase-20 `minimal_kdof_reduction`, or are they new nodes?** §1.33(C)
  flagged "no explicit node found; may be subsumed." The recon could not
  confirm from prose alone. If subsumed, ENTRY shrinks to "Lemma 5.4 (modulo
  OD-1)"; if not, 4.6/4.8 are new combinatorial leaves. **`lean_local_search`
  for the chain dichotomy / split-off-minimality lemmas is the first
  detailed-recon task for ENTRY.**

- **OD-4. Does the general-`d` N3a (the `d+1` points in general position,
  eq. 6.67) take the existence/Zariski route like the `d=3` N3a, or does it
  force the algebraic-independence hammer?** KT p. 698 states it via alg-
  independence: *"the set of the coefficients … is algebraically independent
  over the rational field. Therefore, for any `j` hyperplanes among them,
  their intersection forms a `(d−j)`-dimensional affine space."* The `d=3`
  N3a was **AVOIDED** (existence route — exhibit one explicit seed where the
  4 points are affinely independent; AlgebraicIndependence.md row #106),
  because at `d=3` the construction is explicit (triple-intersection +
  cross-products). *Unsettled at general `d`:* whether an explicit `d+1`-
  point construction exists (giving the existence route again) or the
  symbolic `j`-hyperplanes-meet-in-`(d−j)`-flat genericity genuinely needs
  alg-independence. The seed-rank kernel (`case_III_nested_rank_lower`)
  **already** consumes `AlgebraicIndependent ℚ q` at `d=3`, so the
  alg-independence machinery is live regardless — but the *N3a points* step
  may or may not be a *new* alg-independence site. **A general-`d` row is
  added to `AlgebraicIndependence.md` either way (the standing instruction);
  the relaxation question (§2 risk (c): does the touched-subgraph family
  grow with `d`?) is exactly this OD.**

- **OD-5. Does the general-`d` carrier lift force a motive/carrier change?**
  ScrewSpaceCarrier §6's whole concern was that freezing the opaque API
  against `d=3`-only usage risks a Phase-23 reshape. *Unsettled:* whether
  the symbolic-`k` `screwBasis`/`annihRow` transport (hard-part (d), proven
  defeq-free only at `k=2`) ports verbatim or needs an API addition. **The
  23a detailed recon's opacity-readiness probe at symbolic `k` settles
  this** — and it is the load-bearing reason 23a is first.

- **OD-6. Does CHAIN split (chain bookkeeping vs duality) on contact?** The
  two hard cores (eqs. 6.59–6.64 chain bookkeeping; the `⋀^{d−1}` duality
  finish, eq. 6.67) are largely independent. Whether they are two leaves of
  one sub-phase or warrant a split is a contact decision for the CHAIN open,
  not settleable now.

---

## 5. Source pointers (verified 2026-06-17)

- **KT Lemma 6.13 (general `d`):** §6.4.2, printed pp. 692–698, eqs.
  (6.46)–(6.67). The chain `v₀…v_d`, the `d` candidates `(G,pᵢ)`, isos `ρᵢ`
  (6.54), candidate construction (6.47/6.48/6.57/6.59), matrix bookkeeping
  (6.49–6.64), the `M₀…M_{d−1}` full-rank disjunction (6.65), the ±r chain
  (6.66), the `⋀^{d−1}` + Lemma 2.1 finish (6.67).
- **KT Lemma 6.10 (`d=3`, the template):** §6.4.1, printed pp. 687–691,
  eqs. (6.12)–(6.45); Claims 6.11 (redundant `ab`-row, eq. 6.23), 6.12
  (M₁/M₂/M₃ full-rank disjunction, eqs. 6.42–6.45).
- **Chain entry:** Lemma 4.6 (chain-or-cycle), Lemma 4.8 (split-off
  minimality), §4, printed pp. 666–667; Theorem 4.9 (printed p. 666).
- **Base:** Lemma 5.3 (double-edge, printed p. 669), Lemma 5.4 (cycle base
  `3≤|V|≤D`, [4,34], printed p. 670).
- **Thm 5.6:** §5.2, printed p. 670 (strip + projective-move-free re-add).
- **Generic nonparallel / alg-independence:** §5.1, printed p. 668 (panel
  coefficients alg-indep over ℚ — the eq. 6.67 / OD-4 anchor).
- **Lean spine (grades in §1):** `AlgebraicInduction/Theorem55.lean`,
  `CaseIII/{Realization,Candidate,Arms,Relabel}.lean`,
  `RigidityMatrix/{Basic,Bricks,Claim612}.lean`, `Meet.lean`,
  `Extensor.lean`.
- **Deferred carrier API:** `notes/ScrewSpaceCarrier-design.md` §6.
- **Alg-independence tracker:** `notes/AlgebraicIndependence.md` (Phase-23
  row, §2 risk (c)).

---

## 23a — detailed leaf-level recon

**Status:** detailed-recon done (docs only, 2026-06-17, source-verified +
LSP-probed against the landed tree). Decomposes 23a (§2) into buildable
leaves with exact target signatures, settles **OD-5**, and resolves the
cheap **OD-2/OD-3** in passing. The general-recon §1–§5 above is the parent;
this section is the leaf plan `notes/Phase23a.md` hands off to.

### (a) Per-file reach-in enumeration along the import spine

Spine order (`ScrewSpaceCarrier-design.md` §5): RigidityMatrix/{Basic,
Bricks,Claim612} → PanelLayer → Pinning → PanelHinge → GenericityDevice →
Coupling → CaseI → CaseII → CaseIII/{Arms,Candidate,Relabel,Realization} →
Theorem55. The **central source-verified correction to §1**: the carrier
*infrastructure* and most *bricks* are already general-`k`; the `screwDim 2`/
`Fin 4`/`…2` pins are **numeral specializations at call sites**, not
definitional pins. The lift is therefore mechanical numeral-replacement
(`2`→`k`, `Fin 4`→`Fin (k+2)`, `screwDim 2`→`screwDim k`, `…Realization 2`→
`… k`) **plus** a small symbolic-arithmetic kit and a `Fin 4` panel-geometry
lift — *not* a structure redefinition.

Per-file, dependency-ordered (this ordering IS the leaf sequence):

| File | Pin reach-ins | Lift status for 23a |
|---|---|---|
| **RigidityMatrix/Basic** | `screwDim`=`(k+2).choose 2` (general); `ScrewSpace`/`mk`/`val`/`equivExteriorPower`/3 instances all `(k:ℕ)`; `screwSpace_finrank` uses `change`+`exteriorPower.finrank_eq` (general, no `decide`). 1×`screwDim 2`/`ScrewSpace 2` in a doc-comment only. | **already general.** Add only the `screwDim k` arithmetic kit (below). |
| **RigidityMatrix/Bricks** | none | none |
| **RigidityMatrix/Claim612** | 68×`Fin 4`, 15×`ScrewSpace 2`. **Two families:** (i) general-`k` `{k:ℕ}` algebra (`eq_zero_of_annihilates_span_top`, `mem_hingeRowBlock_iff`, `linearIndependent_sum*_candidateRow*`, `candidateRow_ne_zero`, …) — done; (ii) **`Fin 4` panel-geometry/duality** (`span_omitTwoExtensor_eq_top`, `omitTwoExtensor_*`, `exists_independent_perp_pair`, `exists_homogeneousIncidence_of_normals`, `exists_*complementIso*`, `exists_hduality_witness*`). | family (ii) splits: the **incidence/extensor** lemmas feeding the spine lift in 23a; the **`⋀²ℝ⁴` duality** lemmas (`exists_homogeneousIncidence_of_normals`, `exists_complementIso_ne_zero_of_homogeneousIncidence`, `exists_hduality_witness*`) are **consumed only inside `case_III_candidate_dispatch`** → CHAIN. |
| **PanelLayer** | 46×`Fin 4` vs **174×`Fin (k+2)`** — mostly general. `Fin 4` cluster is the `d=3` **panel-incidence geometry** (≈ll.357–838): `exists_two_perp_of_linearIndependent_normals`, `exists_three_perp`, `exists_linearIndependent_extensor_pair_perp`, `exists_extensor_eq_panelSupportExtensor`, `exists_extensor_in_two_panels`. The `fin_cases`/`decide` (33) are all in this band. | **`screwBasis`/`annihRow`/`annihRowPoly`/`panelSupportExtensor`/`panelSupportPoly`/`triLI_subpairs`/`exists_triangle_normals` are ALL already `(k:ℕ)`** (ll.232,960,1091,1164,1252,1271,1408). Lift only the `Fin 4` incidence band (the dimension count `finrank ℝ (Fin 4→ℝ)=4` → `=k+2`). |
| **Pinning** | 0 `Fin 4`/`screwDim 2`; 1 `fin_cases` (general). | none (general). |
| **PanelHinge** | 0. `PanelHingeFramework (k:ℕ)`, `HasGenericFullRankRealization (k n:ℕ)`, `HasPanelRealization (k n:ℕ)`, `ofNormals (q:α×Fin (k+2)→ℝ)`, `IsGeneralPosition` all parametric. | none (general — and opacity-neutral, L3 probe). |
| **GenericityDevice** | 0 `Fin 4`/`screwDim 2`; the 4×`…Realization 2` are in the forgetful map `hasPanelRealization_of_generic`. The 5× `change … (Pi.single a (screwBasis k t))` blocks (hard-part (d)) are **already `screwBasis k`**; `exists_good_realization_ofParam` is the device proof, stated `screwDim k * card α`. | none for the device; the forgetful-map `2`-pins lift with the `HasGenericFullRankRealization` numeral pass. |
| **Coupling** | **0 `screwDim 2`/`Fin 4`/`…2`** — fully general (`extProj`, `degeneratePlacement (nrm:α→Fin (k+2)→ℝ)`, all coupling producers `ScrewSpace k`). | **none.** |
| **CaseI** | **0 `screwDim 2`/`Fin 4`/`…2`** — fully general (`case_I_realization {n k:ℕ}` is dof-`k`; dimension general). | **none.** |
| **CaseII** | 26×`screwDim 2`, 8×`ScrewSpace 2`, 4×`…Realization 2`. All in `case_II_realization_all_k`'s **rank arithmetic** (`screwDim 2 * (|V|-1) - (k-1)`, the eq.-(6.12) ℤ/ℕ-cast plumbing) + the conclusion numeral. No `decide`/`fin_cases`. | lift: numeral pass + the `screwDim k` arithmetic kit (the cast plumbing is `toNat_le_of_add_pred_eq`-style, already `{D V N:ℕ}`-parametric in Basic). |
| **CaseIII/{Arms,Candidate,Relabel}** | Arms: 8×`…Realization 2` (incl. `case_III_hsplit_producer`, which calls `hasGenericFullRankRealization_of_triangle (k:=2)` — the triangle brick is **already `(k)`-parametric**) + 8 `fin_cases`/`decide` in the M2/M3-arm geometry. Candidate: 0 literal pins, but the Claim-6.11 family is `ScrewSpace k`/`Fin (k+2)` (general); `caseIIICandidate`/`case_III_old_new_blocks`/`case_III_rank_certification` consume the `q : α × Fin 4` dispatch shape. Relabel: 0 pins (general `ofNormals_relabel` machinery). | numeral pass on Arms' `…Realization 2`; the M2/M3 geometry + `caseIIICandidate` chain bookkeeping is **CHAIN** (it is the dispatch internals). 23a stops at the producer *skeleton* `case_III_hsplit_producer` shape, leaving `hcand` explicit. |
| **CaseIII/Realization** | 13×`Fin 4`, 12×`screwDim 2`, 11×`…Realization 2`, 7×`fin_cases`/`decide`. **`case_III_candidate_dispatch` (181–517)** is the structurally-fixed-3-candidate body (`q:α×Fin 4`, fixed `v,a,b,c`, the `linearIndependent_normals_of_algebraicIndependent` (l.99, `Fin 4`-pinned) + `exists_homogeneousIncidence`+`exists_complementIso` `⋀²ℝ⁴` discriminator at ll.351–353) → **CHAIN replace.** `case_III_nested_rank_lower` (561), `case_III_realization_0dof` (518), `case_III_realization` (665) are `screwDim 2`/`q:α×Fin 4`-pinned **spine** decls. | lift `_nested_rank_lower`/`_realization`/`_0dof` (numeral + arithmetic kit); their proofs compose general bricks **except** the `case_III_candidate_dispatch` call → that call becomes the green-modulo `hcand` hypothesis (boundary (d) below). |
| **Theorem55** | 27×`Fin 4`, 73×`screwDim 2`, 40×`…Realization 2`, 21×`…Framework 2`, 6 `decide`. `theorem_55_minimalKDof_k` (2176) is the dof-`k` induction spine, **dimension-pinned at `screwDim 2`** via `hn`; its callback map wires base/cut/CaseI/CaseII/CaseIII bricks at `(k:=2)`. The `theorem_55_d3`/`_all_k` wrappers discharge `hD`/`hn` by `decide`. The cut/coupling helpers carry the assembly `q:α×Fin 4` / `Pi.single 0 1 : Fin 4→ℝ` / `Set.powersetCard (Fin 4) 2`. | the **largest numeral surface**; lift `theorem_55_minimalKDof_k` to `HasGenericFullRankRealization k`, restate `hn:bodyBarDim n = screwDim k` + an `hD` floor giving `screwDim k ≥ 2` (see kit), thread the green-modulo `hcand` up. `rankHypothesis_of_theorem_55_d3` / Thm-5.6 push is **ASSEMBLY** (not 23a). |

`linearIndependent_normals_of_algebraicIndependent` (Realization l.99,
`Fin 4`-pinned) is consumed **both** inside the dispatch (CHAIN) **and** by
`Theorem55.lean:565/678` (cut/base spine) and `Pinning` — so it is a **shared
brick 23a must lift** to `Fin (k+2)` (it is the "any `k`+1 distinct-body
normals are LI from alg-indep" fact; generalizes by the same Vandermonde/
projection argument, no `d=3` content).

### (b) OD-5 verdict — **PORTS VERBATIM. No carrier-API addition; no spike.**

The coordinate transport (hard-part (d): `screwBasis`/`annihRow`) **is already
written at symbolic `k` in the landed tree and already compiles.** Three
source facts, each verified, settle it:

1. **`screwBasis (k:ℕ)`** (PanelLayer:1252)
   `= (Pi.basisFun ℝ (Fin (k+2))).exteriorPower k |>.map (equivExteriorPower k).symm`;
   **`screwBasis_repr_apply := rfl`** at general `k` (1261); the whole
   `annihRow`/`_apply`/`_self`/`_add`/`_smul`/`span_annihRow_eq_dualAnnihilator`/
   `annihRowPoly`/`_eval` family (1271–1419+) is `(k:ℕ)`, proved through
   **abstract `Module.Basis` API** (`repr_self_apply`, `coord_apply`,
   `Basis.ext`, `sum_repr`) — zero `k=2`-concreteness, zero `decide`/`fin_cases`.
2. **`GenericityDevice.exists_good_realization_ofParam`** — the device proof
   exercising the dual-basis coordinate machinery — is stated
   `screwDim k * Fintype.card α` over `Set.powersetCard (Fin (k+2)) k` /
   `Pi.basis (fun _ => screwBasis k)`, with the 5× hard-part-(d)
   `change … (Pi.single a (screwBasis k t)) = …` blocks **already symbolic**
   and green in HEAD.
3. **Carrier API + instances** are `(k:ℕ)` with `inferInstanceAs`
   (ScrewSpaceCarrier §5 OQ4 confirmed instances resolve symbolically);
   `equivExteriorPower` is the `cast (ScrewSpace_def k)` form, `k`-parametric.

So ScrewSpaceCarrier §6's worry — "hard-part (d) gets exercised symbolically
*for the first time* in Phase 23" — is **already false in the landed source**:
the coordinate layer was authored general from the start and the `d=3` usage
only ever specialized the *numerals around it*, never the transport. **OD-5
resolves to "ports verbatim"; 23a needs no carrier-API addition and no
build-spike.** *Residual flag:* the LSP can't prove a clean cap stays at
default under the full general-`k` numeral substitution end-to-end (the same
class of unconfirmable as ScrewSpaceCarrier OQ1) — but that is a perf
observation, not a correctness blocker, and every cap is already at default
(0 overrides). If a lifted file regresses a cap, raise it locally (the
standing idiom), do not treat it as an OD-5 reopening.

**The genuinely-new symbolic surface 23a DOES introduce** is *not* the
coordinate machinery but the **`screwDim k` numeric arithmetic**: at `k=2`
the spine discharges `2 ≤ screwDim 2`, `screwDim 2 - 2 ≤ screwDim 2·(m-1)`,
`screwDim 2 = 6` by `decide`; at symbolic `k` these become `screwDim k`
obligations. **LSP-probed (2026-06-17):** `omega` does **not** close
`2 ≤ screwDim k` after `unfold screwDim` (the `choose 2 = n(n-1)/2` integer
division defeats it), and **`2 ≤ screwDim k` is FALSE at `k=0`**
(`screwDim 0 = (2).choose 2 = 1`); it holds only from the dimension floor
`k ≥ 1` (`screwDim 1 = 3`). `1 ≤ screwDim k` *does* close
(`Nat.one_le_iff_ne_zero.mpr (by simp [screwDim, Nat.choose_eq_zero_iff])`).
⟹ **23a's Leaf 0 is a tiny `screwDim`-arithmetic kit** (below), and the
spine's `hn`/`hD` hypotheses must thread a `k ≥ 1` floor (the body-bar regime
`d = k+1 ≥ 2`) so the `≥ 2` facts are derivable, not `decide`d.

### (c) Buildable-leaf sequence for 23a

Smallest-buildable commits, dependency-ordered. Each re-greens its file(s)
on the still-green tree (the lift is additive/restating, not deleting).

- **Leaf 0 — `screwDim` arithmetic kit** (`RigidityMatrix/Basic.lean`). **DONE
  (c2669b3).** Added `one_le_screwDim {k} : 1 ≤ screwDim k`,
  `two_le_screwDim {k} (hk : 1 ≤ k) : 2 ≤ screwDim k` (the floor-conditioned
  `≥2`), and `screwDim_sub_two_le_mul {k m} (hm : 2 ≤ m) : screwDim k - 2 ≤ screwDim k * (m-1)`
  (the `_nested_rank_lower` l.641/643 `decide` replacements). Tiny `Nat.choose`
  lemmas; no carrier content. Touches Basic only; no consumers yet, so
  trivially green. **Two corrections to this recon spec at build:**
  `screwDim_sub_two_le_mul` takes **`2 ≤ m`**, not the `1 ≤ m` originally
  written — the latter is *provably false* at `m = 1` (RHS `= D·0 = 0 < D−2`
  for `k ≥ 1`); the call site (`case_III_nested_rank_lower`) has `2 ≤ |V'|` in
  scope. And its `(hk)` is unused (`D−2 ≤ D = D·1 ≤ D·(m−1)` needs nothing
  about `k`), so dropped.
- **Leaf 1 — `Fin 4` panel-incidence geometry → `Fin (k+2)`** (`PanelLayer.lean`,
  ll.357–838 band). **Split at build into two commits** (see corrections below):
  - **Leaf 1a (DONE)** — the duality-free rank-nullity core. Landed the general
    brick `exists_linearIndependent_perp_of_normals {r m} (N : Fin r → Fin (k+2)
    → ℝ) (hmr : m + r ≤ k + 2)` (`m` LI vectors in `⋂ⱼ Nⱼ^⊥`, `mulVecLin` kernel
    + `finrank_range_add_finrank_ker`, `Module.finrank_pi`+`Fintype.card_fin` at
    `k+2`); `exists_two_perp_of_linearIndependent_normals` (`r=2,m=2`),
    `exists_three_perp` (`r=1,m=3`), and `exists_extensor_in_two_panels`
    (`r=2,m=2`) now reduce to it (triplicated rank-nullity proof deleted).
  - **Leaf 1b (next)** — the grade-`k` extensor remainder: lift
    `exists_linearIndependent_extensor_pair_perp` and
    `exists_extensor_in_two_panels` to produce `ScrewSpace k` extensors of
    `Fin k`/`Fin (k+1)`-tuples (the `Fin k`-arity geometry, off
    `exists_linearIndependent_perp_of_normals`), with `k=2` wrappers keeping
    `theorem_55_base`/cut-edge green. Detail: `notes/Phase23a.md` *Hand-off*.
  - **DROPPED to CHAIN:** `exists_extensor_eq_panelSupportExtensor` (+ its
    corollary `extensorInPanel_panelSupportExtensor`, helper
    `panelSupportExtensor_join_eq_zero_of_eq_zero`) — routes through `Meet.lean`'s
    `extensor_join_eq_zero_of_complementIso_eq_zero_dotProduct` →
    `complementIso_smul_eq_extensor_join`, the `⋀²ℝ⁴` point-join↔panel-meet
    duality this recon assigns to CHAIN. Lifts only *with* the `⋀^{d−1}(ℝ^{d+1})`
    duality finish.
  - **23a-OD-A — RESOLVED, recommendation was WRONG.** `ExtensorInPanel C n`
    (`Basic.lean:276`) needs `C.val = extensor p` with `p : Fin k → Fin (k+2) →
    ℝ`; the perp arity is the **extensor grade `k`**, not the codim-2 hinge. So
    the extensor-bearing bricks need `Fin k`/`Fin (k+1)` tuples at general `k`
    (Leaf 1b), *not* the ambient-only `Fin 2` the recommendation claimed.
- **Leaf 2 — `Fin 4` incidence/extensor bricks in Claim612 + the shared LI
  brick** (`RigidityMatrix/Claim612.lean`, `CaseIII/Realization.lean` l.99).
  Lift `span_omitTwoExtensor_eq_top`, `omitTwoExtensor_eq_extensor_kept`,
  `omitTwoExtensor_homogenize_eq_extensor_kept`, `exists_independent_perp_pair`
  (the incidence bricks the spine — not the dispatch duality — consumes) and
  `linearIndependent_normals_of_algebraicIndependent` (Realization l.99) to
  `Fin (k+2)`. **Leave the `⋀²ℝ⁴`-duality lemmas
  (`exists_homogeneousIncidence_of_normals`,
  `exists_complementIso_ne_zero_of_homogeneousIncidence`,
  `exists_hduality_witness_of_panel_incidence`) at `Fin 4` — they are
  dispatch-only (CHAIN).** Re-green Claim612 (the general-`k` family is
  untouched). **23a-OD-B:** `span_omitTwoExtensor_eq_top` is stated
  `{pbar : Fin 4 → Fin 4 → ℝ}` (a *square* `(k+2)×(k+2)` system) — confirm its
  proof generalizes (it should: it is `omitTwoExtensor_linearIndependent_of_li {e:ℕ}`
  applied + a `span = top` dimension count, both already general).
- **Leaf 3 — CaseII rank-arithmetic numeral pass** (`CaseII.lean`). Restate
  `case_II_realization_all_k` and its lemmas at `screwDim k` /
  `HasGenericFullRankRealization k`, routing the eq.-(6.12) ℤ/ℕ cast plumbing
  through the (already `{D V N:ℕ}`-parametric) Basic helpers and the Leaf-0
  kit for the `≥2` facts. Re-green CaseII.
- **Leaf 4 — Case-III spine lift with the dispatch left explicit**
  (`CaseIII/Realization.lean` + `CaseIII/Arms.lean`). Restate
  `case_III_nested_rank_lower`, `case_III_realization_0dof`,
  `case_III_realization` at `screwDim k`/`Fin (k+2)`/`… k`; their proofs
  compose general bricks + the Leaf-0 kit, **except** the
  `case_III_candidate_dispatch` call. **Re-state `case_III_realization` (and
  `case_III_hsplit_producer`'s `hcand` slot) to take the chain dispatch as an
  explicit hypothesis** `hcand`/`hdispatch` of the general-`k` shape (boundary
  (d)). Re-green CaseIII.
- **Leaf 5 — Theorem55 spine lift, dispatch threaded up** (`Theorem55.lean`).
  Restate `theorem_55_minimalKDof_k` to `HasGenericFullRankRealization k`
  with `hn : bodyBarDim n = screwDim k` + the `k≥1`/`hD`-floor, lift its
  base/cut/CaseI/CaseII/CaseIII callback wiring numeral-wise, and **thread the
  green-modulo `hcand` hypothesis** through to `theorem_55_minimalKDof_k`'s
  own signature (its callers CHAIN discharges). Keep a `theorem_55_d3` wrapper
  that specializes `k:=2` and discharges the dispatch via the *existing*
  `case_III_candidate_dispatch` (so the `d=3` line stays fully green through
  23a — no regression). Re-green Theorem55. **This leaf closes 23a.**

Carrier-API additions preceding consumers: **none** (OD-5 verbatim). The only
"add" is Leaf-0's three `screwDim` arithmetic lemmas — not carrier API, pure
`Nat.choose`.

### (d) Green-modulo boundary 23a leaves for CHAIN

`case_III_realization` (and through it `theorem_55_minimalKDof_k`) **cannot be
closed at general `k` until CHAIN supplies the chain dispatch**, because the body
calls `case_III_candidate_dispatch` (the fixed-3-candidate `d=3` argument).
23a's boundary: lift `case_III_realization` / `theorem_55_minimalKDof_k` to
carry the dispatch as an **explicit `hcand`/`hdispatch` hypothesis** of the
general-`k` `case_III_hsplit_producer.hcand` shape — i.e. *"given the chain
data + a fresh `e₀` + the IH-generic `v`-split realization at dimension `k`,
produce `HasGenericFullRankRealization k n G`."* (The standing explicit-`h…`
crux idiom; never a `sorry`.) The **`d=3` line stays fully green** because the
`theorem_55_d3` wrapper specializes `k:=2` and fills `hcand` from the existing
`case_III_candidate_dispatch`. CHAIN replaces the fixed-3-candidate dispatch with
the length-`d` chain dispatch + `⋀^{d-1}(ℝ^{d+1})` duality, discharging the
hypothesis at general `k`.

**Boundary as actually built (23a Leaf 5 — wider than this (d) anticipated).**
The dispatch is only one of **six** green-modulo carries `theorem_55_minimalKDof_k_all_k`
takes; the others (base/cut/Case-I/M4-forget producers `d=3`-pinned → CHAIN's
duality; the `6 ≤ bodyBarDim n` chain-extraction floor → ENTRY) are recorded in
the **Scope expansion** note under §"CHAIN" above and in `notes/Phase23a.md`
*Hand-off*. (a)'s per-file claims that base/cut/Case-I and the forgetful map
"lift with the numeral pass" are **superseded** by that finding.

### (e) 23a-specific open decisions

- **23a-OD-A (Leaf 1 point-arity) — RESOLVED at the Leaf-1a build: the
  point-arity IS `d`-dependent; the "ambient-only" recommendation was wrong.**
  `ExtensorInPanel C n` (`Basic.lean:276`) requires `C.val = extensor p` with
  `p : Fin k → Fin (k+2) → ℝ` — the perp tuple's length is the **extensor grade
  `k`**, not the codim-2 hinge. So the extensor-bearing bricks
  (`exists_linearIndependent_extensor_pair_perp`, `exists_extensor_in_two_panels`)
  need `Fin k`/`Fin (k+1)` perp tuples at general `k` (Leaf 1b). The *ambient*
  `Fin 4 → Fin (k+2)` lift and the rank-nullity count are arity-clean (the
  general brick `exists_linearIndependent_perp_of_normals` carries them); only
  the extensor construction is `k`-arity.
- **23a-OD-B (`span_omitTwoExtensor_eq_top` squareness).** Its `Fin 4×Fin 4`
  system generalizes to `(k+2)×(k+2)` via the already-general
  `omitTwoExtensor_linearIndependent_of_li {e:ℕ}` + a `span=top` count.
  Confirm the dimension count ports; expected clean.
- **23a-OD-C (cap regressions under symbolic `k`).** OD-5 is verbatim for
  *correctness*; the LSP cannot confirm the 0-override perf state survives the
  full numeral substitution. *Recommendation:* treat any regressed cap as a
  local `maxHeartbeats` bump at that decl (standing idiom), not an OD-5
  reopening. Not a blocker.

### OD-2 / OD-3 resolution (secondary; for ENTRY scoping)

In tree under `Molecular/Induction/`:
- **KT Lemma 4.6** (chain-or-cycle / degree-2 vertex): `exists_low_degree_vertex`
  + `exists_adjacent_degree_two_pair` (`ReducibleVertex.lean:620/814`, cited
  "KT Lemma 4.6 at `d=3`") and `exists_chain_data_of_noRigid`
  (`ForestSurgery/Reduction.lean:383`).
- **KT Lemma 4.8** (split-off minimality): `splitOff_removeVertex_minimalKDof`
  (`Reduction.lean:1492`) + `lem:reduction-step-pos` (1736), cited "KT Lemma
  4.8(i)/(ii)".

**Verdict (OD-3):** 4.6/4.8 **exist, but only in their fixed-tuple `d=3`
form** — `exists_chain_data_of_noRigid` produces a **fixed `v,a,b,c` 4-tuple**
(`exists_adjacent_degree_two_pair` + two `exists_splitOff_data_of_degree_eq_two`),
**not** a length-`d` chain `v₀…v_d`. So the general-`d` chain producer is a
**new combinatorial leaf for ENTRY**, *not* subsumed; OD-2's "does Phase-20
produce a length-`d` chain?" answer is **no — only the single degree-2 split**.
**Verdict (OD-1, corroborating):** no dedicated Lemma 5.4 short-cycle decl
exists; the `d=3` Case III handles its `|V|=3` floor via the triangle base
`hasGenericFullRankRealization_of_triangle` (Arms.lean), confirming the `d=3`
assembly **dodged 5.4** — whether the general-`d` formalization can likewise
dodge it stays open for ENTRY.

---

## CHAIN — detailed leaf-level recon

**Status:** detailed-recon done (docs only, 2026-06-17, source-verified +
KT §6.4.2 read end-to-end against the landed tree; the minted letter is
**23b**, work log `notes/Phase23b.md`). Decomposes the CHAIN layer (§2) into
buildable leaves with exact target signatures, decides **OD-6**, settles/flags
**OD-4**, and scopes the lift of the four 23a-carried producers + the
`hdispatch` carry. The general-recon §1–§5 and the §"CHAIN" scope note are the
parent; this section is the leaf plan `notes/Phase23b.md` hands off to.

**KT §6.4.2 read (verified 2026-06-17, PDF pp. 692–698 = pdf pages 45–51,
offset −647).** The general-`d` argument, eqs. (6.46)–(6.67): a chain
`v₀v₁…v_d` with `d_G(vᵢ)=2` for `1≤i≤d−1`; one base framework `(G₁,q₁)` on the
split-off `G₁ = G^{v₀v₂}_{v₁}` with `R(G₁,q₁)=D(|V|−2)` (6.46); `d` candidate
frameworks `(G,p₀),…,(G,p_{d−1})` (6.47/6.48/6.57/6.59) built from `(G₁,q₁)`
and the isos `ρᵢ` (6.54)/(6.56); each `R(G,pᵢ)` reduced by column+row ops to a
top-left `D×D` block `Mᵢ` plus `R(G₁∖(v₀v₂)_{i*}, q₁)` (6.50/6.53/6.64), using
the **always-existing redundant `(v₀v₂)_{i*}` row from Claim 6.11** (6.51/6.52);
the ±r chain `∑ⱼλ rⱼ(q(vᵢvᵢ₊₁)) = ±r` for `2≤i≤d−1` (6.66, "in a manner
similar to (6.44)", the degree-2 fact); whence `Mᵢ` fails full rank iff
`r ⊥ C(Lᵢ)`. The eq. (6.67) finish: take `d+1` points `p₀…p_d` with `pᵢ ∈
⋂_{j≠i}Πⱼ ∖ Πᵢ` and `p_d = ⋂ⱼΠⱼ`; they are affinely independent, every
`(d−1)`-subset's `(d−2)`-flat lies in `⋃ⱼΠⱼ`, so the `(d−1)`-extensors of
`(d−1)`-subsets span a `(d+1 choose d−1) = D`-dim space by **Lemma 2.1**,
forcing some `Mᵢ` to have full rank, i.e. `rank R(G,pᵢ) = D + D(|V|−2) =
D(|V|−1)`. KT, p. 692: *"The proof strategy is exactly the same as `d = 3`."*

### (a) Per-file reach-in enumeration along the CHAIN surface

The carrier + arm-realization layer **is already general-`k`** (23a lifted the
spine; the M₁/M₂/M₃ arm closers were authored `(k:ℕ)` from Phase 22h). The
`Fin 4`/`⋀²ℝ⁴`/`screwDim 2`/`Fin 3`-pins that remain are concentrated in **the
dispatch and its `⋀²ℝ⁴` discriminator** — exactly the surface §1/§"CHAIN"
isolate as the new argument. Source-verified per-decl:

| Decl | File:line | Grade as landed | CHAIN action |
|---|---|---|---|
| `case_III_candidate_dispatch` | `CaseIII/Realization.lean:201` | `q : α × Fin 4 → ℝ`, fixed `v,a,b,c`, `na/nb/nc`, `ScrewSpace 2`, `screwDim 2`, `Fin 3` dispatch (`fin_cases u`), `h622lb` over `Fin 4` — **`d=3`-pinned AND structurally fixed-3-candidate** | **REPLACE** by the `d`-chain dispatch (eqs. 6.46–6.67) |
| `exists_homogeneousIncidence_of_normals` | `Claim612.lean:393` | `n : Fin 3 → Fin 4 → ℝ`, returns `pbar : Fin 4 → Fin 4 → ℝ` with the **`d+1`(=4)-point incidence pattern** (`pbar 0 ⊥ all`, `pbar i+1 ⊥ all but n i`) | re-state at `Fin d → Fin (d+1) → ℝ` → `pbar : Fin (d+1) → Fin (d+1) → ℝ` (the eq. 6.67 `d+1` points) |
| `exists_complementIso_ne_zero_of_homogeneousIncidence` | `Claim612.lean:1179` | `r : Dual ℝ (ScrewSpace 2)`, `n : Fin 3`, returns `u : Fin 3` + `n'` with `r(complementIso(k:=2)(j:=2) ⟨extensor ![n u, n'], …⟩) ≠ 0` | re-state at `ScrewSpace (d−1)`, `Fin d`, `complementIso(k:=d−1)`**`(j:=2)`** (a line has 2 normals at every `d` — §(f)/§(i) correction, NOT `(j:=d−1)`); 2-extensor `extensor ![n u, n']`. Full leaf §(j) CHAIN-4d |
| `exists_line_data_of_homogeneousIncidence` | `Claim612.lean:522` | `Fin 4` joins, `omitTwoExtensor pbar`, `exists_independent_perp_pair`, `omitTwoExtensor_eq_extensor_kept` | re-state at `Fin (d+1)`; routes through the duality leaves below |
| `case_III_claim612` | `Claim612.lean` | `Fin 4`/`ScrewSpace 2`, the six-join existential via `span_omitTwoExtensor_eq_top` (general `k`, landed Leaf 2) + the join↔meet duality | re-state at `ScrewSpace (d−1)`/`Fin (d+1)`; **N1 brick `span_omitTwoExtensor_eq_top` already general** |
| `omitTwoExtensor_eq_extensor_kept`, `…_homogenize_…`, `exists_independent_perp_pair` | `Claim612.lean:482/283/319` | `Fin 4`-pinned incidence/extensor bricks (dispatch-internal, 23a moved to CHAIN) | re-state at `Fin (d+1)` (mechanical; the `Fin 4`-arity geometry → `Fin (d+1)`) |
| `extensor_mem_range_map_subtype_of_mem`, `exists_smul_eq_of_mem_range_map_subtype` | `Meet.lean:648/676` | `W : Submodule ℝ (Fin 4 → ℝ)`, `⋀[ℝ]^2`, `finrank_exteriorPower_two_eq_one`, `finrank(range)=2.choose 2=1` | **re-state at** `⋀[ℝ]^{d−1}(Fin (d+1)→ℝ)` with `finrank(⋀^{d−1}W)=(dim W choose d−1)` (W of `dim = d−1` ⟹ `=1`); the route is general mathlib, the lemmas re-state at concrete grade |
| `complementIso_smul_eq_extensor_join` | `Meet.lean:1075` | `n_u n' pi pj : Fin 4 → ℝ`, `complementIso(k:=2)(j:=2)`, `Φ̃ = wedgeFixedLeft n_u ⊔ wedgeFixedLeft n'` `dim 5`, `Ω = dualAnnihilator Φ̃` `dim 1`, `extensor ![…]` (2-extensors) | **re-prove** at `⋀^{d−1}(ℝ^{d+1})` via the **`⋀^{d−1}W`-is-a-line** route (§(f), NOT the `Φ̃` lift): `n_u, n'` stay **2** normals (`complementIso(k:=d−1)(j:=2)`), `pi…` → **`d−1`** points; both members in `range(⋀^{d−1}W ↪)`, a line. `Φ̃`/`Ω`/`finrank_sup_range` route is **dead at `d≥4`** — keep d=3 body as the wrapper |
| `exteriorPower_basis_toDual_eq_pairingDual_comp_map` | `Meet.lean:866` | `(Pi.basisFun ℝ (Fin 4)).exteriorPower n` — `Fin 4`-pinned base | re-state at `Fin (d+1)` (the proof is `Module.Basis.ext` + `pairingDual_ιMulti_ιMulti`, dimension-generic) |
| `exists_extensor_eq_panelSupportExtensor` | `PanelLayer.lean` (23a Leaf-1b DROP) | the `⋀²ℝ⁴` point-join↔panel-meet bridge consumer; **the M4-forget unblocker** | lift **with** the duality finish (the four-producer lift, §"CHAIN"(d)) |
| `case_III_arm_realization`, `_M2`, `_M3` | `Arms.lean:72`, `Relabel.lean` | **ALREADY general `k`** (`q : α × Fin (k+2)`, `ScrewSpace k`, `screwDim k`) — the per-candidate certify-then-rebase + relabel transport | **reuse verbatim** as the per-candidate engine the `d`-chain dispatch feeds |
| `linearIndependent_sum_augment_candidateRow` | `RigidityMatrix/Basic.lean` | **general `k`, graph-free**; augmented by **one** `Unit` candidate | **DONE (CHAIN-1, 2026-06-18):** generalized to the `ιc`-block augment `linearIndependent_sum_augment_candidateRow_block` (+ the abstract `…_pinned_block_augment_block`); this is now the `ιc := Unit` corollary |

**The central structural finding (verified, reshapes the cut): the
arm-realization engine is general-grade; only the DISPATCH (candidate count +
`⋀²ℝ⁴` discriminator) is `d=3`-fixed.** The `d=3` dispatch
(`case_III_candidate_dispatch`) builds the three normals `na,nb,nc`, runs the
`Fin 3`-discriminator (`exists_homogeneousIncidence_of_normals` →
`exists_complementIso_ne_zero_of_homogeneousIncidence`) to pick a discriminating
panel `u : Fin 3` and transversal `n'`, then `fin_cases u` dispatches to the
three (already general-`k`) arm closers W7/W8/W9c. So CHAIN's new content is the
`d`-candidate generalization of *that dispatch shell* + the `⋀^{d−1}` duality
the discriminator rests on — **not** a rewrite of the arm-realization layer.

### (b) The producer-shape mismatch — the load-bearing flag (clause (ii))

**FLAG (motive/producer-level; do NOT force a leaf signature past it).** The
23a-carried `hdispatch` (`Theorem55.lean:2225`, =
`case_III_realization_all_k.hdispatch`, = `case_III_hsplit_producer_all_k.hcand`)
takes a **fixed `v,a,b,c` 4-tuple** with the `d=3` chain shape (`eₐ:va`,
`e_b:vb`, `e_c:ac`, the two degree-2 closures `hclv`/`hcla`). This is the data
`case_III_hsplit_producer_all_k` extracts via `exists_chain_data_of_noRigid`
(`Reduction.lean:383`) — which, verified, produces **only a fixed 4-tuple, not a
length-`d` chain** (the OD-2/OD-3 verdict). But KT's general-`d` Lemma 6.13
**needs the whole length-`d` chain `v₀…v_d`** to build the `d` candidates
(6.54/6.56/6.57). At `d=3` the chain `v₀v₁v₂v₃` *is* exactly `c—a—v—b` (the
4-tuple `v,a,b,c` with `v₁=v` deg-2, `v₂=a` deg-2 in `G₁`, `v₀=b`, `v₃=c`
endpoints), so the fixed-4-tuple dispatch *is* the length-3 chain dispatch and
the carried shape is faithful. At `d≥4` it is **not**: the fixed 4-tuple is too
short, and the carried `hdispatch` cannot be discharged from it.

**Consequence.** CHAIN cannot be a pure "discharge the carried `hdispatch` at
general `k`" — the *producer/extractor that supplies `hdispatch`'s premises must
be reshaped* to extract and pass a length-`d` chain. Concretely, three coupled
changes:
1. **the chain extractor** (`exists_chain_data_of_noRigid`) must produce a
   length-`d` chain `v₀…v_d` (a Phase-20-shape combinatorial lemma — KT Lemma
   4.6/4.8; the **ENTRY** layer, OD-2/OD-3 verdict: "new combinatorial leaf");
2. **the producer** (`case_III_hsplit_producer_all_k`) must thread that chain
   into its `hcand` slot (its `hcand`/`hdispatch` shape changes from fixed
   4-tuple to length-`d` chain);
3. **the dispatch** (CHAIN's deliverable) consumes the chain.
This is a genuine **motive/producer-shape change**, not a numeral lift, and it
**couples CHAIN to ENTRY**: the dispatch's input shape is the chain extractor's
output shape. **Recommendation:** CHAIN and ENTRY co-design the chain-data shape
at CHAIN open (the `hdispatch`/`hcand` signature is the contract between them);
23b should not freeze the dispatch signature before the chain-data record is
agreed with ENTRY. The 23a `hdispatch` carry is **correct as the `d=3` instance
contract** (the `k=2` wrapper fills it from `case_III_candidate_dispatch`), and
stays green through 23a/ASSEMBLY-at-`d=3`; it is the *general-`d`* shape that
must grow. This is exactly the "honest open decision the coordinator/user
adjudicates" clause-(ii) calls for — see OD-6 / OD-7 below.

### (c) Buildable-leaf sequence for CHAIN

Smallest-buildable, dependency-ordered. The two hard cores (chain bookkeeping
CHAIN-1/2; duality CHAIN-3/4) are **largely independent** and feed the dispatch
assembly CHAIN-5. Each leaf re-greens its file on the still-green tree (additive
restating; the `Fin 4`/`d=3` decls stay as `d=3` wrappers so the `d=3` line
never regresses). **CHAIN-0/CHAIN-5 are gated by the (b) flag** — the dispatch
signature depends on the ENTRY chain-data contract.

- **CHAIN-1 — the `d`-fold candidate machinery** (`RigidityMatrix/Basic.lean`).
  **CLOSED 2026-06-18** (Phase23b rows 211–212). Two bricks: (1) the
  row-correspondence swap `linearIndependent_sumElim_candidateBlock_swap` + mirror
  `linearIndependent_sumElim_block_swap` (KT eq. 6.62 — correct an `ιc`-block of
  candidate rows by base-span members); (2) the `ιc`-block candidate augment
  `linearIndependent_sum_pinned_block_augment_block` +
  `linearIndependent_sum_augment_candidateRow_block` (the `+|ιc|` count lift; the
  single-`Unit` `…_augment{,…_candidateRow}` re-derived as `ιc := Unit` corollaries,
  blueprint pins unmoved). Graph-free over `ScrewSpace k`, no `d=3` content. The
  heterogeneous-chain per-candidate column-op (each `i` its own `Φᵢ`) is **CHAIN-2's**
  bookkeeping — the augment fires one body at a time at the chosen split body `v`.
- **CHAIN-2 — the chain matrix bookkeeping (eqs. 6.59–6.64)** (`CaseIII/`, new
  file or extend `Candidate`). The per-candidate-`i` reduction of `R(G,pᵢ)`
  (6.60) to the `Mᵢ ⊕ R(G₁∖(v₀v₂)_{i*},q₁)` form (6.64), via the column op
  (add `vᵢ`-cols to `vᵢ₊₁`-cols), the substitution (6.59), the row
  correspondence (6.62), and the redundant-row weights `λ` (6.52, the Claim
  6.11 redundancy — **reuse `exists_redundant_panelRow_ab_of_finrank_eq`,
  general & GREEN**). The ±r chain (6.66) is the degree-2 fact "in a manner
  similar to (6.44)". *This is the index-heavy generalization of the
  `caseIIICandidate`/`case_III_old_new_blocks`/`case_III_rank_certification`
  chain (now `q : α × Fin 4`-shaped) to a `Fin d`-indexed candidate family.*
  Heaviest mechanical leaf; KT calls it "exactly the same as `d=3`."
- **CHAIN-3 — the `⋀^{d−1}(ℝ^{d+1})` duality bricks** (`Meet.lean` + `MeetHodge.lean`).
  **CLOSED 2026-06-17** — the assembly `extensor_join_proportional_complementIso_meet`
  (`MeetHodge.lean`) landed on the three `_grade` bricks + the OD-8 route-(α) leaf chain h-0…h-3;
  the `⋀^{d−1}W`-is-a-line route as recon'd in §(f). The d=3 `complementIso_smul_eq_extensor_join`
  stays the green d=3 wrapper. Original recon (kept for the CHAIN-4 reach-in reference):
  Re-state `extensor_mem_range_map_subtype_of_mem`,
  `exists_smul_eq_of_mem_range_map_subtype`,
  `exteriorPower_basis_toDual_eq_pairingDual_comp_map`,
  `complementIso_smul_eq_extensor_join` at `⋀[ℝ]^{d−1}(Fin (d+1)→ℝ)` with the
  general `finrank(⋀^{d−1}W) = (finrank W).choose (d−1)`
  (`exteriorPower.finrank_eq`; at `dim W = d−1` this is `1`). The route is
  general mathlib (`exteriorPower.map_injective_field`, `map_apply_ιMulti`,
  `pairingDual_ιMulti_ιMulti`, `topEquiv`/`pairingDualEquiv` mirrors); the
  the proportionality lives in the line `⋀^{d−1}W` (`dim W = d−1`). **Build
  LAZILY at concrete grade `(d−1, d+1)` — do NOT build a general Hodge-star /
  regressive-product API (KT never needs it; §1/§"CHAIN" hard core 2).**
  **CORRECTED by the CHAIN-3-finish recon §(f) (2026-06-17):** the route is the
  **`⋀^{d−1}W`-is-a-line** route (point-join + panel-meet both in `range(⋀^{d−1}W
  ↪)`, a line), NOT the d=3 `Φ̃ = dualAnnihilator` route. The panel-meet is
  `complementIso (k:=d−1)(j:=2)` (`j=2` — a line has **2** normals at every `d`,
  not `d−1`). **`finrank_sup_range_wedgeFixedLeft` / `extensor_toDual_extensor_eq
  _zero_of_perp` do NOT generalize and are NOT needed** (they are the d=3-only
  `Φ̃`/`Ω` route, sound only because `dim Ω = C(d−1,2) = 1` at `d=3`). The one
  genuinely-new leaf is the **panel-meet range-membership** (OD-8). Pinned
  signatures + leaf sequence: §(f); the open route choice: OD-8 §(g).
- **CHAIN-4 — the `Fin (d+1)` incidence + Claim-6.12 discriminator**
  (`Claim612.lean`). **Two mechanical bricks LANDED 2026-06-18**
  (`exists_independent_perp_pair_gen`, `omitTwoExtensor_eq_extensor_kept_gen`);
  **OD-4 RESOLVED 2026-06-18 (§(i)): existence/homogeneous, alg-independence NOT
  forced**. **Remainder decomposed into four leaves with exact signatures in
  §(j):** CHAIN-4a `exists_homogeneousIncidence_of_normals` at `Fin (k+1) →
  Fin (k+2)` (the OD-4 sub-leaf, clean lift), CHAIN-4b
  `exists_line_data_of_homogeneousIncidence` (clean lift; carries the §(i)
  one residual — the per-join panel-membership must close combinatorially),
  CHAIN-4c `case_III_claim612` (the span-`D` existential, **reusing the general
  `span_omitTwoExtensor_eq_top` (landed 23a Leaf 2) + Lemma 2.1** — pure numeral
  lift), CHAIN-4d `exists_complementIso_ne_zero_of_homogeneousIncidence` at
  `ScrewSpace (k)`/`Fin (k+1)` candidates, `complementIso (k:=k)(**j:=2**)` (the
  §(f)/§(i) correction — a line has 2 normals at every `d`; **not** `(j:=d−1)`),
  **consuming the landed CHAIN-3 (h-4)** `extensor_join_proportional_complementIso_meet`.
  *This is the eq. (6.67) finish + the `Mᵢ`-fails-iff-`r⊥C(Lᵢ)` disjunction.*
  **First buildable OD-4 leaf = CHAIN-4a.**
- **CHAIN-5 — the `d`-chain dispatch assembly** (`CaseIII/Realization.lean`).
  Replace `case_III_candidate_dispatch`: given the length-`d` chain data +
  fresh `e₀` + the IH-generic base realization `(G₁,q₁)`, build the `d`
  candidates (CHAIN-2), apply the discriminator (CHAIN-4) to pick a
  full-rank `Mᵢ`, and close via the (already general-`k`) arm closer for that
  `i` (the `ρᵢ`-relabel chain generalizing W9c's single `a↔v` swap). **Gated
  by the (b) flag** — its `hdispatch`/`hcand` signature is the
  CHAIN↔ENTRY contract (the length-`d` chain record). Discharges the
  general-`d` `hdispatch` carried by `theorem_55_minimalKDof_k_all_k` (once that
  carry's shape grows to the length-`d` chain, (b)). Keep the `d=3` dispatch as
  a `k=2`/length-3 wrapper so the `d=3` line stays green.

### (d) Green-modulo boundary CHAIN hands downstream

After CHAIN, the carried `hdispatch` is **discharged at general `k`** (modulo
the (b) producer reshape, which CHAIN co-owns with ENTRY). CHAIN additionally
**unblocks the M4-forget producer** `exists_extensor_eq_panelSupportExtensor`
(it routes through the `⋀²ℝ⁴` duality `complementIso_smul_eq_extensor_join`,
CHAIN-3) — so once CHAIN-3 lands, **`hforget_k`** (the M4 forget map,
`hasPanelRealization_of_generic`, `GenericityDevice.lean:1936/1945`) lifts to
general `k`, and **through it `hbase_k`/`hcut_k`/`hcontract_k`** (every
conditioned-pair producer routes its bare `HasPanelRealization` half through the
forget map — the 23a Leaf-5 finding). **So the four 23a-carried producers fold
into CHAIN's tail** (after CHAIN-3's duality), as the §"CHAIN" scope expansion
predicted — see (e) OD-7 for the fold-vs-successor decision. What CHAIN does
**not** discharge, leaving to downstream:
- **ENTRY** owns the length-`d` chain *extraction* (the reshaped
  `exists_chain_data_of_noRigid` → chain; Lemma 4.6 dichotomy + Lemma 4.8
  split-off + the short-cycle base Lemma 5.4 branch) and the `hD : 6 ≤
  bodyBarDim n` floor lift. The chain-data record shape is the CHAIN↔ENTRY
  contract ((b)).
- **ASSEMBLY** composes the honest general-`d` Theorem 5.5 (the `hdispatch`/
  four-producer carries now discharged), re-greens `prop:rigidity-matrix-prop11`
  + `hub`, derives Thm 5.6, states Conjecture 1.2.

### (e) CHAIN-specific open decisions

- **OD-6 — DECIDED: two leaves within one CHAIN sub-phase (no new letter for
  the duality), but with a CHAIN/ENTRY co-design dependency.** The two hard
  cores are dependency-ordered into one layer: the `⋀^{d−1}` duality (CHAIN-3)
  is *consumed by* the Claim-6.12 discriminator (CHAIN-4), which is *consumed
  by* the dispatch assembly (CHAIN-5); the chain bookkeeping (CHAIN-1/2) feeds
  CHAIN-5 in parallel. They are five leaves of **one** sub-phase 23b, not a
  split — the arm-realization engine they all feed is already general-`k`
  (verified (a)), so neither core stands alone as a deliverable. *Rationale for
  not minting a separate duality letter:* the duality is not a self-contained
  target (it has no consumer outside CHAIN-4/5 and the M4-forget lift), unlike
  21a's meet foundations (which seeded the whole panel layer). If CHAIN-2's
  index bookkeeping proves larger than estimated, **split at contact** into 23b
  (duality + discriminator CHAIN-3/4, which also unblocks the four producers)
  + a later-minted letter (chain bookkeeping CHAIN-1/2/5) — but open as one.
- **OD-7 — DECIDED: the four 23a-carried producers fold into CHAIN's tail
  (after CHAIN-3), not a dedicated successor sub-phase.** Verified ((d)): the
  M4-forget `exists_extensor_eq_panelSupportExtensor` is *the same `⋀²ℝ⁴`
  duality* CHAIN-3 lifts, and `hbase_k`/`hcut_k`/`hcontract_k` route through M4
  for their bare half. So the producer lift is a **direct corollary of CHAIN-3**
  (numeral pass on the producers once their one `Fin 4`-duality reach-in lifts),
  not new mathematics — folding it avoids a successor sub-phase that would
  re-open the same files. *Caveat:* the producers also carry `Fin 4` panel
  geometry beyond the forget call (the 23a Leaf-5 finding said they "bottom out
  in `q : α × Fin 4` panel geometry **and** the duality"); the detailed-build
  recon at CHAIN open must confirm the *only* genuinely-`d=3` reach-in is the
  duality (i.e. the rest is the numeral pass), else the fold is larger than a
  corollary. Present as a fold with this caveat flagged.
- **OD-4 — RESOLVED 2026-06-18: existence/homogeneous route, alg-independence
  NOT forced.** Full verdict + reasoning in §(i) below. The prior "forced" lean
  followed KT's *affine* phrasing (p. 698: `d+1` affinely-independent points →
  `(d−2)`-flats in `⋃Πⱼ` → "any `j` hyperplanes meet in a `(d−j)`-flat" by
  alg-independence). But the **landed d=3 formalization never takes that route**:
  it works homogeneously (§1.42 R1-affine), so the eq.-(6.67) `dim = D` is driven
  by **linear independence of `d+1` homogeneous vectors** (`span_omitTwoExtensor_
  eq_top`, already general-`k`, only hyp `LinearIndependent ℝ pbar`, via Lemma
  2.1) — **no affine independence, no alg-independence, no `(d−j)`-flat fact.**
  The row #106 cross-product construction (whose non-generalization motivated the
  "forced" lean) is **dead — zero live call sites** (verified); the live d=3
  dispatch consumes `exists_homogeneousIncidence_of_normals` (linear, only hyp
  `LinearIndependent ℝ n`). The per-join panel-membership generalizes purely
  combinatorially (join `{a,b}` ⊂ `Πᵢ` iff `i+1∈{a,b}`; §(i)). **No new
  `AlgebraicIndependent`-driven lemma needed.** Alg-independence stays live only
  at site (a) (the nested seed-rank transfer, `AlgebraicIndependence.md` row #107,
  carrier-lifted, unchanged); site (b)/eq.-(6.67) is **not** a site. CHAIN-4
  decomposition: §(j). One build-time residual flagged (the §(i) per-join
  membership must close from the orthogonality hyps alone — CHAIN-4b's job).
- **OD-1 (carried from §4, re-confirmed for CHAIN/ENTRY).** The short-cycle
  base (KT Lemma 5.4, "if `G` is a cycle of length ≤ `d`, done by Lemma 5.4")
  is a **real branch of the general-`d` chain entry** (KT p. 692), unlike `d=3`
  (triangle floor handled inline). Whether CHAIN's dispatch can assume the chain
  branch (ENTRY discharging the cycle branch separately) or must handle a degenerate
  chain is an ENTRY-contract question — flag at CHAIN open, do not pre-commit.

### (f) CHAIN-3-finish recon — the `⋀^{d−1}W`-is-a-line route (corrects the `Φ̃` pin)

**Status:** detailed-build recon, docs-only, 2026-06-17, source-verified against
KT §6.4.1/§6.4.2 (eqs. 6.45–6.67 read end-to-end, page 698 the eq.-6.67 finish)
+ the landed `Meet.lean` bodies + the three already-landed `_grade` bricks. This
sub-section settles the route for CHAIN-3's two remaining pieces
(`finrank_sup_range_wedgeFixedLeft` and `complementIso_smul_eq_extensor_join` at
general `d`) and **overturns the prior pin** (checklist + *Hand-off*) on both.

**The geometry, corrected (the load-bearing fact the prior pin got wrong).** The
per-line duality is about a single line `L = Lᵢ` — KT's `(d−2)`-dimensional
affine subspace, homogeneous span `dim = d−1` in `ℝ^{d+1}`. Two counts follow
and they are **fixed across `d`, not growing**:
- **Normals: exactly 2 at every `d`.** `dim L^⊥ = (d+1) − (d−1) = 2`. The panel-
  meet is the meet of the **2** hyperplanes through `L`: `complementIso(extensor
  ![n_u, n']) ∈ ⋀^{d−1}`, input grade `j = 2` (NOT `j = d−1`), output grade
  `(d+1) − 2 = d−1`. *The prior pin's `complementIso (k:=d−1)(j:=d−1)` is wrong;*
  it is `complementIso (k:=d−1)(j:=2)` (`k=2,j=2` at `d=3` by `d−1=2`, masking
  the error). The d=3 `exists_independent_perp_pair` (find the 2nd normal in
  `L^⊥`) lifts cleanly (ambient `Fin (d+1)`, point family `Fin (d−1)`; the common
  perp has `dim ≥ 2`, so a 2nd independent normal always exists).
- **Points: `d−1` (not 2).** `L` is spanned by `d−1` points; the point-join is
  the **`(d−1)`-extensor** `extensor (p : Fin (d−1) → ℝ^{d+1}) ∈ ⋀^{d−1}` (KT
  p. 698 verbatim: *"any `(d−1)`-extensor obtained from `d−1` points"*). At `d=3`,
  `d−1 = 2` — the two points `![pᵢ, pⱼ]` of the d=3 code.

Both the point-join and the panel-meet are grade `d−1` (NOT grade 2 — at `d=3`
the coincidence `d−1 = 2` collapses them). For `d ≥ 4` a grade-2 point-join and a
grade-`(d−1)` panel-meet **cannot** be proportional — so the d=3 framing where
both are grade-2 is a `d−1=2` artifact.

**The route that DOES generalize (and the dead-end it replaces).** Both members
are the Plücker coordinate of the same `(d−1)`-dim subspace `W = span(L) =
{n_u, n'}^⊥`, i.e. both lie in **`⋀^{d−1}W`, which is a line** (`dim ⋀^{d−1}W =
(d−1).choose (d−1) = 1`). With the point-join nonzero, the two are proportional.
This is **exactly the route the three already-landed `_grade` bricks were built
for** (they have NO consumers in tree — grep-confirmed — they were landed
*forward* for this): `extensor_mem_range_map_subtype_of_mem_grade` (point-join ∈
`range(⋀^{d−1}W ↪ ⋀^{d−1}ℝ^{d+1})`), `exteriorPower_map_subtype_injective_grade`
+ `finrank_exteriorPower_self_eq_one` (that range is a line), and
`exists_smul_eq_of_mem_range_map_subtype_grade` (two members of it are
proportional). The `exists_smul_…_grade` docstring already says the
proportionality *"lives in `⋀^{d−1}(ℝ^{d+1})` itself, so no pull-back … is
needed."*

**Consequence — the two prior-pinned leaves are DEAD ENDS at general `d`:**
- **`finrank_sup_range_wedgeFixedLeft` (the `dim Φ̃ = 5` count) does NOT
  generalize and is NOT needed.** Its `Φ̃ = n_u ∧ ℝ⁴ ⊔ n' ∧ ℝ⁴` /
  `Ω = dualAnnihilator Φ̃` machinery is the **d=3-only "route A-corrected"
  (Phase 22f)**. `Φ̃` is built from the **2** normals, so `dim Φ̃ =
  dim(span{n_u,n'} ∧ ℝ^{d+1}) = C(d+1,2) − C(d−1,2)`, giving `dim Ω = C(d−1,2)`,
  which is `1` **only at `d=3`** (`C(2,2)=1`); for `d≥4` it is `> 1`, so the
  `Ω`-is-a-line argument breaks. The prior pin's "`(d−1)`-summand inclusion–
  exclusion / `A ∧ ℝ^{d+1}` codimension `D−1`" both rest on the false `dim A =
  d−1` (`A` has dim 2, not `d−1`). **Do not generalize this lemma.** Leave the
  d=3 `finrank_sup_range_wedgeFixedLeft` / `inf_range_wedgeFixedLeft` /
  `wedgeFixedLeft` / `extensor_toDual_extensor_eq_zero_of_perp` /
  `complementIso_toDual_extensor_eq_zero_of_shared_vector` as the green d=3
  route (the `d=3` `complementIso_smul_eq_extensor_join` keeps using them).
- **`extensor_toDual_extensor_eq_zero_of_perp` does NOT lift either** — it is the
  Gram-determinant orthogonality feeding the dead `Ω`-route; the general-`d`
  finish never calls it.

**The one genuinely-new leaf: the panel-meet range-membership** `complementIso
(k:=d−1)(j:=2) ⟨extensor ![n_u, n'], _⟩ ∈ range(⋀^{d−1}W ↪ ⋀^{d−1}ℝ^{d+1})` for
`W = {n_u, n'}^⊥` (`dim W = d−1`). This is the never-completed **N3b-2b-α** (at
`d=3` the assembly bypassed it via the `Φ̃`/`Ω` route, so it was *never proved at
any `d`*). Geometrically true (the complement of the decomposable `n_u ∧ n'` is
the `(d−1)`-extensor of `(n_u ∧ n')^⊥ = W`). **Two candidate sub-routes, OD-8
below — flagged, not pre-committed.** What IS in hand: the general
`complementIso_toDual_eq_zero_of_wedgeProd_eq_zero` ({j} hj, LANDED) gives
`toDual`-*annihilation* of the panel-meet by any `(d−1)`-extensor sharing a
factor with `n_u ∧ n'`; range-*membership* is the upgrade.

**Pinned signatures (the CHAIN-3 finish).**
**Phrase `k`-parametrically (`k = d−1`), ambient `Fin (k+2)`, conclusion `⋀^k`.**
This matches the all-`k` engine convention (`ScrewSpace k`, `complementIso (k:=…)`,
`screwDim k`) AND **dodges a real cast trap** (verified in scratch): with `k` written
as `d−1`, the ambient `Fin ((d−1)+2)` is NOT defeq to `Fin (d+1)` for a *variable* `d`
(`(d−1)+2` reduces only under `d ≥ 1`), so `extensor n` (typed `Fin (d+1)`) clashes with
`complementIso (k:=d−1)`'s `Fin ((d−1)+2)` domain. Writing the lemma in `k` with ambient
`Fin (k+2)` makes `k+2−2 = k` and the domains defeq; the `d=3` wrapper instantiates
`k := 2` (then `k+2 = 4 = 3+1` defeq). The `d−1` points spanning `L`, with `k = d−1`, are
the family `p : Fin k → Fin (k+2) → ℝ`; the point-join `extensor p ∈ ⋀^k (Fin (k+2))` — grade
`k`, matching the panel-meet's output grade `(k+2)−2 = k`. ✓
1. The general-`d` per-line duality (replaces the d=3
   `complementIso_smul_eq_extensor_join`; the d=3 line becomes the `k=2` wrapper):
   ```
   theorem extensor_join_proportional_complementIso_meet {k : ℕ}
       (n : Fin 2 → Fin (k + 2) → ℝ)         -- the two line-normals n_u, n'
       (p : Fin k → Fin (k + 2) → ℝ)         -- the k = d−1 points spanning L
       (hp  : LinearIndependent ℝ p)         -- so the point-join ≠ 0
       (hpair : LinearIndependent ℝ n)
       (hperp : ∀ i j, (Pi.basisFun ℝ (Fin (k+2))).toDual (p i) (n j) = 0) :
       ∃ c : ℝ, c • (complementIso (k := k) (j := 2) (by omega)
           ⟨extensor n, extensor_mem_exteriorPower n⟩)
         = (⟨extensor p, extensor_mem_exteriorPower p⟩ : ⋀[ℝ]^k (Fin (k+2) → ℝ))
   ```
   Body: set `W = {n_u,n'}^⊥` (`dim W = (k+2)−2 = k` by rank–nullity on the 2
   functionals `⟨·,n_u⟩,⟨·,n'⟩`, `= k` since the `k` independent points `p` lie in it);
   point-join ∈ `range(⋀^k W)` by `extensor_mem_range_map_subtype_of_mem_grade`
   (each `p i ∈ W` from `hperp`; **note** that brick is stated at grade `d−1`/ambient
   `d+1` — its `k`-form is `(d := k+1)`, `d−1 = k`, `d+1 = k+2`, defeq); panel-meet ∈
   `range(⋀^k W)` by the new leaf (2); point-join ≠ 0 by `hp` +
   `extensor_ne_zero_iff_linearIndependent`; close by
   `exists_smul_eq_of_mem_range_map_subtype_grade` (its `(d := k+1)` form). The d=3
   `complementIso_smul_eq_extensor_join` becomes `:= …_meet (k := 2) …` (`k = 2`,
   `Fin 4`, the 2-point case `p = ![pi, pj]`).
2. The new range-membership leaf (the one genuinely-new piece):
   ```
   theorem complementIso_extensor_mem_range_map_subtype {k : ℕ}
       (n : Fin 2 → Fin (k + 2) → ℝ) (W : Submodule ℝ (Fin (k + 2) → ℝ))
       (hWperp : ∀ w ∈ W, ∀ j, (Pi.basisFun ℝ (Fin (k+2))).toDual w (n j) = 0)
       (hWdim : Module.finrank ℝ W = k) :
       (complementIso (k := k) (j := 2) (by omega)
           ⟨extensor n, extensor_mem_exteriorPower n⟩)
         ∈ LinearMap.range (exteriorPower.map k W.subtype)
   ```

**Buildable-leaf sequence (CHAIN-3 finish), dependency-ordered:**
1. *(no-op)* confirm the d=3 `finrank_sup_range_wedgeFixedLeft` /
   `extensor_toDual_extensor_eq_zero_of_perp` stay as the **green d=3** route —
   do NOT touch (the prior checklist's "generalize these" items are withdrawn).
2. `complementIso_extensor_mem_range_map_subtype` — **the new leaf** (route per
   OD-8). Consumes the general `complementIso_toDual_eq_zero_of_wedgeProd_eq_zero`
   (LANDED) + `finrank_exteriorPower_self_eq_one` (LANDED).
3. `extensor_join_proportional_complementIso_meet` — the assembly; consumes (2) +
   the three landed `_grade` bricks. **Zero new count work.**
4. The `d=3` wrapper (zero regression): the existing
   `complementIso_smul_eq_extensor_join` (the `Φ̃`-route body) stays as-is and the
   d=3 discriminator keeps calling it; OR re-point the discriminator at the new
   general lemma's `d=3` instance once (2)/(3) land. *Recommend keeping the d=3
   body* (it is green and the new route needs (2) first) — re-point is a CHAIN-4
   decision, not forced here.

**Hands to CHAIN-4.** CHAIN-4's discriminator
(`exists_complementIso_ne_zero_of_homogeneousIncidence`, the contrapositive that
some `Mᵢ` has full rank) consumes the per-line duality (3) the way the d=3
`extensor_join_eq_zero_of_complementIso_eq_zero_dotProduct` consumes the d=3
`complementIso_smul_eq_extensor_join`. The eq.-(6.67) `D`-span (the `d+1`-point /
Lemma-2.1 argument, which IS the `dim = D` count — and is **separate** from the
per-line `Φ̃`) stays CHAIN-4's, gated by **OD-4** (the alg-independence route,
still flagged open).

**Coordinator KT-route check (2026-06-17, against KT p. 697–698, eqs. 6.65–6.67
read end-to-end).** Confirmed the `⋀^{d−1}W`-is-a-line route IS KT's argument, not
a convenient substitute. KT proves (6.65) some `Mᵢ` is full rank by: (6.66) `Mᵢ`
fails full rank ⟺ `r ⊥ span C(Lᵢ)`, where `C(Lᵢ)` is *the `(d−1)`-extensor of the
flat `Lᵢ`*; (6.67) so none is full rank ⟺ `r ⊥ span(⋃ᵢ C(Lᵢ))`, and
`dim span(⋃ C(Lᵢ)) = C(d+1, d−1) = D` via `d+1` affinely-independent points (any
`(d−1)`-extensor of `d−1` of them is some `C(Lᵢ)`) **by Lemma 2.1**. The faithfulness
point: **KT writes `C(Lᵢ)` agnostically** — as the *meet* of the 2 panels cutting
out `Lᵢ` (the rank side, 6.66 / CHAIN-2) AND as the *join* of `d−1` points spanning
`Lᵢ` (the `D`-span side, 6.67 / CHAIN-4). **CHAIN-3's
`extensor_join_proportional_complementIso_meet` formalizes the join=meet equality KT
leaves implicit** — the one step the Lean must spell out (a BlueprintExposition-grade
node). The withdrawn `Φ̃`/`finrank_sup_range`/`Ω = dualAnnihilator` machinery is a
`d=3`-only *formalization* artifact (Phase 22f's "route A-corrected"), **not** in KT
— KT works directly with the `C(Lᵢ)` extensors, so the re-route moves the
formalization *toward* KT. (The per-line rank↔orthogonality ±r chain, 6.66, is
CHAIN-2; the `D`-span, 6.67's `d+1` points + Lemma 2.1, is CHAIN-4 / OD-4.)

### (g) CHAIN-specific open decision OD-8 (the panel-meet range-membership route)

- **OD-8 — FLAGGED (genuinely open; the one design call the CHAIN-3 finish
  cannot settle from the source alone).** `complementIso (j:=2) ⟨n_u ∧ n', _⟩ ∈
  range(⋀^{d−1}W ↪)` for `W = {n_u, n'}^⊥`. In hand:
  `complementIso_toDual_eq_zero_of_wedgeProd_eq_zero` gives the *annihilation*
  (the panel-meet is `toDual`-killed by every `(d−1)`-extensor sharing a factor
  with `n_u ∧ n'`). Two candidate routes to upgrade annihilation → membership:
  - **(α) Hodge/complement-direct.** Prove `complementIso (k:=d−1)(j:=2)` carries
    `⋀²(span{n_u,n'})` into `⋀^{d−1}({n_u,n'}^⊥) = ⋀^{d−1}W` — a "the complement
    of a decomposable lives in the exterior power of its orthogonal complement"
    fact. Cleanest geometrically; needs a `complementIso`-image-of-`⋀²S` lemma
    not currently in `Meet.lean` (a small new `complementIso` API leaf, NOT a new
    mathlib-level fact — built from the landed `complementIso_toDual` dictionary).
  - **(β) annihilator = range, via the perfect pairing.** `range(⋀^{d−1}W ↪)` is
    a line (LANDED bricks); show it *equals* the annihilator subspace the
    panel-meet is known (by the in-hand annihilation) to lie in, by a dimension match
    (`dim range = 1 = dim {Z : ⋀^{d−1} | Z ⊥ …}`). Reuses the landed annihilator-
    count machinery but needs the right "`⋀^{d−1}W` = annihilator of `⋀^{d−1}` of
    the `wedge-with-n` images" identification — closer to the d=3 `Φ̃` idea but
    in the correct grade `d−1` with `dim W = d−1`.
  - *Recommendation:* (α) is the cleaner target (a 1–2-decl `complementIso` API
    addition); attempt (α) first, fall back to (β). **Neither needs a new
    mathlib-level fact** (clause (ii) clear: no missing `dim(A∧V)` lemma, no
    Hodge-star API — the count is the LANDED `finrank_exteriorPower_self_eq_one`,
    not a `finrank_sup`). The decision is the *internal* `complementIso`-image
    characterization, settled at build. **This is the only genuinely-open piece
    of the CHAIN-3 finish.**

  > **OD-8 SETTLED by §(h) below (2026-06-17 OD-8 design-pass).** The §(g)
  > recommendation is **superseded**: (α) is the right route but is **NOT** "a
  > 1–2-decl `complementIso` API addition" — its load-bearing step is
  > `complementIso`'s **O(n)-equivariance**, a substantial new sub-lemma flagged
  > as its own leaf. (β) is **not** a safe fallback (its dimension count is the
  > grade-2-vs-grade-`k` `dim Φ̃` trap §(f) already withdrew). See §(h) for the
  > pinned decomposition and the clause-(ii) flag.

### (h) OD-8 design-pass — the route decision for the panel-meet range-membership

**Status:** OD-8 design-pass, docs-only, 2026-06-17. Source-verified against the
**landed** `Meet.lean` bodies (the `complementIso` `def`/`wedgePairing`/
`screwAlgebraTopEquiv` construction read end-to-end, the in-hand annihilation
`complementIso_toDual_eq_zero_of_wedgeProd_eq_zero`, the three landed `_grade`
bricks, the landed base case + standard-frame membership) and against mathlib
(`lean_loogle`/`lean_leanfinder`: no Hodge-star / decomposable-complement API).
LSP-probed: the proportionality engine `exists_smul_eq_of_mem_range_map_subtype_grade`
and the line count `finrank (range (⋀^k W ↪)) = 1` for `dim W = k` both close at
general `k` (scratch, reverted) — **so the entire OD-8 crux reduces to one
membership: `complementIso (j:=2) n ∈ range(⋀^k W.subtype)`.** Everything else of
the CHAIN-3 finish is free once that lands.

**The decisive structural fact (verified against the landed `def`).**
`complementIso` is built as `(wedgePairing as equiv) ≪≫ toDualEquiv.symm`, where
`wedgePairing k hj A B = screwAlgebraTopEquiv (A ∨ₑ B)` and `screwAlgebraTopEquiv
= exteriorPower.topEquiv (k+2)` is the **standard volume form**, and the dual side
uses `(Pi.basisFun …).exteriorPower (…).toDual`, whose `Pi.basisFun.toDual` is the
**standard dot product** (`Module.Basis.toDual_apply` = Kronecker δ). So
`complementIso` **is the Hodge star `⋆` for the standard Euclidean structure on
`ℝ^{k+2}`** (volume form + dot product), up to the unit volume normalization. The
target `complementIso (n₀∧n₁) ∈ ⋀^k W` for `W = {n₀,n₁}^⊥` is therefore the
genuine **Hodge fact**: *`⋆` of a decomposable is the decomposable of the
orthogonal complement* (`⋆(n₀∧n₁) = ±` the `k`-extensor of an oriented orthonormal
basis of `(span{n₀,n₁})^⊥ = W`). This is **true and standard**, but it is the
central nontrivial content — the §(g) framing "cleanest geometrically; a small
`complementIso`-image leaf" **understated it** by reading the in-hand
*annihilation* as if it already were *membership* (it is not — see below).

**Why the in-hand annihilation does NOT directly give membership.** The LANDED
`complementIso_toDual_eq_zero_of_wedgeProd_eq_zero` gives: `b.toDual (complementIso
n) B = vol(n ∨ₑ B) = 0` whenever `n ∨ₑ B = 0`. Equivalently `complementIso n`
lies in the `b.toDual`-annihilator `Ann(Φ)` of `Φ := span{B ∈ ⋀^k : n ∨ₑ B = 0}`
(the `B` sharing a factor with `span{n₀,n₁}`). The point-join `x = extensor(w)`
(`w` a basis of `W`) also lies in `Ann(Φ)` and in the line `L = range(⋀^k W ↪)`.
**To conclude `complementIso n ∈ L` from this one needs `L = Ann(Φ)`, i.e.
`dim Ann(Φ) = 1`, i.e. `dim Φ = D − 1`.** That count is exactly the
**withdrawn `finrank_sup_range_wedgeFixedLeft`/`dim Φ̃` family** — §(f) proved it
does NOT generalize off `d=3` (at grade `k`, `dim Ann(Φ) = C(d−1,2) > 1` for
`d ≥ 4` if `Φ` is taken the d=3 way). **So the annihilation→membership upgrade is
NOT a free dimension match; it is the Hodge fact itself.** This kills the §(g)
"(β) is a clean fallback" sentence — restated honestly below.

**Route decision: (α), via `complementIso`'s O(n)-equivariance.** The route that
genuinely closes — and the only one not re-introducing a withdrawn count — is:

1. **`complementIso` is O(n)-equivariant** (the new sub-leaf, flagged clause (ii)).
   For `O : Fin (k+2) → ℝ` an orthogonal change of frame (preserves the standard
   dot product, so `det O = ±1`), `complementIso (j:=2)` intertwines
   `exteriorPower.map 2 O` and `exteriorPower.map k O` up to the sign `det O`:
   `complementIso (exteriorPower.map 2 O X) = (det O) • exteriorPower.map k O
   (complementIso X)`. This rests on two transformation facts: the volume form
   transforms by the determinant (`screwAlgebraTopEquiv (map (k+2) O · ) = det O ·
   screwAlgebraTopEquiv`, **no ready mathlib lemma** — build from
   `exteriorPower.map`/`topEquiv` + `det`; cf. `LinearMap.det` /
   `exteriorPower.alternatingMapToDual_apply_ιMulti`) and the dot product is
   O-invariant (`Pi.basisFun.toDual (O w) (O v) = Pi.basisFun.toDual w v`,
   `O` orthogonal). This is the substantive new mathematics; it is **not** a
   1–2-decl API addition — it is the genuine reason `complementIso` (Hodge `⋆`)
   is *O(n)*-natural but **not** *GL*-natural (the §(g)/checklist warning).
2. **Frame alignment.** Build an orthogonal `O` carrying `span{n₀,n₁}` to the
   coordinate `2`-plane `span{e₀,e₁}` (Gram–Schmidt on `n₀,n₁`, extend to an
   orthonormal basis of `ℝ^{k+2}`; mathlib `Basis`/orthonormal-extension API).
   Under `O`, `W = {n₀,n₁}^⊥` maps to `span{e₂,…,e_{k+1}}` (a coordinate
   subspace), `extensor n` maps (up to scalar) to the coordinate blade `e_{01}`.
3. **Invoke the LANDED standard-frame membership.**
   `complementIso_exteriorPower_basis_mem_range_map_subtype` gives the conclusion
   for the coordinate blade `e_{01}` and the coordinate `W' = O(W)`; transport
   back along `O` (a linear iso, so `range(⋀^k W ↪)` transports) by (1)+(2).

This honestly names a remaining obstacle (the O(n)-equivariance + the
volume-form-determinant fact) rather than asserting a one-liner a build would
faithfully mis-scope. **It needs no new *mathlib-level* fact** in the sense of a
missing Hodge-star *API* — every ingredient (`exteriorPower.map`, `topEquiv`,
`LinearMap.det`, orthonormal extension) is in mathlib — **but it does need a
genuine new *project-side* sub-lemma** (the equivariance), which is itself the
crux. Clause (ii) verdict: **flag the O(n)-equivariance as its own buildable leaf
(`complementIso_map_orthogonal_eq`-shaped); do not pre-commit it as cheap.**

**Pinned leaf sequence for OD-8 (route α), dependency-ordered:**
- **(h-0)** `screwAlgebraTopEquiv_map_eq_det_smul` (or inline) — the volume form
  transforms by the determinant under `exteriorPower.map (k+2) f`. New; mathlib
  has the pieces, not the fused lemma. *Flagged: confirm the cleanest mathlib
  handle at build (`exteriorPower.map`+`topEquiv`+`det`).*
- **(h-1)** `complementIso_map_orthogonal_eq` — `complementIso`'s O(n)-equivariance
  (the substantive leaf). Consumes (h-0) + dot-product O-invariance. **The OD-8
  clause-(ii) flag lives here.**
- **(h-2)** `exists_orthogonal_map_span_pair_eq_coordPlane` — orthonormal
  alignment carrying `span{n₀,n₁}` to `span{e₀,e₁}` (Gram–Schmidt / orthonormal
  extension; mathlib `Basis` API). Combinatorial-geometry, no `complementIso`.
- **(h-3)** `complementIso_extensor_mem_range_map_subtype` — the target leaf
  (signature §(f) item 2): assemble (h-1)+(h-2)+the LANDED
  `complementIso_exteriorPower_basis_mem_range_map_subtype`. The `extensor n = 0`
  (dependent `n`) case is trivial (`complementIso 0 = 0 ∈ range`); the work is the
  `n`-independent case, where `dim W = k` holds (rank–nullity on the 2 functionals).
  **The build surfaced an input step §(h) glossed** (`extensor n = c • blade`): it
  needs a genuine grade-2 proportionality + a grade-decoupled membership brick, now
  **LANDED** (`exists_smul_extensor_eq_of_mem_span_range` +
  `extensor_mem_range_map_subtype_of_mem_jgrade`, `Meet.lean`, 2026-06-17). The remaining
  (h-3) work is the metric composition; the `W = {n}^⊥` dimension step is the one untested
  piece (rolling detail in `notes/Phase23b.md` *Hand-off*).
- **(h-4)** `extensor_join_proportional_complementIso_meet` — the assembly
  (signature §(f) item 1): consumes (h-3) + the three LANDED `_grade` bricks. Zero
  new count. **Hands the CHAIN-4 discriminator the join=meet proportionality**
  (the step KT leaves implicit — a BlueprintExposition-grade node per the
  coordinator KT-route check §(f)).
- **(h-5)** the `d=3` wrapper `complementIso_smul_eq_extensor_join` stays green
  (its `Φ̃`-route body unchanged; re-point is a CHAIN-4 decision, not forced).

**Honest fallback if (h-1) proves a long pole.** Route (β) is **rejected as a
fallback** (it re-introduces the withdrawn `dim Φ` count, §(f)). The genuine
fallback is to **state (h-3) as an explicit green-modulo hypothesis** on the
CHAIN-4 discriminator (the project's standing idiom) and land (h-1)/(h-3) in a
dedicated follow-on sitting — i.e. if the O(n)-equivariance does not close in one
build, it becomes its own leaf carried as an `h…` premise, never a `sorry`. This
keeps CHAIN-1/2/4/5 unblocked while (h-1) is the one open math obligation.

**What the finished OD-8 leaf hands the assembly.** `complementIso_extensor_mem_
range_map_subtype` (h-3) places the panel-meet `complementIso (n₀∧n₁)` in the line
`range(⋀^k W ↪)`; with the point-join already there (LANDED
`extensor_mem_range_map_subtype_of_mem_grade`) and the proportionality engine
(LANDED), (h-4) yields `extensor_join_proportional_complementIso_meet` — the
per-line point-join↔panel-meet duality CHAIN-4's discriminator
(`exists_complementIso_ne_zero_of_homogeneousIncidence`) consumes (the way the
d=3 discriminator consumes `complementIso_smul_eq_extensor_join`). That closes
CHAIN-3; the eq.-(6.67) `D`-span finish (the `d+1`-points / Lemma-2.1 argument)
stays CHAIN-4, gated by OD-4.

### (i) OD-4 design-pass — the eq.-(6.67) N3a route is RESOLVED: existence/homogeneous, NOT alg-independence

**Status:** OD-4 detailed-build recon, docs-only, 2026-06-18, source-verified
against (i) the KT 2011 PDF p. 698 (eq. 6.67, the `d+1`-points / alg-independence
finish, read verbatim) and (ii) the **landed** `Claim612.lean` bodies —
`exists_homogeneousIncidence_of_normals` (393), `span_omitTwoExtensor_eq_top`
(58), `case_III_claim612` (1064), `exists_line_data_of_homogeneousIncidence`
(549), the live d=3 dispatch call site (`Realization.lean:371`) — and the three
existence-route bricks (`exists_ne_zero_dotProduct_eq_zero` 119,
`exists_affineIndependent_of_det_polynomial_ne_zero` 161,
`exists_detPolynomial_of_pointPolynomial` 190). The prior pin (OD-4 in §(e),
`AlgebraicIndependence.md` row #107(b)) leaned **"forced"**; this pass **overturns
that lean**: alg-independence is **NOT forced** — the formalization's d=3 route
already sidesteps KT's alg-independence argument, and that re-route generalizes.

**VERDICT: existence/homogeneous route — alg-independence is NOT a new site.**
The eq.-(6.67) N3a step (showing `dim span ⋃ C(Lᵢ) = D`, forcing some `Mᵢ` full
rank) lifts as a **mechanical numeral generalization of the already-green d=3
bricks**, with no `AlgebraicIndependent` obligation. The only genuinely-new work
is the `Fin (d+1)` re-statement of `exists_homogeneousIncidence_of_normals` and
its line-data dispatch — both combinatorial/linear-algebra, no genericity device.

**Why the prior "forced" lean was wrong (the decisive structural fact).** The
prior reasoning followed **KT's affine phrasing** — KT (p. 698) takes `d+1`
*affinely-independent points* `p₀…p_d`, observes any `(d−1)` of them span a
`(d−2)`-flat lying in `⋃Πⱼ`, and gets `dim = D` "by Lemma 2.1" — and the
`(d−2)`-flat-in-union step *is* where KT invokes alg-independence ("for any `j`
hyperplanes their intersection forms a `(d−j)`-flat"). But the **landed d=3
formalization never takes this route.** It works at the **homogeneous-vector
layer** (the §1.42 R1-affine decision), and the D-span is driven by **linear
independence of `d+1` homogeneous vectors**, not affine independence of `d+1`
points:
- `case_III_claim612` (the D-span existential) calls
  `span_omitTwoExtensor_eq_top hp` whose **only** hypothesis is
  `hp : LinearIndependent ℝ pbar` (pbar : Fin (k+2) → Fin (k+2) → ℝ). The `D =
  (k+2 choose 2)` omit-two extensors of `k+2` LI homogeneous vectors are LI by
  **Lemma 2.1** (`omitTwoExtensor_linearIndependent_of_li`, `{e:ℕ}`, general) and
  hence a basis of the D-dim `ScrewSpace k` — they span. **`span_omitTwoExtensor_
  eq_top` is ALREADY general-`k` (line 58); zero affine independence, zero
  alg-independence, zero `(d−2)`-flat-in-union.**
- The `pbar` itself comes from `exists_homogeneousIncidence_of_normals`, which
  produces `LinearIndependent ℝ pbar` from the **row-matrix surjectivity** of the
  `d × (d+1)` panel-normal matrix (`LinearIndependent.rank_matrix` ⟹ rank `d` ⟹
  `mulVecLin` surjective onto `ℝ^d` ⟹ preimages of standard targets) plus a
  triangular LI argument. Its **only** genericity input is `LinearIndependent ℝ n`
  (the `d` chain-panel normals nonparallel) — read off the GP split-leg. **No
  cross-products, no triple-intersection, no alg-independence.**

So the row #106 explicit construction (`p₁` = triple-intersection via Cramer/
cross-products, `pᵢ = p₁ + sᵢ·(nⱼ×nₖ)`) and the affine-route bricks
(`exists_affineIndependent_panel_incidence`,
`exists_affineIndependent_of_det_polynomial_ne_zero`,
`exists_detPolynomial_of_pointPolynomial`,
`omitTwoExtensor_homogenize_eq_extensor_kept`,
`exists_hduality_witness_of_panel_incidence`) are **DEAD — verified zero live
call sites** on the dispatch path (grep, 2026-06-18: they appear only in
docstrings + their own defs; the live d=3 dispatch at `Realization.lean:371`
consumes `exists_homogeneousIncidence_of_normals`). They are abandoned earlier-
design scaffolding the §1.42 homogeneous re-route superseded. **The OD-4 question
"does the cross-product construction generalize" is moot — that construction is
not on the live route at d=3, so its non-generalization (correctly noted in row
#107(b)) does not force anything.** The question that actually matters is whether
the *homogeneous* route generalizes, and it does (below).

**The per-line panel-membership generalizes purely combinatorially (the one place
one might fear alg-independence re-enters).** The discriminator needs, for each of
the `D` spanning joins, a panel `Πᵤ` the join's line lies in (CHAIN-3's per-line
duality then transfers `r(join)≠0` to `r(C(Lᵤ))≠0`). At d=3 this is the finite
`htwo`/`hone` dispatch in `exists_line_data_of_homogeneousIncidence`. It
generalizes from the incidence pattern alone — **no `(d−2)`-flat-in-union fact
needed.** Verified combinatorics (scratch, 2026-06-18): with the general pattern
`pbar 0 ⊥` all `d` normals and `pbar (i+1) ⊥` all but `n i`, the unique point off
`Πᵢ` is `pbar (i+1)`, so the line of join `{a,b}` (kept points = complement of
the omitted pair) lies in `Πᵢ` **iff `i+1 ∈ {a,b}`**. Hence every join lies in
**1 panel** (when `0 ∈ {a,b}`: `d` such joins, second normal from the landed
general `exists_independent_perp_pair_gen`) or **2 panels** (when `a,b ≥ 1`:
`C(d,2)` such joins) — exactly the d=3 `hone`/`htwo` split, scaled to `D = d +
C(d,2)` joins (`d=3 ⟹ 3+3=6 ✓`; `d=4 ⟹ 4+6=10`). This panel-membership is a
property of the **orthogonality hypotheses of `pbar` against `n`**, provable
directly — it does **not** reconstruct KT's geometric `(d−2)`-flat-in-union claim.
KT's affine phrasing and the homogeneous re-route are two proofs of the same
`dim = D` fact; the homogeneous one (which is what the tree runs) needs only
Lemma 2.1 + linear independence.

**Where alg-independence DOES stay live (site (a), unchanged) — not site (b).**
Per `AlgebraicIndependence.md` row #107, Phase 23 has two candidate sites: **(a)**
the footnote-6 seed-rank transfer along the chain (the general-`d` lift of
`case_III_nested_rank_lower`, which *already* consumes `AlgebraicIndependent ℚ q`
at d=3) and **(b)** the eq.-(6.67) N3a points step. This pass resolves **(b) is
NOT a site** (existence/homogeneous route). **(a) remains a live site** and is
**unchanged by this verdict** — it is the carrier-lifted nested-rank bridge,
already alg-independence-carrying from 22d, lifted in CARRIER(23a)/CHAIN; the
seed `q` of the IH-generic base `(G₁,q₁)` carries `AlgebraicIndependent ℚ`
regardless. The eq.-(6.67) finish does **not add** an alg-independence obligation
on top of (a).

**Clause (ii) — no genuinely-new math, no motive/IH change.** OD-4 needs **no**
new `AlgebraicIndependent`-driven non-vanishing lemma and **no** `(d−j)`-flat-
intersection lemma. The CARRIER lift already carries the seed's
`AlgebraicIndependent ℚ` for site (a); the eq.-(6.67) finish reuses the already-
general `span_omitTwoExtensor_eq_top` + Lemma 2.1. The CHAIN-4 work is the
mechanical `Fin (d+1)` re-statement of the homogeneous-incidence chain (next
section). This is the honest, source-grounded resolution: the existence route the
pre-22d precedents (Claim 6.4/6.9) and the d=3 N3a used **does** carry to general
`d`, because the formalization phrases N3a homogeneously rather than affinely.

**Residual flag (the one honest caveat, not a blocker).** This verdict rests on
the per-join panel-membership being establishable from the incidence pattern at
general `d` *combinatorially* — verified at the *counting* level (the join↔panel
incidence `i+1 ∈ {a,b}` and the `D = d + C(d,2)` split) but **not yet built**.
The d=3 `exists_line_data_of_homogeneousIncidence` discharges it with a hand
`fin_cases q` over the 6 joins; at general `d` the dispatch must be written as a
**uniform** argument over the `Fin (d+1)`-pair index (two cases on whether `0` is
in the omitted pair), not `fin_cases`. This is a writing obligation (a `Fin`-
indexed reindex of the d=3 builders), not a math one — if it surfaces a genuine
gap at build, *that* would be the place an alg-independence/geometric fact could
sneak back in, so the CHAIN-4 builder must confirm the membership closes from the
orthogonality hyps alone. **Pinned, not pre-committed away:** the verdict is
"existence route; the only new work is the homogeneous-incidence re-statement,"
with this one build-time confirmation flagged.

### (j) CHAIN-4 remainder decomposition — buildable leaves with exact signatures

**Status:** CHAIN-4 detailed-build recon, docs-only, 2026-06-18 (companion to the
OD-4 verdict §(i)). CHAIN-4's two mechanical bricks landed 2026-06-18
(`exists_independent_perp_pair_gen`, `omitTwoExtensor_eq_extensor_kept_gen`); this
decomposes the **remainder** into buildable leaves with exact `Fin (k+2)`/`Fin
(d+1)` signatures, dependency-ordered. Convention (matching §(f) and the all-`k`
engine): phrase `k`-parametrically with `k = d − 1`, ambient `Fin (k+2) =
Fin (d+1)`, the `d` chain normals `n : Fin (k+1) → Fin (k+2) → ℝ` (at d=3, `k=2`:
`Fin 3 → Fin 4`), the `d+1` homogeneous witness vectors `pbar : Fin (k+2) →
Fin (k+2) → ℝ`. Each leaf keeps the `Fin 4`/d=3 lemma as a `k:=2` wrapper (zero
d=3 regression). The leaves below feed CHAIN-5's dispatch (§C.3).

**Leaf CHAIN-4a — `exists_homogeneousIncidence_of_normals` at `Fin (k+1) →
Fin (k+2)` (the OD-4 sub-leaf; clean lift, no residual openness).**
```
theorem exists_homogeneousIncidence_of_normals_gen {k : ℕ}
    {n : Fin (k + 1) → Fin (k + 2) → ℝ} (hn : LinearIndependent ℝ n) :
    ∃ pbar : Fin (k + 2) → Fin (k + 2) → ℝ, LinearIndependent ℝ pbar ∧
      (∀ u, pbar 0 ⬝ᵥ n u = 0) ∧
      (∀ i : Fin (k + 1),
        (∀ j, j ≠ i → pbar i.succ ⬝ᵥ n j = 0) ∧ pbar i.succ ⬝ᵥ n i ≠ 0)
```
*Mechanism (verbatim lift of the d=3 body, lines 427–504).* The `(k+1) × (k+2)`
row matrix `A = of n` has LI rows (`hn`), so `A.rank = k+1 = finrank ℝ^{k+1}`
(`LinearIndependent.rank_matrix`); `A.mulVecLin` is surjective onto `ℝ^{k+1}`
(`Submodule.eq_top_of_finrank_eq`); preimages of the `k+1` standard targets
`e_i : Fin (k+1) → ℝ` give `pbar (i+1) ⊥ n j` for `j≠i` and `≠ 0` against `n i`;
`pbar 0` is the nonzero common-perp of all `k+1` normals (`exists_ne_zero_
dotProduct_eq_zero` at `m = k+1 < k+2`, **already general**, line 119). LI of
`pbar` is the triangular argument: pairing `∑ gᵢ • pbar i = 0` against `n u`
isolates `g (u+1)`, then `g 0 • pbar 0 = 0` with `pbar 0 ≠ 0`. **Clean lift** —
the only d=3-specific tactics are `Fin.sum_univ_four`/`fin_cases`, which become
`Fin.sum_univ_succ`/`Finset.sum_eq_single`-style over `Fin (k+2)`. **No residual
openness** (this is the OD-4 §(i) verdict made concrete: existence/linear, no
genericity device). The `Fin 4` `exists_homogeneousIncidence_of_normals` becomes
the `k:=2` wrapper (a `Fin 3`-vs-`Fin (k+1)` reindex + the `∀ i, …` unpacked to
the three explicit `hb1/hb2/hb3` conjuncts).

**Leaf CHAIN-4b — `exists_line_data_of_homogeneousIncidence` at `Fin (k+2)`
(clean lift; carries the §(i) residual flag). LANDED 2026-06-18 (8496d61).**
**Signature correction at build:** the conclusion's `LinearIndependent ℝ p` (the
kept-points subfamily, which CHAIN-3 (h-4) consumes) does **not** follow from
`hn`/`h0`/`hi` alone — it needs `(hpbar : LinearIndependent ℝ pbar)` (the kept
points are a `pbar`-subfamily, so LI by `LinearIndependent.comp`). `hpbar` is
freely supplied by CHAIN-4a's first conjunct, so it is added as a hypothesis (the
faithful pin completion). Because of this stronger conclusion + the off-one-panel
incidence shape, the d=3 `exists_line_data_of_homogeneousIncidence` (weaker — no
point-LI conclusion, cyclic `h1/h2/h3`) is **not** a clean `k:=2` wrapper; it
stays its own green lemma (pin untouched), and re-pointing the d=3 CHAIN-4d at
`_gen` is the not-forced h-5 decision. §(i) combinatorial claim **CONFIRMED** at
build (no alg-independence resurfaced). Landed signature:
```
theorem exists_line_data_of_homogeneousIncidence_gen {k : ℕ}
    {n : Fin (k + 1) → Fin (k + 2) → ℝ} (hn : LinearIndependent ℝ n)
    {pbar : Fin (k + 2) → Fin (k + 2) → ℝ} (hpbar : LinearIndependent ℝ pbar)
    (h0 : ∀ u, pbar 0 ⬝ᵥ n u = 0)
    (hi : ∀ i : Fin (k + 1), ∀ j, j ≠ i → pbar i.succ ⬝ᵥ n j = 0) :
    ∀ q : {q : Fin (k + 2) × Fin (k + 2) // q.1 < q.2},
      ∃ (u : Fin (k + 1)) (n' : Fin (k + 2) → ℝ)
        (p : Fin k → Fin (k + 2) → ℝ),
        LinearIndependent ℝ ![n u, n'] ∧ LinearIndependent ℝ p ∧
        (∀ i, p i ⬝ᵥ n u = 0) ∧ (∀ i, p i ⬝ᵥ n' = 0) ∧
        omitTwoExtensor pbar (ne_of_lt q.2) = extensor p
```
*Mechanism.* The `d=3` builders `htwo`/`hone` generalize via the §(i) join↔panel
combinatorics: for omitted pair `q = {a,b}`, the kept points are the `k = d−1`
increasing-complement indices (`omitTwoExtensor_eq_extensor_kept_gen`, **LANDED**),
and the line lies in `Πᵢ` iff `i+1 ∈ {a,b}`. Two cases on `0 ∈ {a,b}`: if `0 ∉
{a,b}` the line lies in the **two** panels `Π_{a−1},Π_{b−1}` (take `n' = n (b−1)`,
both kept points ⊥ both normals — the `htwo` analog); if `0 ∈ {a,b}` it lies in
the **single** panel `Π_{b−1}` (take `n'` from the landed
`exists_independent_perp_pair_gen` on the `d−1 = k` kept points, needs `2 ≤ k`
i.e. `d ≥ 3` — the `hone` analog). **Carries the §(i) residual flag:** the d=3
body discharges the per-join dispatch by `fin_cases q` over 6 joins; the general
form must be a **uniform** two-case argument over the `Fin (k+2)`-pair, and the
"kept points ⊥ the shared normal(s)" step must close from `h0`/`hi`
(orthogonality) + the kept-index complement membership alone. **This is the one
leaf whose build must confirm the §(i) combinatorial claim** (the place a hidden
geometric/alg-independence need would surface if §(i) is wrong). Note the points
arity is now `Fin k` (the `k = d−1` points spanning the line), matching CHAIN-3's
`extensor_join_proportional_complementIso_meet` point family `p : Fin k`.

**Leaf CHAIN-4c — `case_III_claim612` at `ScrewSpace (d−1)`/`Fin (d+1)` (clean
lift; the D-span existential).**
```
theorem case_III_claim612_gen {k : ℕ} {r : Module.Dual ℝ (ScrewSpace k)} (hr : r ≠ 0)
    {pbar : Fin (k + 2) → Fin (k + 2) → ℝ} (hp : LinearIndependent ℝ pbar) :
    ∃ q : {q : Fin (k + 2) × Fin (k + 2) // q.1 < q.2},
      r ⟨omitTwoExtensor pbar (ne_of_lt q.2), extensor_mem_exteriorPower _⟩ ≠ 0
```
*Mechanism (verbatim lift of the d=3 body, lines 1064–1079).* Contrapositive:
if `r` annihilated every one of the `D` joins it would annihilate their span
`= ⊤` (the **already-general** `span_omitTwoExtensor_eq_top hp` (23a Leaf 2) via
Lemma 2.1) hence be `0` (`eq_zero_of_annihilates_span_top`, **already general**,
line 100). **Pure numeral lift — both bricks are already `{k:ℕ}`; this is the
cleanest CHAIN-4 leaf.** No residual openness. (This is the §(i) D-span finish:
it needs only LI of `pbar`, no affine independence.)

**Leaf CHAIN-4d — `exists_complementIso_ne_zero_of_homogeneousIncidence` at
`ScrewSpace (d−1)`/`Fin d` candidates (the discriminator; consumes CHAIN-3 (h-4)).**
```
theorem exists_complementIso_ne_zero_of_homogeneousIncidence_gen {k : ℕ}
    {r : Module.Dual ℝ (ScrewSpace k)} (hr : r ≠ 0)
    {pbar : Fin (k + 2) → Fin (k + 2) → ℝ} (hp : LinearIndependent ℝ pbar)
    {n : Fin (k + 1) → Fin (k + 2) → ℝ} (hn : LinearIndependent ℝ n)
    (h0 : ∀ u, pbar 0 ⬝ᵥ n u = 0)
    (hi : ∀ i : Fin (k + 1), ∀ j, j ≠ i → pbar i.succ ⬝ᵥ n j = 0) :
    ∃ (u : Fin (k + 1)) (n' : Fin (k + 2) → ℝ), LinearIndependent ℝ ![n u, n'] ∧
      r (complementIso (k := k) (j := 2) (by omega)
          ⟨extensor ![n u, n'], extensor_mem_exteriorPower _⟩) ≠ 0
```
*Mechanism.* Combine CHAIN-4c's witness join (`r(join q)≠0`) with CHAIN-4b's
per-join line data (the panel `n u`, second normal `n'`, the `k` kept points `p`
with `omitTwoExtensor pbar = extensor p`); the per-line **join=meet duality**
`extensor_join_proportional_complementIso_meet` (**CHAIN-3 (h-4), LANDED**, the
`k`-form) transfers `r(extensor p) = r(join q) ≠ 0` to `r(complementIso⟨extensor
![n u,n'],_⟩) ≠ 0` (the contrapositive of the d=3
`extensor_join_eq_zero_of_complementIso_eq_zero_dotProduct`). **Note the
discriminator's `complementIso` is `(j := 2)`, NOT `(j := d−1)`** — the §(f)/§(i)
correction: a line has exactly 2 normals at every `d`, so the panel-meet is the
meet of 2 hyperplanes (input grade 2, output grade `k`). The prior §(a)-table
entry "`complementIso(k:=d−1)(j:=d−1)`" is wrong; it is `(j:=2)`. **Residual
openness: none beyond CHAIN-4b's flag** — this leaf is the assembly of 4b+4c+(h-4),
all of whose pieces are landed or clean lifts. The `Fin 3` discriminator becomes
the `k:=2` wrapper; the d=3 `exists_complementIso_ne_zero_of_homogeneousIncidence`
re-points at this general lemma's `k:=2` instance (or stays the green d=3 body —
a CHAIN-4-internal call, h-5 territory, not forced).

**Dependency order:** CHAIN-4a (independent) → CHAIN-4b (consumes 4a's incidence +
landed `omitTwoExtensor_eq_extensor_kept_gen` + `exists_independent_perp_pair_gen`)
→ CHAIN-4c (independent; consumes only the landed general N1) → CHAIN-4d (consumes
4b + 4c + the landed CHAIN-3 (h-4) duality). 4a and 4c are buildable now in
parallel (both clean lifts); 4b carries the one §(i) residual confirmation; 4d is
the capstone. **First buildable OD-4 leaf = CHAIN-4a** (the OD-4 verdict made
concrete; no dependency on un-landed work).

---

### (k) OD-7 `hcontract_k` decomposition — buildable leaves with exact signatures

**Status:** recon 2026-06-18 (read-only Plan recon, coordinator-verified against the
landed source — the actual `def`/`theorem` bodies in `Theorem55.lean`/`CaseI.lean`/
`Coupling.lean`/`Pinning.lean`/`GenericityDevice.lean`/`PanelLayer.lean`/
`CaseIII/Realization.lean`). `hcontract_k` is the **last** open OD-7 producer (the
Case-I rigid-subgraph dispatch); its general-`k` lift is **5 leaf commits (6 if h65
splits)**, of which exactly **one is genuinely-new** and the rest are numeral passes.

The `hcontract_k` slot (`theorem_55_minimalKDof_k_all_k`, `Theorem55.lean:2379`) is
filled at `k=2` (`:2471–2495`) by splitting `c=0` (→ `case_I_dispatch :2290`) vs
`c>0` (manual: `case_I_realization_all_k :2194` simple / `case_I_realization_nonsimple
:1899` non-simple / `deficiency_eq_zero… :Contraction:1114` + `hasPanelRealization_of_
generic`). `case_I_dispatch` further routes to `all_k` + `case_I_realization_h65 :691`
(KT Lemma 6.5 all-contractions-non-simple arm). So the FOUR grade-2-pinned producers
(`hn : screwDim 2`, `HasGenericFullRankRealization 2`) are `all_k`/`nonsimple`/`h65`/
`dispatch`. **The `_all_k` name is a TRAP** — its `{k:ℤ}` is the **dof** variable
(all-dof, still grade-2), NOT grade-general.

**Per-producer classification (all reach-ins read at source):**
- `case_I_realization_all_k` → **verbatim numeral pass**, independent. Zero inline
  `Fin 4`; every reach-in already grade-parametric — `couple_geometry_of_isProperRigid
  Subgraph` (`Coupling:562`, grade-agnostic), the coupler `hasGenericFullRank
  Realization_of_couple_blockTriangular_ofNormals_set_kdof` (`CaseI:1310`, `Fin (k+2)`/
  `screwDim k`/`extProj (k:=k)`), `exists_rankPolynomial_of_IH_relabel_linking_set_
  proj` (`CaseI:921`). Subst `screwDim 2→k`, `HGFRR 2→k`; add `hk:1≤k`, `[NeZero k]`
  where threaded.
- `case_I_realization_nonsimple` → numeral pass **+ one swap**: its `Fin 4`
  `exists_linearIndependent_extensor_pair_perp` (`PanelLayer:546`) is itself the
  `k:=2` wrapper of the landed grade-general `…_perp_grade` (`PanelLayer:466`) — swap
  to `_grade`. All other reach-ins (`theorem_55_base`, the splice/coupling/B2 bricks)
  already `BodyHingeFramework k`/`screwDim k`/`extProj (k:=k)`.
- `case_I_realization_h65` → numeral pass over LEAF-0 + lifting the four private
  `case_I_h65_*` helpers (`:590–664`, `BodyHingeFramework 2→k`); **may split** (the
  helpers were extracted to dodge a §38 `ScrewSpace 2` elaboration budget — the
  `ScrewSpace k` carrier can re-trip it). Its load-bearing bricks (`triLI_subpairs`,
  `normalsJoin_pair_linearIndependent_of_triLI`, `exists_independent_pinned_two_edge_
  span_full`, `hasGenericFullRankRealization_of_rigidOn_ofNormals`) are grade-general.
- `case_I_dispatch` + the c>0 manual-dispatch logic → **verbatim numeral pass** (pure
  `by_cases` plumbing over the three producers; pins in signature only).

**LEAF-0 — the one genuinely-new piece (coordinator-verified gap):**
`linearIndependent_normals_of_algebraicIndependent_triple` — a **fixed-3-row** LI at
`Fin (k+2)`:
```lean
lemma linearIndependent_normals_of_algebraicIndependent_triple
    {k : ℕ} {α : Type*} {q : α × Fin (k + 2) → ℝ} (hq : AlgebraicIndependent ℚ q)
    {a b c : α} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    LinearIndependent ℝ (![fun i => q (a,i), fun i => q (b,i), fun i => q (c,i)]
      : Fin 3 → Fin (k+2) → ℝ)
```
**Why new, not a numeral pass:** the landed `…_general` (`Realization:100`) gives LI
of a **`Fin (k+1)`-row** family from `k+1` injective vertices; the `Fin 4` triple
(`:163`) is its `k:=2` instance (3 = k+1 at k=2). h65 has only a **degree-2 vertex +
2 neighbours = 3 vertices**, so for `k≥3` the `k+1`-vertex selector is unavailable —
the triple needs its OWN lemma. Proof: the same `AlgebraicIndependent.aeval_ne_zero`
+ minor-det technique as `…_general`, restricted to a fixed `Fin 3`/3×3 minor.
Routine. Home: `CaseIII/Realization.lean` beside `…_general`; the `Fin 4`
`linearIndependent_normals_of_algebraicIndependent` re-derives as its `k:=2` instance
(so the still-`k=2` consumer `case_III_candidate_dispatch` is unaffected).

**Build order + count** (LANDED 2026-06-18: `all_k_gen`, `nonsimple_gen`, LEAF-0 triple-LI —
with `hk : 1 ≤ k`, the `3×3`-minor restriction of `…_general`): `case_I_realization_all_k_gen` (1st,
independent, cleanest numeral pass) → `case_I_realization_nonsimple_gen` (numeral pass + `_perp_grade`
swap) → LEAF-0 triple-LI → **`case_I_realization_h65_gen`** (next; consumes LEAF-0; may split)
→ `case_I_dispatch_gen` + the general `hcontract_k` wire-up (closes OD-7; the `k=2`
`theorem_55_minimalKDof_k` filler stays green as the `k:=2` instance, blueprint pins
unmoved). **5 commits min, 6 if h65 splits.** **Clause-(ii) flag:** exactly one
genuinely-new leaf (LEAF-0, small/low-risk); **no motive/IH change, no grade-2-only
splice/coupling/extensor brick** surfaced — the `Fin 4` literals in `nonsimple`/`h65`
are presentation pins over grade-general bricks, the landed `hbase_k`/`hcut_k`
pattern. Caveats: `[NeZero k]` where routing through `hasPanelRealization_of_generic`;
h65 §38 `ScrewSpace k` budget may force a per-helper split.

---

### (l) CHAIN-2 decomposition — corrects the §(c) framing + buildable sub-leaves

**Status:** recon 2026-06-18 (read-only Plan recon, coordinator source-verified). **It overturns the
§(c) CHAIN-2 framing.**

**Headline correction (verified against the landed source).** §(c) and the Phase23b checklist/hand-off
say CHAIN-2 generalizes "the `caseIIICandidate` / `case_III_old_new_blocks` / `case_III_rank_certification`
chain (now `q : α × Fin 4`-shaped)" to a `Fin d`-indexed family. **That parenthetical is FALSE:** all
three decls live in `CaseIII/Candidate.lean` under `variable {k : ℕ}` at `q : α × Fin (k+2)` /
`ScrewSpace k` / `screwDim k` — **already general-`k`, need no work.** A grade-2 grep over all four
`CaseIII/` files hits **only `Realization.lean`** (the `case_III_candidate_dispatch` shell + the `Fin 4`
`linearIndependent_normals_of_algebraicIndependent` bridge + `case_III_nested_rank_lower_d3`) — i.e. the
only `d=3`-pinned surface in `CaseIII/` is the **dispatch**, which is **CHAIN-5's** target, not CHAIN-2's.
(This is the same fact §(a) states; §(c) failed to propagate it.)

**What CHAIN-2 actually is.** The candidate machinery is general per dof+grade but **structurally
single-candidate** (every certification reduces ONE `caseIIICandidate` via ONE `Φ = columnOp` at the
single split body, appending ONE `Unit`-tagged row; the dispatch picks ONE panel via `fin_cases`). KT
eqs. 6.59–6.64 are a genuine **`d`-candidate** construction (each `R(G,pᵢ)` reduced via candidate `i`'s
OWN `Φᵢ`, + the ±r chain 6.66). So CHAIN-2 = **build the `Fin d`-indexed reduction LAYER on top of the
already-general (reused-verbatim) `case_III_rank_certification` chain + the closed CHAIN-1 `ιc`-block
augment** — genuinely-new *infrastructure*, but NOT a generalization of the named trio.

**Buildable sub-leaves** (all `{k}`-general, `CaseIII/Candidate.lean` or a new `CaseIII/Chain.lean` if
>~1500 LoC):
- **CHAIN-2a — the per-candidate single-`i` reduction** (the reusable core; heaviest single leaf). A
  re-INDEX (not re-grade) of `case_III_rank_certification` holding the split-body / redundant-row index
  fixed at `i`: `Mᵢ ⊕ R(G₁∖(v₀v₂)_{i*}, q₁)`. Consumes Claim 6.11 `exists_redundant_panelRow_…` (GREEN).
  No grade-2 reach-in.
  **Session-#7 finding (2026-06-18) — CHAIN-2a needs ITS OWN design-pass before a build.** The
  `ChainData` record + the 7 interior-split accessors landed (rows 236/237, supplying the graph-side
  `(v,a,b,e_a,e_b)` tuple), but `case_III_rank_certification` carries **~20 hypotheses** — the `ρ`
  dual-functional gates (`hρgate`/`hρe₀`/`hρGv`) + the rank-certifying `w`-family
  (`hwcard`/`hw`/`hwmem`) — and discharging them at the per-`i` index is the substantial part. An opus
  build self-shrank from it to the accessors (2nd consecutive infra commit feeding the unbuilt core →
  rows 27–29 design-pass trigger). **Key open question the design-pass must settle:** does the d=3
  path's already-general arm closer `case_III_arm_realization` (`CaseIII/Arms.lean`) discharge those
  certification hyps — so CHAIN-2a *re-indexes* it (clean) — or must `ρ`/`w`/the gates be constructed
  per-`i` from scratch (large, several sub-leaves)? Decompose accordingly.
- **CHAIN-2b — the ±r chain (eq. 6.66).** Genuinely-new structure (no d=3 ancestor — d=3 collapses it to
  the 2-index degree-2 fact): `r` is the same up to sign along the chain, so `Mᵢ` fails full rank iff
  `r ⊥ C(Lᵢ)`. `Fin`-induction over chain edges using the (general) degree-2 closures.
- **CHAIN-2c — the `Fin d` candidate-family assembly** (where the per-candidate `Φᵢ` heterogeneity
  lives). Assembles the `d` CHAIN-2a outputs + CHAIN-2b into the "some `Mᵢ` full-rank ⟺ ¬∀i r⊥C(Lᵢ)"
  disjunction. Consumes the **closed CHAIN-1** `…_augment_candidateRow_block` / `…_pinned_block_augment_block`
  / `…candidateBlock_swap` (the `ιc`-block tools, fire one body at a time).
- (CHAIN-2d only if 2a over-grows: split the 6.59 col-op-subst + 6.62 row-correspondence into their own
  bricks — but their d=3 ancestors `panelRow_vb_sub_panelRow_ab_eq_hingeRow_va` / `exists_candidate_row_eq612`
  are already `{k}`-general, so re-index not re-grade; fold into 2a unless contact says otherwise.)

**Order:** CHAIN-2a → CHAIN-2b → CHAIN-2c. **First buildable = CHAIN-2a.** **Count: 3–5 commits**
(most likely record + 2a + 2b + 2c).

**Load-bearing prerequisite (clause (ii) flag) — the `ChainData` record — DISCHARGED 2026-06-18.**
CHAIN-2a/b/c all index a length-`d` chain, so their signatures bind to the `G.ChainData n` record. That
record is now **authored in Lean** (`Induction/Operations.lean`, the `splitOff` home — the zeroth
CHAIN-2 leaf), so the *indexing* prereq is discharged. The shape is the contract-C.1 `structure`
(`vtx : Fin (d+1) → α`, `edge : Fin d → β`, `e₀`, the deg-2 closures + `vtx_inj`/`link`/`edge_inj`/
`e₀_fresh`), and its **`deg_two` `Fin`-arithmetic is settled**: interior vertices guarded by `0 < (i:ℕ)`,
the predecessor edge as `edge ⟨(i:ℕ)-1, _⟩` (the `OfNat (Fin d)` literals don't synth at general `d`),
verified against the d=3 map (C.4) by `rfl`/`decide`. Contract C.1 assigns the *extractor* (which
produces a `ChainData`) to ENTRY; only the record *definition* landed here (the sharable half). So
CHAIN-2a can bind `cd : G.ChainData n` directly and is the next build; the linear-algebra core is
independent of the contract, the indexing now grounded.

**KT "exactly the same as `d=3`" audit:** faithful for CHAIN-2a's linear-algebra core (a re-index of an
already-general body); an honest **understatement** for CHAIN-2b/2c (the `Fin d` indexing layer has no
d=3 ancestor — mechanical, but new infrastructure to *write*, not *copy*). No motive/IH change; no
grade-2-only reach-in blocks CHAIN-2.

---

### (m) CHAIN-2a design-pass — VERDICT: re-index, gates threaded from above; the per-`i` reduction IS a `case_III_arm_realization` instance

**Status:** CHAIN-2a detailed design-pass, docs-only, 2026-06-18, source-verified
against the **landed** bodies (every load-bearing claim re-checked against the
actual `def`/`theorem`, not a prior pin — clause (i)): `case_III_rank_certification`
(`CaseIII/Candidate.lean:1403`, full body), `case_III_arm_realization` (`Arms.lean:72`),
`case_III_arm_realization_M2` (`Arms.lean:318`), `case_III_arm_realization_M3`
(`Relabel.lean:811`), the `d=3` dispatch `case_III_candidate_dispatch`
(`Realization.lean:268`, the gate-production trace, lines 388–520), the W6b
packaging `exists_candidateRow_bottomRows_of_rigidOn` (`Candidate.lean:390`), the
nested-rank producer `case_III_nested_rank_lower_all_k` (`Realization.lean:616`),
the discriminator `exists_complementIso_ne_zero_of_homogeneousIncidence_gen`
(`Claim612.lean:1462`, CHAIN-4d, LANDED), and the bridge
`panelSupportExtensor_eq_complementIso_extensor` (`PanelLayer.lean:331`). The
coordinator's findings (1)/(2)/(3) all **CONFIRMED** below; finding (1) is
refined (the gate-producer is two general-`k` layers, named).

**THE VERDICT (the heart of this pass): RE-INDEX, not construct-from-scratch.**
CHAIN-2a's per-`i` candidate reduction is a **re-instantiation of the already-
general arm closer `case_III_arm_realization`** at the interior split index `i`,
consuming the per-`i` gate family threaded from above — it does **not** construct
the `ρ`/`w`-family + gates per-`i` from scratch. Three source facts force this:

1. **`case_III_arm_realization` is the per-candidate engine, already general-`k`,
   and discharges all the way to `HasGenericFullRankRealization k n G`.** Its body
   (Arms.lean:101–) calls `case_III_rank_certification` verbatim at lines 114–115
   (passing `hLn hρgate hρe₀ hρGv hwcard hw hwmem` through), then re-extracts a
   literal `F₀.panelRow` family from the certified rank (W6e,
   `exists_independent_panelRow_subfamily_of_le_finrank`) and transfers it to a
   good shear `t* ≠ 0` (W6f) to land the generic realization. So the certification
   (the `Mᵢ ⊕ R(G₁∖(v₀v₂)_{i*}, q₁)` rank bound, KT eq. 6.29/6.64) is **already
   wrapped inside** the arm closer — CHAIN-2a does not re-derive it. The thing
   `case_III_arm_realization` is, structurally, *is* KT's per-candidate
   "`(G,pᵢ)` realizes at full rank if `Mᵢ` is full rank" step (eqs. 6.60/6.65).

2. **Neither the certification nor the arm closer discharges the gate family —
   both carry it as their own hypotheses, and the d=3 CALLER supplies them from
   two general-`k` producers** (coordinator finding (1), refined). The gate family
   `hLn`/`hρgate`/`hρe₀`/`hρGv`/`hwcard`/`hw`/`hwmem` is identical across
   `case_III_rank_certification`, `case_III_arm_realization`, `_M2`, `_M3` (the
   `_M2`/`_M3` arms are themselves `case_III_arm_realization` re-instantiations at
   swapped/relabelled roles — Arms.lean:331 `_M2 := …arm_realization … (ρ := -ρ)`;
   Relabel.lean:898 `_M3 := …arm_realization (v:=a)(a:=c)(b:=v)(q:=qρ)`). In the
   `d=3` dispatch the gates arrive **from above**, produced by:
   - **The W6b packaging `exists_candidateRow_bottomRows_of_rigidOn`** (Candidate.lean:390,
     **already general-`k`** — under `variable {k}`, all `screwDim k`/`ScrewSpace k`):
     called once at Realization.lean:388–391, it produces `ρ`, the bottom family
     `w`, and the gates `hρe₀` (`ρ(C(e₀))=0`), `hρGv` (`hingeRow a b ρ ∈ span Gᵥ`),
     `hwmem`, `hw` (LI), `hwcard` (card `= D·(|Vᵥ|−1)`) — the redundant-row + GAP-6
     half. Its only substantive inputs are the IH-base infinitesimal rigidity
     `hrig` on `Gₐᵦ` and the eq.-(6.22) nested rank bound `h622lb`.
   - **`h622lb` is produced by `case_III_nested_rank_lower_all_k`** (Realization.lean:616,
     **already general-`k`**, Phase 23a Leaf 4) — the footnote-6 nested-IH rank
     transfer, the `AlgebraicIndependent ℚ q`-consuming site (a) (OD-4 §(i)).
   - **The discriminator `exists_complementIso_ne_zero_of_homogeneousIncidence_gen`**
     (CHAIN-4d, **LANDED general-`k`**, Claim612.lean:1462): called at
     Realization.lean:439–441, it produces the discriminating index `u` + transversal
     `n'` with `hpair` (`= hLn`, the `![nᵤ, n'] ` LI) and the `complementIso`-form gate,
     which `panelSupportExtensor_eq_complementIso_extensor` (general, PanelLayer:331)
     rewrites into `hρgate` (`ρ(panelSupportExtensor nᵤ n') ≠ 0`).

3. **`case_III_arm_realization`'s grade is `(k : ℕ)` / `ScrewSpace k` / `Fin (k+2)`
   already** (Arms.lean:72, authored general from Phase 22h, confirmed §(a)). So
   the arm closer needs **zero lift** — CHAIN-2a *re-indexes* it: bind `cd :
   G.ChainData n`, pick an interior index `i` (`0 < (i:ℕ) < d`), read the per-`i`
   split tuple `(v,a,b,e_a,e_b)` off the landed interior-split accessors (rows
   236/237: split body `vtx i.castSucc`, edges `edge i`/`edge ⟨(i:ℕ)−1,_⟩` oriented
   out of it, distinct neighbours, re-oriented degree-2 closure), produce the per-`i`
   gate family from the two general producers above, and call `case_III_arm_realization`.

**Consequence — the "large per-`i` gate construction" fear was MISPLACED.** The
session-#7 note "discharging the ~20 ρ/w/gate hyps at the per-`i` index is
substantial" is correct that the hyps must be *supplied*, but **the supply is two
already-general producer calls** (W6b + discriminator), not bespoke per-`i` linear
algebra. CHAIN-2a is a *wiring* leaf (the standing "dispatch is a deliverable, not
just wiring" caveat applies — it gets its own checklist leaf), not a hard-core
construction. The heaviness session #7 sensed is **real but lives elsewhere**: it
is the `Fin d`-indexed *plumbing* of the per-`i` split through the accessors and
the per-candidate `Φᵢ` heterogeneity (CHAIN-2c), and the ±r chain (CHAIN-2b) — the
genuinely-new `Fin d` infrastructure — **not** the per-`i` certification.

**One flag the dispatch trace surfaces (clause (ii); NOT a blocker, but a
re-scoping the build must honor).** The `d=3` dispatch produces **one** `ρ` (one
W6b call, one redundancy, one GAP-6 consumption) and **one** discriminator pick
`(u, n')`, then `fin_cases u` over the 3 *panels* picks which *arm* (`a`/`b`/`c`-side
line) closes. The general-`d` Lemma 6.13 is structurally **one layer up**: it builds
`d` candidate frameworks `(G,pᵢ)`, reduces each via its **own** `Φᵢ` (eq. 6.59), and
the discriminator picks a full-rank `Mᵢ` among the `d` candidates (eqs. 6.65–6.67).
So the d=3 `fin_cases u`-over-panels and the general-`d` pick-a-candidate-`i` are
**not the same dispatch** — the d=3 three-panel split is the `d=3` collapse of the
`d`-candidate disjunction (at `d=3` the chain `b—v—a—c` has the three candidate
lines through `v`/`a`, masking the candidate≠panel distinction). **CHAIN-2a's
deliverable is the SINGLE-`i` reduction** (the reusable core: "candidate `i`'s `Mᵢ`
full-rank ⟹ `R(G,pᵢ) = D(|V|−1)`, hence `HasGenericFullRankRealization` for that
`i`"), which is exactly one `case_III_arm_realization` re-index at the `cd`-derived
split tuple for `i`. The *family* disjunction over `i` and the discriminator-picks-`i`
glue are **CHAIN-2c**, not 2a. This matches §(l)'s 2a/2b/2c split; the design-pass
**confirms** it and pins 2a's exact deliverable below.

**CHAIN-2a buildable sub-leaves (exact signatures, dependency-ordered).** All
`{k}`-general, `CaseIII/Candidate.lean` (or `CaseIII/Chain.lean` if 2a+2b+2c
together exceed ~1500 LoC). The `n` is the phantom `ChainData` index.

> **Build refinement (2026-06-18, Phase23b).** The W6b *half* of the gate-producer
> landed as `chainData_split_w6b_gates` (`CaseIII/Realization.lean`, flat-tuple, axiom-clean):
> steps 3+4 (lines 376–434, the redundancy + GAP-6 producer), emitting the chain-order
> `hρe₀`/`hρGv`/`hw`/`hwmem` bundle. The **discriminator half (step 5, lines 435–442) is NOT
> single-`i`** — `…homogeneousIncidence_gen` picks an *arbitrary* panel `u`; the gate is about
> `n u`, not candidate-`i`'s normal `na`, and matching `u`↔`i` is the family disjunction. So the
> discriminator half folds into **CHAIN-2c** (the discriminator-picks-`i` glue below), not a 2a-i
> sub-leaf. The "two producer calls" are thus W6b (single-`i`, landed) + discriminator (family-level).

- **CHAIN-2a-i — `chainData_split_arm_gates` (the gate-producer at index `i`; the
  one genuinely-load-bearing 2a sub-leaf).** Re-package the d=3 dispatch's
  gate-production (Realization.lean steps 3+5, lines 376–442) as a per-`i`
  producer, calling the two general producers. Target shape (sketch — the build
  pins the exact `cd`-accessor wiring):
  ```
  theorem PanelHingeFramework.chainData_split_arm_gates {k : ℕ}
      [Finite α] [Finite β] [DecidableEq β]
      {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (i : Fin cd.d) (hi : 0 < (i : ℕ))
      (hsimple : G.Simple) (hk1 : 1 ≤ k) (hn : Graph.bodyBarDim n = screwDim k)
      (hG : G.IsMinimalKDof n 0)
      (hIH : <the all-k IH conjunction at smaller graphs, the dispatch's hIH shape>)
      (hsplitGP : HasGenericFullRankRealization k n
          (G.splitOff (cd.vtx i.castSucc) <pred-nbr> <succ-nbr> cd.e₀)) :
      ∃ (ends : β → α × α) (q : α × Fin (k+2) → ℝ) (n' : Fin (k+2) → ℝ)
        (ρ : Module.Dual ℝ (ScrewSpace k)) (ιb : Type) (_ : Finite ιb)
        (w : ιb → Module.Dual ℝ (α → ScrewSpace k)),
        <the full gate bundle: hLn ∧ hgab ∧ hρgate ∧ hρe₀ ∧ hρGv ∧ hwcard ∧ hw ∧ hwmem
         stated against the cd-derived (v,a,b,e_a,e_b) split tuple>
  ```
  Mechanism: verbatim the dispatch steps — unpack `hsplitGP` (the IH-generic base
  on the `vᵢ`-split `G₁`), call `exists_candidateRow_bottomRows_of_rigidOn` (W6b)
  with `h622lb` from `case_III_nested_rank_lower_all_k`, normalize to chain order
  (the `(a,b)`-vs-`(b,a)` `ρ0`-sign-swap, Realization.lean:404–434), call
  `exists_complementIso_ne_zero_of_homogeneousIncidence_gen` (CHAIN-4d) for the
  discriminator pick, `rw` through `panelSupportExtensor_eq_complementIso_extensor`.
  **This is where the ~20 hyps get discharged — by the two producer calls, not by
  hand.** The `linearIndependent_normals_of_algebraicIndependent` (the `![nᵤ,…]`
  LI feeding the discriminator's `hn`) is the `_triple`/`_gen` form (already lifted,
  OD-7 LEAF-0 / Realization.lean:163) — at the `d`-chain it is the `d` chain-panel
  normals' LI, the discriminator's `hn : LinearIndependent ℝ n` over `Fin (k+1)`.

- **CHAIN-2a-ii — `chainData_split_realization` (the per-`i` reduction core =
  the `case_III_arm_realization` re-index). LANDED 2026-06-18** (`CaseIII/Realization.lean`,
  axiom-clean; the build picked `case_III_arm_realization` directly — no `_M3` relabel — and consumed
  `chainData_split_w6b_gates` for the W6b half + `htrans` for the transversal half, the latter the
  single-`i` slot CHAIN-2c fills). Consumes 2a-i + the interior-split
  accessors; the one-line-ish closer. Target shape (as landed):
  ```
  theorem PanelHingeFramework.chainData_split_realization {k : ℕ}
      [Finite α] [Finite β] [DecidableEq β] [DecidableEq α]
      {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (i : Fin cd.d) (hi : 0 < (i : ℕ))
      <the same induction context as 2a-i>
      (hdef : G.deficiency n = 0) :
      PanelHingeFramework.HasGenericFullRankRealization k n G
  ```
  Mechanism: obtain the gate bundle from `chainData_split_arm_gates` (2a-i),
  read the `(v,a,b,e_a,e_b)` split tuple + the `hvVc`/`haVc`/`hbVc`/`hleG`/
  `hsplitG`/`hends_Gv`/`hne_Gv`/`hVone`/`hVcard` graph facts off the
  interior-split accessors (`isLink_succ_edge`/`isLink_pred_edge`/
  `succ_ne_pred_castSucc`/`deg_two_split` + the `splitOff`/`removeVertex` API the
  dispatch builds at Realization.lean:455–474), and **call
  `case_III_arm_realization` (or `_M3` if the relabel orientation is needed for
  the interior split — the build picks)**. The arm closer does the rest.

**What CHAIN-2a does NOT do** (pushed to 2b/2c, confirming §(l)): the ±r chain
6.66 (CHAIN-2b — relating the `r` across chain indices so "some `Mᵢ` full-rank ⟺
¬∀i r⊥C(Lᵢ)"), and the `Fin d`-family assembly + per-candidate `Φᵢ` heterogeneity
+ the discriminator-picks-`i` glue (CHAIN-2c — consuming the closed CHAIN-1
`ιc`-block augment). CHAIN-2a is **one** candidate's reduction; CHAIN-2c is the
disjunction over the `d` candidates that *chooses* which `i` 2a fires at.

**Clause (i) corrections to the prior pins** (the coordinator findings, verified):
- Finding (1) **confirmed and refined**: both decls carry the gates; the d=3
  caller supplies them — and the supplier is precisely the W6b packaging + the
  CHAIN-4d discriminator + `case_III_nested_rank_lower_all_k`, all three
  **already general-`k`**. "The per-`i` caller must still supply those gates" is
  true; "supply" = two producer calls, the `chainData_split_arm_gates` leaf.
- Finding (2) **confirmed**: the gates arrive from above in d=3 (W6b's
  `hpair`/`hgate`/`hρ0e₀`/`hρ0Gv`/`hw0mem`/`hw`/`hcard` are exactly the dispatch's
  `obtain`s at Realization.lean:388/404/439). The phrasing "themselves produced
  upstream by the CHAIN-4 discriminator + the candidate machinery" is exact.
- Finding (3) **confirmed**: the `ChainData` accessors supply the graph-side
  `(v,a,b,e_a,e_b)` per-`i` tuple; the open work was the per-`i` *linear-algebra*
  gates — which this pass resolves as the `chainData_split_arm_gates` producer-call
  leaf, NOT a from-scratch construction.

**Clause (ii) — no motive/IH change forced; no genuinely-new linear algebra in 2a.**
The per-`i` gates come from existing general-`k` producers; the arm closer is
general-`k`; the `ChainData` accessors are landed. The one honest open item is a
**build-time wiring question, not a math one**: whether the interior-split
realization at index `i` uses `case_III_arm_realization` directly (split body
`vᵢ`, neighbours `vᵢ₋₁`/`vᵢ₊₁`) or its `_M3` relabel form (if the chain
orientation forces the `a↔v` swap), and the exact `h622lb` instantiation at the
`cd`-derived split — both settled by the d=3 dispatch template at build, neither a
carried-hypothesis or motive change. **If 2a-i's producer-call wiring surfaces a
genuine gap** (e.g. the all-`k` IH conjunction `hIH` the dispatch threads does not
restrict to the `vᵢ`-split at the right dof), *that* would be a contract-level item
for the coordinator — flagged, not pre-committed away; expected clean (the IH
shape is the existing 0-dof `case_III_realization_all_k.hdispatch` shape, C.3).

**First buildable = CHAIN-2a-i** (`chainData_split_arm_gates`). **Count: CHAIN-2a
is 2 commits** (2a-i producer + 2a-ii re-index), then CHAIN-2b (1) + CHAIN-2c (1) —
so the §(l) "3–5 commits" for all of CHAIN-2 holds (record landed + 2a-i + 2a-ii +
2b + 2c ≈ 4 build commits remaining).

---

### (n) CHAIN-2b/2c design-pass — the `Fin d` family layer, source-verified against KT eqs. (6.46)–(6.67)

**ROUTE β LOCKED (user-adjudicated 2026-06-18; KT-source-verified — model-exp row 242).** A read-only
recon of KT 6.46–6.67 confirmed the single-base construction (ONE `v₁`-split; the other candidates are
index-shift iso-copies, eq. 6.55 "exactly the same framework") and **refuted route α's per-`i`-splits
premise** — KT does not split `d` times, so there is no per-`i` split to iso-transport. Build 2c on the
single `v₁` base + the uniform `Fin (k+1)` relabel arm (2c-ii). **Blueprint-clarity obligation
(owner-flagged, "absolutely clear"):** route β absorbs KT's explicit isos (6.54–6.56) + ±r chain (6.66)
into the Lean relabel arm, so the `lem:case-III` general-`d` blueprint node's prose must materialize them
— the single-base construction, the relabel isos `ρᵢ`, the single redundancy `r` carried ±-ly across the
`d` panels, and the (6.67) discriminator (tracked in the BlueprintExposition ledger; written as
2c-ii/CHAIN-5 land + at phase-close). The route-decision detail below is retained as the rationale.

**Status:** CHAIN-2b/2c detailed design-pass, docs-only, 2026-06-18, source-verified
against KT 2011 §6.4.2 (the `.refs/` published PDF, eqs. 6.46–6.67 read end-to-end,
pp. 692–698) **and** the landed bodies (clause (i)): the discriminator
`exists_complementIso_ne_zero_of_homogeneousIncidence_gen` (CHAIN-4d,
`Claim612.lean:1462`), its `pbar`/incidence producer `exists_homogeneousIncidence_of_normals_gen`
(`Claim612.lean:470`), the panel bridge `panelSupportExtensor_eq_complementIso_extensor`
(`PanelLayer.lean:331`), the landed `chainData_split_realization` + its `htrans`
slot (`Realization.lean:941`–970), the CHAIN-1 augment
(`Basic.lean:1175`/`1338`), and the **whole** `d=3` dispatch `u`-matching trace
(`Realization.lean:435`–599, all three arms `case_III_arm_realization` /
`_M2` / `_M3`). **This pass surfaces a load-bearing structural correction to the
§(l)/§(m) framing of 2b/2c (clause ii); it pins 2b's *role* and re-scopes 2c, but
flags ONE genuine design decision for the build/coordinator rather than forcing a
confident wrong signature.**

**KT route confirmed (eqs. 6.46–6.67).** Lemma 6.13 considers `d` candidate
frameworks `(G, p₀), …, (G, p_{d−1})` built from **ONE** base realization
`(G₁, q₁)` — the split at `v₁` (eq. 6.46, `G₁ = (V∖{v₁}, E∖{v₀v₁,v₁v₂}∪{v₀v₂})`).
The other candidates `(Gᵢ, qᵢ)` (`2 ≤ i ≤ d−1`) are **isomorphic copies** of
`(G₁, q₁)` via the index-shift iso `ρᵢ` (eqs. 6.54–6.56) — *not* fresh splits. The
matrix bookkeeping (eqs. 6.49–6.64) embeds the **same** `R(G₁, q₁)` as a submatrix
of each `R(G, pᵢ)`, reducing it to a top-left `D×D` block `Mᵢ` + `R(G₁∖(v₀v₂)_{i*}, q₁)`.
Crucially the bottom row of *every* `Mᵢ` is `r = Σⱼ λ(v₀v₂)ⱼ rⱼ(q(v₀v₂))` (eq. 6.52,
the **one** redundancy vector from `M₀`/the redundant row `(v₀v₂)_{i*}`), up to sign
— **this is eq. (6.66), the "±r chain":** the degree-2 closure at each interior `vᵢ`
forces `Σⱼ λ(vᵢvᵢ₊₁)ⱼ rⱼ(q(vᵢvᵢ₊₁)) = ±r`. So `Mᵢ` fails full rank ⟺ `r ⊥ C(Lᵢ)`
(eq. 6.65 footnote), and (eq. 6.67) *none* of `M₀…M_{d−1}` is full rank for any `Lᵢ`
⟺ `r ⊥ ⋃ᵢ (⋃_{Lᵢ⊂Πᵢ} C(Lᵢ))`, whose span is `D`-dimensional by Lemma 2.1 (the
`d+1` points `p₀…p_d`, one per panel-incidence pattern). `r ≠ 0` then can't be ⊥
everything ⇒ some `Mᵢ` is full rank.

**The decisive landed fact (clause i — corrects §(l)/§(m)): the `d=3` dispatch uses
ONE base split, ONE `ρ₀`, ONE W6b call, ONE discriminator call — the candidates are
role-relabels of a single realization, NOT `d` separate splits.** Verified at
`Realization.lean:388` (one `exists_candidateRow_bottomRows_of_rigidOn`), 439–441
(one `exists_complementIso_ne_zero_of_homogeneousIncidence` on `ρ₀`), 495 (`fin_cases u`
over the 3 *panels* `![na, nb, nc]`). All three arms consume the **same** `ρ₀`, the
**same** `q`, the **same** base span `ofNormals (G.removeVertex v) ends₀ q` (the
`v₁`-split `M₀`); `_M2` is the `(ρ := −ρ₀)`/`a↔b` swap, `_M3` the `qρ = q ∘ swap a v`
relabel — both reference `G.removeVertex v` and `ρ₀` (Relabel.lean:838/839). **So
eq. (6.66) is absorbed into the reuse of a single `ρ₀` across candidate roles, not
materialized as a separate `r`-equality lemma.** This is the single biggest
structural fact for 2b/2c, and it diverges from how §(l)/§(m) framed them.

**The structural mismatch this surfaces (the flagged decision).** The **landed**
`chainData_split_realization` (CHAIN-2a-ii) is parameterized by a **per-`i` split
`splitOff (vtx i.castSucc) (vtx i.succ) (vtx (i−1).castSucc) e₀`** (the split at the
interior vertex `vᵢ` *itself*) with a **per-`i` `htrans`** quantified over the `ρ`
that candidate `i`'s OWN W6b call (on that per-`i` split) produces. That is a
faithful standalone "candidate `i`'s `Mᵢ` full-rank ⇒ realization" lemma — but it is
**NOT the shape KT's family disjunction (and the d=3 dispatch) assembles**, because:
- KT/d=3 run W6b **once** on the `v₁` split to get the **one** `r = ρ₀`, then run the
  discriminator **once** with that `r` against **all** `d` panels, picking `u`.
- The landed 2a-ii instead wants, for the chosen candidate `i`, the `ρ` from
  candidate `i`'s **own** split realization, and an `htrans` against *that* `ρ`.
- For the discriminator's single `r = ρ₀` to discharge candidate `u`'s `htrans`,
  either (α) candidate `u`'s per-`i` `ρ` must be shown **equal** to the shared `ρ₀`
  (transported through the eq.-6.54 iso `ρ_u : G₁ ≅ G_u` and the ±r identity 6.66 —
  the genuinely-new transport), **or** (β) the family assembly must be re-shaped to
  run off the **single** `v₁`-split base (matching d=3 / KT exactly), in which case
  the per-`i`-split parameterization of the landed 2a-ii is only used at the **one**
  candidate `i = 1` (the `v₁` split = `M₀`), and the *other* candidates are reached
  by the relabel arms (`_M2`/`_M3`-style), NOT by re-running 2a-ii at a fresh `vᵢ`
  split.

**Verdict on 2b (consumer-grounded, per the rule).** Reading 2c's need first: the
"±r chain" content 2b was pinned to deliver (§(l): "`r` is the same up to sign along
the chain, so `Mᵢ` fails full rank iff `r⊥C(Lᵢ)`") is, in the landed architecture,
**the statement that ONE `ρ₀` (from the `v₁`/`M₀` W6b) serves as the discriminator's
`r` for every candidate panel** — i.e. it is consumed as "the shared-`r` fact" inside
2c, not as a standalone `Mᵢ`-bottom-row lemma. Two honest shapes, decided by which
route (α)/(β) 2c takes:
- Under **route β** (single base, matches d=3): 2b is **not a separate lemma** — the
  ±r chain is discharged by the *same* mechanism the d=3 dispatch uses (one `ρ₀`,
  the role-relabel arms carry the sign via `panelSupportExtensor_swap` /
  `hingeRow_swap`, exactly as `case_III_candidate_dispatch` lines 412–434/507–519).
  CHAIN-2b folds into 2c. **This is the recommended route** (it is a faithful
  numeral/`Fin d`-generalization of the landed, green d=3 dispatch — lowest risk,
  no new transport).
- Under **route α** (per-`i` splits + iso transport): 2b is the genuinely-new lemma
  `chain_redundancy_eq_pm` — for each interior `i`, the candidate-`i` W6b functional
  `ρᵢ` equals `±ρ₁` (the `v₁`-split functional) transported through the eq.-6.54
  index-shift iso. This needs the iso `ρᵢ : Gᵢ ≅ G₁` formalized (eq. 6.54) and the
  rank-transport along it — a real new `Fin d` construction, larger than §(l)'s "1
  commit" estimate.

**Recommendation (route β) + the re-scope it implies for 2a-ii.** Build CHAIN-2c as
a `Fin d`-generalization of `case_III_candidate_dispatch` that runs off the **single**
`v₁`/`M₀` base split, exactly as d=3: one W6b call (`chainData_split_w6b_gates` at the
`v₁` split — *already landed and reusable*), one discriminator call
(`exists_complementIso_ne_zero_of_homogeneousIncidence_gen` with `r := ρ₀`, panel
normals `n := the d chain-candidate panels`, `hn` from the LI of `d` panel normals),
then **`Fin (k+1)`-case** on `u` (replacing `fin_cases u : Fin 3`) into the per-`i`
arm closer. Under this route, the landed `chainData_split_realization` (2a-ii) is
re-used only as the **`i = 1` / `M₀`-candidate arm** (its per-`i` split *is* the
`v₁` split there), and the other candidates reach the arm closer through the
relabel transport — so **2a-ii's per-`i`-split parameterization is sound for the
`M₀` candidate but is NOT the assembly path for the rest of the family.** This is
the honest open item the build must settle; it does not invalidate the landed
2a-ii (it is a correct standalone lemma and the `M₀`-arm of the family), but it
means **2c is not "supply `htrans` to the landed 2a-ii at the discriminator's `u`"**
— it is the `Fin (k+1)`-case dispatch, with the relabel arms carrying the non-`M₀`
candidates as in d=3.

**CHAIN-2c sketched signature (route β; the build pins the exact `cd`-accessor +
relabel wiring).** Replaces / generalizes `case_III_candidate_dispatch`. Lives in
`CaseIII/Realization.lean` (or `CaseIII/Chain.lean` if it + the relabel-`Fin d`
plumbing exceed ~1500 LoC):
```
theorem PanelHingeFramework.chainData_dispatch {k : ℕ}
    [DecidableEq α] [DecidableEq β] [Finite α] [Finite β]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n)
    (hk1 : 1 ≤ k) (hn : Graph.bodyBarDim n = screwDim k)
    (hG : G.IsMinimalKDof n 0) (hV3 : 3 ≤ V(G).ncard) (hSimple : G.Simple)
    (hIH : <the all-k IH conjunction, the chainData_split_realization hIH shape>)
    -- the M₀ base: the v₁-split deficiency-0 fact + its IH-generic realization
    (hdef_G1 : (G.splitOff (cd.vtx 1) (cd.vtx 2) (cd.vtx 0) cd.e₀).deficiency n = 0)
    (hdef : G.deficiency n = 0)
    (hsplitGP : PanelHingeFramework.HasGenericFullRankRealization k n
        (G.splitOff (cd.vtx 1) (cd.vtx 2) (cd.vtx 0) cd.e₀))
    -- the d candidate panel normals are linearly independent (the eq.-6.67 prep;
    -- supplied from the GP base realization's pairwise-LI normals + alg-indep, the
    -- `linearIndependent_normals_of_algebraicIndependent_*` family OD-7 LEAF-0 lifted)
    (hpanelLI : <LinearIndependent ℝ (the Fin (k+1)-family of chain-candidate normals)>) :
    PanelHingeFramework.HasGenericFullRankRealization k n G
```
Mechanism (the `Fin d`-generalization of the d=3 dispatch body):
1. **One** W6b on the `v₁` split: `chainData_split_w6b_gates` (LANDED) → `ρ₀`, `w`,
   the chain-order gate bundle (`hρe₀`/`hρGv`/`hw`/`hwmem`). This is the shared `r`.
2. Build the `d`-panel normal family `n : Fin (k+1) → ℝ^{k+2}` from `q₁` at the
   candidate vertices (KT's `Πᵢ`: `Π₀ = Π(v₀)`, `Πᵢ = Π(vᵢ₊₁)`), `hn := hpanelLI`.
3. **One** discriminator: `exists_homogeneousIncidence_of_normals_gen hn` → `pbar` +
   incidence, then `exists_complementIso_ne_zero_of_homogeneousIncidence_gen` with
   `r := ρ₀` → `(u, n', hpair, hgate)`; `rw [← panelSupportExtensor_eq_complementIso_extensor]`.
   **This is eqs. (6.65)–(6.67) in one shot** (no separate 2b).
4. **`Fin (k+1)`-case on `u`** (the `fin_cases u : Fin 3` generalization, the
   genuinely-new `Fin d` family disjunction — the `u`↔candidate match): for each `u`,
   call the arm closer at candidate `u`'s split tuple read off the `cd` accessors,
   with the relabel/sign transport (the `_M2`/`_M3` pattern) carrying the
   shared `ρ₀` to candidate `u`'s role. The `M₀` candidate (`u` = the `v₁`-split
   index) is the `case_III_arm_realization` arm; the rest are relabel arms.

**The genuinely-new crux (clause ii) and why it is NOT pre-committed.** Step 4 — the
`Fin (k+1)`-case `u`↔candidate match — is the only part with **no d=3 ancestor of the
right shape** (d=3 has a fixed 3-way `fin_cases`, hand-written per arm; the general
`d` needs a *uniform* relabel transporting `ρ₀` to an arbitrary candidate `u`'s role).
The honest open item: **does a uniform `Fin d` relabel arm exist, or does each `u`
need bespoke role-swap plumbing?** The d=3 dispatch hand-writes three arms (M₁ direct,
M₂ sign-swap, M₃ `swap a v` relabel) — there is *not* a single landed lemma that takes
"candidate `u`" and produces the arm. **Building that uniform arm (the relabel iso
`ρ_u` of eq. 6.54 + the rank/functional transport) is the real `Fin d` work**, and it
is what 2c must produce. This is **flagged, not forced**: if the build finds the
uniform relabel needs an iso-transport lemma (route α's `chain_redundancy_eq_pm`
resurfacing inside the arm) or a `ChainData`-iso API (eq. 6.54 as a Lean
`Graph` iso `Gᵤ ≅ G₁`), **that is the genuinely-new construction**, and 2c should be
split (2c = the uniform relabel arm; 2c' = the dispatch). It is **not** a motive/IH
change (the IH is the same all-`k` 0-dof conjunct, confirmed C.6) and **not** a
carried-hypothesis change to the spine — it is new linear-algebra/`Graph`-iso
*infrastructure* below the dispatch. No `sorry`; carried as the standing `h…` idiom
if the build can't close it in one sitting.

**One honest unknown for the coordinator (NOT adjudicated here).** The landed
`chainData_split_realization`'s per-`i`-split shape was authored on the §(m) reading
that 2c "supplies `htrans` to it at the discriminator's `u`." This pass finds that
reading does not assemble (the discriminator's single `r = ρ₀` is the `v₁` functional,
not candidate `u`'s per-split `ρ`). **2a-ii is not wrong** — it is a correct
standalone per-candidate lemma and the `M₀`-arm — but **2c will likely NOT consume it
as the design assumed**; 2c is the single-base dispatch above. Whether to (β) build
2c on the single base and re-use 2a-ii only at `M₀`, or (α) keep the per-`i`-split
2a-ii and add the iso-transport 2b so the discriminator's `r` matches each
candidate's `ρ`, is the **route decision the first 2c build commit settles**. Route
β is recommended (faithful to d=3, lowest risk). **First buildable below assumes β.**

**Buildable-leaf sequence (route β; supersedes §(l)/§(m)'s 2b-then-2c order).**
- **First buildable = CHAIN-2c-i — the `d`-panel-normal LI + the single-discriminator
  pick.** Author the `hpanelLI` producer (the `Fin (k+1)` candidate-normal family is
  LI — from the GP base's pairwise-LI normals + `AlgebraicIndependent ℚ q₁`, the
  OD-7 LEAF-0 `linearIndependent_normals_of_algebraicIndependent_*` family lifted to
  the `d`-normal family) and the one-shot discriminator call producing `(u, n', hgate)`
  off the shared `ρ₀`. §38: graph-free past the `cd`-accessor reads; the discriminator
  is already general-`k`. This is the smallest self-contained brick and is
  **independent of the relabel-arm question** (it is steps 1–3 of `chainData_dispatch`).
- **CHAIN-2c-ii — the uniform `Fin (k+1)` relabel arm (the genuinely-new crux).** The
  step-4 `u`↔candidate dispatch + the relabel transport of `ρ₀` to candidate `u`'s
  role. **This is where the flagged decision is resolved at build**; split off 2b
  (the iso-transport) here if route α is forced.
- **CHAIN-2c-iii — `chainData_dispatch` assembly** (steps 1–4 wired; the `d=3` line a
  `k=2`/`fin_cases`-3 zero-regression wrapper, C.4).
- Then **CHAIN-5** consumes `chainData_dispatch` (the contract's `hdispatch`).

**KT "exactly the same as `d=3`" audit (clause ii).** Faithful for steps 1–3 (one
W6b, one discriminator — verbatim `Fin d` generalization of the landed, green d=3
body). An honest **understatement** for step 4: the d=3 dispatch's three hand-written
arms hide that a *uniform* `Fin d` relabel arm is genuinely-new infrastructure (the
eq.-6.54 iso transport KT states in one line, eqs. 6.54–6.56). No motive/IH change;
no grade-2-only reach-in; the only `d`-dependence past the dispatch is the relabel.

**First buildable for the re-pointed hand-off = CHAIN-2c-i** (`chainData_dispatch`
steps 1–3: the `d`-panel-LI producer + the single-discriminator pick). It is buildable
now (all dependencies landed: `chainData_split_w6b_gates`,
`exists_complementIso_ne_zero_of_homogeneousIncidence_gen`, the `ChainData` accessors,
the LEAF-0 normal-LI family), is the faithful d=3-generalization with the lowest risk,
and defers the genuinely-new crux (the uniform relabel arm) to 2c-ii where the build
adjudicates route α vs β.

---

### (o) CHAIN-2c-ii design-pass — the uniform `Fin d` relabel arm: the iso `ρᵢ` is a genuinely-new construction (FLAGGED)

**Status:** CHAIN-2c-ii detailed design-pass, docs-only, 2026-06-18, source-verified
(clause (i)) against KT 2011 §6.4.2 (the `.refs/` published PDF, eqs. 6.46–6.67 read
**verbatim**, pp. 692–698) **and** the landed bodies: the d=3 relabel arms
`case_III_arm_realization_M2` (`Arms.lean:318`) / `case_III_arm_realization_M3`
(`Relabel.lean:811`), the relabel-transport engine `ofNormals_relabel`
(`Relabel.lean:78`) / `rigidityRows_ofNormals_relabel` (`Relabel.lean:216`) /
`hasGenericFullRankRealization_of_splitOff_relabel` (`Relabel.lean:304`), the M₀ arm
`chainData_split_realization` (`Realization.lean:941`), the discriminator pick
`exists_chainData_discriminator_pick` (`Realization.lean:1130`, 2c-i LANDED), and the
whole d=3 dispatch `u`-match trace (`case_III_candidate_dispatch` lines 435–599, all
three `fin_cases u` arms). **This pass FLAGS a genuinely-new construction (clause (ii)):
KT's index-shift iso `ρᵢ` is a `(i−1)`-cycle, and the landed relabel machinery is
transposition-only — it does NOT generalize uniformly. It does not force a motive/IH or
spine-carried-hypothesis change; it is new infrastructure below the dispatch.**

**KT eqs. 6.54–6.67 confirmed (verbatim).** The `d` candidates `(G,pᵢ)`, `0 ≤ i ≤ d−1`,
all built from ONE base `(G₁,q₁)` = the `v₁`-split (eq. 6.46):
- `M₀`/`(G,p₀)` (eq. 6.47): `L₀ ⊂ Π_{G₁,q₁}(v₀)` placed at `v₀v₁`. The `r` of eq. 6.66
  is `r = Σⱼ λ(v₀v₂)ⱼ rⱼ(q₁(v₀v₂))` — the redundancy of the `(v₀v₂)ᵢ*` row of `R(G₁,q₁)`.
- `M₁`/`(G,p₁)` (eq. 6.48): `L₁ ⊂ Π_{G₁,q₁}(v₂)` placed at `v₁v₂`. Symmetric to `M₀`.
- `Mᵢ`/`(G,pᵢ)` for `2 ≤ i ≤ d−1` (eqs. 6.54–6.59): `Gᵢ = Gᵥᵢ` (split at `vᵢ`),
  `(Gᵢ,qᵢ)` = "exactly the same framework as `(G₁,q₁)`" via the **index-shift iso**
  `ρᵢ : V∖{vᵢ} → V∖{v₁}` (eq. 6.54): `ρᵢ(u) = u` off `{v₁,…,vᵢ}`, `ρᵢ(vⱼ) = vⱼ₊₁` for
  `1 ≤ j ≤ i−1`. The ±r chain (eq. 6.66): `Σⱼ λ(vᵢvᵢ₊₁)ⱼ rⱼ(q(vᵢvᵢ₊₁)) = ±r`, so `Mᵢ`
  full-rank-fails ⟺ `r ⊥ C(Lᵢ)`. The discriminator (eq. 6.67): none full-rank ⟺
  `r ⊥ span ⋃ᵢ(⋃_{Lᵢ⊂Πᵢ} C(Lᵢ))` = `D`-dim by Lemma 2.1 ⇒ `r ≠ 0` ⇒ some `Mᵢ` full.

**The d=3 ↔ general-`d` correspondence (clause i, the decisive structural fact).**
At `d=3` the candidates are `i ∈ {0,1,2}` (`d−1 = 2`); the landed dispatch's three
`fin_cases u` arms map to them as:
- d=3 **M₁** = `case_III_arm_realization` at `(v,a,b) = (v₁,v₀,v₂)` ↔ KT `M₀` (the
  `L₀ ⊂ Π(v₀)` candidate; the **direct** base arm, no relabel).
- d=3 **M₂** = `case_III_arm_realization_M2` (`ρ := −ρ₀`, roles `a↔b`) ↔ KT `M₁` (the
  `L₁ ⊂ Π(v₂)` candidate; the **sign-swap** of the base arm, eqs. 6.53/6.48).
- d=3 **M₃** = `case_III_arm_realization_M3` (relabel at `G−a`, `qρ = q∘swap a v`,
  `ρ := −ρ₀`) ↔ KT `M₂` (the lone `i=2` interior candidate via iso `ρ₂`).

**`ρ₂` at `d=3` is a *transposition* — and that is exactly why M₃'s machinery works.**
KT's `ρ₂(v₁) = v₂` (and identity elsewhere) is the single swap `swap v₁ v₂`. In the
landed M₃ that is `Equiv.swap a v` (the dispatch's `a = v₀`… no: M₃ relabels at `G−a`
swapping the split body `v=v₁` with `a=v₀`'s neighbour role — read directly,
`ofNormals_relabel` sets `ρ := Equiv.swap a v`, a transposition, and `σ = swap e_b e₀ *
swap e₁ e_c`, two edge-transpositions). For `i ≥ 3`, `ρᵢ` is a genuine `(i−1)`-cycle
(`v₁→v₂→…→vᵢ`), **not** a transposition.

**THE VERDICT (clause ii — a genuinely-new construction, FLAGGED, not forced).** The
landed relabel-transport engine — `ofNormals_relabel` / `rigidityRows_ofNormals_relabel`
/ `hasGenericFullRankRealization_of_splitOff_relabel` — does **NOT** generalize
uniformly to KT's `ρᵢ`. The block is structural, not cosmetic, verified in the bodies:
1. **It is hard-wired to `Equiv.swap a v` as an involution.** `ofNormals_relabel`'s
   transport rests on `hρρ : ρ(ρ x) = x` (`Equiv.swap_apply_self`, `Relabel.lean:117`)
   and `hσσ : σ(σ f) = f` (`hσσ_relabel`, two disjoint edge-swaps, `Relabel.lean:41`).
   The rigidity pullback (a motion `S` of the relabelled framework ↦ `S∘ρ` of the base)
   and the link-recording both fire the involution twice. A `(i−1)`-cycle `ρᵢ` is **not**
   an involution for `i ≥ 3`, so this whole transport must be re-derived for a general
   `Equiv.Perm α` — the swap-specific lemmas (`Equiv.swap_apply_left/right/of_ne_of_ne`)
   that the body leans on throughout do not survive.
2. **It transports between exactly TWO single-`splitOff` graphs.**
   `hasGenericFullRankRealization_of_splitOff_relabel` goes
   `HasGenericFullRankRealization (G.splitOff v a b e₀) → … (G.splitOff a v c e₁)` —
   one source split, one target split, related by the one transposition. KT's `Gᵢ`
   (`Gᵥᵢ`, eq. 6.54) is a *different* interior split for each `i`, reached from `G₁`
   (the `v₁`-split) by the cumulative shift `ρᵢ`. There is no landed lemma taking
   "the base `v₁`-split realization" to "the candidate-`i` framework `(G,pᵢ)`" for an
   arbitrary interior `i`; the d=3 M₃ is the bespoke `i=2` instance.
3. **The graph-iso the transport intertwines is `splitOff_isLink_relabel`** — itself
   stated for the `swap a v` / `splitOff a v c e₁` pair (`Relabel.lean:165`). The
   general-`d` analogue (a `Graph` iso `Gᵢ ≅ G₁` realizing eq. 6.54 as a Lean
   `Equiv.Perm`-relabel between two interior splits) is **not in tree**.

So **route α's `chain_redundancy_eq_pm` / iso-transport resurfaces here, inside the
arm** — exactly the contingency §(n) flagged. The honest verdict: 2c-ii is the
genuinely-new content, and it needs a new `Fin d` relabel construction, NOT a numeral
pass over M₂/M₃. The economical d=3 trick (three hand-written arms, the cycle degenerate
to a swap) is precisely what does **not** scale.

**Recommended decomposition (route β still LOCKED; the relabel arm is its `i ≥ 2` tail).**
Build the uniform arm as a `Fin d`-cycle generalization of the relabel engine, then the
dispatch consumes it. Four dependency-ordered buildable leaves:

- **CHAIN-2c-ii-α — the index-shift iso as a Lean `Equiv.Perm α` (KT eq. 6.54).** Author
  `ChainData.shiftPerm` (working name): for an interior index `i` (`2 ≤ i`), the cyclic
  permutation `ρᵢ` of `α` fixing everything off `{vtx 1,…,vtx i}` and sending
  `vtx j ↦ vtx (j+1)` for `1 ≤ j ≤ i−1` (built from the `ChainData.vtx` family via
  `Equiv.Perm` of a finite cycle, e.g. `List.formPerm` on `[vtx 1,…,vtx i]` or an
  iterated `Equiv.swap` composition with the cycle decomposition proved by `decide`-free
  index arithmetic). Plus its action lemmas (`shiftPerm_apply_interior`,
  `shiftPerm_apply_off`, `shiftPerm_vtx_i` showing `vtx i` is the cycle's "removed"
  fixed-image). **§38-clean** (graph-free, pure `Equiv.Perm`/`Fin` arithmetic). This is
  the genuinely-new brick; it is **independent of all rigidity content** and is the
  smallest self-contained piece — the first *new* brick, and (per *First buildable* below)
  the recommended next commit.
- **CHAIN-2c-ii-β — the general-`Equiv.Perm` relabel transport. LANDED 2026-06-18**
  (`PanelHingeFramework.ofNormals_relabel_perm`, `CaseIII/Relabel.lean`, axiom-clean). The
  involution-free generalization of `ofNormals_relabel`. The graph layer is **abstracted into one
  hypothesis** `hiso : Gt.IsLink e x y ↔ Gs.IsLink (σ e) (ρ x) (ρ y)` (the `splitOff_isLink_relabel`
  shape — supplied per candidate by the arm closer, so the heavy interior-split combinatorics stay
  out of the transport) + the forward vertex-region transport `hρst : u ∈ st → ρ u ∈ sr`. The four
  conjuncts (GP / rigidity-pullback via `S∘ρ.symm` / link-recording / AlgIndep) re-derive with
  `ρ.symm`/`σ.symm` where the swap body fired `hρρ`/`hσσ`. The `.symm`-placement is **forced** (the
  d=3 body hides it: with `ρ.symm = ρ` the two `ρ`s cancel): `qρ p := q₀ (ρ p.1, ·)` keeps forward
  `ρ`, but `endsσρ e := (ρ.symm (ends₀ (σ e)).1, …)` flips to `.symm`; FRICTION idiom. Specializes to
  the d=3 `ofNormals_relabel` at the swaps. No further splitting needed (one ~100-line body, a
  mechanical transcription of the swap body — no build-failure iterations).
- **CHAIN-2c-ii — the uniform arm closer `chainData_relabel_arm` (working name).** For an
  interior candidate index `i`, transports the shared base `(G₁,q₁)` realization to the
  candidate-`i` framework via `ρᵢ = shiftPerm i` (2c-ii-α) and the landed perm-transport
  2c-ii-β, then closes `HasGenericFullRankRealization k n G`. **The exact wiring — which two
  splits the graph-iso brick relates, what `σ` is, and whether the arm keeps the shared `ρ₀`
  (M₃-style W9a/W9b/G4d-i transport) or runs a per-`i` W6b off the relabel-transported split
  (the `ofNormals_relabel_perm` route) — was imprecise here and is freshly source-verified in
  §(o′) below.** (This bullet's earlier "`Fin d` generalization of M₃'s body, with
  `shiftPerm`/2c-ii-β where M₃ has `swap a v`/`ofNormals_relabel`" framing was wrong on both
  counts: the landed M₃ does **not** route through `ofNormals_relabel`, and 2c-ii-β is a
  different mechanism — see §(o′).)
- **CHAIN-2c-iii — `chainData_dispatch` assembly.** Steps 1–4 of §(n)'s sketch wired:
  one W6b (`chainData_split_w6b_gates`, LANDED), the LI panel family + one discriminator
  (`exists_chainData_discriminator_pick`, 2c-i LANDED), then **`Fin (k+1)`-case on `u`**
  routing each candidate to its arm — `u = M₀-index` → `chainData_split_realization`
  (the M₀ arm, 2a-ii) or `case_III_arm_realization` directly; `u = M₁-index` → the
  sign-swap arm; all interior `u` → `chainData_relabel_arm` (2c-ii). The d=3 line is a
  `k=2`/length-3 zero-regression wrapper (C.4). **This is the only leaf that consumes 2c-i.**

**Whether the M₀ arm (2a-ii) is reused, or the uniform arm subsumes it (SETTLED here).**
Reused, at exactly one candidate. `chainData_split_realization` (2a-ii) is the **M₀ /
`v₁`-base arm** of the family: its per-`i` split `splitOff (vtx i.castSucc) (vtx i.succ)
(vtx (i−1).castSucc) e₀` at `i = 1` **is** the `v₁`-split (`vtx 1`, `vtx 2`, `vtx 0`),
i.e. KT's `G₁`. So the dispatch's `u`-case calls 2a-ii (or its inner `case_III_arm_realization`)
at the `M₀`-candidate and `chainData_relabel_arm` (2c-ii) at the *interior* candidates
`2 ≤ i ≤ d−1`. The uniform arm does **not** subsume 2a-ii — they are the `i=1` (direct)
and `i ≥ 2` (relabel) tails of the same `fin_cases`. The `htrans` slot of 2a-ii is
filled at the dispatch from the discriminator's `(u, n')` once `u` is matched to `i=1`;
the relabel arm fills the analogous slot from the *same* `(u, n')` transported through
`ρᵢ`. The d=3 M₂ arm (KT `M₁`) is the third leg — at d=3 it is a sign-swap of M₀; at
general `d` it is the `i=1`-`L₁` candidate, also reachable as a relabel-arm instance (or
kept as the dedicated `_M2`-style sign-swap; the build picks the cheaper).

**Assembly coherence (confirmed).** `chainData_dispatch` (2c-iii) closes
`HasGenericFullRankRealization k n G` for the discriminator's picked `u`: every
`fin_cases u` leg lands that conclusion (the M₀ arm, the sign-swap arm, and the uniform
relabel arm all return it), so the `Fin (k+1)`-case is exhaustive and the dispatch's
return type is uniform across legs. CHAIN-5 then consumes `chainData_dispatch` as the
contract's `hdispatch` against the frozen `G.ChainData n` shape (C.3) — unchanged by this
pass (the contract is interface-only; 2c-ii is infrastructure *below* the dispatch).

**Blueprint-clarity obligation (owner-flagged, "absolutely clear") — what the
`lem:case-III` general-`d` node MUST spell out.** Route β absorbs KT's explicit isos +
±r chain into Lean infrastructure, so the blueprint prose must materialize, in order:
(1) the **single `v₁`-base** construction `(G₁,q₁)` (eq. 6.46) and that all `d`
candidates `(G,pᵢ)` are built from it — *not* `d` independent splits; (2) the
**index-shift iso `ρᵢ`** (eq. 6.54, the `(i−1)`-cycle `v₁→…→vᵢ`) and that `(Gᵢ,qᵢ)` is
"exactly the same framework as `(G₁,q₁)`" read through `ρᵢ` (eqs. 6.55–6.56); (3) the
**single redundancy `r`** (eq. 6.52, the `(v₀v₂)ᵢ*` row of `R(G₁,q₁)`) carried **±-ly**
across all `d` panels (eq. 6.66), so `Mᵢ` fails full rank ⟺ `r ⊥ C(Lᵢ)`; (4) the
**eq.-6.67 discriminator** — `r` cannot be ⊥ the `D`-dim span (Lemma 2.1 on the `d+1`
points), so some `Mᵢ` is full rank. The Lean economizes the iso into a `shiftPerm`
relabel arm and the ±r chain into the shared `ρ₀`; **the exposition must not.** Tracked
in BlueprintExposition (the `lem:case-III` general-`d` entry); written as 2c-ii/CHAIN-5
land + at phase-close. The CHAIN-2c-ii-α/β construction (the cycle iso + general-perm
transport, which KT states in two lines) is itself a BlueprintExposition candidate (the
project spells out a step KT compresses).

**The two new bricks LANDED; the arm-closer wiring is re-pinned in §(o′).** The lowest-risk
foundations both landed 2026-06-18: **CHAIN-2c-ii-α** (`ChainData.shiftPerm` + action lemmas,
`Induction/Operations.lean`, `List.formPerm (List.ofFn …)`, axiom-clean) and **CHAIN-2c-ii-β**
(`ofNormals_relabel_perm`, the general-perm framework-transport, `CaseIII/Relabel.lean`,
axiom-clean — see `notes/Phase23b.md` *Decisions made*). The arm closer `chainData_relabel_arm`
(2c-ii) is **next**, but its wiring was under-pinned here (the "M₃'s body" framing); §(o′) below
is the freshly source-verified leaf decomposition that resolves the graph-iso-brick signature
(A), the arm-closer wiring (B), and reconciles this section's imprecision (C). Carry the arm
closer as the standing `h…` idiom if it cannot close in one sitting — never a `sorry`.

**Clause-(ii) summary (this section's, retained).** The uniform `Fin d` relabel arm is **not** a
numeral pass over the landed M₂/M₃: KT's `ρᵢ` is a cycle, the swap-specific transport must be
re-derived for a general `Equiv.Perm` (2c-ii-β did this). This is **new infrastructure**, **not**
a motive/IH change (C.6) and **not** a spine carried-hypothesis change (C.3). Route β stays
LOCKED. **§(o′) sharpens the remaining open item: the arm-closer wiring has a genuine
architectural fork (M₃-style shared-`ρ₀` row-span transport vs. the `ofNormals_relabel_perm`
per-`i`-W6b route), and 2c-ii-β being landed does NOT settle which composes — see §(o′)(B).**

---

### (o′) CHAIN-2c-ii arm-closer wiring — the graph-iso brick signature + the architectural fork (FLAGGED)

**Status:** CHAIN-2c-ii detailed design-pass, docs-only, 2026-06-18, clause-(i) source-verified
against the landed bodies, read end-to-end this pass (file:line cited per claim): the perm-transport
`PanelHingeFramework.ofNormals_relabel_perm` (`CaseIII/Relabel.lean:76`–158), the d=3 graph-iso
template `Graph.splitOff_isLink_relabel` (`Induction/Operations.lean:937`–1115), the d=3
swap-transport `ofNormals_relabel`/`hasGenericFullRankRealization_of_splitOff_relabel`
(`Relabel.lean:190`/`416`), the **landed M₃ arm closer** `case_III_arm_realization_M3`
(`Relabel.lean:923`–1127) and the W9a/W9b/G4d-i bricks it consumes (`Relabel.lean:546`/`653`/`813`),
the arm engine `case_III_arm_realization` (`Arms.lean:72`–101), the dispatch M₃ call site
(`Realization.lean:520`–599), the per-`i` reduction `chainData_split_realization`
(`Realization.lean:941`–1095) + W6b producer `chainData_split_w6b_gates` (`Realization.lean:771`–918),
2c-i `exists_chainData_discriminator_pick` (`Realization.lean:1130`–1147), and the `shiftPerm` action
lemmas (`Operations.lean:1434`–1478). **This pass reconciles §(o)'s imprecise "M₃'s body" framing
(C below) and FLAGS a genuine architectural fork in the arm-closer wiring (B) — 2c-ii-β being landed
does NOT pre-decide which route composes. Route β stays LOCKED; the fork is *within* route β.**

**(C) §(o)'s "M₃'s body" framing is wrong — the landed M₃ does NOT route through `ofNormals_relabel`.**
Verified at `Relabel.lean:961`–1126: `case_III_arm_realization_M3` builds the relabelled seed
`qρ := q ∘ swap a v` **inline** (`:961`) and instantiates `case_III_arm_realization` directly
(`:1010`), filling its three candidate/bottom slots by **row-span transport** of the *shared* base
data, **not** by transporting an `ofNormals` framework:
- the candidate gate `hρe₀`-slot via **G4d-i** `acolumn_mem_hingeRowBlock_of_span_rigidityRows`
  (`Relabel.lean:813`, invoked `:991`),
- the candidate-span `hρGv`-slot via **W9a** `funLeft_dualMap_sub_acolumn_mem_span_rigidityRows`
  (`:546`, invoked `:1085`),
- the bottom `hwmem`-slot via **W9b** `case_III_bottom_relabel` (`:653`, invoked `:1122`).
Crucially the dispatch hands M₃ the **same** `ρ₀`/`w` as M₁/M₂ (`Realization.lean:588`–592 passes
`hρ0e₀ hρ0Gv … (w := w) … hw0mem`, the *base* W6b outputs), negated to `−ρ₀` inside the engine call.
So M₃ keeps the single shared `ρ₀` and transports its row-memberships; it never produces a
candidate-`i` `ofNormals` realization. By contrast `ofNormals_relabel` (`:190`) /
`hasGenericFullRankRealization_of_splitOff_relabel` (`:416`) — and their landed general-perm
generalization `ofNormals_relabel_perm` (2c-ii-β, `:76`) — transport a *whole framework* between two
**`splitOff`** graphs (`G.splitOff v a b e₀ → G.splitOff a v c e₁`). **These are two distinct relabel
mechanisms in the tree; the dispatch's M₃ arm uses the row-span one (W9a/W9b/G4d-i), not the
framework one.** §(o)'s "`Fin d` generalization of M₃'s body, with `shiftPerm`/2c-ii-β where M₃ has
`swap a v`/`ofNormals_relabel`" conflates them on both counts. Corrected in §(o)'s CHAIN-2c-ii bullet.

**(A) The graph-iso brick (the `hiso` supplier) — exact signature, determinable now.** The
`hiso : Gt.IsLink e x y ↔ Gs.IsLink (σ e) (ρ x) (ρ y)` hypothesis of `ofNormals_relabel_perm` (`:78`)
is supplied by a `shiftPerm`-relabel analogue of `splitOff_isLink_relabel` (`Operations.lean:937`).
Its shape is fully determinable from the landed `ChainData` accessors (no build-time discovery
needed):
- **Source `Gs`** = KT's `v₁`-base split = `G.splitOff (cd.vtx 1) (cd.vtx 2) (cd.vtx 0) cd.e₀` (the
  `i=1` instance of 2a-ii's per-`i` split, contract C.3/C.4 verified). **Arg order matches the landed
  2a-ii body verbatim** (`v=vtx 1, a=vtx 2, b=vtx 0`; `Realization.lean:951`); `splitOff` is
  **`a,b`-symmetric** (its `e₀`-clause is `(x=a∧y=b)∨(x=b∧y=a)`, `Operations.lean:583`–584), so the
  new (v₀v₂)-edge endpoints are immaterial *to the graph* — but state the brick in the landed
  `(succ, pred)` order so it composes with 2a-ii without an intervening `a,b`-symmetry rewrite.
- **Target `Gt`** = the candidate-`i` interior split = `G.splitOff (cd.vtx i.castSucc) (cd.vtx i.succ)
  (cd.vtx (i−1).castSucc) cd.e₀` — the split at the interior vertex `vtx i`, exactly the per-`i`
  split `chainData_split_realization` (2a-ii) names (`Realization.lean:951`), using the **same** fresh
  edge `cd.e₀` as `Gs` (2a-ii reuses `cd.e₀` for every `i`; there is no per-`i` primed edge).
- **`ρ`** = `cd.shiftPerm i` (2c-ii-α, `Operations.lean:1434`); its action is pinned by
  `shiftPerm_apply_interior` (`vtx j ↦ vtx (j+1)`, `:1451`), `shiftPerm_vtx_top` (`vtx i ↦ vtx 1`,
  `:1465`), `shiftPerm_apply_vtx_off` (fixes `vtx 0` and the tail, `:1444`). This is the `(i−1)`-cycle
  `v₁→v₂→⋯→vᵢ→v₁` carrying the candidate split back to the base split.
- **`σ`** = an edge permutation analogous to `splitOff_isLink_relabel`'s
  `swap e_b e₀ * swap e₁ e_c` (`Operations.lean:948`): it must map the candidate split's
  short-circuit + chain edges to the base split's, edge-by-edge along the cycle. The exact factor
  list is a build detail (the `Fin d`-indexed cycle's edge action), but the **shape** is determined:
  a product of transpositions swapping each `cd.edge j`/`cd.e₀` pair the cycle moves.
- **Hypotheses:** mirror `splitOff_isLink_relabel`'s — the chain links `cd.isLink_*_edge`, the
  distinctness `vtx_inj`/`edge_inj`/`pred_edge_ne`, the interior degree-2 closures `cd.deg_two_split`
  at each cycle index, and `cd.e₀_fresh`. All are landed accessors.
- **Home:** `Induction/Operations.lean`, beside `splitOff_isLink_relabel` and `shiftPerm` (graph-side,
  `DecidableEq α`/`DecidableEq β`). **Determinable now — a real lemma a build can target.** The one
  honest caveat: `splitOff_isLink_relabel`'s ~150-line exhaustive case analysis is for a *single*
  transposition between *two* splits; the cycle version case-analyzes a `Fin i`-indexed family of
  edge/vertex moves, so it is genuinely longer (a build may want to prove it by induction on the
  cycle length rather than a flat `splitOff_isLink` expansion). The *signature* is fixed; the *proof
  shape* (flat vs. inductive) is build-discovered.

**(B) The arm-closer wiring — a genuine architectural fork, NOT settled by 2c-ii-β landing.** The
hand-off points at "instantiate `ofNormals_relabel_perm` at `ρ := cd.shiftPerm i`, feed
`case_III_arm_realization`." Reading the two consumers end-to-end, that composition is **not
mechanical** — there are two architectures, and which one closes is the genuinely-unresolved item:

- **Route A (the `ofNormals_relabel_perm` route the hand-off names).** Build a perm-analogue of
  `hasGenericFullRankRealization_of_splitOff_relabel` (`:416`) off 2c-ii-β: transport the base
  `HasGenericFullRankRealization k n Gs` to `HasGenericFullRankRealization k n Gt` via
  `shiftPerm i` + the (A)-brick. Then feed *that* as the `hsplitGP` of `chainData_split_realization`
  (2a-ii) at candidate `i`. **The hidden cost:** 2a-ii runs its **own** `chainData_split_w6b_gates`
  call on `Gt` (`Realization.lean:1006`), producing candidate `i`'s **own** functional `ρᵢ` and bottom
  family `w` — **not** the discriminator's shared `ρ₀`. For the single-discriminator argument (2c-i
  returns one shared `ρ₀` and an arbitrary panel `u`) to discharge candidate `i`'s `htrans` slot
  (`Realization.lean:961`–970, quantified over candidate `i`'s *own* `ρ`), one must show the per-`i`
  W6b `ρᵢ` **equals** the `shiftPerm`-image of `ρ₀` — KT's eq. (6.66) ±r chain. **This is the
  genuinely-new fact route A needs, and it is NOT supplied by 2c-ii-β** (which transports the
  *framework*, not the *W6b candidate functional*). It is §(n)'s route-α `chain_redundancy_eq_pm`
  resurfacing. If it does not hold definitionally, route A does not close as the hand-off assumes.

- **Route B (the M₃-style shared-`ρ₀` row-span route).** Generalize the dispatch's actual M₃ wiring:
  keep the shared `ρ₀`/`w`, build the candidate framework on a `removeVertex`/`splitOff` graph with
  the relabelled selector `ends`/`qρ = q ∘ shiftPerm i`, and transport the three slots
  (`hρe₀`/`hρGv`/`hwmem`) by `shiftPerm`-analogues of **G4d-i/W9a/W9b**, then call
  `case_III_arm_realization` with `±ρ₀`/`w` exactly as M₃ does. **The hidden cost:** W9a
  (`:546`) and W9b (`:653`) are **hard-wired to `Equiv.swap a v` as a single transposition of a
  degree-2 body with its lone surviving neighbour** — the load-bearing trick is the *a-column
  subtraction* `hingeRow v c (φ ∘ single a)` cancelling the `e_c`-content (`Relabel.lean:592`–626),
  which works *because* `a` is degree-2 with exactly one surviving edge `e_c = ac`. The BlueprintExposition
  `lem:case-III-claim612-eq644` entry confirms the mechanism is "precisely *that `a` is degree-2*."
  A `(i−1)`-cycle moves a *chain* of degree-2 bodies, so the single-column-subtraction trick does
  **not** transcribe; the row-span transport must be re-derived for the cycle (an a-column subtraction
  *per cycle step*, or a different inductive transport).

**Verdict (flag-don't-force) — superseded by the §(o″) adjudication below.** The fork was left open
in this pass pending (1) a source-verify of *whether* route A's eq.-(6.66) identity is even provable
and (2) a KT-structure cross-check. Both are now done in **§(o″)** (2026-06-19): **route A is
REJECTED (unprovable as stated); route B is the verdict.** This block's framing — that the first
build commit should land the (A) graph-iso brick, route-independent, then adjudicate — was correct
and is now discharged: the (A) brick LANDED (graphiso COMPLETE, `splitOff_isLink_shiftRelabel_iff`),
and §(o″) is the adjudication it deferred. The leaf decomposition (graphiso → transport → arm) below
stands; only the *transport* leaf's route is now decided (B).

**2c-ii is three leaves.** (1) **2c-ii-graphiso** — `splitOff_isLink_shiftRelabel_iff` (A), **LANDED**
2026-06-19, route-independent. (2) **2c-ii-transport** — the cycle-generalized W9a/W9b row-span
transport (**route B**, §(o″)). (3) **2c-ii-arm** — `chainData_relabel_arm`, wiring (1)+(2) into
`case_III_arm_realization` at the relabelled roles. The d=3 M₃ instance is route B at the degenerate
`i=2` (cycle = single transposition `swap a v`); the general-`d` arm follows B (faithful to *both*
the landed dispatch and KT's text — see §(o″)).

**(C, completing the reconciliation) 2c-iii / dispatch unchanged.** `chainData_dispatch` (2c-iii) and
`chainData_split_realization` (2a-ii, the `M₀` arm) are **unaffected** by which route 2c-ii takes —
both consume the arm closer's `HasGenericFullRankRealization k n G` conclusion, and 2c-i's
discriminator returns the same `(u, n')` regardless. `chainData_dispatch` still consumes the result
unchanged; CHAIN-5's `hdispatch` contract (C.3, frozen) is untouched (2c-ii is infrastructure below
the dispatch). The §(o)/§(n) blueprint-clarity obligation (materialize KT's isos 6.54–6.56 + the ±r
chain 6.66 in the `lem:case-III` general-`d` prose) is **reinforced** by this pass: route A's
eq.-(6.66) identity / route B's cycle-degree-2 mechanism is exactly the step KT compresses, and the
BlueprintExposition ledger's `lem:case-III-claim612-eq644` entry already names it at d=3 — the
general-`d` write-up extends it to the cycle.

---

### (o″) CHAIN-2c-ii-transport route adjudication — VERDICT: route B, route A REJECTED (FLAGGED for commit-count)

**Status:** the §(o′)(B) fork adjudication, docs-only, 2026-06-19. Clause-(i) source-verified against
the landed bodies (file:line per claim) **and** clause-(2) cross-checked against KT 2011 §6.4.2,
eqs. (6.60)–(6.67), read end-to-end from the `.refs/` PDF (pdf pp. 50–52 = paper pp. 696–698). The
graph-iso brick (A) **LANDED** since §(o′) (`splitOff_isLink_shiftRelabel_iff`, `Operations.lean:2122`,
the `(ρ,σ) = (shiftPerm i.castSucc, shiftEdgePerm i)` intertwiner of the candidate-`i` split with the
`i:=1` base split). What remains is **2c-ii-transport**, and the §(o′)(B) fork is now decided.

**VERDICT: route B (the M₃-style shared-`ρ₀` row-span transport). Route A is REJECTED — its
load-bearing eq.-(6.66) identity is unprovable as stated.**

**(1) Route A is unprovable: `ρ` is a choice-on-choice existential, not a function of the framework.**
Traced to source: the per-`i` W6b candidate functional `ρ` that route A would have to match to `ρ₀`
is produced by `chainData_split_w6b_gates` (`Realization.lean:1005`) calling
`exists_candidateRow_bottomRows_of_rigidOn` (`Candidate.lean:390`), which **extracts `ρ` via
`Submodule.mem_map`** (`Candidate.lean:434`–435, `obtain ⟨ρ, hρ_blk, hρ⟩ := hrhat_Eb`) as *some*
preimage of `r̂ = ∑ⱼ λⱼ rⱼ` under the `screwDiff`-dualMap. And `r̂` itself is built from the **triple
existential** `(r, lam, i*)` of `exists_redundant_panelRow_ab_lam_of_rigidOn` (`Candidate.lean:309`–332,
`∃ r lam i, …`) — the independent `ab`-rows `r`, the unit-normalized coefficients `lam`, and the
redundant index `i*` are all `Classical.choice` picks. So `ρ` is choice-on-choice with **no canonical
or functional relationship** to `ρ₀` (the base split's independently-chosen pick). The eq.-(6.66)
identity route A needs (`ρᵢ = shiftPerm`-image-of-`ρ₀`) is therefore **not a provable equation** — it
equates two independent existential witnesses. Route A "feed the relabel-transported split as 2a-ii's
`hsplitGP`, then discharge `htrans`" cannot close, because 2a-ii (`chainData_split_realization`,
`Realization.lean:941`) runs its **own** W6b on `Gt` (`:1005`) producing candidate `i`'s own `ρᵢ`, and
the `htrans` slot (`:961`–970) is quantified over **that** `ρᵢ`, not `ρ₀` — there is no bridge.

**(2) KT does route B: ONE redundancy `r`, the ±r chain (6.66), no per-candidate W6b.** Verified at KT
p. 698: `r := ∑ⱼ λ_{(v₀v₂)j} rⱼ(q(v₀v₂)) ∈ ℝ^D` is defined **once** off the single base `(G₁,q₁)`.
KT then writes (6.66): *"due to the fact that `vᵢ` is a vertex of degree two in `G₁` for all
`2 ≤ i ≤ d−1`, we can easily show the following fact in a manner similar to the previous lemma (cf.
(6.44)): `∑ⱼ λ_{(vᵢvᵢ₊₁)j} rⱼ(q(vᵢvᵢ₊₁)) = ±r`"*, and concludes "`Mᵢ` does not have full rank iff
`r` is in the orthogonal complement of `C(Lᵢ)`" — for the **single shared `r`**, tested against every
candidate's panel-meet `C(Lᵢ)`. The discriminator (6.67) then asks for one `r`-non-annihilated line
across `⋃ᵢ ⋃_{Lᵢ⊂Πᵢ} C(Lᵢ)`. KT runs **no** per-candidate redundancy extraction — the `±r` chain
recycles the one `r`. **KT eq. (6.66) IS route B's content** (the degree-2/a-column fact of (6.44),
chain-generalized), not a separate "route-A identity." This also matches the landed d=3 dispatch
(`case_III_candidate_dispatch`): one `ρ0` produced at `Realization.lean:404`, fed unchanged (negated
to `−ρ0` inside M₃) to all three arms (`:501`/`:513`/`:588`–592); M₃ relabels the *seed*
`qρ = q ∘ swap a v` (`:541`), never the functional. So route B is faithful to **both** KT and the tree.

**(3) Route B's genuinely-new piece + the leaf decomposition. FLAG: this is a real construction, ~2–4
commits, not a numeral pass.** Route B keeps the shared `ρ₀` (the §(o′)(B) "shared-`ρ₀`" arm) and
transports the candidate `hρGv` slot by the **cycle-generalization of W9a**
(`funLeft_dualMap_sub_acolumn_mem_span_rigidityRows`, `Relabel.lean:546`) + **G4d-i**
(`acolumn_mem_hingeRowBlock_of_span_rigidityRows`, `:813`) and the bottom `hwmem` slot by the
cycle-generalization of **W9b** (`case_III_bottom_relabel`, `:653`). The d=3 W9a trick
(`Relabel.lean:592`–626) is a **single a-column subtraction** `hingeRow v c (φ ∘ single a)` that
cancels the lone surviving edge `e_c` of the *single* degree-2 body `a` (verified: the three-case
split `x=a` / `y=a` / off forces `f = e_c` via `hdeg2`, and the cancellation is exactly KT's eq.
(6.44) "`a` is degree 2"). KT's `ρᵢ` is the `(i−1)`-cycle `v₁→⋯→vᵢ→v₁`, moving a **chain of `i−1`
degree-2 bodies** `v₁,…,v_{i−1}` (KT (6.66) ranges `2≤i≤d−1`). So the single-column subtraction must
become a **per-cycle-step (or inductive) a-column subtraction** — one stripped column per moved
degree-2 body. This is genuinely-new infrastructure; honest commit estimate **2–4 build commits** (a
cycle-W9a, a cycle-W9b, plus the arm closer). The cleanest shape is likely an **induction on cycle
length**: each step is one W9a-style transposition transport of an adjacent degree-2 body (the
landed `shiftPerm` already factors as a `List.formPerm`, and the graphiso brick already proves the
per-step link correspondence), composing `i−1` single-body subtractions. **No motive/IH change (C.6),
no spine carried-hypothesis change (C.3)** — route B is infrastructure below the dispatch, exactly as
M₃ is at d=3; the shared `ρ₀` is `chainData_split_w6b_gates`'s output reused, the same data flow as
the landed dispatch (one W6b, three arms).

**Pinned leaf signatures — CORRECTED 2026-06-19 to the LANDED T-W9a shape (the prior pin was STALE).**
The original pin here named T-W9a as a single lemma
`ChainData.funLeft_shiftPerm_dualMap_sub_acolumns_mem_span_rigidityRows` ("mirror W9a's
Fv/Fva/htrans/hdeg2 shape, one body per cycle index"). **That lemma was never built and does not
exist** — T-W9a landed (commits c0421c6, c6d8087) through a different, more granular route. The dead
pin is removed. The LANDED T-W9a shape (all axiom-clean, in `Relabel.lean` + `Operations.lean`):
```
-- The abstract wstep fold core (graph-free over BodyHingeFramework, Relabel.lean:750):
theorem BodyHingeFramework.wstep_foldr_mem_span_rigidityRows (F : ℕ → BodyHingeFramework k α β)
    (ec : ℕ → β) (bodies : List (α × α × α)) (hstep : ∀ s, (hs : s < bodies.length) → … six
      per-step conjuncts: (c≠a ∧ c≠v) ∧ link e_c a c ∧ hdeg2 ∧ hdeg2r ∧ hnov ∧ htrans, all at F(s+1))
    {φ} (hφ : φ ∈ span (F bodies.length).rigidityRows) :
    (bodies.foldr (fun b T => (wstep b.1 b.2.1 b.2.2).comp T) id) φ ∈ span (F 0).rigidityRows
-- where wstep v a c := (funLeft (swap a v)).dualMap − (screwDiff v c).dualMap ∘ (single a).dualMap
--   (the single-step W9a transport: relabel MINUS the a-column subtraction).
-- The removeVertex framework chain (Relabel.lean:833, NOT splits — endpoints are removeVertex):
def ChainData.shiftBodyFramework (cd) {s} (hs : s+1 < cd.d+1) ends q : BodyHingeFramework k α β :=
  (ofNormals (cd.shiftBodyGraph hs) ends q).toBodyHinge          -- shiftBodyGraph s := G − vₛ₊₁
theorem ChainData.shiftBodyFramework_htrans … -- the per-step hstep conjunct (le_refl block-agree)
-- The SPAN-ONLY membership half (Relabel.lean:940, the genuinely-new crux):
theorem ChainData.shiftBodyList_foldr_mem_span_rigidityRows (cd) (i : Fin (cd.d+1)) (hi : 2 ≤ ↑i)
    ends q {φ} (hφ : φ ∈ span (cd.shiftBodyFramework (s := ↑i − 1) _ ends q).rigidityRows) :
    ((cd.shiftBodyList i).foldr (fun b T => (wstep b.1 b.2.1 b.2.2).comp T) id) φ
      ∈ span (cd.shiftBodyFramework (s := 0) _ ends q).rigidityRows
-- Transports span (G − vᵢ)-rows → span (G − v₁)-rows for 2 ≤ i. SPAN-ONLY: the funLeft-relabel
-- rewrite (wstep_foldr_funLeft_eq + shiftPerm_eq_prod_map_swap_shiftBodyList, both LANDED) is
-- DEFERRED — applied at the arm closer, not here.
```
The next leaf is **T-W9b** (the cycle bottom-tag transport), decomposed below. The arm closer
(2c-ii-arm), unchanged in shape from §(o′):
```
theorem PanelHingeFramework.chainData_relabel_arm
    [DecidableEq β] [Finite α] [Finite β]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (i : Fin cd.d) (hi : 1 < (i : ℕ))
    (hk1 : 1 ≤ k) (hn : Graph.bodyBarDim n = screwDim k) … (the G/IH/deficiency context) →
    -- the shared base W6b bundle (ρ₀, w) from chainData_split_w6b_gates at the i:=1 base split:
    (hρ0… : ρ₀ ≠ 0 ∧ ρ₀ ⊥ C(base ab) ∧ hingeRow … ρ₀ ∈ span (base-rows) ∧ w-bundle) →
    -- the transversal gate from 2c-i's discriminator at this candidate i (the htrans contribution):
    (htrans : ρ₀ (panelSupportExtensor (q(vtx i.succ,·)) n') ≠ 0 ∧ LI ![q(vtx i.succ,·), n']) →
    PanelHingeFramework.HasGenericFullRankRealization k n G
-- d=3 M₃ (case_III_arm_realization_M3, Relabel.lean:923) is the i=2 instance (cycle = swap a v).
```
**Decomposition of 2c-ii-transport + 2c-ii-arm into buildable leaves (status 2026-06-19):**
**(T-W9a) the cycle a-column span transport — LANDED** (the genuinely-new piece; span-only, see the
LANDED-shape pin above + the addenda below) → **(T-W9b) the cycle bottom-tag transport — NEXT
BUILDABLE** (decomposed in the *T-W9b decomposition* addendum below) → (2c-ii-arm)
`chainData_relabel_arm` instantiating `case_III_arm_realization` at the relabelled roles
`(v,a,b) := (vtx i.succ, vtx (i−1).castSucc, vtx i.castSucc)` with `−ρ₀`, the cycle-transported
`hρGv` (T-W9a span + its deferred relabel bridge) / `hwmem` (T-W9b), feeding 2c-i's `htrans`. Then
2c-iii (`chainData_dispatch`) `fin_cases u`-es over the discriminator's panel, `i=1`/`M₀` arm = 2a-ii
(landed `chainData_split_realization`), interior `2≤i≤d−1` arm = `chainData_relabel_arm`.

**Caveat — RESOLVED.** The §(o′)-flagged telescoping risk (whether the per-step a-column subtractions
compose cleanly along the cycle) is **settled**: the cycle-W9a a-column telescoping *is* clean, proved
in the fold core `wstep_foldr_mem_span_rigidityRows` (the binary
`funLeft_dualMap_sub_acolumn_comp_mem_span_rigidityRows` confirms the two-body compose; the `List`
induction lifts it). What actually cost the extra leaf was the *graph correspondence* — the fold core's
`hstep` needs an **un-relabelled** per-step link inclusion between consecutive *intermediate*
frameworks, supplied by the NEW (T-W9a-chain) `shiftBodyFramework` removeVertex chain, not by the
whole-cycle endpoint graphiso. That chain is built; T-W9a is COMPLETE. **Route B remains NOT a
motive/IH or spine-carry change** (C.3/C.6 unmoved). The remaining honest unknown is now T-W9b's
commit-count (~1–2, per the *T-W9b decomposition* addendum below).

**Coordinator addendum (2026-06-19) — the route-A rejection orphans `ofNormals_relabel_perm`
(2c-ii-β, row 246).** The §(o″) decomposition (T-W9a → T-W9b → `chainData_relabel_arm`) is M₃-style
row-span transport; the landed d=3 M₃ (`case_III_arm_realization_M3`) uses **no** `ofNormals_relabel`,
so the cycle-generalized route B (very likely) uses **no** `ofNormals_relabel_perm` either. Grep
confirms `ofNormals_relabel_perm` currently has **zero call sites** — it was built (row 246) for the
now-rejected route-A whole-framework transport. It is the framework-transport `hiso`-consumer; the
landed graph-iso `splitOff_isLink_shiftRelabel_iff` (rows 248–250) is **NOT** orphaned — route B's
T-W9a is stated *against* it (the per-step link correspondence), so that work stands. **Action: at the
2c-ii-arm build, confirm `chainData_relabel_arm` does not use `ofNormals_relabel_perm` (it should not,
mirroring M₃), then delete `ofNormals_relabel_perm` + reword its two Operations.lean docstring
references** (or, if the arm finds a GP/algindep use for it, keep + re-pin). Tracked as a checklist
item; do not delete pre-emptively (1% the arm wants its GP/algindep conjuncts for the relabelled seed).

**Coordinator addendum (2026-06-19) — T-W9a needs a NEW 7th prerequisite: the partially-shifted
intermediate-framework chain (read-only recon, source-verified).** After 6 consecutive build commits
front-loaded the T-W9a *linear-algebra* prerequisites (fold core `wstep_foldr_mem_span_rigidityRows`,
body list `shiftBodyList`, perm bridge `shiftPerm_eq_prod_map_swap_shiftBodyList`, its linear-map
companion `wstep_foldr_funLeft_eq`), a decomposition recon found the membership half is **not** the
"3-step assembly with all prerequisites landed" the build hand-offs claimed. The gap (verified against
source): the fold core's per-step `hstep` (`Relabel.lean:759-760`) demands an **un-relabelled** link
inclusion `(F (s+1)).graph.IsLink f x y → (F s).graph.IsLink f x y` between *consecutive intermediate*
frameworks `F : ℕ → BodyHingeFramework`, but the only landed graph-iso `splitOff_isLink_shiftRelabel_iff`
(`Operations.lean:2246`) is a **whole-cycle, fully-relabelled** intertwiner between the two *endpoint*
splits (candidate-`i` ↔ base, applying the entire `shiftPerm i.castSucc` to both endpoints). Wrong
shape. The landed d=3 M₃ discharges its W9a `htrans` from `Fv/Fva = ofNormals (removeVertex v/a)`
agreeing off `{a,v}` (`Relabel.lean:1232-1255`) — an un-relabelled inclusion, the swap living only on
the `funLeft` side — confirming `F s` must be a chain of **un-relabelled** partially-shifted splits, not
endpoint relabels. **This corrects line 2573 above** ("T-W9a is stated against `splitOff_isLink_shiftRelabel_iff`
as the per-step link correspondence" — it is the whole-cycle iff, NOT the per-step correspondence) and
the telescoping caveat (2558-2565): the a-column telescoping IS clean (settled by the fold core); the
unresolved risk is the **graph correspondence**, not the algebra.

Corrected decomposition (route B unchanged, no motive/IH/contract change): **(T-W9a-chain)** [NEW, the
missing prerequisite] the intermediate-framework chain `F = ofNormals ∘ shiftBodyGraph` with
`shiftBodyGraph s := G − vₛ₊₁` + its per-step un-relabelled link correspondence + the per-step
degree-2/`cₛ`-link/off-`vₛ` conjuncts (from `deg_two`/`removeVertex` once `F s` is pinned) — ~190-line
difficulty class (an induction on cycle length over the removeVertex chain); re-uses the d=3 `M₃`
`removeVertex`-agreement reasoning → **(T-W9a)** the membership half proper [feed `shiftBodyList i` +
`F` into the fold core, rewrite the relabel via `wstep_foldr_funLeft_eq` + the perm bridge].
**Endpoint correction (2026-06-19, at the graph-layer build):** the chain/membership endpoints are the
**removeVertex frameworks** `F (i−1) = ofNormals (G − vᵢ)`, `F 0 = ofNormals (G − v₁)`, mirroring the
single-step W9a's `Fv`/`Fva` (`Relabel.lean:546-561`, "the `G − a` framework"); the recon's "endpoints
= candidate-`i`/base splits" framing above was imprecise — **the splits enter only at the arm closer
`chainData_relabel_arm`** (via the W6b/W9b/seed composition, as in d=3 `M₃`), NOT as the W9a chain's
endpoints. So T-W9a transports `span (ofNormals (G − vᵢ) rows) → span (ofNormals (G − v₁) rows)`.
**Estimate ≥2 build commits for the membership half (several sessions).** `splitOff_isLink_shiftRelabel_iff`
(the whole-cycle graphiso) is consumed at the **arm**, not the per-step chain.

**T-W9a-chain `G`-substrate LANDED 2026-06-19** (`Operations.lean`, axiom-clean). The first leaf of
(T-W9a-chain) — the per-moved-body `G`-level geometry the chain's `hstep` reads — is built: the
`ChainData.shiftBody_{isLink_succ_edge, isLink_pred_edge, deg_two, pred_ne, pred_ne_succ, ne_succ}`
accessor block (for cycle step `s`, `s + 1 < i`: the body `vₛ₊₁`'s successor edge `edge (s+1)`→`vₛ₊₂`,
predecessor edge `edge s`→`vₛ`, the `G`-degree-2 closure at the body, and the three triple-vertex
distinctnesses, in the `(v,a,c) = (vₛ₊₂, vₛ₊₁, vₛ)` shape the fold core's `hstep` consumes) + the
namespace `vtx_ne` helper (the graphiso bricks' local `hvtx_ne_of` have, hoisted). These are pure
`ChainData.{link, deg_two, vtx_inj}` reads — no framework, no relabel — supplying the per-step
degree-2/`cₛ`-link/off-`vₛ` conjuncts of the chain `hstep`.

**T-W9a-chain intermediate-graph layer LANDED 2026-06-19** (`Operations.lean`, axiom-clean). The graph
layer the framework chain lifts: the intermediate graph `ChainData.shiftBodyGraph s := G − vₛ₊₁`
(indexed by the minimal chain-vertex bound `s + 1 < cd.d + 1`, decoupled from the cycle top `i` — it
is a graph op, FRICTION) and the per-step `G`-level link correspondence between consecutive graphs
`shiftBodyGraph (s+1) = G − vₛ₊₂` and `shiftBodyGraph s = G − vₛ₊₁` (`(v,a,c) = (vₛ₊₂, vₛ₊₁, vₛ)`):
`shiftBodyGraph_isLink_pred_edge` (the surviving `e_c = edge s` link `a→c`), `shiftBodyGraph_deg_two`
(+ `_right`) (the body `a` at degree 2 in `G − v`, its successor edge `edge (s+1)` cut by the removal,
via `IsLink.right_unique`), `shiftBodyGraph_off_succ` (every link of `G − v` avoids `v`), and the
un-relabelled inclusion `shiftBodyGraph_isLink_of_off_body` (a link of `G − v` off the body `a` is a
link of `G − a` — the `htrans` graph shape `wstep_foldr_mem_span_rigidityRows`'s `hstep` consumes).
This mirrors the d=3 `M₃` arm's single step `Fv/Fva = ofNormals (G − v)/(G − a)`
(`case_III_arm_realization_M3`'s `htrans`, off `removeVertex_isLink`) at the cycle level.

**T-W9a-chain framework layer LANDED 2026-06-19** (`CaseIII/Relabel.lean`, axiom-clean; T-W9a-chain
COMPLETE). The chain `Graph.ChainData.shiftBodyFramework hs ends q := (ofNormals (shiftBodyGraph hs)
ends q).toBodyHinge` lifts the graph layer through `ofNormals`/`toBodyHinge` with the selector `ends`
and seed `q` *fixed across the chain* (only the graph shrinks). Its per-step `htrans`
`shiftBodyFramework_htrans` is the fold core's `hstep` second conjunct: the graph half is the landed
`shiftBodyGraph_isLink_of_off_body` (read through the `shiftBodyFramework_graph` simp lemma), and the
`hingeRowBlock`-agreement half is `le_refl` — the two frameworks' supporting extensors
`panelSupportExtensor (q((ends f).1)) (q((ends f).2))` coincide (`shiftBodyFramework_supportExtensor`,
`s`-independent), so the blocks are *equal*. This is **simpler** than the d=3 `M₃` `htrans`, which
changes the seed/selector (`q→qρ`, `ends→ends₃`) and so needs an off-`{e_a,e_b,e_c}` extensor-coincidence
argument; here no edge-exclusion is needed. Declared with the `_root_.Graph.ChainData.` prefix (the
in-`CombinatorialRigidity.Molecular`-namespace declaration trap, TACTICS-QUIRKS §56).

**T-W9a membership half LANDED 2026-06-19** (`CaseIII/Relabel.lean`, axiom-clean; the genuinely-new
crux of route B). `Graph.ChainData.shiftBodyList_foldr_mem_span_rigidityRows`: the iterated W9a
transport over the moved-body list carries the source span `span (G − vᵢ)`-rows
(`shiftBodyFramework (i−1)`, top of chain) down to the target `span (G − v₁)`-rows
(`shiftBodyFramework 0`, bottom), for any `i : Fin (cd.d+1)` with `2 ≤ i`. The proof feeds the fold
core `wstep_foldr_mem_span_rigidityRows` all six per-step `hstep` conjuncts off the landed
graph-layer accessors (`shiftBodyGraph_isLink_pred_edge`/`_deg_two(_right)`/`_off_succ`) + the
framework-layer `shiftBodyFramework_htrans`, reading the moved-body triple off
`getElem_shiftBodyList`. The total `F : ℕ → BodyHingeFramework` the fold demands is the new
`shiftBodyFrameworkTotal` (`dite` on the validity bound `s+1 < cd.d+1`, out-of-range tail = the
always-valid `s=0` member from `cd.hd`) + `shiftBodyFrameworkTotal_eq` (`dif_pos`); the per-step
`F (s+1)`/`F s`/`ec s` resolutions use `simp only` not `rw` (proof-irrelevant `getElem` bound +
un-beta-reduced `dite` redex — FRICTION idiom). The relabel side (`funLeft`-of-swap-product →
`funLeft (shiftPerm i)`, via `wstep_foldr_funLeft_eq` + `shiftPerm_eq_prod_map_swap_shiftBodyList`)
stays a *separate* bridge applied by the arm closer — the membership half is span-only. **Next: (T-W9b)**
the cycle bottom-tag transport (mirror `case_III_bottom_relabel`), then **2c-ii-arm**
`chainData_relabel_arm`.

**T-W9b decomposition — the cycle bottom-tag transport (design-pass 2026-06-19, source-verified
against the landed `case_III_bottom_relabel`/`case_III_arm_realization_M3` bodies + KT p.696–698
eqs. 6.60–6.66; clause (i)/(ii)). VERDICT: T-W9b is a genuinely-new cycle construction, NOT a numeral
pass over d=3 W9b, but it does NOT reuse the T-W9a fold core (different transport shape). It is its OWN
cycle treatment — ~1–2 build commits. No motive/IH (C.6) / spine-carry (C.3) change.**

*Why W9b does not ride the landed T-W9a machinery.* T-W9a's `wstep v a c := (funLeft (swap a
v)).dualMap − (a-column subtraction)` transports a **span member** of `(G−vᵢ)`-rows down to a span
member of `(G−v₁)`-rows. W9b (`case_III_bottom_relabel`, `Relabel.lean:1019`) is a structurally
**different** object: it transports one **tagged** bottom-family member `φ` — a *disjunction*
`φ ∈ (ofNormals Gv ends₀ q).rigidityRows ∨ ∃ ρ', ρ' ⊥ C(q(ab)) ∧ φ = hingeRow a b ρ'` — across the
**pure relabel** `(funLeft (swap a v)).dualMap φ` (verified: line 1036/1041, **no a-column
subtraction**), to a tagged member in the candidate shape (`(G−a)`-row ∨ `(cv)`-block disjunct). The
genuine-`Gv`-row disjunct *could* in principle route through the span machinery, but the `(ab)`-block
redundancy-tag disjunct is **not a span member** of the `Gv`-rows — it is the redundant `r̂`-row KT
carries separately (eq. 6.52). So W9b cannot be expressed as a `wstep` fold; it needs a per-step **tag
re-classification**, the cycle generalization of `case_III_bottom_relabel`'s three-way case split
(`x=a` / `y=a` / off-`a`) plus the `(ab)`-tag arm.

*How the tag transports per cycle step — KT eq. 6.62/6.66 (the ±r carry), source-verified.* The tag
shifts **once per moved body** (per cycle step), NOT once total. KT's row correspondence (6.62) reads
edge-by-edge along the chain: `(v₀v₂)i*` in `R(G₁,q₁)` ↔ `(v₀v₁)i*` in `R(G,pᵢ)`, `(vⱼvⱼ₊₁)` ↔
`(vⱼ₋₁vⱼ)` for `2≤j≤i`, etc.; and the single redundancy `r := ∑ⱼ λ_{(v₀v₂)j} rⱼ(q(v₀v₂))` is carried
`= ±r` to candidate `i` (eq. 6.66), "due to the fact that `vᵢ` is a vertex of degree two in `G₁`"
(verbatim p.698 — exactly cf. eq. 6.44, the same degree-2/a-column mechanism W9a uses). So each of the
`i−1` moved degree-2 bodies re-tags one block: a `(ab)`-block row at body `vₛ₊₁` becomes a `(cv)`-block
row at the predecessor `vₛ`, exactly as the single-step W9b maps `(ab)` → `(cv)` (`Relabel.lean:1077`,
the `x=a`/`y=a` arms tag a `(cv)`-block row; `hends₃_eb` maps the genuine `(ab)`-block to the `e_b`-row
`(v,b)`). **The d=3 M₃ is the `i=2` instance: a single moved body `a = vtx 1`, one tag shift.** The
cleanest cycle shape is an **induction on the moved-body list** (same `shiftBodyList i` / head-peel
`shiftPerm_eq_swap_mul` the T-W9a fold uses): each step applies the landed single-step
`case_III_bottom_relabel` to the running tagged member, the genuine-row disjunct staying genuine
(transported through the un-relabelled `shiftBodyFramework` chain step), the block-tag disjunct
re-classifying `(vₛ₊₁vₛ₊₂)` → `(vₛvₛ₊₁)` per step.

*Pinned T-W9b signature (build-discovered; mirror the landed cycle-W9a membership shape — over
`shiftBodyFramework`, NOT splits).* The likely shape — stated against the same `shiftBodyFramework`
chain T-W9a transports over, so the genuine-row disjunct reuses T-W9a's span result and only the
`(ab)`-tag arm is new:
```
-- ChainData.shiftBodyList_foldr_bottomTag_relabel (working name): per-member cycle bottom-tag.
theorem ChainData.<…> (cd) (i : Fin (cd.d+1)) (hi : 2 ≤ ↑i) ends q {φ}
    (hφ : φ ∈ (cd.shiftBodyFramework (s := ↑i − 1) _ ends q).rigidityRows ∨
      ∃ ρ', ρ' (panelSupportExtensor (q(vtx i, ·)) (q(vtx ?, ·))) = 0 ∧ φ = hingeRow (vtx i) ? ρ') :
    (funLeft (cd.shiftPerm i)).dualMap φ ∈
      (cd.shiftBodyFramework (s := 0) _ ends q).rigidityRows ∨
      ∃ ρ', ρ' (panelSupportExtensor (q(vtx 1, ·)) (q(vtx 0, ·))) = 0 ∧
        (funLeft (cd.shiftPerm i)).dualMap φ = hingeRow (vtx 1) (vtx 0) ρ'
-- (the (ab)/(cv) block endpoints are the chain's top/bottom interior bodies; the exact role tuple
--  is build-discovered from the arm's hwmem slot — see the arm signature below.)
```
The relabel side uses the **already-LANDED** `wstep_foldr_funLeft_eq` +
`shiftPerm_eq_prod_map_swap_shiftBodyList` to expose `(funLeft (shiftPerm i)).dualMap` (the W9b
transport is *pure* relabel, so unlike W9a there is no a-column residue to carry — the relabel bridge
is the whole transport on the genuine-row disjunct). **Next concrete buildable leaf: T-W9b**, as the
per-member cycle bottom-tag analogue of `case_III_bottom_relabel`, proved by induction on
`shiftBodyList i` reusing the landed single-step W9b at each head-peel.

*The downstream `chainData_relabel_arm` shape (§(o″) check, clause-(deliverable-5)) — STILL CORRECT
given the span-only + deferred-relabel split.* The arm signature pinned above is unchanged. The
membership-half/relabel-bridge split is internal to how the arm *fills* `case_III_arm_realization`'s
`hρGv` slot (span transport via T-W9a + relabel rewrite) and `hwmem` slot (T-W9b) — it does not change
the arm's premises. Verified against the d=3 `case_III_arm_realization_M3` (`Relabel.lean:1289`): the
`hρGv` slot is filled at line 1451 by the single-step W9a (`funLeft_dualMap_sub_acolumn_…`) + the
`hingeRow v b ρ` genuine-row `sub_mem` (1464–1476), and the `hwmem` slot at line 1488 by single-step
W9b (`case_III_bottom_relabel`) — the cycle arm replaces each with its cycle analogue (T-W9a span +
its deferred relabel bridge; T-W9b), feeding the **shared** `ρ₀`/`w` exactly as M₃ does
(`Realization.lean:592` passes the base `w`/`hw0mem` unchanged to M₃'s `hwmem`). So `hwmem`'s
disjunction shape (genuine-`Gv`-row ∨ `(ab)`-block) is what T-W9b must produce at the relabelled roles
`(v,a,b) := (vtx i.succ, vtx (i−1).castSucc, vtx i.castSucc)` — confirming the arm's frozen shape and
that no contract (C.3/C.6) moves.

#### (o″) THE DEGREE-2 REDUNDANCY BRIDGE — the missing W9b-membership leaf (BLOCKED row 266 → pinned)

**Status:** the W9b-membership build (HEAD 86a60be, row 266) hit a genuine gap and BLOCKED rather
than force a wrong proof — a win. This sub-section pins the gap, decomposes it into a buildable leaf
with the correct signature, and re-points. **Clause-(i): every load-bearing claim source-verified
against the landed bodies** (file:line) **and KT 2011 §6.4.2** (pdf pp. 50–52 = paper pp. 696–698,
eqs. 6.60–6.67, read end-to-end). **Clause-(ii): no motive/IH (C.6) or spine-carry (C.3) change; the
bridge is a degree-2 row-identity leaf, NOT genuinely-new math** (it generalizes a LANDED d=3 lemma)
— so the W9b/2c-ii-arm approach is structurally sound and stands.

**The gap (build-found, coordinator-verified vs the single-step signature `Relabel.lean:1181`).**
The fold core `bottomTag_foldr_mem_rigidityRows` (`Relabel.lean:1273`) threads a per-step
`Tag : ℕ → Dual → Prop` whose `hstep s` is discharged by the single-step
`funLeft_dualMap_bottomTag_mem_rigidityRows` at body `bodies[s] = (vₛ₊₂, vₛ₊₁, vₛ)`. Tracing the
block-tag disjunct (worked at `i=3`, `shiftBodyList 3 = [(v₂,v₁,v₀),(v₃,v₂,v₁)]`): the single-step's
INPUT block-tag at step `s` is `∃ρ', ρ' Cab = 0 ∧ φ = hingeRow a b ρ'` with
`Cab = Fva.supportExtensor e_b` (`e_b` links `v=vₛ₊₂, b`, the **successor** panel), and its OUTPUT
block-tag is `∃ρ', ρ' Cca = 0 ∧ … = hingeRow c v ρ'` with `Cca = Fv.supportExtensor e_c`
(`e_c = edge s` links `a=vₛ₊₁, c=vₛ`, the **predecessor** panel). So a tag *produced* annihilating
`C(edge s)` must be *consumed* annihilating `C(edge s+1)` at the next step — two **distinct** adjacent
panels sharing the degree-2 vertex `vₛ₊₁`. The landed single-step ties `Cab`/`Cca` rigidly to specific
edges and supplies **no bridge** between them. The `d=3` arm (`i=2`, `shiftBodyList 2` length 1) chains
**zero** times — the block discharges to a genuine `e_b`-row in one step (single-step `(ab)`-block case,
`Relabel.lean:1246–1252`) — so the gap is invisible there; it first appears at `i ≥ 3` (genuinely
general-`d`).

**WHAT EXACTLY IS THE BRIDGE (source-verified KT eqs. 6.64/6.66/6.44).** **Route (a) as the build
stated it (`ρ'⊥C(edge s) ⟹ ρ'⊥C(edge s+1)`) is WRONG/too-strong** — the two panels are distinct
subspaces of `ScrewSpace k` and no orthogonality *implication* holds between them. **The real
mechanism is a ±-sign-flip carry of the redundancy ROW VECTOR, an EQUALITY, not an annihilation
implication.** KT p. 698 verbatim: define the redundancy `r := ∑ⱼ λ_{(v₀v₂)j} rⱼ(q(v₀v₂)) ∈ ℝ^D`
**once** off the base `(G₁,q₁)`; then (6.64) shows the carried redundant row at candidate `i` is
`∑ⱼ λ_{(vᵢvᵢ₊₁)j} rⱼ(q₁(vᵢvᵢ₊₁))` (SAME `λ`s, panel `q₁(vᵢvᵢ₊₁)`), and (6.66): *"due to the fact that
`vᵢ` is a vertex of degree two in `G₁` for all `2 ≤ i ≤ d−1`, we can easily show … (cf. (6.44)):
`∑ⱼ λ_{(vᵢvᵢ₊₁)j} rⱼ(q(vᵢvᵢ₊₁)) = ±r`"*. So the carried row **equals ±r as a vector**; only THEN
(6.66 continues) does "Mᵢ not full rank ⟺ `r` ⊥ C(Lᵢ)" follow — the orthogonality is read off the
**single shared `r`**, never transported panel-to-panel. The precise Lean form of the mechanism: at a
degree-2 body `a` (edges `ab`, `ac`), if the full `a`-column of the redundant `G_v`-row combination
vanishes, then `∑ⱼ λ_{(ac)j} rac_j = −∑ⱼ λ_{(ab)j} rab_j` — i.e. the redundancy ROW computed at the
`ac`-panel is `−` the row computed at the `ab`-panel.

**A LANDED d=3 lemma ALREADY ENCODES THIS — the bridge REUSES/generalizes it, it is NOT new math.**
`BodyHingeFramework.candidateRow_ac_eq_neg` (`RigidityMatrix/Claim612.lean:1194`,
`lem:case-III-claim612-eq644`, KT eq. 6.44) is *exactly* the degree-2 two-panel row identity:
from `hcol` (the `a`-column of `(∑ lamAB • hingeRow a b rab) + (∑ lamAC • hingeRow a c rac) + grest`
vanishes) and `hrest` (the off-`a` rest vanishes on `a`'s column), it concludes
`∑ⱼ lamAC j • rac j = −∑ⱼ lamAB j • rab j`. It is **graph-free, abstract over `ιab`/`ιac`/`a,b,c`**
(no `d=3` pin), so it lifts to the chain verbatim. At `d=3` it is consumed at the **discriminator/
criterion level** (`Claim612.lean:1034`: the `M₃` candidate functional `ρ_c` is `−r̂` restricted to
the `c`-endpoint, so the Claim-6.12 capstone reads its criterion off the same `r̂`), **not** inside
the W9b row-transport — which is *why* the W9b single-step never needed it and the general-`d` fold
exposes the gap. The bridge leaf is the chain-step instance of `candidateRow_ac_eq_neg`: it carries
the single redundancy `r` across one degree-2 body, flipping its sign, so the W9b membership can
re-express each step's `(ab)`-tag input as the `(cv)`-tag output of the previous step. **This is the
reuse, not new math** (clause-ii).

**The buildable-leaf decomposition.** The fix is **not** to strengthen the single-step's orthogonality
hypotheses (route a, unprovable); it is to **change what the W9b `Tag` carries**. The current
`bottomTag` block-disjunct carries a *free existential* `∃ρ', ρ' ⊥ C(panel)` — which cannot chain
because the panels differ. The correct `Tag` **pins the block functional to the single redundancy
`±r`** (KT's one `r`), so the per-step carry is the eq.-(6.44) VECTOR identity, not a per-step
orthogonality re-derivation. Two equivalent shapes (build picks at contact; both reuse
`candidateRow_ac_eq_neg`):
- **(B1, recommended) a bridge leaf BEFORE the fold instantiation**, slotting between the landed fold
  core (`bottomTag_foldr_mem_rigidityRows`) and the W9b membership:
  ```
  -- working name: ChainData.redundancy_panel_carry (CaseIII/Relabel.lean, after the fold core)
  theorem ChainData.redundancy_panel_carry [DecidableEq α] (cd : G.ChainData n) {i s : ℕ}
      (hs : s + 1 < i) (hi : i < cd.d + 1) (q : α × Fin (k + 2) → ℝ)
      {r : Module.Dual ℝ (ScrewSpace k)}
      (hr : r (panelSupportExtensor (q at the edge-s/predecessor panel) …) = 0) :
      r (panelSupportExtensor (q at the edge-(s+1)/successor panel) …) = 0   -- ⟸ via ±r equality
  ```
  built by the eq.-(6.44) identity at body `vₛ₊₁` (`candidateRow_ac_eq_neg` instance: the redundant
  combination's `a`-column at `vₛ₊₁` vanishes, so its `(vₛ₊₁vₛ)`-panel row = `−` its
  `(vₛ₊₁vₛ₊₂)`-panel row, hence `r ⊥ C(edge s) ⟺ r ⊥ C(edge s+1)` **for this one fixed `r`** — the
  honest, provable form of "route a", scoped to the single carried `r`, not all `ρ'`). The W9b
  membership then defines `Tag s` with the block-disjunct pinned to `r` and supplies each `hstep`'s
  panel-match by this carry.
- **(B2, alternative) absorb the carry into a strengthened single-step.** Re-state
  `funLeft_dualMap_bottomTag_mem_rigidityRows` so its `(ab)`-block hypothesis carries the eq.-(6.44)
  `a`-column-vanishing fact (the redundant combination decomposition,
  `exists_redundant_panelRow_ab_decomposition_acolumn_zero`, `Candidate.lean:522`) and its output
  block-tag re-pins to the SAME `r` at the shifted panel. Heavier (touches the landed single-step);
  **prefer B1** (additive, leaves the green single-step/fold core untouched).

**How the W9b membership then instantiates the fold's `Tag`** (the leaf row 266 BLOCKED on). Define
`Tag s ψ := ψ ∈ span (shiftBodyFramework s)-rows ∨ (the block-disjunct, with ρ' pinned to ±r at the
edge-s panel)`. The genuine-row disjunct's per-step `hstep` reuses T-W9a's
`shiftBodyFramework`/`shiftBodyGraph` accessors (LANDED). The block-disjunct's per-step `hstep` is the
single-step `funLeft_dualMap_bottomTag_mem_rigidityRows` **plus** the (B1) `redundancy_panel_carry`
discharging the panel-match `Cab(step s) = ±` of the predecessor `Cca(step s+1)` for the pinned `r`.
The single redundancy `r` is the W6b candidate functional `ρ` from `chainData_split_w6b_gates`
(`Realization.lean:1005`) — the SAME `ρ`/`w` reused across all candidates (route β, KT's one-`r`
discipline), so it is in scope.

**The rest of the W9b / 2c-ii-arm decomposition HOLDS once the bridge lands.** The arm closer
`chainData_relabel_arm` shape is **unchanged** (pinned above, §(o″) check): it fills
`case_III_arm_realization`'s `hwmem` slot with the (now-chainable) W9b membership output and `hρGv`
with T-W9a span + the deferred relabel bridge, feeding the shared `ρ₀`/`w`. **`d=3` zero-regression is
preserved**: the `d=3` arm routes through `case_III_arm_realization_M3` (`Relabel.lean:1423`) at `i=2`
(chain length 1, zero carries), which does **not** call the bridge — `redundancy_panel_carry` is only
invoked for `s+1 < i` with `i ≥ 3`, vacuous at `i=2`. So the d=3 M₃ body and its
`complementIso_smul_eq_extensor_join` wrapper stay green, untouched.

**Updated per-leaf tracker (CHAIN-2c-ii-transport):** T-W9a-chain ✓ → T-W9a ✓ → W9b-step ✓ → W9b fold
core ✓ → **redundancy_panel_carry ✓ (LANDED 2026-06-19, axiom-clean)** → **block-carrying single-step
(NEXT BUILDABLE — the irreducible piece; see *Sharpened recon* below: the landed single-step
terminates the `(ab)`-block, the chain interior cannot)** → W9b membership (fold) → 2c-ii-arm → 2c-iii
→ CHAIN-5.

**As-landed bridge signature (shape B1, `Graph.ChainData.redundancy_panel_carry`, `Relabel.lean`).** The
leaf landed in the *abstract eq.-(6.44) form* — it carries the redundant-combination decomposition data
(the `λ_{(ab)}`-weighted `ab`-`hingeRow`-sum, the `λ_{(ac)}`-weighted `ac`-`hingeRow`-sum, the `grest`
remainder) with the `a`-column-vanishing hyps `hcol`/`hrest`, and concludes the `±r` *vector* identity
`∑ⱼ λac_j • rac_j = −∑ⱼ λab_j • rab_j` (not a `panelSupportExtensor`-to-`panelSupportExtensor`
annihilation transfer). This is the honest, fully-provable core; it is a thin chain-step wrapper of
`candidateRow_ac_eq_neg` naming the moved body `a = vtx⟨s+1⟩` and its chain neighbors
`b/c = vtx⟨s+2⟩/vtx⟨s⟩` (distinctness off `vtx_ne`). The W9b membership consumes the `±r` identity to
pin `Tag`'s block functional to the single `r` (testing both adjacent panels up to sign), supplying the
`hcol`/`hrest` from the W6b redundancy decomposition at instantiation.

**Salvaged build diagnosis (row 266, so it is not lost).** The W9b-membership build traced the `Tag`
fixpoint at `i=3` and found the fold cannot be instantiated mechanically: the single-step output
annihilates `C(edge s)` but the next step's input needs `⊥ C(edge s+1)` (distinct adjacent panels at
the degree-2 vertex). Bridge = KT's ±r-via-degree-2 (eq. 6.66/6.44), not encoded by the landed
single-step; gap first appears at chain length ≥ 2 (d=3 never chains). The diagnosis was
coordinator-sanity-checked vs the single-step signature before BLOCKED — a high-value genuine-gap
find, not a model failure. **The blueprint-clarity obligation (route β absorbs eqs. 6.54–6.56/6.66)
gains a concrete anchor here:** the `lem:case-III` general-`d` prose's point (3) "the single
redundancy `r` carried ±-ly across the `d` panels (eq. 6.66)" is exactly `redundancy_panel_carry`
generalizing `candidateRow_ac_eq_neg`.

**Sharpened recon (2026-06-19, read-only, source-verified vs the landed single-step body
`funLeft_dualMap_bottomTag_mem_rigidityRows`, `Relabel.lean:1181`): the landed single-step is NOT
reusable for the fold's `(ab)`-block disjunct — W9b membership needs a NEW block-CARRYING single-step,
not a `Tag` choice over the landed one.** Two structural facts, each verified against the body:

  1. *The landed single-step's `(ab)`-block input arm always produces a GENUINE `e_b`-row, never a
  `(cv)`-block carry.* At `Relabel.lean:1246–1252` the `φ = hingeRow a b ρ'` input is relabelled to
  `hingeRow v b ρ'` and discharged by `Or.inl ⟨e_b, v, b, hlink_eb, ρ', …⟩` — i.e. it *terminates*
  the block into the genuine `e_b`-row of `Fva`. (Only the *genuine-row* input arm, lines 1204–1245,
  can emit a `(cv)`-block, via the degree-2 edge `e_c`.) So a `Tag` whose block-disjunct is pinned to
  `±r` cannot chain across an interior step by feeding the landed single-step: the step would convert
  the carried block into a genuine row.

  2. *That termination is structurally IMPOSSIBLE in the interior chain frame* (so it is not merely
  the wrong arm — the arm's `hlink_eb` premise is unsatisfiable at the natural successor edge). The
  single-step's `(ab)`-block arm needs `hlink_eb : Fva.graph.IsLink e_b v b` with `Fva = F s =
  G − vₛ₊₁` and `v = vₛ₊₂`. The natural successor edge `edge (s+1)` links `vₛ₊₁, vₛ₊₂` in `G`, so it
  is incident to the *removed* vertex `vₛ₊₁` and does **not** survive `removeVertex vₛ₊₁`. Hence there
  is no surviving `e_b` for the block to terminate into — the carried block MUST stay a `(cv)`-block
  at the predecessor panel, exactly the carry `redundancy_panel_carry` was built to license. (At
  `d=3`/`i=2` the chain has length 1 and the block is at the *bottom* already, so the M₃ single-step's
  termination is correct there — which is why the gap is d≥4-only and the landed single-step is the
  *d=3 terminal* form, not the chain-interior form.)

  **Consequence for the next session.** The W9b membership is NOT "instantiate `bottomTag_foldr_mem_
  rigidityRows` with a `±r`-pinned `Tag` over the landed single-step." It requires a **new
  block-carrying single-step** `funLeft_dualMap_pinnedBlock_carry` (working name) whose `(ab)`-block
  input maps to a `(cv)`-block OUTPUT re-pinned to `±r` at the predecessor panel (consuming
  `redundancy_panel_carry` for the panel-match), with the genuine-row arm reusing the landed
  single-step's first case. THEN the fold instantiation. This is the shape B2 of §(o″)
  ("absorb the carry into a strengthened single-step") more precisely than B1 — B1's standalone bridge
  lemma is landed but does not by itself let the *landed* single-step chain; the strengthened step is
  the irreducible piece. Honest re-estimate: **the new carrying single-step is itself a build commit**
  (the three-way case split with a `(cv)`-output block arm, the bridge wire-up, the per-step
  coordinate bookkeeping `e_b = edge (s+1)` / `e_c = edge s` off `ChainData`), THEN the fold +
  relabel-bridge instantiation a second. No motive/IH (C.6) / spine-carry (C.3) change (the new step
  is below the dispatch, like the landed one); `d=3` zero-regression preserved (the landed terminal
  single-step + M₃ are untouched). Per-leaf tracker gains a node: **redundancy_panel_carry ✓ →
  block-carrying single-step [NEXT] → W9b membership (fold) → 2c-ii-arm → …**.

#### (o″) DESIGN-PASS — frozen carrying-step signature + the `hcol`-supply correction (2026-06-19)

> ⚠ **INVALIDATED (row 272, 2026-06-19) — retained as the source-verified record, NOT the live plan.
> Live successor: §(o‴) below (the telescoping design-pass).**
> This pass froze a *single-pinned-`Tag`* carrying-step signature; a build then verified it is
> **unprovable** — the carry leaves a generically-nonzero residual `hingeRow vₛ₊₂ b ρ`. The telescoping
> design-pass **§(o‴)** then established (machine-verified) that NO per-body fold — pinned-`Tag`,
> pure-span, or accumulating-sum — carries the bottom-family `(ab)`-block disjunct, because that block
> row is not a `(G−vᵢ)`-span member and its residual has no interior `e_b`-row home; the honest GLOBAL
> transport is KT's (6.62) **whole-relabel** row correspondence (the cycle generalization of d=3 M₃
> `case_III_bottom_relabel`'s genuine-row arm), NOT a `bottomTag_foldr`. §(o‴) returns **FLAG-DON'T-FORCE**
> on one open structural fact. **Still-usable** content below: the G4d-i panel-match supply, the W6b
> `ρ`-gate, the abstract-`Tag` fold core, the d=3 M₃ structure, and the orphan confirm-and-delete flag
> (now extended in §(o‴) to the `bottomTag_foldr` chain). The single-pinned-`Tag` carrying-step shape
> itself is dead.

**Status:** the row-270-BLOCKED design pass, docs-only, source-verified against the landed bodies
(file:line per claim) + KT §6.4.2 eqs. (6.24)/(6.43)/(6.44)/(6.62)/(6.66). **VERDICT: the carrying
step is buildable AND its panel-match has a CLEANER supply than `redundancy_panel_carry` — the d=3 M₃
already uses it (G4d-i, `acolumn_mem_hingeRowBlock_of_span_rigidityRows`), and the
`redundancy_panel_carry`/`candidateRow_ac_eq_neg` route the BLOCKED agent named is NOT cleanly
suppliable at the chain step (its `hcol`/`hrest` decomposition data is out of scope). Flag-don't-force:
this reroutes the panel-match supply but does NOT block the carrying step — no motive/IH/spine change,
d=3 zero-regression. The next buildable leaf is the carrying step, signature frozen below.**

**(A) The frozen carrying-step signature** (`funLeft_dualMap_pinnedBlock_carry`, working name; in
`CaseIII/Relabel.lean`, between the bridge `redundancy_panel_carry`/`bottomTag_foldr_mem_rigidityRows`
fold core and the W9b membership fold instantiation). It is the chain-INTERIOR analogue of the landed
*terminal* single-step `funLeft_dualMap_bottomTag_mem_rigidityRows` (`Relabel.lean:1181`, verified):
same `Fv`/`Fva` abstract-carrier shape, same genuine-row arm, but the `(a,v)`-block input maps to a
`(c,v)`-block OUTPUT re-pinned to `±ρ` (NOT terminated into an `e_b`-row). Roles at chain step `s`
(`s + 1 < i`): moved body `a = vtx⟨s+1⟩`, post-swap position `v = vtx⟨s+2⟩` (via successor edge
`e_b := edge(s+1)`), surviving predecessor `c = vtx⟨s⟩` (via predecessor edge `e_c := edge s`).
```
theorem BodyHingeFramework.funLeft_dualMap_pinnedBlock_carry
    [DecidableEq α] {Fv Fva : BodyHingeFramework k α β}
    {v a b c : α} {e_b e_c : β}                                  -- b := vtx⟨s+2⟩ = v's successor role
    (hab : a ≠ b) (hvb : v ≠ b) (hca : c ≠ a) (hcv : c ≠ v) (hav : a ≠ v)
    (hlink_ec : Fv.graph.IsLink e_c a c)                         -- predecessor panel, survives G−v
    (hdeg2  : ∀ f x, Fv.graph.IsLink f a x → f = e_c)            -- a is degree 2 in Fv = G−vₛ₊₂
    (hdeg2r : ∀ f x, Fv.graph.IsLink f x a → f = e_c)
    (hnov   : ∀ f x y, Fv.graph.IsLink f x y → x ≠ v ∧ y ≠ v)
    (htrans : ∀ f x y, Fv.graph.IsLink f x y → x ≠ a → y ≠ a →
      Fva.graph.IsLink f x y ∧ Fv.hingeRowBlock f ≤ Fva.hingeRowBlock f)
    -- the single carried redundancy functional ρ (KT's one r), pinned to BOTH adjacent panels.
    -- (supportExtensor reads only ends/q, NOT graph membership — shiftBodyFramework_supportExtensor,
    --  Relabel.lean:851 — so Fva.supportExtensor e_b is the SEED (a,v)-panel even though e_b ∉ Fva.graph;
    --  these match the d=3 M₃ form `ρ (panelSupportExtensor (q(a,·)) (q(b,·)))` etc., Relabel.lean:1488–9.)
    {ρ : Module.Dual ℝ (ScrewSpace k)}
    (hρ_ab : ρ (Fva.supportExtensor e_b) = 0)   -- ⊥ successor (a,v)-panel C(edge s+1) — the W6b gate
    (hρ_ac : ρ (Fv.supportExtensor e_c)  = 0)   -- ⊥ predecessor (a,c)-panel C(edge s) — from G4d-i
    {φ : Module.Dual ℝ (α → ScrewSpace k)}
    (hφ : φ ∈ Fv.rigidityRows ∨ φ = BodyHingeFramework.hingeRow a b ρ) :   -- block PINNED to ρ
    (LinearMap.funLeft ℝ (ScrewSpace k) (Equiv.swap a v)).dualMap φ ∈ Fva.rigidityRows ∨
      (LinearMap.funLeft ℝ (ScrewSpace k) (Equiv.swap a v)).dualMap φ
        = BodyHingeFramework.hingeRow c v ρ           -- (c,v)-block re-pinned to the SAME ρ
```
*Differences from the landed terminal step (line-verified):* (1) the input/output block disjunct is
**pinned to the single `ρ`** (`φ = hingeRow a b ρ`), not a free `∃ρ', ρ' Cab = 0 ∧ φ = hingeRow a b ρ'`
— this is what lets the `Tag` chain (the free existential cannot, §(o″) gap). (2) The `(a,v)`-block
input arm produces a `(c,v)`-block (`hingeRow c v ρ`), NOT a genuine `e_b`-row — the landed step's
`Or.inl ⟨e_b,v,b,hlink_eb,…⟩` termination (`:1246–1252`) is dropped (it is structurally impossible in
the interior: `e_b = edge(s+1)` is incident to the removed `vₛ₊₁`, does not survive `Fva = G−vₛ₊₁`,
*Sharpened recon*). (3) The proof: the genuine-row input arm is **verbatim the landed step's first case**
(lines 1204–1245 — the `x=a`/`y=a`/off split producing the `(c,v)`-block via `e_c`, or a genuine
`Fva`-row); the block-input arm is NEW — relabel `hingeRow a b ρ` under `swap a v`, giving
`hingeRow v b ρ`, then convert to the `(c,v)`-block via `hingeRow v c`/`hingeRow_sub_hingeRow_eq`-style
identities using `hρ_ab`/`hρ_ac`. (No `e_b`-link needed — that is exactly the structural fix.) The
genuine-row arm needs `hnov`'s `y ≠ v` etc. exactly as the landed step.

**(B) The `hcol`/`hrest` supply — VERIFIED, and the BLOCKED route is REPLACED.** The coordinator's
caution holds: `exists_redundant_panelRow_ab_decomposition_acolumn_zero` (`Candidate.lean:522`) does
**NOT** cleanly supply `redundancy_panel_carry`'s `hcol`/`hrest`. Three source-verified facts:
- Its last conjunct `∀ a, (wGv + wOther − r i).comp (single a) = 0` is the **trivial zero-functional**
  vanishing (`:557`, proof `rw [hsum, sub_self, LinearMap.zero_comp]`, since `r i = wGv + wOther`). It
  is the column-vanishing of an **opaque** combination — `wGv` is *some* `Submodule.span` member, `wOther`
  *some* member of `span (r '' {j≠i})` — NOT the per-edge-grouped
  `∑ lamAB • hingeRow a b rab + ∑ lamAC • hingeRow a c rac + grest` shape that `candidateRow_ac_eq_neg`
  (`Claim612.lean:1194`) / `redundancy_panel_carry` (`Relabel.lean:1318`) demand as `hcol`. **There is
  no landed lemma re-expressing `wGv + wOther − r i` into that ab/ac/grest decomposition** (grep: no
  caller regroups it by edge). So the decomposition mapping the coordinator asked to confirm **does not
  exist** in the tree at the chain-body level.
- `candidateRow_ac_eq_neg` + `_acolumn_zero` have **zero live call sites** (grep, verified): they appear
  only in docstrings + the lemma defs + the new `redundancy_panel_carry` wrapper. The d=3 dispatch never
  routes through them — confirming §(o″)'s "consumed at the discriminator/criterion level, not the W9b
  row-transport." And `chainData_split_w6b_gates` (`Realization.lean:771`) outputs **only** `ρ`/`w` + the
  gate facts (`:789–807`); the redundancy decomposition `lam`/`rab`/`rac`/`grest` is existentially
  consumed *inside* `exists_candidateRow_bottomRows_of_rigidOn` (`:880`) and is **out of scope** at the
  membership/arm. So `redundancy_panel_carry`'s premises **cannot be discharged** at the chain step.
- **The d=3 M₃ arm ALREADY supplies the panel-match by the right route — G4d-i, not eq.-(6.44).** At
  `Relabel.lean:1532` the M₃ arm derives `hρ_ac : ρ ⊥ C(q(ac)) = 0` from `hρGv` (the candidate's
  `hingeRow a b ρ ∈ span (G−v)-rows`, in scope from W6b) via
  `acolumn_mem_hingeRowBlock_of_span_rigidityRows` (G4d-i, `Relabel.lean:1355`): the `a`-column of
  `hingeRow a b ρ` is `ρ`, which the degree-2-at-`a` constraint inside `Fv` lands in `Fv.hingeRowBlock
  e_c`, i.e. `ρ ⊥ Fv.supportExtensor e_c`. **This is the carrying step's `hρ_ac` supply** — it needs
  only `hρGv` (W6b output, in scope) + the degree-2 geometry (chain accessors, landed), NOT any (6.24)
  decomposition. `hρ_ab` (⊥ the successor panel) is the candidate's existing `ρ ⊥ C(q(ab))` gate
  (`chainData_split_w6b_gates` `:799`) re-read at the step's successor panel.

  **CONSEQUENCE (flag, not a blocker).** `redundancy_panel_carry` as landed (the eq.-(6.44) vector
  identity carrying `lam`/`rab`/`rac`/`grest`) is the **wrong tool** for the carrying step — its data is
  unavailable. The carrying step instead pins both `hρ_ac`/`hρ_ab` for the single `ρ` directly: `hρ_ab`
  from the W6b gate, `hρ_ac` from **G4d-i** at the chain body. The eq.-(6.44) `±r` story is real KT math
  (and the blueprint point (3) still anchors there), but the **provable Lean carry at the chain body is
  G4d-i** (the candidate's own column-membership), exactly as d=3 M₃ does it — *simpler* than (6.44),
  and it is why the d=3 W9b never needed (6.44). So `redundancy_panel_carry` is, on this verification,
  an **orphan-in-waiting** (built row-268 for the route this pass replaces); confirm-and-delete at the
  carrying-step / 2c-ii-arm build alongside the two existing orphans (route-A `ofNormals_relabel_perm`,
  the binary `funLeft_dualMap_sub_acolumn_comp_…`). It is NOT new math missing — the replacement (G4d-i)
  is **landed and already in d=3 use**; the carrying step wires the *known* d=3 supply into the interior
  step shape. (Do not delete `redundancy_panel_carry` pre-emptively: 1% the fold's `Tag` plumbing finds
  a use for the abstract `±r` identity; decide at the carrying-step build.)

**(C) The W9b-membership fold-instantiation plan** (after the carrying step lands). Define the fold's
`Tag s ψ := ψ ∈ span (cd.shiftBodyFramework s).rigidityRows ∨ ψ = hingeRow (vtx⟨s+1⟩) (vtx⟨s+2⟩) ρ`
(block-disjunct **pinned to the single `ρ`**, the W6b candidate functional from
`chainData_split_w6b_gates` `:799–801`, reused across all candidates — route β's one-`r` discipline, in
scope). Feed `bottomTag_foldr_mem_rigidityRows` (`Relabel.lean:1273`, the landed fold core threading
`Tag : ℕ → Dual → Prop`) with `F := shiftBodyFrameworkTotal` and `bodies := shiftBodyList i`:
- each `hstep s` (`s < length = i−1`) is the **carrying step** at `bodies[s] = (vₛ₊₂, vₛ₊₁, vₛ)`
  (`getElem_shiftBodyList`): genuine-row disjunct reuses T-W9a's `shiftBodyFramework_htrans`
  (`Relabel.lean:874`) + the graph-layer accessors (`shiftBodyGraph_isLink_pred_edge`/`_deg_two(_right)`/
  `_off_succ`, `Operations.lean:1698+`, all landed); block disjunct discharged by the carrying step with
  `hρ_ab`/`hρ_ac` supplied as in (B). The `Tag (s+1)→Tag s` re-pinning to the *same* `ρ` is automatic
  (both disjuncts name `ρ`); the supporting extensors are `s`-independent
  (`shiftBodyFramework_supportExtensor`, `:851`).
- the **terminal step** at the bottom (`s = 0`, the M₃-style block-at-bottom) is where the block tag
  *can* terminate into a genuine row, but the fold's last step `s=0` lands `Tag 0` (the
  `shiftBodyFramework 0 = G−v₁` span ∨ the bottom `(c,v)`-block); the arm's `hwmem` slot consumes the
  disjunction shape directly (it does not need a genuine-row collapse — the M₃ `hwmem` at `:1495` is
  exactly `Gv-row ∨ ∃ρ', ρ'⊥C(ab) ∧ = hingeRow a b ρ'`, and the cycle output is that with `ρ' := ρ`).
- the `funLeft (shiftPerm i)` identification: the fold's leading swap-product
  `(funLeft (swap …)).dualMap ∘ ⋯` is rewritten to `(funLeft (shiftPerm i)).dualMap` by the LANDED
  bridge `wstep_foldr_funLeft_eq` + `shiftPerm_eq_prod_map_swap_shiftBodyList` (the W9b transport is
  *pure relabel*, no a-column residue — `bottomTag_foldr` composes the bare relabels). This is the
  same relabel bridge T-W9a's arm-closer half uses; applied at 2c-ii-arm.

  **Sub-crux NOT yet a clean build (flagged):** the carrying step's **block-input arm** (the NEW case)
  — converting `(funLeft (swap a v)).dualMap (hingeRow a b ρ) = hingeRow v b ρ` into the `(c,v)`-block
  `hingeRow c v ρ` using `hρ_ab`/`hρ_ac`. The landed terminal step *terminates* here (into `e_b`); the
  carry must instead emit the `(c,v)`-block. The exact identity chain (likely
  `hingeRow_sub_hingeRow_eq` / `hingeRow_swap` against the two pinned annihilations) is build-discovered
  — it is the irreducible new content. Everything else in (C) is wiring of landed bricks.

**(D) d=3 zero-regression — CONFIRMED.** `shiftBodyList i` has length `i−1` (`length_shiftBodyList`,
`Operations.lean:1564`). The M₃ arm is the `i=2` instance → length-1 list → the single step `s=0` is the
*terminal* step (block already at the bottom), with **zero interior carrying steps** (`s+1 < i = 2`
forces `s=0`, but `s+1=1 < length=1` is false — no `hstep` chains). So the carrying step fires only at
chain length ≥ 2 / `i ≥ 3`, vacuous at `i=2`; the landed `case_III_arm_realization_M3` (`Relabel.lean:1465`)
+ `case_III_bottom_relabel` + the d=3 dispatch are **untouched**. The carrying step is purely additive.

**Frozen next buildable leaf:** `funLeft_dualMap_pinnedBlock_carry` (signature (A) above), one build
commit (the new block-input arm + the genuine-row arm reusing the landed terminal step's first case),
THEN the W9b membership fold (C) + the relabel-bridge instantiation a second commit. No motive/IH (C.6)
or spine-carry (C.3) change; route B holds; d=3 zero-regression preserved.

#### (o‴) THE TELESCOPING DESIGN-PASS — the GLOBAL fold invariant for the W9b-membership crux (2026-06-19)

> **This is the live successor to the INVALIDATED §(o″) *DESIGN-PASS*** (the single-pinned-`Tag`
> carrying step). The §(o″) blocks above are preserved as the source-verified record of the
> still-usable inputs (G4d-i panel-match, the W6b `ρ`-gate, the abstract-`Tag` fold core, the d=3 M₃
> structure, the orphan confirm-and-delete list); the single-pinned-`Tag` carrying-step *shape* is
> dead. This §(o‴) settles the GLOBAL-invariant question: **no per-body fold-invariant works** — the
> honest transport is KT's whole-relabel row correspondence, a bottom-family-transport reshape — and
> returns FLAG-DON'T-FORCE on one open structural fact.

**Status:** user-adjudicated comprehensive telescoping design-pass, docs-only, 2026-06-19. Clause-(i):
every load-bearing Lean claim verified against the **landed bodies** (file:line per claim), and the two
decisive arithmetic single-steps **machine-checked** (a scratch `lake env lean` compile, no `sorry`).
Clause-(ii) source: a close end-to-end read of **KT 2011 §6.4.2 pp. 696–698** (pdf pp. 50–52, offset
`printed = pdf + 646`), eqs. (6.60)–(6.67), with (6.44)/(6.50)–(6.59) read for the setup.
**VERDICT: FLAG-DON'T-FORCE STOP — see (E). The fold-invariant question has a clean answer for the
genuine-row part of the bottom family, but the `(ab)`-block disjunct of the bottom family `w` has NO
landed span-membership property at the chain interior and CANNOT be carried by either the §(o″)
pinned-`Tag` (residual, invalidated) OR a pure-span `Tag` (the block row is not a `(G−vᵢ)`-span
member). The honest GLOBAL invariant requires re-deriving the bottom-family transport at the
candidate-framework level (KT's (6.62) row correspondence applied whole, NOT a per-body chain) — a
real reshape of how `w` is produced/transported, NOT a leaf below the dispatch.** Detail below; the
arithmetic walk (b) is the heart.

---

**(a) What KT actually does — source-verified, decisive, and DIFFERENT from a per-body chain.**

KT does **not** carry the redundancy step-by-step across the `i−1` cycle bodies. The whole index-shift
`ρᵢ` (6.54) is applied **at once** as a graph isomorphism `G₁ ≅ Gᵢ` (on `V∖{vᵢ}`→`V∖{v₁}`), and the
redundancy reduces in **two single shots**:

- **(6.61)→(6.64) via (6.62) + (6.52).** KT performs column ops + substitutes (6.59) to bring `R(G,pᵢ)`
  to the form (6.61) `[ r(Lᵢ) , 0 ; r(q₁(vᵢvᵢ₊₁)) , R(G₁,q₁) ]`, using the **row correspondence (6.62)**:
  the rows of `R(G,pᵢ; E∖{vᵢvᵢ₊₁}, V∖{vᵢ})` are in bijection with the rows of `R(G₁,q₁)`, the bijection
  being exactly `ρᵢ` (the relabel) — verbatim p.696 "`(v₀v₁) ⇔ (v₀v₂)`, `(vⱼ₋₁vⱼ) ⇔ (vⱼvⱼ₊₁)` for
  `2≤j≤i`, `(vⱼ'vⱼ'₊₁) ⇔ (vⱼ'vⱼ'₊₁)` for `i+1≤j'≤d−1`, `e ⇔ e` else". The single `G₁`-redundancy (6.52)
  `∑_{e,j} λ_{ej} R(G₁,q₁;eⱼ) = 0` (`λ_{(v₀v₂)i*}=1`) is then pushed forward by this correspondence and
  added to the `(v₀v₁)i*` row of (6.61). By **(6.52), the new row restricted to `V∖{vᵢ}` is identically
  zero** (one application: the transported dependency is zero). The ONLY surviving part is the single
  block at body `vᵢ`, which the column ops left as `∑ⱼ λ_{(vᵢvᵢ₊₁)j} rⱼ(pᵢ(vᵢ₋₁vᵢ)) = ∑ⱼ λ_{(vᵢvᵢ₊₁)j}
  rⱼ(q₁(vᵢvᵢ₊₁))` (since `pᵢ(vᵢ₋₁vᵢ) = q₁(vᵢvᵢ₊₁)` by (6.59)). Result (6.64): `Mᵢ = [ r(Lᵢ) ;
  ∑ⱼ λ_{(vᵢvᵢ₊₁)j} rⱼ(q₁(vᵢvᵢ₊₁)) ]`, top-left `D×D`, atop `R(G₁∖(v₀v₂)i*, q₁)`.

- **(6.66): ONE degree-2 reduction at the SINGLE body `vᵢ`.** Verbatim p.698: "due to the fact that
  `vᵢ` is a vertex of degree two in `G₁` for all `2≤i≤d−1`, we can easily show … (cf. (6.44)):
  `∑ⱼ λ_{(vᵢvᵢ₊₁)j} rⱼ(q(vᵢvᵢ₊₁)) = ±r`" where `r := ∑ⱼ λ_{(v₀v₂)j} rⱼ(q(v₀v₂))` is defined ONCE. This
  is **eq. (6.44) applied once at `vᵢ`** (the degree-2 body of `G₁`), exactly as the d=3 Lemma-6.10
  proof applies (6.44) once at the degree-2 body `a`.

**The conceptual telescoping is therefore (6.52): a single GLOBAL dependency of `R(G₁,q₁)` whose
pushforward under the whole relabel `ρᵢ` is zero on `V∖{vᵢ}`.** The `i−1` adjacent bodies are NOT
visited one at a time; they are subsumed by the row correspondence (6.62) = the relabel. The "`±r`
chain" of (6.66) is a *family* of `d−1` independent single-body facts (one per candidate `i`), each a
one-shot (6.44), **not** a composition along a chain.

---

**(b) The end-to-end arithmetic walk — general `i`, then `i=3`, `i=4` — and where the Lean fold breaks.**

The Lean route B decomposes the single relabel `funLeft (shiftPerm i)` into a **product of `i−1`
transpositions** (`shiftPerm_eq_prod_map_swap_shiftBodyList`, landed) and transports row-membership
**one transposition at a time** over the `shiftBodyList i = [(v₂,v₁,v₀),…,(vᵢ,v_{i−1},v_{i−2})]`
(length `i−1`). This is a faithful re-expression of the *relabel* (the W9a span half proves it), but it
forces the redundancy to be carried per-body — which is where the structure that KT subsumes globally
must be reconstructed step-by-step. Two transports run in parallel along the chain:

- **The `hρGv` candidate-row (the redundant `±r` row) — a SPAN-membership transport, telescopes
  cleanly. MACHINE-VERIFIED.** The candidate row enters as `hingeRow a b ρ ∈ span (G−vᵢ).rigidityRows`
  (`hρGv`, W6b output, a genuine span member). Each transposition step is W9a:
  `(funLeft (swap a v)).dualMap φ − hingeRow v c (φ∘single a) ∈ span (lower).rigidityRows`. For the
  block row `φ = hingeRow a b ρ` (a-column `= ρ`): the W9a single step lands
  `(funLeft swap).dualMap φ − hingeRow v c (φ∘single a) ∈ span (lower)`, i.e.
  `hingeRow v b ρ − hingeRow v c ρ ∈ span (lower)`. **The span-membership invariant
  `ψ ∈ span (shiftBodyFramework s).rigidityRows` is the GLOBAL invariant for THIS transport** — it is
  exactly the LANDED **T-W9a** `shiftBodyList_foldr_mem_span_rigidityRows`, axiom-clean, and it is
  **interior-safe at every step with NO `e_b`-row needed**: the residual `hingeRow v c (φ∘single a)`
  is handled inside the W9a `span_induction` (it cancels on the degree-2 generator at `a`, is zero
  off-`a`, and the survivor is a genuine lower-framework row via `htrans`). So the candidate row's
  span membership transports cleanly down the whole chain. The ONE place an `e_b`-row enters is the
  d=3 M₃ arm's *bare-row extraction* (`hρGv` slot, `Relabel.lean:1583`–1652): to turn the span member
  back into the literal row `hingeRow c v (−ρ)` it does `sub_mem` against the genuine `e_b`-row
  `hingeRow v b ρ` (present because `ρ ⊥ C(ab)` AND, at d=3, `b` is the OFF-CHAIN neighbour so `e_b`
  survives). *Machine-verified*: the abstract single-step (premises `hingeRow a b ρ ∈ span Fv`,
  `ρ ⊥ Fva.supportExtensor e_b`, the W9a degree-2 hyps; conclusion `hingeRow c v (−ρ) ∈ span Fva`)
  compiles `sorry`-free. **The span transport is clean; the bare-row extraction is a separate, d=3-only
  repackaging that the cycle arm performs ONCE at the chain bottom (not per interior step).** No
  per-step pinned functional, no §(o″) residual on the candidate-row half.

- **The bottom family `w`'s `(ab)`-block disjunct — the OBSTRUCTION. NOT a span member; the residual
  has nothing to absorb it.** The bottom family enters tagged `w j ∈ (G−vᵢ).rigidityRows ∨ ∃ρ', ρ'⊥C(ab)
  ∧ w j = hingeRow a b ρ'` (W7's `hwmem`, `Arms.lean:96`; the block disjunct is the redundant candidate
  rows `r '' {j≠i*}`, which live in the **`ab`-edge block `Eb = span(range r) ⊄ span (G−vᵢ).rows`**, NOT
  the source split's row span — `exists_candidateRow_bottomRows_of_rigidOn`, `Candidate.lean:411`/`448`–
  `474`). So the block disjunct CANNOT ride the span-membership invariant: `hingeRow a b ρ' ∉ span
  (G−vᵢ).rows`, so the W9a step has no premise to feed. The §(o″) single-step
  (`funLeft_dualMap_bottomTag_mem_rigidityRows`, `Relabel.lean:1181`) instead carries the block as a
  *free-existential `Tag`* and **terminates** it into a genuine `e_b`-row at the bottom step
  (`:1246–1252`). At the chain INTERIOR this termination is **structurally impossible**:
  `e_b = edge(s+1)` links `vₛ₊₁,vₛ₊₂` in `G`, so it is incident to the removed vertex `vₛ₊₁` and does
  NOT survive `Fva = G−vₛ₊₁` (verified: `shiftBodyGraph_off_succ`/`_deg_two`). So the carried block must
  become a `(cv)`-block at the predecessor — and the iter-11 single-pinned-`Tag` tried exactly that and
  **left the residual** `(funLeft swap).dualMap (hingeRow a b ρ) = hingeRow v b ρ ≠ hingeRow c v ρ` (the
  desired `(cv)`-output). *Machine-verified: `hingeRow v b ρ − hingeRow c b ρ = hingeRow v c ρ`
  (`hingeRow_sub_hingeRow_eq`, shared 2nd endpoint `b`) but `hingeRow v b ρ` and `hingeRow c v ρ` share
  NO endpoint and do not collapse* — exactly the §(o″) invalidation (row 272). There is no third object
  to absorb `hingeRow v b ρ` (no surviving `e_b`-row interior, and `hingeRow a b ρ'` is not a span
  member), so neither the pinned-`Tag` (residual) NOR the pure-span `Tag` (no premise) carries the block
  disjunct. **This is the irreducible gap.**

*Instantiation at `i = 3`* (`shiftBodyList 3 = [(v₂,v₁,v₀),(v₃,v₂,v₁)]`, length 2, the smallest chaining
case): the cycle `funLeft (shiftPerm 3) = (v₁v₂)(v₂v₃)` is the fold of step `s=0` (move `v₁`, swap
`v₁v₂`) after step `s=1` (move `v₂`, swap `v₂v₃`). **Candidate row** `hingeRow a b ρ ∈ span (G−v₃)`:
T-W9a transports the SPAN membership `span (G−v₃) → span (G−v₂) → span (G−v₁)`, interior-safe, no `e_b`
(verified, landed) — fine at both steps. **Bottom family `w`'s `(ab)`-block disjunct** `w j = hingeRow
a b ρ'`, `ρ'⊥C(ab)`: this is NOT a span member of `(G−v₃).rows` (it lives in the `ab`-edge block `Eb`),
so it cannot ride T-W9a. The §(o″) per-body relabel sends it `hingeRow a b ρ' ↦ hingeRow v b ρ'` (swap
`a↦v`, `b` fixed) — a `(v,b)`-block at the SUCCESSOR, while the next step's input needs a `(c,v)`-block
at the predecessor. To terminate it into a genuine row needs the `e_b = edge(s+1)`-row, but `edge(s+1)`
links the moved body `vₛ₊₁` to `vₛ₊₂` and is **cut** by `removeVertex vₛ₊₁` (interior) — so there is no
genuine row to terminate into, and the §(o″) residual `hingeRow v b ρ' − hingeRow c v ρ'` (no shared
endpoint, no collapse) is unconstrained. **The block disjunct has no per-body transport.** Note the
d=3 M₃ (`i=2`) closes only because its single step IS the bottom step: there `b` is the OFF-CHAIN
neighbour (`hG_eb : G.IsLink e_b v b`, `b ∉ {v,a,c}`), so `e_b` survives `G−a` and the block terminates
into the genuine `e_b`-row. The chain interior has no off-chain `b`, so this termination has no analogue.

*Instantiation at `i = 4`* (`shiftBodyList 4 = [(v₂,v₁,v₀),(v₃,v₂,v₁),(v₄,v₃,v₂)]`, length 3): candidate
row transports by T-W9a through `span (G−v₄) → (G−v₃) → (G−v₂) → (G−v₁)` (fine); the bottom-family block
disjunct hits the identical no-per-body-home obstruction at the two interior steps `s=1,2`, confirming it
is not an `i=3` artifact. **The arithmetic walk thus localizes the gap precisely: the candidate-row
half is clean (T-W9a, done); the bottom-family `(ab)`-block disjunct is the sole obstruction, and it is
not a fold-invariant problem at all — it is that this block row is transported, in KT, by the whole
relabel `ρᵢ` as the single redundant `(v₀v₂)i*`-row pushforward, not by any per-body chain.**

**Walking the arithmetic end-to-end thus shows the gap is NOT a missing carry leaf: it is that the Lean
per-body decomposition reconstructs, step-by-step, a redundancy structure KT only ever needs GLOBALLY
(one (6.52) pushforward + one (6.44) at `vᵢ`), and the per-body residuals have no per-body home.**

---

**(c) Why neither candidate GLOBAL invariant works as a fold over the landed single-steps.**

| Invariant shape | Genuine-row disjunct | `(ab)`-block disjunct | Verdict |
|---|---|---|---|
| §(o″) pinned-`Tag` `ψ = hingeRow … ρ` (block pinned to `±r`) | n/a | residual `hingeRow v b ρ ≠ hingeRow c v ρ`, unconstrained | **INVALIDATED** (row 272) |
| pure-span `Tag` `ψ ∈ span (shiftBodyFramework s).rows` | ✓ (= landed T-W9a) | block row ∉ `span (G−vᵢ).rows` — no premise | **fails** on block disjunct |
| accumulating-sum `Tag` (running `∑` of block rows) | ✓ | the sum's per-step residual `hingeRow v b ρ` still needs an `e_b`-row home, absent interior | **fails** — same residual, now inside a sum |

The "accumulating sum" the prompt hypothesized would only help if the per-step residuals **cancelled
pairwise** along the chain (telescoped to `0`). They do not: each step's residual `hingeRow vₛ₊₂ b ρ`
sits at a *different* body pair and there is no later step that produces its negative (the W9b transport
is a pure relabel + this one termination, with no second occurrence of `(vₛ₊₂,b)`). The W9a a-column
subtractions DO telescope (verified, T-W9a) **because they are span members that the span absorbs** —
but the bottom-family block disjunct is not a span member, so its analogue has no span to fall into.

---

**(d) The honest GLOBAL invariant — and why it is a reshape, not a leaf (FLAG).**

KT's transport of the *whole bottom family* (not just the candidate row) is eq. (6.62)'s **row
correspondence applied to ALL of `R(G₁,q₁)` at once**: under the relabel `ρᵢ`, every row of `R(G₁,q₁)`
(the source split `M₀`'s rows, both the genuine `(G−v₁)`-rows AND the redundant `(v₀v₂)`-block rows)
maps to a row of `R(G,pᵢ; E∖{vᵢvᵢ₊₁})` (the candidate split). The correct invariant is therefore at the
**candidate-framework / matrix level**, NOT a per-step row tag:

> **Carry the whole row-space identity `span (R(G,pᵢ; E∖{vᵢvᵢ₊₁})-rows) = (funLeft ρᵢ).dualMap ''
> span (R(G₁,q₁)-rows)` (KT (6.62)), and read the rank lower bound off it directly** — i.e., the
> candidate split's bottom block `R(G₁∖(v₀v₂)i*, q₁)` has the SAME rank as `M₀`'s bottom block because
> it IS `M₀`'s bottom block relabelled, and the redundancy (6.52) transports verbatim as a *single*
> dependency (not `i−1` carries).

This is what the d=3 dispatch does implicitly by reusing ONE W6b package `(ρ,w)` across all three arms
(`Realization.lean:404`, fed unchanged to `M₁/M₂/M₃`): the bottom family `w` is the SAME `w` at every
arm, transported by ONE relabel per arm (`M₃`'s `(funLeft (swap a v)).dualMap ∘ w`). The chain
generalization must do the same — transport the WHOLE shared `w` by ONE `funLeft (shiftPerm i)`, reading
the membership off the relabel's image of the source rows — rather than fold a per-row tag across `i−1`
bodies. Concretely the membership obligation `hwmem` at candidate `i` is:
`(funLeft (shiftPerm i)).dualMap (w j) ∈ (candidate-split).rigidityRows ∨ (the relabelled ±r block)`,
and the disjunction's genuine-row arm is the relabel-image of `w j`'s `(G−v₁)`-row (a genuine
candidate-split row, by the graph iso `splitOff_isLink_shiftRelabel_iff`, LANDED), while the block arm
is the SINGLE redundant `±r` row at `vᵢ` (one (6.44), G4d-i-suppliable). **The per-body `shiftBodyList`
fold is the wrong granularity for the bottom family** — it is right for the *relabel itself* (T-W9a,
landed) but the bottom-family membership should be read off the *whole* relabel's graph-iso row
correspondence, exactly as the genuine-row half already is.

**Why this is a reshape and a FLAG, not a buildable leaf below the dispatch.** The landed W9b fold core
(`bottomTag_foldr_mem_rigidityRows`) and the §(o″) single-step are built for the per-body tag chain — the
wrong granularity per the above. Replacing them with the whole-relabel transport means: (1) the bottom
family `w`'s membership is established via the graph-iso `splitOff_isLink_shiftRelabel_iff` (the
candidate↔base intertwiner, LANDED, consumed at the arm) applied to the *genuine-row* disjunct, and (2)
the *block* disjunct is the relabel-image of `M₀`'s single redundant `(v₀v₂)i*`-row, re-expressed as the
`±r` row at `vᵢ` by (6.44)/G4d-i. This is **not** a fold over the landed single-steps; it is a different
arm-closer shape (`chainData_relabel_arm`'s `hwmem` slot filled by a graph-iso relabel of the shared `w`,
not a `bottomTag_foldr`). It does NOT touch the motive/IH (C.6) or spine-carry (C.3) — the bottom family
is still the shared W6b `w`, the base is still the same `M₀` — but it **abandons the `bottomTag_foldr` /
pinned-/span-`Tag` chain entirely** and re-routes the bottom-family membership through the whole-cycle
graph iso. The T-W9a span fold STAYS (it correctly transports the *candidate row* `hρGv`); only the
*bottom-family `hwmem`* transport changes.

---

**(E) FLAG-DON'T-FORCE — the precise obstruction and what unblocks it.**

I am **not pinning a 5th `Tag`/carry signature.** The end-to-end walk (b) shows the per-body fold is the
wrong granularity for the bottom-family block disjunct, and (d) names the right shape (whole-relabel
graph-iso transport of the shared `w`) — but that shape is **not yet build-verified end-to-end**, and it
turns on one open structural fact I could not settle from the landed bodies alone:

**OPEN FACT (needs adjudication / a focused recon before any build).** Does the genuine-row arm of the
bottom-family membership at candidate `i` close via `splitOff_isLink_shiftRelabel_iff` *for the WHOLE
shared `w`* — i.e., is `(funLeft (shiftPerm i)).dualMap (w j)` a genuine row of the candidate split
whenever `w j` is a genuine `(G−v₁)`-row of `M₀`? The graph iso is landed (`Operations.lean:2122`), and
the relabel-of-a-rigidity-row identity is `hingeRow_funLeft_dualMap` (landed) — so this *should* be a
clean assembly. BUT: the candidate split `M₀ = (G₁,q₁)`'s rows and the candidate-`i` split's rows live
over DIFFERENT graphs (`G₁ = splitOff v₁` vs `Gᵢ = splitOff vᵢ`-relabelled), and the W7 `hwmem` slot
wants membership in the candidate-`i` split's rows at the candidate-`i` SEED `qᵢ = q₁∘ρᵢ` (6.56). Whether
the relabel `funLeft (shiftPerm i)` + the seed change `qᵢ = q₁∘ρᵢ` line up so that genuine `M₀`-rows map
to genuine candidate-`i`-rows (the (6.62) genuine-row correspondence) is the load-bearing fact — and it
is the SAME shape as the d=3 M₃ `case_III_bottom_relabel` genuine-row arm (`Relabel.lean:1109–1144`,
which closes it for the SINGLE swap via `hrecGv`/`hends₃_off`/the off-`{e_a,e_b,e_c}` extensor
coincidence). The cycle generalization of THAT arm (over the whole `shiftPerm i`, not a per-body fold) is
the genuinely-new piece, and its difficulty is unknown until someone writes the seed/selector
bookkeeping for the whole relabel.

**What I established (so the next session does not re-walk it):** (1) the §(o″) pinned-`Tag` is
dead (residual, machine-confirmed); (2) the pure-span `Tag` fails on the block disjunct (not a span
member — proved by the W5 rank arithmetic `Candidate.lean:339–355`: `finrank(span Fab)=D(m−1)` but
`finrank(span Fv)=D(m−1)−k'`, `k'=dof(Gv)≥1`, so `span Fv ⊊ span Fab` forces `Eb ⊄ span Fv`; the `:448`
cited earlier is just a `set`, not the proof); (3) an accumulating-sum `Tag` fails identically (the
residuals do not telescope — no pairwise cancellation); (4) the candidate-row `hρGv` transport IS clean
and IS the landed T-W9a span fold (machine-verified single-step) — **that half is done and correct**;
(5) the honest GLOBAL transport for the bottom family is the **whole-relabel graph-iso correspondence**
(KT (6.62)), the cycle generalization of the d=3 M₃ `case_III_bottom_relabel` genuine-row arm, NOT a
`bottomTag_foldr`; (6) this is a **bottom-family-transport reshape** (the `chainData_relabel_arm`
`hwmem` slot), no motive/IH/spine change.

**What unblocks the build:** a focused recon that writes out the cycle generalization of
`case_III_bottom_relabel`'s genuine-row arm against the whole `shiftPerm i` + seed `qᵢ = q₁∘ρᵢ` (6.56),
confirming the genuine `M₀`-row → genuine candidate-`i`-row correspondence (6.62) closes via the landed
graph iso `splitOff_isLink_shiftRelabel_iff` + `hingeRow_funLeft_dualMap`, and that the block disjunct
reduces to the single `±r` row at `vᵢ` via G4d-i (one (6.44), as d=3 M₃ does). If that recon closes,
the leaf is `chainData_relabel_arm` directly (the bottom-family `hwmem` filled by the whole-relabel
transport), with NO new `bottomTag` infrastructure — and the landed `bottomTag_foldr_mem_rigidityRows`
+ §(o″) single-step + `redundancy_panel_carry` become orphans (confirm-and-delete, joining the existing
list). If it does NOT close cleanly, the obstruction is genuinely at the bottom-family production level
(how `w`'s block disjunct is generated) and is a `ChainData`/W6b-producer question for the coordinator —
NOT a CHAIN-2c-ii leaf.

**Leaf decomposition (named ONLY conditionally on the OPEN FACT above closing — per the prompt's
clause, secondary to the invariant).** IF the recon confirms (d): the single remaining leaf is the arm
closer `chainData_relabel_arm` (signature unchanged, §(o″) addendum at row ~2556), with its `hwmem` slot
filled by a NEW whole-cycle bottom-family transport `chainData_relabel_hwmem` (working name): for the
shared `w` and candidate `i`, `(funLeft (shiftPerm i)).dualMap (w j) ∈ (candidate-i split).rigidityRows
∨ (the ±r block at vᵢ)`, proved by the graph-iso correspondence (genuine arm) + G4d-i (block arm).
**Do NOT build this until the OPEN FACT is reconned** — it is exactly the kind of "mechanically
plausible" shape the 4× mis-pins were.

**`d=3` zero-regression — preserved.** `shiftBodyList i` length `i−1`, so the M₃ arm is `i=2` → the
whole `shiftPerm 2 = (v₁v₂)` is a single swap = the landed `case_III_bottom_relabel` (the bottom step,
where `b` IS off-chain and the termination is correct). The reshape fires only for `i≥3`; the d=3 M₃ /
`case_III_arm_realization_M3` / dispatch are untouched.

**(F) ADVERSARIAL SECOND READ — RE-ROUTE CONFIRMED (read-only recon, opus, 2026-06-19).** An
independent reader (told to *refute* this verdict against KT verbatim + the landed bodies, not to trust
the prose — warranted because this is the 4×-mis-pinned crux and a re-route) failed all three attacks:
(A) the block disjunct is genuinely not a `(G−vᵢ)`-span member (the rank argument above) and has no
per-body home (interior `e_b = edge(s+1)` is graph-structurally cut by `removeVertex vₛ₊₂` — confirmed
vs `shiftBodyGraph_deg_two`, `Operations.lean:1710`; a paired/companion object only relocates the
homelessness); (B) KT §6.4.2 read line-by-line confirms (6.66)'s ±r is a *family of `d−1` independent
single-body facts* transported by the ONE whole-relabel row correspondence (6.62) — verbatim (6.52)
"this dependency will play a key role", (6.63)→(6.64) adds it ONCE, (6.66) is one (6.44) per candidate
at the single degree-2 body `vᵢ` — there is **no per-body chain in KT**; (C) the abandoned machinery
(`bottomTag_foldr`, the §(o″) single-step, `redundancy_panel_carry`) has **zero live consumers** and
`chainData_relabel_arm`/the T-W9a fold are unbuilt scaffolding, so abandoning the per-body chain orphans
no live obligation (no sorries in CaseIII).
- **OPEN FACT sharpened (the second read's (D)).** The genuine-row arm is a buildable leaf *conditional
  on* one concretely-named new obligation, NOT a trivial reuse of the two landed lemmas: the
  **`shiftPerm`-fixed-point / seed-extensor-coincidence identity for non-chain edges** — that
  `shiftPerm i` fixes every non-chain edge's endpoints so the shifted seed `qᵢ = q₁∘ρᵢ` reproduces
  `q₁`'s extensors there (KT (6.55)/(6.56)), the *whole-cycle* analogue of d=3 M₃'s single-swap
  `hends₃_off` off-`{e_a,e_b,e_c}` extensor coincidence. The T-W9a chain deliberately keeps `ends`/`q`
  FIXED (`shiftBodyFramework_htrans` closes by `le_refl`), so it does **not** supply this seed-change
  reasoning — it is the genuinely-new piece the OPEN-FACT recon must write before any build.
- **Nuance (safe direction).** `candidateRow_ac_eq_neg` (`Claim612.lean`, its own home) is used term-level
  ONLY inside `redundancy_panel_carry` — but the re-route's block arm still needs eq. (6.44)/G4d-i, so it
  will most likely be **re-consumed** by the new arm; re-check at the arm build rather than delete it
  blindly (fewer deletions than the orphan list claims — never an orphaned obligation).

**(G) OPEN-FACT PAIR RECON — the (F) OPEN FACT DOES NOT CLOSE as stated; a fix-fork for adjudication (two
independent read-only opus recons, 2026-06-19).** Run as a robustness pair (user-requested) on the crux.
Both reads **converged** on a refutation neither §(o‴) nor (F) caught, and **diverged** on the fix.
- **CONVERGED REFUTATION (coordinator-verified):** the (d)/(F)-pinned transport `funLeft (shiftPerm i)`
  is the **WRONG DIRECTION for `i ≥ 3`**. `shiftPerm i` is **not an involution** for `i≥3`
  (machine-checked: `formPerm[v₁v₂v₃]` applied twice to `v₂` = `v₁ ≠ v₂`). By `hingeRow_funLeft_dualMap`
  (forward `(u,v)↦(ρu,ρv)`, coordinator-confirmed `Basic.lean:551`), a genuine base row `hingeRow x y r`
  (`r ⊥ C(q x, q y)`) maps to `hingeRow (ρx)(ρy) r`, whose candidate extensor at seed `qᵢ=q∘ρ` reads
  `C(q(ρ²x), q(ρ²y))` — equal to `C(q x, q y)` **only if `ρ²` fixes**, i.e. only for an involution. So
  the annihilation does NOT transport for the cycle; the seed-coincidence over-shifts to `ρ²`. **d=3 M₃
  closes ONLY because `shiftPerm 2 = swap a v` is an involution** (`ρ²=id`), which **masks** the
  direction — the bug is invisible at `d=3`. KT (6.62)/(6.59) state the genuine correspondence with a
  one-step-DOWN shift (candidate `vⱼ₋₁vⱼ ⇔ base vⱼvⱼ₊₁`), i.e. inherently `ρ⁻¹`. Building the forward
  signature would be the **5th mis-pin**. (Traced concretely at `i=3,4` by both reads; the over-shift is
  not an `i=3` artifact.)
- **DIVERGED FIX — the fork to adjudicate:**
  - **Fix A (Recon A) — CHAIN-2c-ii leaf, *invert the relabel*.** Use `(shiftPerm i)⁻¹` for the
    `hwmem` transport + build a NEW **inverse-cycle action-lemma block** (`shiftPerm_inv_apply_interior`
    / `_inv_vtx_one` wrap / `_inv_apply_off` / the `shiftEdgePerm`-inverse companions — quick `Fin`/
    `formPerm` consequences of the forward lemmas) + the whole-cycle selector bookkeeping. Est. **~3–4
    commits.** **Caveat (Recon A's own gating flag):** the landed T-W9a is oriented *candidate→base*
    while the candidate-`i` `hρGv` slot needs *base→candidate* — the SAME direction tension may sit on
    the "done" candidate-row half, possibly forcing T-W9a to be re-applied contravariantly. Reconcile the
    T-W9a orientation against the `hρGv` slot BEFORE any build (Recon A calls this "the true gating
    question").
  - **Fix B (Recon B) — producer-reshape, *re-seed per-`i`*.** Don't transport the shared base `w` by a
    relabel at all (for the genuine arm): invoke the W6b producer
    (`exists_candidateRow_bottomRows_of_rigidOn`, `Candidate.lean:390`) **directly on the candidate-`i`
    split `(Gᵢ, qᵢ)`** at its own seed `qᵢ=q∘ρᵢ`. By KT (6.55) each `(Gᵢ,qᵢ)` is "exactly the same
    framework as `(G₁,q₁)`", so its bottom family `wᵢ` is genuine in its own split **by construction** —
    no row-relabel / seed-coincidence needed for the genuine arm; only the redundant `±r` block (one
    (6.44)/G4d-i at `vᵢ`) transports. **Caveats:** (i) confirm W6b's output type re-seeds at `qᵢ` keeping
    the rank/independence counts (`hwcard`/`hw`) `case_III_arm_realization` needs; (ii) **interaction
    with the locked route β** — §(n) pinned "ONE base, ONE W6b call"; a per-`i` W6b invocation may
    tension with that lock (a user-adjudicated decision), so this fix is not purely a coordinator call.
- **Verdict status:** the forward-direction pin of (d)/(F) is **WITHDRAWN** (do NOT build the forward
  `chainData_relabel_hwmem`). The re-route's *core* (per-body fold dead; whole-relabel/per-`i` is KT's
  structure; (A)/(B)/(C) of (F)) **stands** — only the *transport direction/shape* is the open fork.
  This is a **design fork for user adjudication** (Fix B touches the locked route β + the producer; Fix A
  touches the "done" T-W9a half) — surfaced 2026-06-19; not a coordinator-unilateral pick.

---

#### (o‴)(H) FIX-FORK ADJUDICATION — VERDICT: corrected Fix A (inverted relabel, shared `ρ₀`). Fix B is INFEASIBLE (2026-06-19)

> **This settles the §(o‴)(G) fork.** Docs-only design-pass, user-steered (follow KT as closely as
> possible; tear up wrong-direction landed work; take a truly-obvious simplification if one exists).
> Clause-(i): every load-bearing claim verified against the **landed `def`/`theorem` bodies** (file:line
> below) via reads + lean-lsp; clause-(ii) source: KT §6.4.2 pp. 693–698 (pdf 46–51, offset +646) read
> **verbatim** end-to-end, eqs. (6.46)–(6.67). **VERDICT: settle on the corrected Fix A** (invert the
> relabel to `(shiftPerm i)⁻¹`, keep the shared `ρ₀`). **Fix B (re-seed W6b per-`i`) is genuinely
> infeasible** — it breaks KT's single-`r`/single-discriminator argument, the same fundamental obstruction
> that already rejected §(o′) route A (§(o″)(1)). The likely-obvious simplification (reuse
> `chainData_split_realization` per-`i`) **does not hold** for the same reason.

**(H.1) What KT actually does — the deciding lines (clause ii).** KT §6.4.2 settles the math direction
*against* the user's a-priori "works in each candidate's own framework" reading, and *for* a
single-base relabel-transport:

- **(6.55), p.694 — the SETUP (the "same framework" the user cited):** the candidate framework
  `(Gᵢ, qᵢ)` for `2≤i≤d−1` is "**exactly the same framework as `(G₁,q₁)`**" with `ΠGi,qi(u) =
  ΠG1,q1(ρᵢ(u))`, and (6.56) `qᵢ(uw) = q₁(ρᵢ(u)ρᵢ(w))` — i.e. `qᵢ` is the base seed `q₁`
  **precomposed with `ρᵢ`** (`qᵢ = q₁∘ρᵢ`). This is the SETUP that justifies the substitution (6.59); it
  is NOT a fresh independent realization.
- **(6.60)→(6.64), pp.696–697 — the ACTUAL rank machinery (the deciding lines):** KT works with
  `R(G,pᵢ)` (the FULL graph `G` at candidate placement `pᵢ`), and by column ops + substituting (6.59)
  converts it to (6.61) whose bottom block "**contains `R(G₁,q₁)` as its submatrix**" — *"where we used
  the following **row correspondence** between `R(G,pᵢ;E∖{vᵢvᵢ₊₁},V∖{vᵢ})` and `R(G₁,q₁)` derived from
  (6.59)"* — **(6.62)**: candidate `vⱼ₋₁vⱼ ⇐⇒ base `vⱼvⱼ₊₁`** for `2≤j≤i` (and `v₀v₁ ⇐⇒ v₀v₂`,
  `e ⇐⇒ e` else). **So KT's rank bookkeeping transports the SINGLE base matrix `R(G₁,q₁)` into each
  candidate via the relabel `ρᵢ` — the (6.62) row correspondence IS that relabel-transport.** The
  candidate edge index is **one less** than the base edge index (`j−1 ⇐⇒ j`), i.e. the correspondence is
  inherently `ρ⁻¹` (one-step-DOWN).
- **(6.52)+(6.66), pp.693/698 — ONE redundancy, the `±r` chain:** `r := ∑ⱼ λ(v₀v₂)ⱼ rⱼ(q(v₀v₂))` is
  defined **once** off `(G₁,q₁)`; (6.66) is the *family* of `d−1` independent one-shot (6.44) facts
  `∑ⱼ λ(vᵢvᵢ₊₁)ⱼ rⱼ(q(vᵢvᵢ₊₁)) = ±r` (one per candidate, at the single degree-2 body `vᵢ`).
- **(6.65)–(6.67), p.698 — the SINGLE-`r` discriminator (the load-bearing argument):** "`Mᵢ` does not
  have full rank **iff `r` is in the orthogonal complement of `C(Lᵢ)`**" — for the **one shared `r`**,
  tested against EVERY candidate's panel-meet `C(Lᵢ)`. None of `M₀…M_{d−1}` full-rank iff the **single**
  `r ⊥ ⋃ᵢ⋃_{Lᵢ⊂Πᵢ}C(Lᵢ)`, whose span is `D`-dim by Lemma 2.1 — so `r≠0` forces some `Mᵢ` full-rank.
  **KT's full-rank existence rests on ONE functional `r` against all panels; this is irreducible.**

**Verdict on the user's a-priori read:** KT's *setup* (6.55) works in each candidate's framework, but
KT's *rank argument* (6.60)–(6.67) relabel-transports the single base `R(G₁,q₁)` (via (6.62)) and uses
ONE shared `r`. The faithful Lean is "ONE base, ONE `ρ₀=r`, relabel-transport into each candidate, ONE
discriminator over all panels" — exactly the landed d=3 dispatch's shape (verified H.2), NOT a per-`i`
re-seed.

**(H.2) The landed-body facts that decide it (clause i, file:line).**
1. **The producer supplies ONLY the `v₁`-split realization** (`case_III_hsplit_producer_all_k`,
   `Arms.lean:828–857`): it extracts the chain, builds **one** split `G.splitOff v a b e₀` (at `v=v₁`),
   pulls its generic realization from the IH **once** (`:854`), feeds it to `hcand`. **Per-`i` split
   realizations `(Gᵢ,qᵢ)` for `i≥2` are NOT produced** — Fix B would have to manufacture them, and the
   only route is relabel-transport of the `v₁`-split (the over-shift problem) or a fresh IH pull on
   `G.splitOff vᵢ…` (a DIFFERENT graph, no guarantee it equals `(G₁,q₁)`-relabelled without transport).
2. **The d=3 dispatch shares ONE `ρ₀` across ALL arms** (`case_III_candidate_dispatch`,
   `Realization.lean:404` one W6b → `ρ₀`; `:439–441` one discriminator on `ρ₀`; `:495` `fin_cases u`;
   `:501/:513/:588` M₁/M₂/M₃ all consume the **same** `ρ₀`/`w`, M₃ negated to `−ρ₀`). It calls
   `case_III_arm_realization` DIRECTLY with the shared `ρ₀` — it **never** calls
   `chainData_split_realization`.
3. **`chainData_split_realization` (2a-ii, the per-`i` arm = the prompt's "obvious simplification") has
   ZERO live callers** (grep: mentioned only in docstrings) and its `htrans` slot (`Realization.lean:961–
   970`) is quantified over candidate `i`'s **OWN** `ρᵢ` — it runs its own `chainData_split_w6b_gates`
   at the per-`i` split (`:1005–1007`), producing an independent `ρᵢ`.
4. **The W6b producer re-seeds at any `(Gab,Gv,ends,q)`** (`exists_candidateRow_bottomRows_of_rigidOn`,
   `Candidate.lean:390`): `q` is a free parameter; its output `(ρ,w)` is genuine in `Gv`'s rows. So Fix B
   *can* mechanically re-seed — but `ρ` is a choice-on-choice existential (`Candidate.lean:421/434`,
   `Submodule.mem_map` + the triple-`∃` of `exists_redundant_panelRow_ab_lam_of_rigidOn`), with **no
   provable relationship to the discriminator's shared `ρ₀`** (§(o″)(1), re-verified).
5. **Both d=3 relabel engines rely on the swap being an involution:** `rigidityRows_ofNormals_relabel`
   (`Relabel.lean:350`, `hρρ : ρ∘ρ = id`) and the W9b `case_III_bottom_relabel` (`Relabel.lean:1052`,
   forward `funLeft (swap a v)`). The cycle `shiftPerm i` is **not an involution for `i≥3`**
   (`shiftPerm_apply_interior`/`_vtx_top`, `Operations.lean:1485/1499`: `vⱼ↦vⱼ₊₁`, `vᵢ↦v₁`), so the
   forward transport over-shifts the seed to `ρ²` (§(o‴)(G), coordinator-verified vs
   `hingeRow_funLeft_dualMap`, the forward `(u,v)↦(ρu,ρv)`, `Basic.lean:549`).

**(H.3) Why Fix B is INFEASIBLE — the irreducible obstruction.** Fix B re-seeds W6b on `(Gᵢ,qᵢ)` to get
`wᵢ`, `ρᵢ` genuine in `Gᵢ`'s rows. Feasibility of the *re-seed itself* is fine (H.2.4). But the genuine
arm closer needs an `htrans` (transversal gate) for the functional it actually uses — `ρᵢ` — while the
discriminator picks its panel `u` off the **shared `ρ₀`** (the only way KT's single-`r`-against-all-panels
existence argument runs, H.1). There is **no bridge `ρᵢ ↔ ρ₀`** (H.2.3/H.2.4 — independent existentials,
KT's (6.66) `±r` identity is between *abstract sums*, not the Lean `Classical.choice` witnesses). Two
escape attempts, both fail:
- *Per-`i` discriminator (run the discriminator off `ρᵢ`):* finds SOME panel `uᵢ` for `ρᵢ`, but to close
  candidate `i` you need `uᵢ = i` (the discriminator's panel must BE this candidate's). The discriminator
  returns an arbitrary panel; the `uᵢ=i` match is exactly what fails. Worse, with `d` independent `ρᵢ`,
  KT's "ONE `r` can't annihilate the `D`-dim span" existence is GONE — each `ρᵢ ⊥ C(Lᵢ)` is a separate
  condition with no disjunction forcing some `Mᵢ` full-rank.
- *Equate `ρᵢ = ±shiftPerm-image-of-ρ₀` (= §(o′) route A):* unprovable — choice-on-choice existentials
  (§(o″)(1), re-confirmed). This is precisely the route already REJECTED.
**So Fix B = §(o′) route A in disguise** ("re-seed / relabel-transport the split, then discharge the
per-`i` `htrans`"), already adjudicated REJECTED for the fundamental reason that KT's argument is
single-`r`. The user-flagged "obvious simplification" (reuse `chainData_split_realization`) is exactly
this dead route. **Not a coordinator-side punt: the obstruction is mathematical, in KT's structure.**

**(H.4) The corrected Fix A — the buildable path (KT-faithful, the (6.62) `ρ⁻¹` direction).** Keep the
shared `ρ₀`/`w` (KT's single `r`); transport the candidate's row-memberships into candidate `i`'s role by
the **inverse cycle** `(shiftPerm i)⁻¹`. The inversion fixes the over-shift: a base row `hingeRow x y r`
(`r⊥C(qx,qy)`) maps under `(funLeft (shiftPerm i)⁻¹).dualMap` to `hingeRow (ρ⁻¹x)(ρ⁻¹y) r`, whose
candidate extensor at seed `qᵢ=q∘ρᵢ` reads `C(q(ρ·ρ⁻¹x), q(ρ·ρ⁻¹y)) = C(qx,qy)` — the seed `ρ` and the
relabel `ρ⁻¹` **cancel**, so the annihilation transports. This matches KT (6.62)'s one-step-down
`vⱼ₋₁ ⇐⇒ vⱼ` correspondence exactly. The shared `ρ₀` stays the discriminator's functional (route β
preserved); only the *row-membership transport into candidate `i`'s role* inverts.

**(H.5) TEAR-UP list (orphaned by the verdict — confirm-and-delete; `git grep` to confirm zero live
callers at the deleting commit).**
- The per-body W9b chain (already orphaned per §(o‴), wrong granularity): `bottomTag_foldr_mem_rigidityRows`,
  the §(o″) single-step `funLeft_dualMap_bottomTag_mem_rigidityRows` (+ the seed-advance single-step
  `funLeft_dualMap_bottomTag_seedAdvance_mem_rigidityRows` + the `foldl` core
  `bottomTag_foldl_mem_rigidityRows`), `redundancy_panel_carry` (`Relabel.lean`) — **DELETED 2026-06-19**
  (build/lint-verified, §(I.1) confirm-and-delete). Still pending (docstring back-references / re-check
  coupling): `funLeft_dualMap_sub_acolumn_comp_mem_span_rigidityRows` (binary, superseded by `wstep`) and
  `ofNormals_relabel_perm` (2c-ii-β, route A) — orphaned (Fix A is row-span, M₃-style, not
  framework-transport).
- **`chainData_split_realization` + `chainData_split_w6b_gates`** (CHAIN-2a-ii / the per-`i` W6b half):
  zero live callers (H.2.3). They are the per-`i`-W6b architecture Fix B would have used; under Fix A the
  family runs off the **single** `v₁`-split via `chainData_split_w6b_gates`'s sibling (the shared-`ρ₀`
  W6b the dispatch already does inline). **Re-check at the CHAIN-2c-iii build:** if the dispatch reuses
  the `v₁`-split W6b extraction by calling `chainData_split_w6b_gates` at `i=1`, keep it; if it inlines
  (as the d=3 dispatch does), both become dead. **Do NOT blind-delete — verify at the dispatch build.**
- `candidateRow_ac_eq_neg` likely **re-consumed** by Fix A's `±r` block arm (G4d-i/eq.6.44) — re-check,
  don't delete (§(o‴)(F)).

**KEEP list (NOT orphaned).** The graph iso `splitOff_isLink_shiftRelabel_iff` (`Operations.lean:2122`)
+ `shiftEdgePerm` (the `hiso` supplier — but its INVERSE companions are the new block, H.6); G4d-i
`acolumn_mem_hingeRowBlock_of_span_rigidityRows` (the `±r` block arm); the W6b `ρ⊥C(q(ab))` gate; 2c-i
`exists_chainData_discriminator_pick` (the shared-`ρ₀` discriminator, route β); the `ChainData` record +
accessors. **The base→candidate W9a `_foldl` fold `shiftBodyListAsc_foldl_mem_span_rigidityRows`** +
**both G1 bridges `wstep_foldl_funLeft_eq` / `shiftPerm_eq_prod_map_swap_shiftBodyListAsc`** STAY — they
are the `hρGv` consumers (the (I.7) bare-row extraction is built ON them, not around them). **Orientation
reconciled by H.10:** the candidate→base `_foldr` fold `shiftBodyList_foldr_mem_span_rigidityRows` is
**orphaned-for-the-arm** (wrong direction, `wstep` non-invertible); the base→candidate `_foldl` fold is
the keeper. The bare-row extraction route (the H.7 "applied via its inverse" caveat, now resolved) is the
(I.7) residue-telescope decomposition — see §(o‴)(I.7).

**(H.6) Buildable-leaf decomposition (dependency order; exact intended signatures).**
1. **CHAIN-2c-ii-inv — the inverse-cycle action-lemma block** (`Operations.lean`, beside `shiftPerm`):
   `shiftPerm_inv_apply_interior` (`(shiftPerm i)⁻¹ (vtx (j+1)) = vtx j` for `1≤j<i`),
   `shiftPerm_inv_vtx_one` (`(shiftPerm i)⁻¹ (vtx 1) = vtx i`, the inverse wrap),
   `shiftPerm_inv_apply_off` (fixes `vtx 0` + the tail), and the `shiftEdgePerm`-inverse companions —
   all quick `Equiv.Perm.inv`/`formPerm` consequences of the landed forward lemmas (`Equiv.symm_apply_eq`
   + the forward action). Graph-free over `ChainData`. **First buildable leaf.**
2. **CHAIN-2c-ii-arm — `chainData_relabel_arm`** (`Relabel.lean`; the closer; d=3 M₃ = `i=2` instance):
   ```
   theorem PanelHingeFramework.chainData_relabel_arm
       [DecidableEq α] [DecidableEq β] [Finite α] [Finite β]
       {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (i : Fin cd.d) (hi : 1 < (i : ℕ))
       (hk1 : 1 ≤ k) (hn : Graph.bodyBarDim n = screwDim k)
       (hG : G.IsMinimalKDof n 0) (hV3 : 3 ≤ V(G).ncard) (hSimple : G.Simple)
       (hIH : <the all-k IH conjunction, the chainData_dispatch hIH shape>)
       -- the shared base W6b bundle from the v₁-split (ρ₀ ≠ 0, ρ₀ ⊥ C(base ab),
       --   hingeRow … ρ₀ ∈ span (base-rows), w-bundle):
       (base : <ρ₀ / w bundle at the v₁ split>)
       -- the transversal gate from 2c-i's discriminator at this candidate i (the htrans contribution,
       --   stated against the SHARED ρ₀ — route β preserved):
       (htrans : ρ₀ (panelSupportExtensor (q(vtx i.succ,·)) n') ≠ 0 ∧ LI ![q(vtx i.succ,·), n'])
       (hdef : G.deficiency n = 0) :
       PanelHingeFramework.HasGenericFullRankRealization k n G
   ```
   Body: instantiate `case_III_arm_realization` at the relabelled roles `(v,a,b) := (vtx i.castSucc,
   vtx i.succ, vtx (i−1).castSucc)`, seed `qρ = q ∘ (shiftPerm i)` (KT (6.56), `qᵢ = q₁∘ρᵢ`), `±ρ₀`,
   transporting the three slots: `hρGv` via the landed T-W9a (applied through the INVERSE, H.5/H.7);
   `hwmem` (the bottom family) via the **inverse-cycle** generalization of W9b `case_III_bottom_relabel`
   (the genuine-row arm by the graph-iso correspondence + `hingeRow_funLeft_dualMap` at `(shiftPerm i)⁻¹`,
   the block arm by G4d-i / one (6.44) at `vᵢ`); `hρe₀` via G4d-i. The genuinely-new piece beyond the
   inverse action lemmas is the **cycle generalization of the W9b genuine-row + bottom-block transport**
   (the d=3 single-swap `case_III_bottom_relabel` over the `(i−1)`-cycle). Honest estimate **~3–5
   commits** (inverse block + cycle-W9b + the arm). NO motive/IH/spine-carry change (C.3/C.6).
3. **CHAIN-2c-iii — `chainData_dispatch`** (`Realization.lean`; the assembly): one W6b at the `v₁` split
   (shared `ρ₀`/`w`), the panel-LI producer, one discriminator (2c-i `exists_chainData_discriminator_pick`),
   then **`Fin (k+1)`-case on `u`**: the `i=1`/`M₀` candidate is the direct `case_III_arm_realization`
   arm (shared `ρ₀`, as d=3 M₁), the interior `2≤i≤d−1` candidates are `chainData_relabel_arm`. Replaces
   `case_III_candidate_dispatch`; the d=3 line is the `k=2`/length-3 wrapper.
4. **CHAIN-5** consumes `chainData_dispatch` as the contract's `hdispatch` (signature frozen, C.3).

**(H.7) Route-β disposition (task 2β).** **Route β is PRESERVED, not touched.** Route β is about the
genericity/discriminator structure (ONE base `(G₁,q₁)`, ONE `ρ₀`, ONE discriminator, `fin_cases u`),
which Fix A keeps verbatim — the shared `ρ₀` IS the discriminator's functional, and the relabel transports
its row-memberships (not a second W6b). **It was Fix B that would have broken route β** (a per-`i` W6b =
a second functional `ρᵢ`, no shared discriminator) — another reason Fix B is rejected. The ONE caveat is
internal to Fix A, not route β: the landed T-W9a's candidate→base orientation must be reconciled with the
`hρGv` slot's base→candidate need (Recon A's "true gating question"); the inverse-cycle framing (H.4)
resolves it directionally, but the build must confirm T-W9a composes through its inverse. **Resolve in
the CHAIN-2c-ii-arm build, before pinning the arm signature.** No producer/route-β user-decision needed.

**(H.8) `d=3` zero-regression (task 3) — PRESERVED.** The reshape fires only for the interior cycle arm
`i≥3` (cycle length `i−1≥2`). At d=3 the only candidates are M₁ (`i=1`, direct), M₂ (`i=1` swapped), M₃
(`i=2`, cycle length 1 = single swap = involution = the landed `case_III_bottom_relabel`). So
`chainData_dispatch` at d=3 dispatches M₃ to the `i=2` instance of `chainData_relabel_arm`, whose cycle
is `shiftPerm 2 = (v₁v₂)` — a single swap, where `(shiftPerm 2)⁻¹ = shiftPerm 2` (involution), so Fix A's
inversion is a no-op and the arm reduces to the landed M₃ engine verbatim. **The current d=3 dispatch
`case_III_candidate_dispatch` stays green untouched until CHAIN-5/ENTRY reshape it into the `ChainData`
wrapper** (C.4); the reshape preserves it as a `k=2`/length-3 specialization (zero new linear algebra at
`i=2`). The d=3 line — the conjecture at `d=3`, GREEN — does not regress.

**(H.9) First concrete buildable leaf.** **CHAIN-2c-ii-inv** (H.6 leaf 1): the inverse-cycle action-lemma
block in `Operations.lean`. It is buildable now (all forward `shiftPerm`/`shiftEdgePerm` action lemmas
landed; the inverses are `Equiv.symm_apply_eq` rewrites of them), self-contained, graph-free, and
unblocks the arm. **Do NOT build `chainData_relabel_arm` until the H.10 base→candidate re-orientation is
done** — that is the one structural gating question, and it is exactly the kind of "mechanically
plausible" shape the 4× mis-pins were.

**(H.10) ADVERSARIAL VERIFICATION of (H) — Fix-B rejection CONFIRMED; corrected-Fix-A algebra CONFIRMED;
but H.5/H.7 "reuse T-W9a through its inverse" is REFUTED (read-only recon, opus, 2026-06-19).** An
independent reader told to refute (H) against KT verbatim + the landed bodies:
- **Fix-B rejection CONFIRMED sound.** KT's single-`r` existence (6.65–6.67) is irreducible; the W6b `ρ`
  is a genuine choice-on-choice (`Candidate.lean:435` `mem_map` preimage of the triple-`∃`
  `:309`), no provable bridge to `ρ₀`. The specific rescue — "construct `ρᵢ` as the relabel-image of
  `ρ₀`" — does NOT rescue Fix B: it IS corrected Fix A (reuse the shared `ρ₀`, transport memberships).
  Fix B *as defined* (re-seed W6b for an independent `ρᵢ`) stays dead.
- **Corrected-Fix-A seed-cancellation CONFIRMED** (lean-verified via `lean_multi_attempt`: with relabel
  `(shiftPerm i)⁻¹` + seed `qρ=q∘ρ`, `qρ(ρ⁻¹x)=q(x)`, goals `[]`). The d=3 involution case is its
  degenerate instance.
- **REFUTED — H.5/H.7's "apply the landed T-W9a through its inverse" does NOT close (structural, not a
  residual caveat).** The landed T-W9a (`shiftBodyList_foldr_mem_span_rigidityRows`, `:940`) and W9b fold
  (`bottomTag_foldr`, `:1273`) transport **candidate→base with the seed FIXED** (only the graph shrinks,
  `:827/:890`; relabel = forward `funLeft (shiftPerm i)`, `wstep_foldr_funLeft_eq:808`). The arm's
  `hρGv`/`hwmem` slots need **base→candidate with the seed jumping `q→qρ`** (as the d=3 M₃ arm
  `case_III_arm_realization_M3:1465` does: source `Fv=ofNormals(G−v) q` → target `Fva=ofNormals(G−a) qρ`,
  `:1627`). These are opposite, and **`wstep = (funLeft swap).dualMap − a-column` is NON-INVERTIBLE**
  (the a-column subtraction is rank-degrading, its purpose — d=3 W9a `:592–604`), so a span-membership
  implication `φ∈span(cand)→Tφ∈span(base)` does NOT yield its converse. You cannot "invert the fold." The
  involution masked this at d=3 exactly as it masked the forward `ρ²` over-shift.
- **Corrected build path (H.10):** re-author the transport **base→candidate directly** — source
  `F 0 = G−v₁` seed `q`, target `F(i−1) = G−vᵢ` seed `q∘shiftPerm i`, per-step relabel `(shiftPerm)⁻¹`
  head-peeled, the seed advancing one swap per step — the direct cycle generalization of the d=3 M₃
  single W9a/W9b step. **Reuse** the base→candidate single-step
  `funLeft_dualMap_sub_acolumn_mem_span_rigidityRows` (already the right orientation), re-folded in the
  opposite chain order. The **landed candidate→base T-W9a/W9b folds are orphaned *for the arm*** (they
  prove the converse implication — real work, now superseded for this purpose; add to the tear-up
  re-check). **The CHAIN-2c-ii-inv first leaf SURVIVES** (the `(shiftPerm)⁻¹` per-step relabels are still
  needed). **De-risk gate:** write the base→candidate single-step seed-advance lemma at `i=3` (cycle
  length 2, first non-involution case) and confirm it closes BEFORE pinning the arm / fold signature.
  No motive/IH/spine-carry change (the correction is internal to the arm's transport). d=3 zero-regression
  unaffected (H.8).

**(H.11) DE-RISK GATE + FOLD CORE LANDED, TOP STEP RESOLVED (2026-06-19).** The base→candidate single-step
gate `funLeft_dualMap_sub_acolumn_seedAdvance_mem_span_rigidityRows` and the abstract seed-advancing fold
core `wstep_foldl_mem_span_rigidityRows` (both `CaseIII/Relabel.lean`, axiom-clean) landed. **The
top-step worry (H.10's "build it separately" caveat) is resolved by generalizing the gate to a single
bound `s + 2 < cd.d`** (the phantom `i` parameter, used only in `omega`-bound proofs, was dropped). The
candidate-vertex top step `s = i−2` (moving `a = vtx i`) closes with the *identical* proof because the
interior candidates run `2 ≤ i ≤ d−1` — so `vᵢ` is itself an interior degree-2 chain vertex (`vtx i`,
`i < d`) reading the same `deg_two`/`isLink_edge`/`vtx_ne` accessors. Both interior (`s+2 < i`) and top
(`s+2 = i < d`) steps satisfy `s + 2 < d`, so the concrete fold instance discharges every step `s = 0 …
i−2` through the one gate; **no separate top-step lemma is needed.** NEXT = the concrete `ChainData`
seed-advancing instance feeding the core.

---

#### (o‴)(I) BUILD-PATH CONSOLIDATION — the `hwmem`-slot + Leaf-B path, re-verified against the landed bodies post-W9b-fold (2026-06-19)

> **Design-settle / recon pass, docs-only, 2026-06-19.** Consolidates the CURRENT build path for
> `chainData_relabel_arm`'s `hwmem` slot + the block-disjunct leaf (Leaf B) after the W9b single-step +
> `bottomTag_foldl` core landed (b6c780f / caee6ab). Clause-(i): every load-bearing claim verified
> against the **landed `def`/`theorem` bodies** (file:line below) via reads + `git grep`. **Net verdict:
> the landed W9b per-body chain (`bottomTag_foldl_mem_rigidityRows`, the W9b single-steps,
> `redundancy_panel_carry`) is OFF the critical path — it encodes the per-body block transport that
> §(o‴)(b)/(c)/(d)/(H) machine-refuted; it is a confirm-and-delete orphan (Q1). The arm's `hwmem` slot is
> the d=3 `case_III_bottom_relabel` per-member map (no fold), cycle-generalized to the whole `(shiftPerm
> i)⁻¹` relabel; the block disjunct is a SINGLE G4d-i at `vᵢ`, not a fold instantiation (Q2/Q3).**

**(I.0) The current callsite picture (the decisive `git grep`).** No arm/dispatch exists yet
(`chainData_relabel_arm`, `chainData_dispatch`, `chainData_relabel_hwmem`: zero decls in tree), so the
*entire* CHAIN-2c-ii fold stack is **unbuilt scaffolding with zero live consumers today** — including the
W9a concrete fold `shiftBodyListAsc_foldl_mem_span_rigidityRows`, not just the W9b pieces. The live
general-`d` critical path is still the d=3 wrapper: `Theorem55.lean:2635` → `case_III_candidate_dispatch`
(`Realization.lean:1218`) → `case_III_arm_realization`(M₁) / `_M2` / `_M3`, and M₃ discharges its `hwmem`
at `Relabel.lean:2264` by `intro j; … exact case_III_bottom_relabel … (hwmem j)` — a **per-member map over
`w`, NO fold of any kind**. So "is X on the critical path" must be read as the *prospective* question:
when `chainData_relabel_arm` is built per §(H.6)/§(H.10), will it consume X?

**(I.1) Q1 — `bottomTag_foldl_mem_rigidityRows` is OFF the critical path (a confirm-and-delete orphan).**
The body (`Relabel.lean:1866`) is exactly the abstract pure-relabel `List.reverseRec` `foldl` core the
prompt describes: it threads a generic `Tag : ℕ → Dual → Prop` one-step-up `Tag s ⇒ Tag (s+1)` under
bare swaps `(funLeft (swap bodies[s].2.1 bodies[s].1)).dualMap`, never opening a framework. It is sound
and axiom-clean — but it is the *engine for a per-body block-disjunct chain*, and that chain is the route
§(o‴)(b)/(c) machine-refuted. The refutation, re-confirmed against the landed single-step: the W9b
single-step `funLeft_dualMap_bottomTag_mem_rigidityRows` (`Relabel.lean:1632`) maps the input block tag
`hingeRow a b ρ'` to an OUTPUT block tag `hingeRow c v ρ'` (a `(c,v)`-block at the predecessor;
`:1650–1653`), AND maps a genuine-row-at-the-moving-body to a `(c,v)`-block too (`:1672–1678`, the `x=a`
branch). To *terminate* the carried block into a genuine row it needs the `e_b`-row of the target
framework (`:1601`, the `(ab)`-tag → genuine `e_b`-row branch) — which exists in d=3 M₃ only because `b`
is the OFF-chain neighbour so `e_b` survives `removeVertex a`. At the chain interior `e_b = edge(s+1)`
links the removed vertex and is graph-structurally cut (`shiftBodyGraph_deg_two`, machine-verified
§(o‴)(b)), so the per-step block residual `hingeRow vₛ₊₂ b ρ'` has **no home** — the chain cannot
terminate. The `foldl` core would faithfully *compose* the single-steps, but composing a chain that
cannot terminate produces nothing the arm can use. **Try-hard-to-refute outcome: I could not find a
consumer, and the structural argument says there cannot be one** — `git grep bottomTag_foldl` returns
ONLY its own def site + `notes/`. **b6c780f is dead infra** (the 5th-mis-pin-shape risk the prompt
flagged); it joins the §(H.5) tear-up list with `bottomTag_foldr_mem_rigidityRows` (`:1819`, the
converse-orientation sibling, also zero live callers), the two W9b single-steps
(`funLeft_dualMap_bottomTag_mem_rigidityRows` `:1632`, used only by
`funLeft_dualMap_bottomTag_seedAdvance_mem_rigidityRows` `:1739`, which is itself zero-consumer), and
`redundancy_panel_carry` (`:1922`, zero callers). **DELETED 2026-06-19** (the full 5-decl cluster
`funLeft_dualMap_bottomTag{,_seedAdvance}_mem_rigidityRows` + `bottomTag_{foldr,foldl}_mem_rigidityRows`
+ `redundancy_panel_carry`; build/lint-verified, ahead of the arm build per the §(H.5) discipline —
`git grep` zero callers, removed).
Caveat unchanged from §(H.5): `candidateRow_ac_eq_neg` (the eq.-(6.44) primitive, `Claim612.lean`, its
own home) is **kept** — Leaf B re-consumes it via G4d-i.

**(I.2) Q2 — Leaf B is a SINGLE direct G4d-i at `vᵢ`, NOT a `bottomTag_foldl` instantiation.** The block
disjunct is the whole-relabel image of `M₀`'s single redundant `(v₀v₂)i*`-row, which (6.66)/(6.44) reduce
to the single `±r` row at the degree-2 body `vᵢ` — ONE application of eq.~(6.44) at ONE body, exactly as
the d=3 Lemma-6.10 proof applies (6.44) once at the degree-2 body `a` (§(o‴)(a)/(d), KT p.698 verbatim).
The landed G4d-i primitive is `acolumn_mem_hingeRowBlock_of_span_rigidityRows`
(`Relabel.lean`, consumed already at `case_III_arm_realization_M3:2138` to get `ρ ⊥ C(q(ac))`). **Leaf B
is therefore not a separate fold-bearing lemma at all** — it is the block-arm branch *inside*
`chainData_relabel_arm`'s `hwmem` proof: for the bottom-family member tagged `w j = hingeRow a b ρ'`
(`ρ' ⊥ C(base ab)`), produce `(funLeft (shiftPerm i)⁻¹).dualMap (w j) = hingeRow (ρ⁻¹a)(ρ⁻¹b) ρ'` (via
`hingeRow_funLeft_dualMap`, `Basic.lean:549`) and discharge its annihilation against the candidate-`i`
`±r` panel by the single (6.44) at `vᵢ` (`candidateRow_ac_eq_neg` / G4d-i). Concretely this is the
**inverse-cycle generalization of the d=3 single-swap block branch** `case_III_bottom_relabel:1596–1611`
(the `(ab)`-tag branch), where the single swap `(a v)` is replaced by `(shiftPerm i)⁻¹` — but since the
block branch touches only the two bodies `a = vtx i` and its neighbours (the swap acts non-trivially only
near `vᵢ`), it does NOT chain over the `i−1` cycle bodies. **Signature:** Leaf B is not minted as a
standalone decl; it is the `Or.inr` arm of `chainData_relabel_arm`'s `hwmem` case-split, ~the size of
`case_III_bottom_relabel:1596–1611` plus the inverse-swap evaluation bookkeeping (`shiftPerm_inv_*`
action lemmas, the §(H.6) leaf-1 block — which **stays needed**, H.10). **UPDATE 2026-06-19: Leaf B
LANDED as a named abstract `(ρ,σ)` brick** `PanelHingeFramework.blockRow_relabel_perm` (`Relabel.lean`,
axiom-clean) — the recon-preferred named form, abstracted exactly like `rigidityRow_relabel_perm`: from
`hingeRow a b ρ'` (`ρ' ⊥ panelSupportExtensor (q₀ a)(q₀ b)`) plus a target edge `e_t` with
`Gt.IsLink e_t (ρ.symm a)(ρ.symm b)` and target support extensor `= panelSupportExtensor (q₀ a)(q₀ b)`,
conclude `(funLeft ρ.symm).dualMap (hingeRow a b ρ') ∈ (ofNormals Gt endsσρ qρ).rigidityRows`. A 4-line
proof. The arm consumes it (supplying `hlink`/`hsupp` from the `ChainData` accessors); the `(ab)`-edge
survival + the single eq.-(6.44) at `vᵢ` are how the caller discharges `e_t`/`hsupp`.

**(I.3) Q3 — the `hwmem` assembly: per-member `case_III_bottom_relabel`-shape, cycle-generalized; the
genuine-row arm via the inverse-relabel graph-iso, the block arm via Leaf-B's single G4d-i.** The slot
`case_III_arm_realization` (the engine, `Arms.lean:72`) demands is, per member `j`
(`Arms.lean:96–99`, verbatim):
```
hwmem : ∀ j, w j ∈ (ofNormals Gv ends q).toBodyHinge.rigidityRows ∨
  ∃ ρ', ρ' (panelSupportExtensor (q a) (q b)) = 0 ∧ w j = hingeRow a b ρ'
```
i.e. each bottom-family member is *either* a genuine `Gv`-row *or* an `(ab)`-block row. The arm
`chainData_relabel_arm` instantiates the engine at the relabelled roles (`(v,a,b) := (vtx i.castSucc,
vtx i.succ, vtx (i−1).castSucc)`, seed `qρ = q ∘ shiftPerm i`, shared `±ρ₀`; §(H.6) leaf-2), and its
`hwmem` proof is `intro j; <transport the disjunction of (hwmem₀ j)>` — the **cycle generalization of the
d=3 M₃ `hwmem` discharge** (`Relabel.lean:2264–2272`), where the shared base `w` is the v₁-split W6b
family and `hwmem₀ j` is its base disjunction. **The two disjuncts transport differently and neither is a
W9b fold:**
- **Genuine-row disjunct (`w j ∈ base-split rows`):** transported by the WHOLE inverse relabel
  `(funLeft (shiftPerm i)⁻¹).dualMap` as a graph-iso row correspondence (KT (6.62)) — a genuine base-row
  maps to a genuine candidate-`i` row via `splitOff_isLink_shiftRelabel_iff` (`Operations.lean:2122`,
  LANDED) + `hingeRow_funLeft_dualMap`, with the seed cancellation `qρ(ρ⁻¹x) = q(x)` (H.10
  lean-verified). This is the cycle generalization of `case_III_bottom_relabel`'s genuine-row branch
  (`:1499–1595`, the three-way `x=a`/`y=a`/neither split), NOT a span fold and NOT W9a. **Correction to
  the prompt's coordinator paraphrase + the Phase23b tracker's "Leaf-A finding":** the bottom-family
  *genuine-row* disjunct does **not** "ride the W9a span fold `shiftBodyListAsc_foldl…` verbatim". What
  rides W9a is the *candidate row* `hρGv` (the redundant `±r` row that enters as `hingeRow a b ρ ∈ span
  (G−vᵢ).rows`, a span member — §(o‴)(b) bullet 1, machine-verified). The bottom-family genuine-row
  disjunct is a *literal row membership* (not a span membership), and a pure relabel does NOT preserve
  genuine-span membership across the cycle (the W9b single-step sends a genuine-row-at-the-moving-body to
  a `(c,v)`-block, `:1672`), so it needs the **graph-iso row correspondence**, transported by the whole
  relabel at once — exactly as the d=3 M₃ genuine arm does (one swap), generalized to `(shiftPerm i)⁻¹`.
  The W9a span fold and the bottom-family genuine-row arm are DIFFERENT mechanisms on DIFFERENT objects;
  conflating them is a (harmless-but-misleading) tracker imprecision to fix. (The candidate-row half
  `hρGv` IS the W9a-fold consumer — `shiftBodyListAsc_foldl_mem_span_rigidityRows`, transporting a *span*
  membership; that fold stays, H.5 KEEP list.)
- **Block disjunct (`w j = hingeRow a b ρ'`):** Leaf B (I.2) — the single G4d-i at `vᵢ`.

So the `hwmem` assembly is **one per-member case-split, two non-fold arms** (graph-iso relabel +
single G4d-i), structurally the d=3 M₃ `case_III_bottom_relabel` lifted from a single swap to
`(shiftPerm i)⁻¹`. **No `bottomTag_foldl`, no `bottomTag` chain, no per-body block carry.** This reconciles
with §(H.6) leaf-2 ("`hwmem` via the inverse-cycle generalization of W9b `case_III_bottom_relabel`") and
§(H.10) (re-author base→candidate directly; the candidate→base folds are orphaned) — and it supersedes the
Phase23b *Hand-off*'s earlier "the W9b foldl core is the infra the block disjunct + the arm's pure-relabel
form need" reading: the block disjunct needs G4d-i (not the foldl core), and the genuine-row disjunct
needs the graph-iso relabel (not the foldl core). The W9b foldl core needs nothing.

**(I.4) MANDATE check — what is settled vs. what stays flagged.** Settled from the landed bodies: Q1
(orphan, deletable), Q2 (single G4d-i), Q3 (per-member two-non-fold-arm assembly). **STILL FLAGGED (the
§(o‴)(E)/(F)(D) open fact, un-discharged by this pass):** the genuine-row arm's *cycle generalization* of
`case_III_bottom_relabel:1499–1595` over `(shiftPerm i)⁻¹` + seed `qρ` is the genuinely-new piece, and
its difficulty is unknown until the seed/selector bookkeeping for the whole inverse relabel is written
(the `shiftPerm`-fixed-point / seed-extensor-coincidence identity for non-chain edges, §(F)(D)). This pass
does **not** build it and does **not** pin it past "it is the cycle generalization of the landed d=3
single-swap genuine arm" — that is exactly the kind of mechanically-plausible shape the 4× mis-pins were,
and the honest status is FLAG. **The §(H.6) leaf-1 CHAIN-2c-ii-inv (the inverse-cycle action lemmas) is
already LANDED** (`Operations.lean:1550–2110`, the 4 `shiftPerm_inv_*` + 7 `shiftEdgePerm_inv_*`), and as
of 2026-06-19 BOTH `hwmem` transports are landed as named abstract `(ρ,σ)` bricks: the genuine-row
`rigidityRow_relabel_perm` AND the block-disjunct `blockRow_relabel_perm` (this `(I.2)` Leaf B). So the
next build step is **`chainData_relabel_arm` itself** (§(H.6) leaf-2) — gated now only by the
arm-instantiation bookkeeping (wiring the two `hwmem` bricks + the W9a fold into the engine's slots at the
per-`i` roles), the genuinely-new transport math all landed. No motive/IH/spine-carry change (C.3/C.6);
route β + d=3 zero-regression preserved (the d=3 M₃ `i=2` cycle is the single-swap involution,
`(shiftPerm 2)⁻¹ = shiftPerm 2`).

**(I.5) CORRECTION — the (I.3)/(I.4) "genuine-row `hwmem` via the split-level graph-iso" reading is WRONG;
the genuine-row `hwmem` disjunct is the OPEN §6.4.2 crux (2026-06-19, a build BLOCKED + read-only recon-1,
source-verified; user-adjudicated → de-risk recon).** (I.3) said the genuine-row disjunct rides
`splitOff_isLink_shiftRelabel_iff` (split→split) and (I.4) closed "the next build step is the arm, gated
only by bookkeeping, the transport math all landed." **Both are wrong about the genuine-row `hwmem`
slot.** Source check of the three deciding signatures:
- The arm **engine** `case_III_arm_realization` (`Arms.lean:72`) binds BOTH `hwmem` (`:96`) and `hρGv`
  (`:91`) at `ofNormals Gv ends q` with `hleG : Gv ≤ G` (`:79`) and `v ∉ V(Gv)` (`:76`). Since
  `splitOff … e₀ ⋬ G` (the fresh `e₀`), `Gv` is **removeVertex-level**, never a split.
- The d=3 wiring `case_III_arm_realization_M3` (`:1870`) instantiates the engine with `Gv := G.removeVertex
  a` (`:1957`) and discharges `case hwmem` (`:2065`) by `case_III_bottom_relabel (hwmem j)` — i.e. the
  transport is `(G−v) → (G−a)`, **removeVertex→removeVertex**, by the **bespoke degree-2 argument**
  `case_III_bottom_relabel` (`:1600`, NOT a graph-iso, NOT `splitOff_isLink_shiftRelabel_iff`).
- `rigidityRow_chainData_relabel` (`:270`) / `rigidityRow_relabel_perm` (`:180`) transport split→split (both
  sides `ofNormals (G.splitOff … cd.e₀) …`). Wrong graph level for `hwmem`/`hρGv` ⇒ **orphaned-for-the-arm**
  (add to the H.5 confirm-and-delete list).

So the genuine-row `hwmem` disjunct = the **literal per-member removeVertex** cycle transport generalizing
`case_III_bottom_relabel:1499–1595` from a single swap to `(shiftPerm i)⁻¹` — exactly the §(I.4)/(F)(D)
"open fact, difficulty unknown", now the **live blocker**, NOT discharged. The removeVertex cycle
intertwiner is *false* (the bijection closes through `e₀`), and `hwmem` needs *literal* rows (not the W9a
span). The obstruction to settle (the de-risk recon's question): a pure relabel sends a
genuine-row-at-a-moving-body to a block (`:1672`); does a single inverse-cycle relabel keep the rest genuine
or spawn a homeless interior block (the (I.1) obstruction that killed the W9b fold)? Also corrected:
`hρGv` is **not closed** — its G1 seed/relabel bridges (`shiftPerm_eq_prod_map_swap_shiftBodyListAsc`,
`wstep_foldl_funLeft_eq`) are unbuilt (grep: zero def-sites); only the W9a fold core + concrete instance
landed. **Correctly slotted:** only the block disjunct `blockRow_relabel_perm` (I.2). Live verdict: the
de-risk recon settles tractability before any build leaf.

**(I.6) DE-RISK VERDICT — the genuine-row `hwmem` cycle transport is TRACTABLE via a per-row case analysis
(NOT a graph-iso); make-or-break confirmed favorable by `deg_two` (2026-06-19, recon-2 + coordinator
correction + source check).** A read-only de-risk recon (recon-2) returned TRACTABLE; coordinator scrutiny
**corrected its mechanism** and **confirmed its conclusion** against the landed bodies + KT pp.696–698:
- **No clean removeVertex graph-iso** (recon-2's proposed `removeVertex_isLink_shiftRelabel_iff` is
  mis-framed — recon-0/recon-1 were right). `splitOff_isLink` (`:620`): `G.splitOff v a b e₀ = (G−v) +
  {fresh e₀ : a—b}`. The split iso `splitOff_isLink_shiftRelabel_iff` (`:2576`) MIXES the fresh and genuine
  edges — `shiftEdgePerm` sends candidate `e₀ ↦ base edge i` (`:2028`) and candidate `edge 0 ↦ base e₀`
  (`:2018`) — so it does NOT restrict to a links-bijection of the removeVertex graphs.
- **The transport is a per-row case analysis** (the cycle generalization of `case_III_bottom_relabel:1600`,
  NOT an iso): a base `(G−v₁)`-row `hingeRow x y r` maps under `(shiftPerm i)⁻¹` by `hingeRow_funLeft_dualMap`
  to `hingeRow (ρ⁻¹x)(ρ⁻¹y) r`, and the case-split is:
  - **off-cycle endpoints** → fixed (`shiftPerm_inv_apply_off` + `seedShift_off_cycle`), genuine `(G−vᵢ)`-row;
  - **interior chain edge** `edge s` (`2≤s≤i−1`, link `vₛvₛ₊₁`) → `edge(s−1)` (link `vₛ₋₁vₛ`), a genuine
    `(G−vᵢ)` chain-edge row (KT (6.62) `vⱼ₋₁vⱼ ⇐⇒ vⱼvⱼ₊₁`; both endpoints `<i` survive `removeVertex vᵢ`);
  - **the wrap edge** `edge i` (link `vᵢvᵢ₊₁`) → `hingeRow vᵢ₋₁ vᵢ₊₁ r`, NOT a `G`-edge ⇒ the candidate
    `(a,b)=(vᵢ₊₁,vᵢ₋₁)` BLOCK disjunct (`vᵢ₊₁vᵢ₋₁` is the candidate's fresh `e₀`), discharged like
    `case_III_bottom_relabel`'s `x=a` block branch via the single (6.44) at `vᵢ`.
- **Make-or-break (no homeless interior block) — CONFIRMED.** A homeless row could only come from a
  *non-chain* edge at an interior cycle vertex `vₛ` (`2≤s≤i−1`); `deg_two` (`Operations.lean:1303–1308`,
  KT 6.46 `d_G(vₛ)=2`) says interior chain vertices carry ONLY their two chain edges, so no such edge
  exists. The §(o‴)(I.1) homeless-block obstruction was specific to the *step-by-step W9b fold* (which
  passed through intermediate `removeVertex vₛ₊₂` cuts); the single whole-cycle relabel has no steps.
- **d=3 zero-regression:** `i=2`, `shiftPerm 2 = (v₁v₂)` involution, the wrap edge `edge 2 (v₂v₃) ↦
  (v₁v₃)` = candidate `(a,b)=(v₃,v₁)` block — exactly the landed `case_III_bottom_relabel` M₃ behaviour.

**The leaf (corrected, replacing recon-2's graph-iso framing):** a per-member transport `chainData_bottom_relabel`
(working name, `Relabel.lean`) — the cycle generalization of `case_III_bottom_relabel`: takes the base
`(G−v₁)`-disjunction (`φ ∈ rows ∨ ∃ρ', (a,b)-block`) to the candidate `(G−vᵢ)`-disjunction under
`(funLeft (shiftPerm i)⁻¹).dualMap`, via the off-cycle/interior-chain/wrap case-split above. P≈2–3 (faithful
generalization of a landed lemma; the new bookkeeping is the cycle endpoint case-split + `deg_two`
discharge). Est. ~2 commits for the genuine-row disjunct; then `hρGv`'s G1 bridges + the arm wiring → 2c-iii.
No motive/IH/spine-carry change; route β + d=3 zero-regression preserved.

**Status update 2026-06-20.** All three abstract genuine-row branches are LANDED (`Relabel.lean`,
axiom-clean): off-cycle `rigidityRow_relabel_off_cycle`, wrap-edge→block `rigidityRow_relabel_to_block`,
and the interior-chain-edge moving branch `rigidityRow_relabel_to_genuine`. The interior brick is the
general moving form (free `f'`/`u'`/`w'`), so the off-cycle sibling now delegates to it at
`(u',w',f')=(u,w,f)` (a strict subsumption — same 5-line proof). The remaining build leaf is the
per-member assembly `chainData_bottom_relabel` itself (the `(shiftPerm i)⁻¹`-relabel dispatch of the
base disjunction through these branches, with the per-row `deg_two`/chain-edge case-split supplying the
`hsupp`/`hlinkGt`/`hu`/`hw` ingredients each branch consumes), then `hρGv`'s G1 bridges + the arm wiring.

**Sizing-BLOCKED findings (2026-06-20, the first assembly attempt; reverted clean).** The assembly was
drafted in full and elaborates, but is >1 sitting. **Builds clean:** the off-cycle + interior-chain
dispatch (through `rigidityRow_relabel_{off_cycle,to_genuine}`) and a unified `hsupp_of` support-extensor
coincidence helper (off-cycle `σf=f` and interior-moving `σf'=f` via `seedShift`/`apply_symm_apply`).
**The one genuine gap is the wrap case's orientation/sign.** The landed `rigidityRow_relabel_to_block`
demands a *strict* `hsupp : panelSupportExtensor (qρ a)(qρ b) = Q.supportExtensor f` and emits `ρ':=r`;
but `ends₀ (edge i)` records the wrap link `vᵢvᵢ₊₁` in either order, so for the swapped order the relabel
sends the base endpoints to `(b,a)` not `(a,b)`, needing `hingeRow b a r = hingeRow a b (-r)`
(`hingeRow_swap`) and `ρ':=-r`. This is exactly the d=3 `case_III_bottom_relabel` block branch's two
sub-cases (`Relabel.lean:1790–1821`: `ρ':=-r` vs `r`, annihilation via
`panelSupportExtensor_swap`+`map_neg`+`neg_zero`). **Decomposition (coordinator, 2026-06-20):** peel a
swapped-orientation sibling `rigidityRow_relabel_to_block_swap` (`(b,a)`-order, `ρ':=-r`) as its own
commit; then the assembly's wrap case is a 2-way `rcases` on the recorded orientation → apply one of the
two block bricks (mechanical). **Trap (cost the bulk of the BLOCKED session):** an inline `(by omega : T)`
type-ascription inside a `rw […]` bracket parse-cascades to a truncated file + a spurious
`⊢ ℕ`/`introN failed` that masquerades as an elaboration pathology — use a named `have he : … := by omega`
then `rw [he]`, and the §61 `m = m₂+2` destructure for the `Fin (i−1)`/`i−2` index arithmetic.

**LANDED 2026-06-20 — `chainData_bottom_relabel` (`Relabel.lean`, axiom-clean).** The assembly fit one
sitting after the de-risk. Two findings refining the BLOCKED decomposition: (1) the swapped-orientation
block brick `rigidityRow_relabel_to_block_swap` (peeled as planned) ultimately was **not** used — the
two pre-built block bricks demand a *literal* `hsupp : C(qρ a)(qρ b) = base.supportExtensor f`, but the
recorded `ends₀ f` orientation is **independent** of the endpoint-classification order from
`removeVertex_genuine_shiftRelabel`, so 2 of the 4 combinations have a `C(q x,q y)` vs
`C(q y,q x) = −C(q x,q y)` sign mismatch the literal `hsupp` cannot express. The fix: **inline the `±r`
wrap-block** (`refine Or.inr ⟨±r, ?_, ?_⟩` + one hoisted `hperp : r (C(q x,q y)) = 0` absorbing the
recorded orientation via `panelSupportExtensor_swap`/`map_neg`), exactly the d=3 `case_III_bottom_relabel`
`±r` body. (2) A **new `whnf` trap**: `refine`-ing a relabel brick with implicit seed `qρ`/endpoints
`a,b` into the heavy `ofNormals (removeVertex …)` disjunction goal triggers a higher-order-unif `whnf`
timeout — pin them explicit (→ TACTICS-QUIRKS §38). The wrap-block was discharged by inlining, not by
the swap brick. Two arm-supplied recording hyps surfaced: `hrec` + `he₀rec` (the latter records the base
fresh edge `ends₀ e₀ = (vtx 2, vtx 0)`, needed for the base-block→`edge 0` `blockRow_relabel_perm` arm).
NEXT = `hρGv` G1 bridges + the arm wiring (`notes/Phase23b.md` *Hand-off*).

#### (o‴)(I.7) `hρGv` DESIGN-PASS — the bare-row extraction decomposition (recon-before-build, 2026-06-20)

> **Design-pass, docs-only, 2026-06-20.** Decomposes the arm wiring's `hρGv` slot — the "bare-row
> extraction" repackaging the landed W9a span fold back into the engine's *literal* `hingeRow a b ρ`
> slot — into buildable leaves with exact signatures. Clause-(i): every load-bearing claim re-verified
> against the **landed `def`/`theorem` bodies** (file:line below). Clause-(ii): one honest open decision
> is named (the residue identification's selector/`hsupp` bookkeeping), pinned to a buildable leaf, not
> forced.

**(I.7.0) What the two sides actually are (source-verified, file:line).** The engine's slot
(`case_III_arm_realization`, `Arms.lean:91`) is the **literal row** `hingeRow a b ρ ∈ span (ofNormals Gv
ends q).rigidityRows` at `Gv = G − vᵢ`, the arm's seed `qρ`, the candidate-`i` roles `(a,b,ρ)`. The
landed W9a fold (`shiftBodyListAsc_foldl_mem_span_rigidityRows`, `Relabel.lean:1752`) concludes
`(shiftBodyListAsc i).foldl (wstep) φ ∈ span (shiftBodyFrameworkAsc (i−1) ends q).rigidityRows`
**given** `φ ∈ span (shiftBodyFrameworkAsc 0 ends q).rigidityRows`. Reading the two endpoints:
- `shiftBodyFrameworkAsc 0 ends q = ofNormals (G − v₁) ends q` (`shiftBodyGraph 0 = G − v₁`, seed
  `shiftSeedAdv q 0 = q`; `Relabel.lean:1699`/`1683`) — the **base** removeVertex framework.
- `shiftBodyFrameworkAsc (i−1) ends q = ofNormals (G − vᵢ) ends (shiftSeedAdv q (i−1))`
  (`shiftBodyGraph (i−1) = G − vᵢ`, advanced seed) — the **candidate-`i`** removeVertex framework, the
  same graph level as the engine's `Gv`, with the seed-advance `Q (i−1) = q ∘ (the i−1 cycle swaps)`
  matching the arm's `qρ = q ∘ shiftPerm i.castSucc`.
**So the span level MATCHES** (clause-(i) confirmed by reading both `def` bodies, not name similarity):
both endpoints are removeVertex frameworks at the SAME graphs (`G − v₁` / `G − vᵢ`); the seed identity
`shiftSeedAdv q (i−1) = q ∘ shiftPerm i.castSucc` on the relevant slots is the seed-cancellation the
H.10 lean-verification already confirmed (`qρ(ρ⁻¹x) = q(x)`) and the bottom-relabel leaf already uses.
The hand-off's flagged worry "(2) confirm the spans are the same" is therefore **RESOLVED in the
favorable direction**: no span-equality mismatch leaf is needed.

**(I.7.1) The fold-vs-literal-row gap is REAL (the genuine crux, NOT spurious).** The W9a fold output
`(shiftBodyListAsc i).foldl wstep φ` is NOT the literal candidate row. Feed it the **base literal row**
`φ := hingeRow (vtx 0) (vtx 2) ρ₀` (the base `(v₀v₂)`-block redundancy `r` of KT (6.52), supplied by the
W6b gate as `hingeRow a b ρ₀ ∈ span (G − v₁) rows` — this is the engine's `hρGv` AT THE BASE, the d=3 M₃
input `hρGv`, `Relabel.lean:2344`). The fold output is, by the `wstep` def (`Relabel.lean:1237`,
`wstep v a c = (funLeft (swap a v)).dualMap − (screwDiff v c).dualMap ∘ (single a).dualMap`):
```
(relabel-only foldl) φ  −  Σ (a-column residues)   ∈ span (G − vᵢ) rows
```
where the **relabel-only foldl** is the bare `(funLeft swap).dualMap` foldl — exactly the LHS of the G1
bridge `wstep_foldl_funLeft_eq` (`Relabel.lean:1446`), which rewrites it to `(funLeft (shiftPerm
i.castSucc)⁻¹).dualMap φ = hingeRow (ρ⁻¹(vtx 0))(ρ⁻¹(vtx 2)) ρ₀` (via `hingeRow_funLeft_dualMap`,
`Basic.lean:549`) = the **literal candidate row** at the candidate roles; and the `Σ residues` is the
`i−1` accumulated a-column subtractions `hingeRow vₛ vₛ₊₂ (…)`, one per moved degree-2 body. So
`hρGv` = (literal candidate row) is the fold output **PLUS** the residue sum:
`literal = fold-output + Σ residues`, and the extraction needs `Σ residues ∈ span (G − vᵢ) rows` to add
back via `Submodule.add_mem` (or `sub_mem`).

**(I.7.2) This is EXACTLY the d=3 M₃ mechanism, with `i−1` residues instead of one (source-verified).**
The d=3 M₃ `hρGv` discharge (`case_III_arm_realization_M3`, `Relabel.lean:2437–2506`) is the `i=2`
instance — ONE residue. Reading it verbatim:
1. `hw9a := funLeft_dualMap_sub_acolumn_mem_span_rigidityRows … (φ := hingeRow a b ρ) hρGv` (`:2481`) —
   the **single-step** W9a at the base literal row, giving `(funLeft (a v)).dualMap (hingeRow a b ρ) −
   hingeRow v c (· ∘ single a) ∈ span Fva.rigidityRows`.
2. `rw [hingeRow_funLeft_dualMap, swap_apply_left, …, hingeRow_comp_single_tail hab]` (`:2490`) collapses
   it to `hingeRow v b ρ − hingeRow v c ρ ∈ span` — i.e. (relabelled literal row) − (the one residue).
3. `hvb_row : hingeRow v b ρ ∈ span Fva.rigidityRows` (`:2494–2504`) — the relabelled literal row IS a
   genuine `e_b`-row of `Fva` (built by `subset_span ⟨e_b, v, b, hlink, ρ, hperp, rfl⟩`, the `hperp`
   coming from the engine's `hρe₀` = `ρ ⊥ C(q(ab))`).
4. `Submodule.sub_mem _ hvb_row hw9a` then `sub_sub_cancel` (`:2505–2506`) extracts the residue
   `hingeRow v c ρ ∈ span`, which (after `hingeRow_swap`, `:2442`) is the engine's `hρGv` slot
   `hingeRow c v (−ρ)`.
**The general-`d` extraction is the `i−1`-residue generalization of steps 1–4:** the fold (I.7.1) is the
`i−1`-fold compose of step-1's single W9a; the bare-row extraction is the `i−1`-residue generalization of
steps 2–4. The hand-off's framing ("repackaging the span member back to the literal bottom row is the
unbuilt hard step") is CORRECT — and it is precisely a multi-residue `sub_mem`/`add_mem` telescope.

**(I.7.3) The decomposition — buildable leaves with signatures.** The cleanest route mirrors d=3 but
threads the residues through a fold-with-residue invariant. Two viable shapes; the recon recommends
**Route R (residue-tracking fold)** over **Route S (rewrite-then-extract)** because the landed W9a fold's
conclusion bundles relabel+residue inside `wstep`, so a post-hoc rewrite (Route S) would have to peel the
`wstep` foldl apart anyway.

- **LEAF-ρ1 — the residue-membership invariant** (`Relabel.lean`, the genuinely-new piece, P≈3). A fold
  lemma stating that the W9a `foldl` output **differs from the relabel-only `foldl` output by a span
  member**, i.e. for `φ ∈ span (shiftBodyFrameworkAsc 0)` the difference
  `(relabel-only foldl) φ − (wstep foldl) φ ∈ span (shiftBodyFrameworkAsc (i−1)).rigidityRows`.
  Equivalently (the form the arm wants): `(wstep foldl) φ + [Σ residues] = (relabel-only foldl) φ` with
  `Σ residues ∈ span (candidate rows)`. **Signature sketch** (working name
  `ChainData.shiftBodyListAsc_foldl_residue_mem` or fold it into a strengthened
  `…_foldl_mem_span_rigidityRows` conclusion):
  ```
  theorem _root_.Graph.ChainData.shiftBodyListAsc_foldl_relabel_sub_mem
      [DecidableEq α] {G} {n} (cd : G.ChainData n) (i : Fin cd.d)
      (ends) (q) (hrec : ∀ f x y, G.IsLink f x y → ends f = (x,y) ∨ ends f = (y,x))
      {φ} (hφ : φ ∈ span (cd.shiftBodyFrameworkAsc (s:=0) _ ends q).rigidityRows) :
      ((cd.shiftBodyListAsc i).foldl (fun T b => ((funLeft (swap b.2.1 b.1)).dualMap).comp T) id) φ
        - ((cd.shiftBodyListAsc i).foldl (fun T b => (wstep b.1 b.2.1 b.2.2).comp T) id) φ
      ∈ span (cd.shiftBodyFrameworkAsc (s := (i:ℕ)-1) _ ends q).rigidityRows
  ```
  **Proof shape:** the SAME `reverseRec` induction the two landed folds use
  (`wstep_foldl_mem_span_rigidityRows` / `wstep_foldl_funLeft_eq`), run jointly: at each
  `append_singleton` step the head residue is the single a-column term `hingeRow vₛ₊₁ vₛ₊₃ ((inner
  fold φ) ∘ single vₛ₊₂)`, which is a **genuine `(G − vₛ₊₂)`-chain row at the SURVIVING successor edge
  `edge (s+2)`** (link `vₛ₊₂—vₛ₊₃`, both `< i` so surviving `removeVertex vᵢ`; the `c`-vertex `vₛ₊₃` of
  the gate) with functional `(inner fold φ) ∘ single vₛ₊₂` lying in the hinge-row block by **G4d-i**
  `acolumn_mem_hingeRowBlock_of_span_rigidityRows` (`Relabel.lean:2209`) applied to the inner fold's span
  membership. The inductive residues compose by `Submodule.add_mem` over the chain (each lands in the
  top span `span (G − vᵢ)` by the landed forward chain inclusions). This is the multi-residue telescope;
  it is genuinely-new but every primitive it needs is landed (the two fold cores, G4d-i, the chain graph
  accessors `shiftBodyGraph_isLink_pred_edge`/`_deg_two`).
- **LEAF-ρ2 — the literal-row identification** (`Relabel.lean`, P≈2, the d=3 step-2/3 generalization).
  The relabel-only foldl output IS the literal candidate row: via the G1 bridges
  `wstep_foldl_funLeft_eq` + `shiftPerm_eq_prod_map_swap_shiftBodyListAsc` (both LANDED) the relabel-only
  foldl is `(funLeft (shiftPerm i.castSucc)⁻¹).dualMap`, and `hingeRow_funLeft_dualMap` evaluates it on
  `hingeRow (vtx 0)(vtx 2) ρ₀` to `hingeRow ((shiftPerm i)⁻¹ (vtx 0)) ((shiftPerm i)⁻¹ (vtx 2)) ρ₀` =
  `hingeRow (candidate a)(candidate b) ρ₀` (the arm's roles, via the `shiftPerm_inv_*` action lemmas,
  LANDED `Operations.lean:1550–2110`). This is a rewrite chain, no new induction.
- **LEAF-ρ3 — the `hρGv` assembly** (inline in `chainData_relabel_arm`, P≈2). Combine: by LEAF-ρ1,
  `(relabel-only foldl) φ − (wstep foldl) φ ∈ span`; by the landed W9a fold, `(wstep foldl) φ ∈ span`;
  so by `Submodule.sub_mem`/`add_mem` the relabel-only foldl output ∈ span; by LEAF-ρ2 that output is the
  literal candidate row `hingeRow a b ρ₀` — which is exactly the engine's `hρGv` slot. (The d=3 M₃
  collapses ρ1+ρ2+ρ3 into the ~25-line `case hρGv` block; the general-`d` arm spends them as the three
  leaves above because the residue count is `i−1`, not 1.)

**(I.7.4) Clause-(ii) — the ONE honest open decision, pinned to a leaf (not forced).** LEAF-ρ1's residue
identification needs, at each step `s`, that the a-column residue `hingeRow vₛ₊₁ vₛ₊₃ (ψ ∘ single
vₛ₊₂)` (for `ψ` = the inner fold output, a span member of `span (G − vₛ₊₂) rows`) lands in
`span (G − vᵢ) rows` — i.e. it is a genuine row of the FINAL candidate framework, not merely of the
intermediate `G − vₛ₊₂`. The d=3 case has one residue at the final framework, so the question is vacuous;
at general `d` the intermediate residues must be transported UP the chain to the top span. **Two ways
this closes, the choice deferred to the LEAF-ρ1 build:** (a) the residue at step `s` is genuinely a
`(G − vᵢ) rows` member directly (the surviving successor edge `edge (s+2)` and both its endpoints
`vₛ₊₂, vₛ₊₃` survive `removeVertex vᵢ` for `s + 2 < i`, so the residue's underlying link is a genuine
`G − vᵢ` link and the residue is a genuine row of the TOP framework on the advanced seed — the favorable
case, likely, by the same `deg_two`/`shiftBodyGraph_isLink_pred_edge` reasoning that makes the (I.6)
genuine-row `hwmem` branches work); or (b) if the seed/selector at the intermediate vs. top framework do
not coincide on the residue's edge, the residue rides the **already-landed forward chain inclusion**
(`shiftBodyFramework_htrans` analogue) up to the top. **This is the genuine unknown** (the difficulty of
LEAF-ρ1's per-step `hsupp`/seed bookkeeping, the same flavor as the (F)(D) "open fact" the genuine-row
`hwmem` leaf ultimately resolved favorably). It is NOT a motive/IH/contract change (the residues are span
members of the existing candidate rows; no new carried hypothesis), NOT a span-level mismatch (I.7.0
resolved that), and NOT new math beyond the multi-residue telescope. **If LEAF-ρ1's build finds the
residue does NOT land in the top span by either (a) or (b)** — e.g. an intermediate residue at a
non-surviving edge — that would be a genuinely-new obstruction and the build should STOP and report (a
de-risk gate at `i=3`, the first 2-residue case, is the cheap check, mirroring the H.11 de-risk gate).

**(I.7.5) Leaf count + P-ratings (for sequencing).** Three leaves: **LEAF-ρ1** residue-membership
invariant (P≈3, the genuinely-new multi-residue telescope, ~1–2 commits; gate at `i=3` first) →
**LEAF-ρ2 — LANDED 2026-06-20** literal-row identification `shiftBodyListAsc_relabel_foldl_hingeRow`
via the landed G1 bridges + `hingeRow_funLeft_dualMap` (the `shiftPerm_inv_*` endpoint resolution
moves to the arm closer; the lemma is stated generically over `x y ρ₀`) → **LEAF-ρ3** the `hρGv`
assembly inline in the arm (P≈2, the `sub_mem`/`add_mem` combine). Total for `hρGv`: **~2–3 commits**,
the LEAF-ρ1 telescope the only real risk. The arm wiring `chainData_relabel_arm` then consumes `hwmem` (landed `chainData_bottom_relabel`),
`hρGv` (LEAF-ρ3), block (`blockRow_relabel_perm`), `hρe₀`/`htrans` (G4d-i + 2c-i) — a further ~1 commit
of slot-instantiation bookkeeping (the §38 explicit-seed pins, the `−ρ₀` shared functional). So the
hand-off's "multi-commit effort with real convergence risk" is confirmed: **~3–4 commits to the closed
arm**, the LEAF-ρ1 residue telescope being where to gate before committing the arm signature.

**(I.7.6) De-risk gate (do BEFORE pinning LEAF-ρ1's signature).** Write the 2-residue case `i = 3`
(cycle length 2, the first non-involution case — the d=3 `i=2` is the 1-residue involution that masks
multi-residue behaviour) and confirm `(relabel-only foldl) φ − (wstep foldl) φ ∈ span (G − v₃) rows`
closes with the two residues `hingeRow v₁ v₃ (…)` + `hingeRow v₂ v₄ (…)` both landing in the top span by
(I.7.4)(a). If it closes, pin LEAF-ρ1 at general `i` (the `reverseRec` lifts the 2-residue case the same
way W9a's fold core lifted its single step). This is the H.11-discipline de-risk: confirm the new piece
at the first honest case before committing the general signature.

**(I.7.7) KT-FAITHFULNESS RECON VERDICT + LEAF-ρ1 statement correction (read-only source-verification
recon, opus, 2026-06-20; coordinator-locked).** Prompted by the owner asking "are we grounding the routes
on what KT did?", an adversarial read-only recon tested the hypothesis *"`hρGv` = a single clean
`(shiftPerm i).symm` relabel (the span-level `chainData_bottom_relabel`), W9a fold orphan-able."*
**VERDICT: hypothesis REFUTED — the W9a residue machinery is KT-faithful and load-bearing for `hρGv`.**
- **KT grounding (PDF §6.4.1, verbatim):** KT does NOT transport `r` by a clean relabel. `ρᵢ` (6.54) acts
  on the columns/panels; the redundancy transport (6.63)–(6.66) is **fundamental row operations** — the
  degree-2-vertex `a`-column cancellation (eq 6.44/6.43, p.690–691: `r = −Σ λ_{(ac)j} rⱼ(q(ac))` from the
  degree-2-at-`a` dependence, "since only `ab` and `ac` are incident to `a`"), iterated `i−1` times along
  the cycle to `±r` (6.66, "in a manner similar to … (6.44)"). **That `a`-column cancellation IS the W9a
  `wstep` residue** (`wstep v a c = (funLeft (swap a v)).dualMap − (screwDiff v c).dualMap ∘ (single
  a).dualMap`). So the fold faithfully models KT; it is not a Lean detour.
- **Lean obstruction to the clean relabel (why `T` is not span-to-span):** the moving-body generator
  `hingeRow a c r` (the `e_c = ac` row, degree-2 at `a`) maps under the *bare* relabel to `hingeRow v c r`,
  which is NOT a genuine `(G − vᵢ)` row (in `G − a` the only `v–c` link is the candidate fresh edge `e₀`
  with support `C(q(vᵢ₋₁ vᵢ₊₁))`, which `r` need not annihilate). Only the `a`-column subtraction cancels
  it (read off the landed `span_induction` in `funLeft_dualMap_sub_acolumn_mem_span_rigidityRows`,
  `Relabel.lean:911–945`). No circularity; the deeper reason is that a bare `dualMap` is span-functorial
  only if it carries every generator into the target span, and it does not.
- **Why `hwmem` CAN be a clean relabel but `hρGv` cannot:** different panel level / generator set —
  `chainData_bottom_relabel` transports the bottom-row *family* (moving body `vᵢ` still present at degree 2
  in `G − v₁`, classified genuine-or-block, no orphan); the `hρGv` redundancy is the one object riding the
  `a`-column dependence.
- **I.7.4(a) SUPERSEDED.** Its "the residue is a `(G − vᵢ)` row at the surviving successor edge
  `edge(s+2)`" is WRONG: the `wstep` residue link is `v–c = vtx(s+1)–vtx(s+3)` (the freed slot `v` to `c`),
  a NON-edge, NOT `a–c = edge(s+2)`. The residue is not a standalone span member; it is extracted by the
  **d=3 M₃ template** (`case_III_arm_realization_M3`, `Relabel.lean:2437–2506`): feed the base redundancy
  through W9a (`hingeRow v b ρ − hingeRow v c ρ ∈ span`), identify `hingeRow v b ρ` as the genuine `e_b`-row
  (via `hρe₀`), then `sub_mem` + `sub_sub_cancel` extracts the engine's `hρGv` slot (= the residue
  `hingeRow v c ρ`). LEAF-ρ1 at general `d` is the `i−1`-step generalization of THIS, not an "add residues
  at surviving edges" telescope.
- **The row-306 build's "LEAF-ρ1 is false for general φ" was FLAWED reasoning** ("relabel-only foldl not a
  span member ⟹ the difference not a span member" is a non-sequitur — the difference can be a span member
  while neither term is). It correctly caught the I.7.4(a) link error and correctly refuted the
  clean-relabel collapse, but its conclusion that LEAF-ρ1 must be dropped does not follow. The route is the
  fold + the d=3 M₃ extraction structure.

**Next (hand-off):** build LEAF-ρ1 via the d=3 M₃ template generalized to `i−1` steps, doing the `i=3`
de-risk *for real* (the row-306 build bailed into the clean-relabel tangent before finishing it). The
clean-relabel route is CLOSED (refuted-against-KT); `T` still appears as LEAF-ρ2 (the literal-row
identification), which is correct and load-bearing, but does not discharge the slot alone.

**(I.7.8) De-risk SHARPENING (read-only analysis, opus session #16, 2026-06-20).** A read-only
re-derivation against the landed bodies pins the precise open question the `i=3` de-risk must answer —
this is the question rows 306/308 circled but never stated crisply, and what the next build must settle
FIRST. Reduce the slot: the engine `hρGv` is `hingeRow a b ρ ∈ span (ofNormals Gv ends qρ)` at the
**advanced-seed** candidate framework `Gv = G − vᵢ`, `qρ = Q(i−1)`; by LEAF-ρ2 the relabel-only fold of
the base redundancy `hingeRow (vtx 2)(vtx 0) ρ₀` IS that literal slot row `hingeRow ((shiftPerm)⁻¹(vtx 2))
((shiftPerm)⁻¹(vtx 0)) ρ₀ = hingeRow (vtx 1)(vtx 0) ρ₀` (`vtx 0` off-cycle/fixed, `vtx 2 ↦ vtx 1` under
the inverse cycle, link = the surviving `edge 0`). Since `(relabel-only fold) = (wstep fold) + Σ residues`
and `wstep fold (base redundancy) ∈ span Gv` is the **landed** `shiftBodyListAsc_foldl_mem_span_rigidityRows`,
**the entire `hρGv` slot reduces to: `Σ residues ∈ span (ofNormals (G−vᵢ) ends Q(i−1)).rigidityRows`,
equivalently `hingeRow (vtx 1)(vtx 0) ρ₀ ∈ span` (the literal slot row, the `edge 0` link).** TWO
exhaustive ways it closes, and the `i=3` de-risk must determine WHICH (they are mutually exclusive and the
choice changes the proof shape):
- **(A) genuine-row route (would make the residue machinery unnecessary for `hρGv`, contradicting the
  I.7.7 recon — so EXPECT this to FAIL):** `hingeRow (vtx 1)(vtx 0) ρ₀` is directly a genuine `edge 0` row
  of `F(i−1)`, i.e. `ρ₀ ⊥ C(Q(i−1)(vtx 1), Q(i−1)(vtx 0))`. The d=3 M₃ slot is the *residue* `hingeRow v c ρ`
  at the NON-edge `v–c`, NOT the genuine `e_b` row, so (A) is almost certainly false at the **advanced**
  seed (the seed-advance breaks the base `hρe₀` perpendicularity at `edge 0`); confirming it false at `i=3`
  is the cheap first check.
- **(B) difference route (the M₃ generalization, EXPECTED):** `Σ residues = (genuine row) − (wstep fold)`
  where the *genuine* row is the `e_b`-analogue (NOT the slot). **The unbuilt crux this exposes:** at `i=2`
  `Σ residues` is the SINGLE residue = the slot; at general `i` it is a SUM of `i−1` residues, but the
  engine slot `hingeRow a b ρ` is a SINGLE hinge row. So route (B) needs KT's eq. (6.66) collapse (the
  iterated degree-2 `a`-column cancellation folding the `i−1` residues to `±r`) realized in Lean — and it is
  NOT yet clear whether (i) the `wstep` fold already performs that collapse internally (so `wstep fold
  output` is itself congruent to a single row mod span and the difference is one residue), or (ii) the
  collapse is a separate post-hoc identity on `Σ residues`. **This (i)-vs-(ii) fork is the genuine
  convergence risk; the `i=3` 2-residue case decides it.** Do `i=3` FOR REAL: compute both residues
  explicitly (`hingeRow v₁ v₃ (…)` + `hingeRow v₂ v₄ (…)`, the latter relabelled by step 1's swap) and see
  whether they collapse to a single `hingeRow` at the slot's `(a,b)` link — if they do NOT, the engine slot
  shape may need re-examination (NOT a free motive change — flag to owner) before the arm can be built.

**(I.7.9) THE `i=3` DE-RISK DONE FOR REAL — VERDICT: NEITHER; engine `hρGv` slot wrong for `i ≥ 3`
(BLOCKED, flag-to-owner; Lean-verified, opus session #17, 2026-06-20).** The computation the prior
sessions circled is now done in Lean (two axiom-clean lemmas
`Graph.ChainData.i3_{wstep_foldl_base_redundancy,residue_collapse}_deRisk`, `Relabel.lean` tail; chain
`v0…v4`, base redundancy `φ = hingeRow v0 v2 ρ₀`, ascending bodies `[(v1,v2,v3),(v2,v3,v4)]`):
- **`W φ` (landed `wstep` foldl) `= hingeRow v0 v1 ρ₀ + hingeRow v1 v2 ρ₀ + hingeRow v2 v4 ρ₀`** —
  verified by `ext S; ring` against the `wstep_apply`/`hingeRow_funLeft_dualMap` unfold.
- **`R φ` (relabel-only foldl, LEAF-ρ2) `= hingeRow v0 v1 ρ₀`** — the literal `edge 0` row at the
  surviving link `v₀—v₁`.
- **`D φ = R φ − W φ = hingeRow v1 v2 (−ρ₀) + hingeRow v2 v4 (−ρ₀)` collapses (shared `v₂` telescopes) to
  the SINGLE row `hingeRow v1 v4 (−ρ₀)`** at link `v₁—v₄`.

So the residues **DO collapse to a single `hingeRow`** (the (B)(i)-vs-(B)(ii) fork's collapse question:
YES, internal to the fold — the (i) branch). **But at the WRONG link.** The engine slot
`case_III_arm_realization.hρGv` is the single row `hingeRow a b ρ` at candidate `i`'s fresh-edge pair
`(a,b) = (vᵢ₋₁, vᵢ₊₁)` (`splitOff vᵢ vᵢ₋₁ vᵢ₊₁ e₀`, link `vᵢ₋₁—vᵢ₊₁`; verified against `splitOff`
`Operations.lean:580`). At `i=3` the slot link is `v₂—v₄`, but the fold delivers neither it nor a genuine
candidate row:
- `R φ` (= `hingeRow v0 v1 ρ₀`) is at the surviving edge `v₀—v₁` — **not** the fresh-edge slot pair;
- `D φ` (the residue) collapses to `hingeRow v1 v4 (−ρ₀)` at **`v₁—v₄`** — a *non-edge*, and a
  *different* link from the slot's `v₂—v₄`.
- **`v₁—v₄ ≠ v₂—v₄`** (they differ in the first endpoint) — so the W9a-fold route produces a row the
  engine cannot consume at its `hρGv` slot.

**Why `i=2` (the d=3 `M₃` engine) hides this:** at `i=2`, `vᵢ₋₁ = v₁`, so the slot pair `vᵢ₋₁—vᵢ₊₁ =
v₁—v₃` *equals* the residue link `v₁—v₃` (single residue, the involution); all three links coincide. For
`i ≥ 3`, `vᵢ₋₁ = v₂ ≠ v₁`, and the residue's leading endpoint stays `v₁` (it is the cycle head, the base
removed vertex) while the slot's leading endpoint is `vᵢ₋₁` — they diverge. Exactly the §(o‴)(I.7.6)
warning ("the `i=2` involution masks multi-residue behaviour") realized.

**Verdict (flag-to-owner).** The engine `case_III_arm_realization`'s single-`hingeRow a b ρ` `hρGv` slot
is **not the right shape** for interior candidates `i ≥ 3` under the corrected-Fix-A W9a-fold route: the
fold delivers `hingeRow v1 v_{i+1} (−ρ₀)` (residue, link `v₁—v_{i+1}`, a non-edge) plus the separate
genuine row `R φ = hingeRow v0 v1 ρ₀`, neither matching the slot's fresh-edge pair `vᵢ₋₁—vᵢ₊₁`. This is
NOT a free motive change — it needs an owner decision on one of: (a) re-derive the engine slot's `(a,b)`
roles so the candidate slot link is `v₁—v_{i+1}` (does the candidate split's fresh edge actually connect
`v₁` and `vᵢ₊₁` rather than `vᵢ₋₁` and `vᵢ₊₁`? — re-check KT eq. (6.46)/(6.55) candidate-split endpoints
vs. the formalized `splitOff vᵢ vᵢ₋₁ vᵢ₊₁`), or (b) feed the engine the residue at `v₁—v_{i+1}` plus a
KT-(6.66)-style further reduction transporting it to the fresh-edge pair, or (c) a different engine slot
contract. The fold route + LEAF-ρ2 + the landed `chainData_bottom_relabel` all stand; the break is
purely the **slot-link mismatch** between what the fold produces and what `case_III_arm_realization.hρGv`
demands.

> **⚠ INTERPRETATION CORRECTED by §(I.7.10) (KT-source re-derivation, 2026-06-20).** The "engine slot
> wrong for `i ≥ 3` / flag-to-owner motive decision" verdict ABOVE **overstates**. The slot is RIGHT
> (KT-faithful); what is missing is the buildable KT-eq.-(6.66) fresh-edge telescope, NOT an engine/motive
> change. The `i=3` computation (the three links) is correct, but `D φ` at `v₁—v₄` was never the slot. Read
> §(I.7.10) before acting on the verdict above.

**(I.7.10) KT-SOURCE RE-DERIVATION VERDICT — option (b); engine slot KT-faithful, missing leaf is the
KT-(6.66) fresh-edge telescope (read-only recon, opus, 2026-06-20; coordinator-locked).** An adversarial
read-only recon against KT §6.4.2 (eqs 6.46–6.66) + the landed bodies tested the hypothesis "slot link is
`v₁—vᵢ₊₁` (option a)" and REFUTED it:
- **The `(a,b)=(vᵢ₊₁,vᵢ₋₁)` binding is KT-faithful, structurally forced — NOT a d=3 extrapolation.**
  `case_III_arm_realization` takes `hG_ea : G.IsLink e_a v a` / `hG_eb : G.IsLink e_b v b` (`Arms.lean:77`),
  so `a,b` ARE the split vertex `v`'s two genuine neighbors; for candidate `i` (split at `vᵢ`) they are
  `vᵢ₋₁, vᵢ₊₁`. KT eq. (6.57) places the free panel at `vᵢvᵢ₊₁`, the reproduced panel at `vᵢ₋₁vᵢ`,
  forcing engine-`a = vᵢ₊₁` (free) / engine-`b = vᵢ₋₁` (reproduced). The slot link `vᵢ₋₁—vᵢ₊₁` IS KT's
  `Mᵢ` redundant row `Σⱼ λ(vᵢvᵢ₊₁)ⱼ rⱼ(q(vᵢvᵢ₊₁))` (eq. 6.64), via the fresh edge `vᵢ₋₁vᵢ₊₁` carrying
  seed `q(vᵢvᵢ₊₁)` (eq. 6.56). So the slot is correct (option (c) rejected) and the binding is correct
  (option (a) rejected). [Coordinator-verified the `hG_ea/hG_eb` forcing against `Arms.lean:77`.]
- **The fold is KT-faithful only up to eqs. (6.62)+(6.63).** `R φ = hingeRow v₀ v₁ ρ₀` is exactly where
  KT (6.62) puts the transported redundancy (the `(v₀v₁)ᵢ∗` row) BEFORE the row operations; the `wstep`
  residues are KT (6.63)'s `a`-column subtractions; `W φ ∈ span` is landed. **What is genuinely missing is
  KT eq. (6.66)** — the iterated degree-2 `±r` identification carrying the `(v₀v₁)`-row form to the
  fresh-edge `Mᵢ` slot row `hingeRow vᵢ₊₁ vᵢ₋₁ ρ₀`. This is the "±r chain the design kept noting d=3
  collapses"; it is NOT absorbed into the fold.
- **VERDICT: option (b), buildable from landed pieces, NO engine/motive/IH/signature change.** The fix is
  inside the arm's `hρGv` discharge (LEAF-ρ1/ρ3): the M₃ three-step extraction (W9a image → identify the
  genuine reproduced-edge row at `vᵢ₋₁vᵢ` → `sub_mem`/`sub_sub_cancel` to peel the fresh-edge slot row),
  generalized over the `i−1` cycle bodies, with KT (6.66) realized as the iterated degree-2 telescope via
  `acolumn_mem_hingeRowBlock_of_span_rigidityRows` + `hingeRow_sub_hingeRow_eq` + `shiftPerm_inv_*` +
  `case_III_bottom_relabel` + the landed `W φ ∈ span`. ~3–5 commits; d=3 (`i=2`) = the landed M₃ verbatim
  (zero regression). The `i3_*_deRisk` lemmas (06f11bf) stay as the correct fold-output record (their
  "wrong link" is by design, not a defect).
- **RESIDUAL (honestly flagged, not certified):** the recon did not mechanize the `i−1`-step telescope;
  the residue-to-genuine-row identification (the degree-2 closure the M₃ `hρ_ac` step does, `Relabel.lean`
  ~`:2419–2430`) is asserted-buildable but unbuilt. **Re-targeted `i=3` de-risk:** confirm the fresh-edge
  row `hingeRow v₂ v₄ ρ₀` reaches `span(G−v₃)` via the iterated telescope (NOT "does `D φ` = slot" — it
  provably does not, by design). High confidence, KT-verbatim-grounded.
- **RE-TARGETED `i=3` DE-RISK GATE — PASSED 2026-06-20 (Lean-verified, axiom-clean,
  `i3_freshEdge_slot_mem_deRisk`, `Relabel.lean` tail).** The membership-algebra skeleton of the
  KT-(6.66) peel-off is now mechanized: from the landed `W φ = hingeRow v₀v₁ + hingeRow v₁v₂ +
  hingeRow v₂v₄ ρ₀ ∈ span` (`i3_wstep_foldl_base_redundancy_deRisk` value, `∈ span` by
  `shiftBodyListAsc_foldl_mem_span_rigidityRows`) and the two **genuine surviving** chain-edge rows
  `hingeRow v₀v₁ ρ₀` (`edge 0`) + `hingeRow v₁v₂ ρ₀` (`edge 1`) in `span` (both endpoints survive
  `G−v₃`), `Submodule.sub_mem` leaves the fresh-edge slot row `hingeRow v₂v₄ ρ₀ ∈ span` — exactly the
  engine `hρGv` slot. So the telescope route **converges at `i=3`**: option (b) is buildable, the slot
  is reached as `W φ − (surviving rows)` (NOT via `D φ`, the red herring — `i3_residue_collapse_deRisk`
  is kept as the correct-but-irrelevant fold-output record).
- **LEAF-ρ1 ALGEBRAIC CORE LANDED 2026-06-20 (`wstep_foldl_hingeRow_telescope` + helpers
  `wstep_hingeRow_off`/`wstep_hingeRow_frontier`, `Relabel.lean`, all axiom-clean).** The `i−1`-step
  `reverseRec` generalization of the `i=3` gate is now built: over an injective vertex `w` and the
  ascending body list (length `m=i−1`), the W9a `wstep` foldl of the base redundancy `hingeRow (w 0)(w 2)
  ρ₀` is the EXACT closed-form sum `(∑_{s<m} hingeRow (w s)(w (s+1)) ρ₀) + hingeRow (w m)(w (m+2)) ρ₀`.
  **Finding: the telescope is an exact sum, NOT the per-step `sub_mem` residue telescope this section
  sketched** — the two per-step helpers (off-body rows `wstep`-fixed; the frontier row `hingeRow x a ρ`
  advances to `hingeRow x v ρ + hingeRow v c ρ`) make the induction-on-`m` collapse via
  `Finset.sum_range_succ` + `abel`, with no residue-membership bookkeeping. `m=2` recovers
  `i3_wstep_foldl_base_redundancy_deRisk` verbatim; realizes KT eq. (6.66). **What remains** (the LEAF-ρ3
  arm wiring): the `m` leading summands are genuine surviving `G−vᵢ` rows (both endpoints `< i`) — supply
  via the landed `hwmem`/`chainData_bottom_relabel` machinery — then `sub_mem` peels the fresh-edge slot.
  NEXT = wire LEAF-ρ1 + LEAF-ρ3 into `chainData_relabel_arm`.

#### (o‴)(I.8) ARM-WIRING DECOMPOSITION — `chainData_relabel_arm` slot→brick map + TWO genuinely-new prerequisites the algebraic-core lemmas defer (recon-before-build, 2026-06-20)

> **Design-pass, docs-only, 2026-06-20 (opus).** Decomposes the general-`i` arm wiring
> `chainData_relabel_arm` into a buildable sub-step sequence, having re-verified against the **landed
> `def`/`theorem` bodies** (file:line below) which engine slot each landed brick fills and at what graph
> level. Clause (i): the engine-slot ↔ brick map below is source-verified. Clause (ii): the wiring is
> **NOT** the "purely graph-level, one instantiation" the prior pins (*Current state*, *Hand-off*,
> (I.7.10) tail) asserted — two genuinely-new prerequisites surface, both Lean-confirmed below, neither a
> motive/IH/signature change but neither a clean instantiation either. **The arm is NOT yet a mechanical
> assembly; it needs these two leaves FIRST.** The owner-chosen route (option (b), engine slot
> KT-faithful) is UNCHANGED — these are missing rungs *inside* it, not a re-decision.
>
> **PRIOR-PIN CORRECTION.** "`The hρGv algebraic core is COMPLETE`; the remaining work is **purely
> graph-level** … instantiate `wstep_foldl_freshEdge_slot_mem` at `S := span (G−vᵢ).rigidityRows`,
> supply `hW` + the `m` `hsurv` memberships" (Phase23b *Hand-off* rows 312–375, design (I.7.10) tail) is
> **OVERSTATED**: the algebraic *closed form* is done, but (P1) the corollary's `w : ℕ → α` /
> `Function.Injective w` interface is **un-instantiable over the finite vertex type** the arm runs on, and
> (P2) the `m` `hsurv` summand memberships were **deferred as abstract-`S` hypotheses** (in both the
> general corollary and the `i=3` gate) and are *themselves* a genuinely-new perpendicularity obligation,
> not a landed-brick instantiation. Both are buildable; the arm is gated on them.

**(I.8.0) What the arm must produce (source-verified, file:line).** `chainData_relabel_arm` discharges
the per-`i` candidate (interior `2 ≤ i ≤ d−1`) by `refine PanelHingeFramework.case_III_arm_realization …`
at the candidate roles — exactly the d=3 `M₃` shape (`case_III_arm_realization_M3`, `Relabel.lean:2352`,
which `refine`s the same engine at `Relabel.lean:2439`). The engine (`Arms.lean:72`) binds `Gv ends q`
+ `(v,a,b)` + the slots. Reading the **landed `chainData_bottom_relabel` output type** (`Relabel.lean:1960–1972`)
pins the *exact* framework the arm's `Gv ends q` must be, because that leaf is what fills `hwmem` and the
engine consumes `hwmem`/`hρGv` against ONE framework:
- **`Gv = G.removeVertex (cd.vtx i.castSucc) = G − vᵢ`** (`shiftBodyGraph (i−1) = G − vᵢ`, `Operations.lean:1800`).
- **`ends = ` the relabelled selector** `fun e => ((cd.shiftPerm i.castSucc).symm (ends₀ (cd.shiftEdgePerm i e)).1, …)`.
- **`q = qρ := fun p => q₀ (cd.shiftPerm i.castSucc p.1, p.2)`** (the inverse-cycle relabelled base seed).
- **`(a,b) = (cd.vtx i.succ, cd.vtx ⟨i−1,_⟩.castSucc) = (vᵢ₊₁, vᵢ₋₁)`** — the candidate fresh pair, in the
  order `chainData_bottom_relabel`'s block tag emits (`Relabel.lean:1971`) and KT eq. (6.57)/(6.64) force
  (engine-`a` = free `vᵢ₊₁`, engine-`b` = reproduced `vᵢ₋₁`; (I.7.10) bullet 1, coordinator-verified vs
  `Arms.lean:77`). [Coordinator-verified the four bindings against `Relabel.lean:1960–1972` + `Arms.lean:74–99`.]

**(I.8.1) Engine-slot → landed-brick map (source-verified; the slots that ARE clean).** With the four
bindings of (I.8.0) fixed, the engine's non-`hρGv` slots are mechanical (d=3 `M₃` shows each, generalized
by the inverse cycle replacing the single swap):
- **`hwmem` (`Arms.lean:96`) ← `chainData_bottom_relabel` (`Relabel.lean:1939`, LANDED axiom-clean).**
  Each base bottom-row member (`hwmem` at the `v₁`-base, supplied by the W6b gate) maps through the
  per-member `(shiftPerm i.castSucc)⁻¹` transport to a candidate `G − vᵢ` row OR the `(a,b)`-block tag —
  exactly the engine's `hwmem` disjunction at the (I.8.0) framework. The arm supplies the two recording
  hyps `hrec`/`he₀rec` (`Relabel.lean:1943/1946`). Clean. (d=3: `case_III_arm_realization_M3`'s `case hwmem`
  → `case_III_bottom_relabel`, `Relabel.lean:2551`.)
- **`hρe₀` (`Arms.lean:90`) ← G4d-i `acolumn_mem_hingeRowBlock_of_span_rigidityRows`.** The candidate
  functional's annihilation `ρ ⊥ C(qρ(ab))` is read off the base `hρGv` via the `a`-column-in-block lemma,
  exactly as `M₃`'s `hρ_ac` (`Relabel.lean:2419–2430`) does it at `vᵢ` (ONE application, not a per-body
  carry; `candidateRow_ac_eq_neg` STAYS for this). Clean.
- **`htrans`/`hLn`/`hgab`/`hρgate`/`hsplitG`/`hleG`/`hVone`/`hVcard`/`hw`/`hwcard`** — the same
  removeVertex-bookkeeping + discriminator (2c-i `exists_chainData_discriminator_pick`) the `M₃` template
  fills (`Relabel.lean:2446–2546`), generalized to the cycle. Clean, ~1 commit of §38 explicit-seed slot
  bookkeeping (pin `qρ` + the panel endpoints `a,b` explicitly to dodge the `whnf` blowup, TACTICS-QUIRKS §38).
- **`hρGv` (`Arms.lean:91`) ← `wstep_foldl_freshEdge_slot_mem` (`Relabel.lean:2792`) — the slot the wiring
  does NOT yet reach cleanly; see (I.8.2)/(I.8.3).** Target: `hingeRow vᵢ₊₁ vᵢ₋₁ ρ ∈ span (G−vᵢ ends qρ)`.

**(I.8.2) PREREQUISITE P1 (Lean-confirmed BLOCKER) — the algebraic-core corollary's `w : ℕ → α` /
`Function.Injective w` interface is un-instantiable over the finite vertex type.** `wstep_foldl_freshEdge_slot_mem`
(`Relabel.lean:2792`) and its closed-form base `wstep_foldl_hingeRow_telescope` (`:2739`) are stated over
`(w : ℕ → α) (hw : Function.Injective w)`. To supply `hρGv` the arm must instantiate `w` so that
`w m = vᵢ₋₁`, `w (m+2) = vᵢ₊₁`, and the `hW`/`hsurv` rows match `cd.vtx` — i.e. `w` must AGREE WITH
`cd.vtx` on indices `0 … i+1`. But the engine (`Arms.lean:73`) and the whole arm run under **`[Finite α]`**,
and `Function.Injective (w : ℕ → α)` is **contradictory for finite `α`** (`ℕ` is infinite). Lean-verified
this session: `example {α} [Finite α] (w : ℕ → α) (hw : Function.Injective w) : False` closes via
`Finite.of_injective w hw` + `not_finite ℕ`. So **the `hw` slot can NEVER be filled in the arm** — the
corollary as stated is dead-on-arrival for the finite-`α` arm, even though it is a true theorem (it holds
vacuously-only for infinite `α`). The fold list / hypotheses / conclusion of the *instantiated* statement
touch only indices `0 … i+1 ≤ cd.d` (verified: `shiftBodyListAsc i` entries reach `vtx ⟨i+1,_⟩`,
`Operations.lean:1694–1697`; `hsurv`/conclusion reach `w(i−1)`/`w(i+1)`), so **only finite-range
distinctness is actually USED** — but the *hypothesis* demands global injectivity. **THE FIX (a
genuinely-new leaf, ~1 commit):** RESTATE `wstep_foldl_hingeRow_telescope` + `wstep_foldl_freshEdge_slot_mem`
with a finite-range injectivity hypothesis instead of `Function.Injective w` — either `(w : ℕ → α)` with
`Set.InjOn w (Set.Iic (m+2))` (or `(↑(Finset.range (m+3)))`), or (cleaner) re-index over
`(w : Fin (m+3) → α)` with `Function.Injective w`, or thread the per-step `≠` facts the proof actually uses
(the `hoff`/`wstep_hingeRow_{off,frontier}` calls at `:2759–2772` apply `hw` only to index pairs `≤ m+3`).
The proof body changes minimally (replace each `fun h => by have := hw h; omega` with the range-scoped
analogue). Then the arm instantiates with `w := cd.vtx ∘ (Fin.castLE/⟨·,_⟩)` and discharges the
finite-range injectivity from `cd.vtx_inj` (`ChainData`, the chain vertices are distinct). **This is the
make-or-break for the whole `hρGv` route: until the algebraic core is re-stated finite-range, there is no
way to call it from the arm.** [Lean-confirmed `False` from the hypothesis; NOT a motive/contract change —
the *content* is unchanged, only the injectivity interface.]

**(I.8.3) PREREQUISITE P2 (genuinely-new, deferred-as-`hsurv`-hyp by both the corollary and the `i=3`
gate) — the `m` surviving summands' membership is a real perpendicularity obligation, not an
instantiation.** `wstep_foldl_freshEdge_slot_mem` takes `hsurv : ∀ s < m, hingeRow (w s)(w (s+1)) ρ₀ ∈ S`
as a HYPOTHESIS (and `i3_freshEdge_slot_mem_deRisk` takes `h01`/`h12` likewise — both are abstract over
`S`, so the `i=3` gate "PASSED" verdict NEVER checked these at the concrete `span (G−v₃)` level; it checked
only the `sub_mem` algebra). At the arm, `S := span (G−vᵢ ends qρ).rigidityRows` and a summand
`hingeRow (vtx s)(vtx (s+1)) ρ₀` is in `rigidityRows` (`Basic.lean:603`) iff (a) `vtx s — vtx (s+1)` is a
genuine `G − vᵢ` link — TRUE (it is `cd.edge s`, `cd.link`; both endpoints `s, s+1 ≤ i−1 < i` survive
`removeVertex vᵢ`); AND (b) **`ρ₀ ∈ hingeRowBlock (edge s)`, i.e. `ρ₀ ⊥ panel(qρ(vtx s, vtx (s+1)))`** —
NOT automatic. `ρ₀` is the base redundancy `r` (KT eq. 6.52), built to annihilate the **base spliced panel**
`C(q(v₀v₂))` only; that it also annihilates each *intermediate chain-edge* panel is precisely what KT eq.
(6.62)+(6.66) ASSERTS (the transported-redundancy form is a genuine row at each surviving edge), but it is
**unbuilt in Lean** and is the one substantive math step the telescope's exact-closed-form (I.7.10 LANDED)
*does not by itself supply* — the closed form says `W φ = (∑ hingeRow … ρ₀) + slot` as linear maps; it does
**not** say each `∑`-summand is a span member. **THE FIX (a genuinely-new leaf, ~1–2 commits, the real
math):** a per-summand membership lemma `hingeRow (vtx s)(vtx (s+1)) ρ₀ ∈ span (G−vᵢ ends qρ).rigidityRows`
for `s < i−1`, whose crux is `ρ₀ ⊥ panel(qρ(vtx s, vtx (s+1)))`. Two candidate routes, **choose at build**:
(a) derive the perp from the base `hρe₀`/`hρGv` via the **same G4d-i `a`-column-in-block argument** the
`hρe₀` slot uses (KT's degree-2 cancellation makes each chain-edge panel a scalar multiple of the base
panel along the cycle — likely, KT-grounded, but UNVERIFIED here); or (b) read the summand membership off
the **landed `chainData_bottom_relabel`** genuine-row branch directly (the surviving chain edges ARE the
`rigidityRow_relabel_to_genuine` images — but that brick transports a *base bottom-row member*, so this
needs the summand to first BE a base member, circular unless ρ₀'s base-perp transports). **Until P2 is
built, `hsurv` cannot be supplied, so `wstep_foldl_freshEdge_slot_mem` cannot conclude.** [Source-verified
the `rigidityRows` membership predicate `Basic.lean:603–604`; the perp is genuinely-new.] **De-risk:** do
P2 at `i=3` FOR REAL at the *concrete* `span (G−v₃)` level (the gate did it only abstractly) — supply
`h01`/`h12` from actual `G−v₃` rows; if `ρ₀ ⊥ panel(q(v₀v₁))` / `ρ₀ ⊥ panel(q(v₁v₂))` does NOT follow from
the base `hρe₀`, that is the genuinely-new obstruction and the build STOPS + reports (mirrors the H.11 gate).

**(I.8.4) The buildable sub-step sequence (ordered; exact signatures).** The arm is NOT one
instantiation; it is **P1 → P2 → the assembly**, each sized to one sitting:
1. **P1 restatement — LANDED 2026-06-20 (the unblocker).** Both algebraic-core lemmas
   (`wstep_foldl_hingeRow_telescope` + `wstep_foldl_freshEdge_slot_mem`) restated **in place** (same names,
   zero callers existed) over `(hinj : Set.InjOn w (Set.Iic (m + 2)))` instead of the dead
   `Function.Injective (w : ℕ → α)`. Chosen over the `Fin (m+3) → α` re-index: `Set.InjOn` over `w : ℕ → α`
   keeps the `induction m` clean (the `Fin`-index type would change between `m` and `m+1`). Proof = the
   landed body with the IH fed `hinj.mono (Set.Iic_subset_Iic.mpr (by omega))` and each
   `fun h => hw h; omega` replaced by a local `hne i j (≤N) (≤N) (≠)` distinctness helper. Axiom-clean,
   warning-clean, full project green. The arm supplies `hinj` from `cd.vtx_inj` (`Fin (d+1) → α` injective)
   via `Set.InjOn.mono`. Lesson → FRICTION [idiom] *A `(w : ℕ → α)`-indexed lemma whose carrier will be
   `[Finite α]`…*.
2. **`chainData_freshEdge_surviving_row_mem` (P2, ~1–2 commits, the real math).** For `s < (i:ℕ)−1`:
   ```
   theorem … (cd : G.ChainData n) (i : Fin cd.d) (s : ℕ) (hs : s + 1 < (i:ℕ)) (ends₀ q …) :
       BodyHingeFramework.hingeRow (cd.vtx ⟨s,_⟩) (cd.vtx ⟨s+1,_⟩) ρ₀
         ∈ Submodule.span ℝ (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx i.castSucc))
             (relabelled ends) qρ).toBodyHinge.rigidityRows
   ```
   crux: `ρ₀ ⊥ panel(qρ(vtx s, vtx (s+1)))` (route (a) G4d-i degree-2 chain, or (b) via
   `chainData_bottom_relabel`); link via `cd.link` + survival `s, s+1 < i`.
3. **`hW`-supplier (clean instantiation, folded into step 4).** `hW := shiftBodyListAsc_foldl_mem_span_rigidityRows`
   (`Relabel.lean:1785`, LANDED) at the candidate `i`, the relabelled `ends`, seed `q`, base `hφ` = the
   W6b-gate base redundancy `hingeRow (vtx 0)(vtx 2) ρ₀ ∈ span (G−v₁ ends q)`. **GAP-to-watch (P3, see
   I.8.5):** the fold's output lands in `span (shiftBodyFrameworkAsc (i−1)) = span (ofNormals (G−vᵢ) ends
   (shiftSeedAdv q (i−1)))`, whose seed is `shiftSeedAdv q (i−1)`, but the engine framework's seed is
   `qρ = q ∘ shiftPerm i.castSucc` — these must be the SAME function for `hW`'s `S` to be the engine's `S`.
4. **`chainData_relabel_arm` (the assembly, ~1 commit).** `refine case_III_arm_realization …` at the (I.8.0)
   bindings; `hwmem ← chainData_bottom_relabel`; `hρGv`: `rw [hingeRow_swap]` to flip the engine's
   `hingeRow vᵢ₊₁ vᵢ₋₁ ρ` to the telescope's `hingeRow vᵢ₋₁ vᵢ₊₁ ρ₀` orientation (the corollary emits
   `hingeRow (w m)(w (m+2)) = hingeRow vᵢ₋₁ vᵢ₊₁`, the OPPOSITE order to the engine slot — a `hingeRow_swap`
   + the shared `−ρ₀` sign, exactly as `M₃`'s `case hρGv` opens with `rw [hingeRow_swap c v (-ρ), neg_neg]`,
   `Relabel.lean:2475`), then `wstep_foldl_freshEdge_slot_mem_finite` (P1) with `hW` (step 3) + `hsurv`
   (step 2); remaining slots per (I.8.1). d=3 (`i=2`) = the landed `M₃` verbatim (the cycle is the single
   swap, `m=1` 1-summand, zero regression).

**(I.8.5) PREREQUISITE P3 (flagged, likely-clean-but-UNVERIFIED) — the fold seed `shiftSeedAdv q (i−1)`
vs the engine seed `qρ = q ∘ shiftPerm i.castSucc` must coincide.** The W9a fold's output span (step 3)
carries seed `shiftSeedAdv q (i−1)` (recursive: `shiftSeedAdv q (s+1) = fun p => shiftSeedAdv q s
(shiftSeedSwap s p.1, p.2)`, `shiftSeedSwap s = swap (vtx⟨s+2⟩)(vtx⟨s+1⟩)`, `Relabel.lean:1695–1714`); the
engine/`chainData_bottom_relabel` framework carries `qρ = fun p => q (shiftPerm i.castSucc p.1, p.2)`. For
`hρGv` (in the fold's span) and `hwmem` (in the `qρ` span) to live in the **same** engine `S`, need
`shiftSeedAdv q (i−1) = qρ` as functions. There is **NO landed lemma** for this (searched; the seed half
`seedShift_inv_cancel`/`seedShift_off_cycle`, `Operations.lean:1595/1605`, and the perm-level G1 bridge
`shiftPerm_eq_prod_map_swap_shiftBodyListAsc`, `Operations.lean:1905`, are the ingredients but not the
composed seed identity). The design's (I.7.0) claim "the seed identity is the H.10-confirmed
`qρ(ρ⁻¹x)=q(x)`" conflates the *single-step* cancellation with the *composed* `shiftSeedAdv = q ∘
shiftPerm`. **Likely a clean ~½-commit `simp`-over-the-recursion bridge** (`shiftSeedAdv` unfolds to the
swap product that `shiftPerm_eq_prod_map_swap_shiftBodyListAsc` identifies with `shiftPerm`), but it is a
NAMED un-landed lemma `shiftSeedAdv_eq_funLeft_shiftPerm`, not an instantiation. Build it alongside step 3.
[Source-verified the two seed defs diverge syntactically; the equality is unbuilt.]

**(I.8.6) VERDICT (clause ii).** The arm wiring is **NOT mechanical**. The slot→brick map (I.8.1) is clean
and source-verified for every slot EXCEPT `hρGv`, and the engine bindings (I.8.0) are KT-faithful and
confirmed against the landed `chainData_bottom_relabel` output. But three prerequisites stand between the
landed algebraic core and a callable arm: **P1 (BLOCKER, Lean-confirmed)** — the `Function.Injective (ℕ→α)`
interface is un-instantiable over finite `α`; restate finite-range (the unblocker, ~1 commit). **P2 (real
math)** — the `m` `hsurv` summand memberships need `ρ₀ ⊥` the intermediate chain-edge panels, deferred as
abstract-`S` hyps by both the corollary AND the `i=3` gate, never checked concretely (~1–2 commits, de-risk
at `i=3` for real). **P3 (flagged, likely clean)** — the fold seed `shiftSeedAdv q (i−1)` = engine seed
`qρ` is unbuilt (~½ commit). None is a motive/IH/signature change; option (b) stands; d=3 zero-regression
stands. **P1 LANDED 2026-06-20** (`wstep_foldl_{hingeRow_telescope,freshEdge_slot_mem}` restated finite-range
in place, `Set.InjOn w (Set.Iic (m+2))`, axiom-clean). **Remaining to the closed arm: ~3–4 commits** (P2 →
P3 → assembly), the **smallest next commit = P2** (the `hsurv` summand perp-membership, de-risked at `i=3`
concretely). The "purely graph-level, one instantiation" framing in *Hand-off* / (I.7.10) tail was corrected
by this pass; P1 (the unblocker) is now discharged.

---

## CHAIN↔ENTRY chain-data contract

**Status:** settled 2026-06-17 (docs-only design-settle pass, source-verified
against KT §6.4.2 eqs. 6.46–6.67 read end-to-end + the landed `d=3` producer/
consumer/dispatch in tree). This section freezes the **shared interface** the
recon's flag (b) (§"CHAIN"(b)) left open: the length-`d` chain-data shape that
the ENTRY extractor produces and the CHAIN-5 dispatch consumes. **Authoritative
for the interface only** — it does NOT build any leaf, does NOT decide OD-4 (the
eq.-6.67 alg-independence route), and does NOT mint ENTRY. Every CHAIN leaf and
the ENTRY extractor is to be authored against the frozen shape below.

### C.0 — Where the chain data actually flows (the producer reshape, verified)

The recon's flag (b) located the carried `hdispatch` shape, but the
**load-bearing structural fact for the contract is one level deeper**: the chain
*extraction* does **not** live in a separate ENTRY lemma feeding the dispatch —
it lives **inside the producer** `case_III_hsplit_producer_all_k`
(`CaseIII/Arms.lean:777`). Verified in tree (Arms.lean:828–857, the `|V(G)| ≥ 4`
arm): the producer (i) calls `Graph.exists_chain_data_of_noRigid`
(`Reduction.lean:383`) to get the 4-tuple `v,a,b,c` + edges, (ii) picks a fresh
`e₀`, (iii) proves `G.splitOff v a b e₀` is a smaller minimal-0-dof graph + is
simple, (iv) pulls its **generic** realization `hsplitGP` from the IH's GP
conjunct, and (v) feeds all of that to `hcand`. So the **producer is the chain
extractor's only consumer**, and the `hcand`/`hdispatch` premise bundle is the
*output type of the extractor* re-expressed as the *input type of the dispatch*.

**Consequence for the contract.** The reshape is **three decls changing in
lockstep, all carrying the identical premise bundle** (verified byte-identical
across the three):
1. `Graph.exists_chain_data_of_noRigid` (`Reduction.lean:383`) — the **producer
   side** (ENTRY): its `∃`-output tuple is the record.
2. `case_III_hsplit_producer_all_k.hcand` (`Arms.lean:797–807`) **and** the
   identical extraction-arm body (Arms.lean:828–857) — the **producer** threads
   the record into `hcand`.
3. `case_III_realization_all_k.hdispatch` (`Realization.lean:699–709`) and
   `theorem_55_minimalKDof_k_all_k.hdispatch` (`Theorem55.lean:2230–2240`,
   wrapped under a per-`G` `∀`) — the **consumer side** (CHAIN-5): the carried
   crux hypothesis whose shape must be the record.

The `d=3` premise bundle, verbatim (the four files agree):
```
(v a b c : α) (eₐ e_b e_c e₀ : β)
v ∈ V(G) → a ∈ V(G) → b ∈ V(G) → c ∈ V(G) →
a ≠ v → b ≠ v → b ≠ a → c ≠ v → c ≠ a → b ≠ c →
eₐ ≠ e_b → eₐ ≠ e_c →
G.IsLink eₐ v a → G.IsLink e_b v b → G.IsLink e_c a c →
(∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b) →
(∀ e x, G.IsLink e a x → e = eₐ ∨ e = e_c) →
e₀ ∉ E(G) →
(G.splitOff v a b e₀).deficiency n = 0 →
HasGenericFullRankRealization k n (G.splitOff v a b e₀) →
HasGenericFullRankRealization k n G
```

### C.1 — The length-`d` chain-data record (item 1)

KT §6.4.2 (eqs. 6.46–6.59, p. 692–694) needs the **whole chain `v₀v₁…v_d`** with
`d_G(vᵢ)=2` for `1≤i≤d−1`, the base framework on `G₁ = splitOff at v₁` (KT's
`G^{v₀v₂}_{v₁}`), and the redundant-`(v₀v₂)` row of Claim 6.11. The recommended
shape is a **`structure`** (not an anonymous `∃`-tuple — at `d=3` the tuple is
already 17 fields; at general `d` the vertex/edge sequences are `Fin`-indexed
families and an anonymous tuple is unmaintainable). Grounded field-by-field in
the KT chain definition + the landed `splitOff` API (`Operations.lean:579`,
`splitOff_isLink` 619):

```
/-- Length-`d` Case-III chain data (KT §6.4.2, the chain v₀v₁…v_d). -/
structure ChainData (G : Graph α β) (n : ℕ) where
  d        : ℕ                         -- the chain length = the body-bar dim index (d = k+1)
  hd       : 1 ≤ d                     -- nondegenerate chain (d ≥ 1; d=3 ⟹ 2)
  vtx      : Fin (d + 1) → α           -- v₀ … v_d  (KT 6.46: the chain vertices)
  edge     : Fin d → β                 -- the chain edges: edge i = vᵢvᵢ₊₁
  e₀       : β                         -- the fresh short-circuit label for the v₁-split (6.46)
  -- KT chain conditions:
  vtx_mem    : ∀ i, vtx i ∈ V(G)
  vtx_inj    : Function.Injective vtx                       -- the vᵢ are distinct (6.67 affine-indep prep)
  link       : ∀ i : Fin d, G.IsLink (edge i) (vtx i.castSucc) (vtx i.succ)
  edge_inj   : Function.Injective edge
  deg_two    : ∀ i : Fin d, 1 ≤ (i : ℕ) → (i : ℕ) ≤ d - 1 → -- d_G(vᵢ)=2 for 1≤i≤d−1 (6.46):
                 (∀ e x, G.IsLink e (vtx i.castSucc?) x →    -- every vᵢ-edge is edge(i−1) or edge(i)
                   e = edge (prev i) ∨ e = edge i)            -- (the degree-2 closure, KT's two-edge fact)
  e₀_fresh   : e₀ ∉ E(G)
```
(The `deg_two` field is sketched against the `splitOff_isLink` two-edge-closure
pattern the `d=3` `hclv`/`hcla` carry; the exact `Fin`-arithmetic of "the two
edges incident to `vᵢ` are `edge (i−1)` and `edge i`" is a build detail for
ENTRY — the *content* is "interior chain vertices have degree exactly two, with
their two edges being the two chain edges at that index", which is precisely
KT's `d_G(vᵢ)=2`.) **The base framework `(G₁,q₁)` is NOT a record field** — it is
produced *inside* the dispatch from the IH (as the `d=3` producer does at
Arms.lean:854, pulling `hsplitGP` from `(hIH …).1`); the record carries only the
*combinatorial* chain. The `splitOff` that builds `G₁` is `G.splitOff v₁ v₀ v₂ e₀`
(splice the `v₀v₂` edge, delete `v₁`), matching the landed `splitOff v a b e₀`
with `(v,a,b) = (v₁,v₀,v₂)` — see C.4.

**Carried minimality / conditioned-IH hypotheses** stay *outside* the record, on
the producer/dispatch signature exactly as the `d=3` bundle has them: `hG :
G.IsMinimalKDof n 0`, `hnoRigid`, `hSimple`, the IH conjunction `hIH`, and the
per-split `(G.splitOff …).deficiency n = 0`. The record is the *chain witness*;
the realization/minimality data is the surrounding induction context (this
matches the `d=3` split: `exists_chain_data_of_noRigid` returns only the
combinatorial tuple, and `case_III_hsplit_producer_all_k` supplies `hG`/`hIH`/
`hsplitGP` from its own context).

### C.2 — Producer-side signature (item 2): the reshaped extractor

ENTRY reshapes `exists_chain_data_of_noRigid` from the fixed 4-tuple to a
`ChainData` producer. Target signature (general `d`, against the record):
```
theorem Graph.exists_chainData_of_noRigid [DecidableEq β] [Finite α] [Finite β]
    {G : Graph α β} {n : ℕ}
    (hD : (some-D-floor) ≤ bodyBarDim n)        -- ENTRY lifts the d=3 `6 ≤ bodyBarDim n` floor
    (hV : (d + 1) ≤ V(G).ncard)                 -- enough vertices for a length-d chain
    (hG : G.IsMinimalKDof n 0)
    (hnp : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n) :
    G.ChainData n                                -- the record (or the cycle-branch disjunct, OD-1)
```
This is KT **Lemma 4.6 (chain) + Lemma 4.8 (split-off minimality)** at general
`d` — the "new combinatorial leaf for ENTRY" the OD-2/OD-3 verdict named (not
subsumed in Phase-20, which produces only the single degree-2 split). The
`d=3` `exists_chain_data_of_noRigid` becomes the `d=3` instance / a wrapper that
fills `ChainData` with `d = 3` and `(vtx 0,1,2,3) = (b,v,a,c)` (C.4). **The
hD floor is ENTRY's to lift** (the `6 ≤ bodyBarDim n` of the `d=3` extractor is
the `d=3` regime; the general floor is the body-bar-dim ↔ chain-length relation,
a separate ENTRY obligation — see §"CHAIN"(d), `hD`-floor lift).

### C.3 — Consumer-side signature (item 3): the CHAIN-5 dispatch

CHAIN-5's dispatch (`hdispatch`/`hcand`) takes the record + the surrounding
induction context and produces the realization. Target shape:
```
(hdispatch : ∀ (cd : G.ChainData n),
    (G.splitOff (cd.vtx 1) (cd.vtx 0) (cd.vtx 2) cd.e₀).deficiency n = 0 →
    HasGenericFullRankRealization k n
        (G.splitOff (cd.vtx 1) (cd.vtx 0) (cd.vtx 2) cd.e₀) →   -- the base (G₁,q₁) seed
    HasGenericFullRankRealization k n G)
```
i.e. *"given the length-`d` chain, the deficiency-0 fact on `G₁ = splitOff at v₁`,
and the IH-generic base realization on `G₁`, build the `d` candidate frameworks
(CHAIN-2, eqs. 6.47/6.48/6.57/6.59), apply the `⋀^{d−1}`-duality discriminator
(CHAIN-3/4, eq. 6.67) to find a full-rank `Mᵢ`, and close via the (already
general-`k`) arm closer for that `i`."* The `G₁` here is `splitOff (vtx 1) (vtx
0) (vtx 2) e₀` — the `v₁`-split splicing `v₀v₂` — which is the *single* split the
`d=3` bundle's `(G.splitOff v a b e₀)` already names (C.4). The remaining `d−2`
candidate splits `Gᵢ = splitOff at vᵢ` (KT 6.54–6.56) are built *internally* by
the dispatch from `cd` and the isos `ρᵢ` (which are *derived* from the chain by
eq. 6.54, not carried — see C.5). **CHAIN-5's signature is frozen as this shape**
(per the (b) co-design gate); the only build-time latitude is the exact `Fin`
arithmetic of indexing `cd.vtx`/`cd.edge`.

### C.4 — The `d=3` specialization (item 4): zero-regression wrapper

At `d=3` the chain `v₀v₁v₂v₃` **is** `b—v—a—c` (verified against the `d=3`
extractor `exists_chain_data_of_noRigid`, which returns `v,a,b,c` with `v`,`a`
the adjacent degree-2 pair via `eₐ`, `b` the other `v`-neighbour, `c` the other
`a`-neighbour). The record-to-tuple map:

| Record (`ChainData`, general `d`) | `d=3` value | `d=3` tuple field |
|---|---|---|
| `d` | `3` (= `k+1` at `k=2`) | — |
| `vtx 0` | `b` | `b` (the `v₀` endpoint) |
| `vtx 1` | `v` | `v` (interior, deg 2) |
| `vtx 2` | `a` | `a` (interior, deg 2 in `G₁`) |
| `vtx 3` | `c` | `c` (the `v₃` endpoint) |
| `edge 0` (= `v₀v₁` = `bv`) | `e_b` | `e_b` |
| `edge 1` (= `v₁v₂` = `va`) | `eₐ` | `eₐ` (the shared edge) |
| `edge 2` (= `v₂v₃` = `ac`) | `e_c` | `e_c` |
| `e₀` | `e₀` | `e₀` |

So **`G₁ = splitOff (vtx 1) (vtx 0) (vtx 2) e₀ = splitOff v b a e₀`** — but the
landed `d=3` bundle uses `splitOff v a b e₀` (note `a`,`b` swapped). `splitOff`
is symmetric in its `a,b` arguments (verified: `splitOff_isLink`,
`Operations.lean:619`, makes `v₀v₂` and `v₂v₀` the same `e₀`-link via the
`(x=a∧y=b) ∨ (x=b∧y=a)` disjunct), so `splitOff v a b e₀ = splitOff v b a e₀` as
graphs — the `d=3` wrapper instantiates cleanly either way. The degree-2 closures
`hclv` (every `v`-edge is `eₐ` or `e_b`) and `hcla` (every `a`-edge is `eₐ` or
`e_c`) are exactly `ChainData.deg_two` at `i=1` (vtx 1 = v: edges `edge 0 = e_b`,
`edge 1 = eₐ`) and `i=2` (vtx 2 = a: edges `edge 1 = eₐ`, `edge 2 = e_c`). **The
`d=3` line stays a zero-regression wrapper**: `exists_chain_data_of_noRigid`
(the existing 4-tuple lemma) becomes the `d=3` `ChainData` constructor, and the
`theorem_55_d3`/`case_III_realization` wrappers fill `hdispatch` from the
existing `case_III_candidate_dispatch` via this map — no `d=3` proof changes,
only an adapter from the 4-tuple to the `ChainData` projection.

### C.5 — OD-1 reconciliation (item 5): the chain/cycle division of labor

KT p. 692: *"By Lemma 4.6, either `G` is a cycle of length at most `d` or `G`
has a chain of length `d`. If `G` is a cycle of length at most `d`, then we are
done by Lemma 5.4."* So the **dichotomy is upstream of the dispatch**. Pinned
division of labor:

- **The extractor (ENTRY) owns the dichotomy.** `exists_chainData_of_noRigid`
  (C.2) is where Lemma 4.6 fires. It has two honest shapes, and **OD-1 chooses
  between them at ENTRY-build, not now** — the contract is written so CHAIN-5
  works under **either**:
  1. *Extractor returns the chain only, ENTRY discharges the cycle branch
     separately* (preferred if Lemma 5.4 can be folded into the base/short-cycle
     case the way the `d=3` triangle floor was, §"23a"-OD verdict that `d=3`
     dodged 5.4). Then `exists_chainData_of_noRigid : G.ChainData n` returns a
     genuine chain, and CHAIN-5 **assumes the chain branch** — the cycle case
     never reaches the dispatch. **This is the contract's default assumption**:
     CHAIN-5's `hdispatch` consumes a `ChainData` and is *not* responsible for
     the cycle branch.
  2. *Extractor returns a disjunction* `G.ChainData n ⊕ (G is a short cycle,
     |V| ≤ D)`, and the producer routes the cycle disjunct to a **Lemma 5.4
     short-cycle realization** brick (a genuine new ENTRY leaf, risk #4, the
     Crapo–Whiteley cycle realization). CHAIN-5 still only sees `ChainData`.
- **CHAIN never handles the cycle branch.** Under both shapes, CHAIN-5's input
  is a `ChainData`; the cycle realization (if load-bearing) is ENTRY's. This is
  the safe pin: it does not pre-commit OD-1 (whether 5.4 is needed at all), and
  it keeps the dispatch signature stable regardless of how the dichotomy
  resolves. **ENTRY decides at build** whether the cycle branch is vacuous /
  base-folded (shape 1) or needs the 5.4 brick (shape 2); the dispatch contract
  is invariant under that choice.

### C.6 — Clause (ii): no motive/IH-level change forced by the interface

Pinning the contract did **not** surface a motive/IH-level blocker. The chain
data is purely combinatorial (`ChainData` carries no realization, no nested-IH
seed); the base framework `(G₁,q₁)` is supplied to the dispatch as the
**existing** `HasGenericFullRankRealization k n (G.splitOff …)` premise (the
`d=3` `hsplitGP` shape, already general-`k` from 23a), pulled from the *same*
0-dof IH conjunct the `d=3` producer uses (Arms.lean:854). The `d`-candidate
splits `Gᵢ` are *smaller* minimal-0-dof graphs realized by the same IH at the
same dof — **no higher-dof `G_v` GAP-6 pattern, no conditioned-pair data the
0-dof motive cannot supply**. The one genuine open question the interface
*touches* but does **not** resolve is **OD-4** (the eq.-6.67 `d+1`-points step:
existence route vs. the alg-independence hammer) — that is a CHAIN-4 *internal*
build decision, not an interface field, and the contract is invariant under it
(the record carries the chain; OD-4 concerns how the dispatch *uses* the
generic base `(G₁,q₁)`, whose `AlgebraicIndependent ℚ` data the 23a-lifted
`case_III_nested_rank_lower` already consumes). **The interface is frozen; the
two honest unknowns it routes downstream are OD-1 (ENTRY's dichotomy shape, C.5)
and OD-4 (CHAIN-4's alg-independence route), both build-time, neither a motive
change.**
