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

## 23a — recon verdicts (closed; full leaf-level detail in git)

**Status: CLOSED (sub-phase 23a CARRIER landed).** Full blow-by-blow in git +
`notes/Phase23a.md`; this is the verdict residue. The detailed per-file
reach-in table, the OD-5 source-facts derivation, and the Leaf-0…Leaf-5
buildable sequence are consumed — collapsed here to the verdicts that
downstream (CHAIN / ENTRY) and the cross-refs still resolve against.

**OD-5 verdict — PORTS VERBATIM (no carrier-API addition, no build-spike).**
The coordinate transport (hard-part (d): `screwBasis`/`annihRow`/`annihRowPoly`,
PanelLayer; `GenericityDevice.exists_good_realization_ofParam`, stated
`screwDim k * card α`) was authored at symbolic `k` from the start through
abstract `Module.Basis` API — ScrewSpaceCarrier §6's "exercised symbolically
for the first time in 23" worry is already false in the landed source. Residual:
cap-regression under the full numeral substitution is a local `maxHeartbeats`
bump (standing idiom), not an OD-5 reopening (23a-OD-C).

**The lift was mechanical numeral-replacement** (`2`→`k`, `Fin 4`→`Fin (k+2)`,
`screwDim 2`→`screwDim k`, `…Realization 2`→`… k`) along the import spine, **plus**
the genuinely-new `screwDim k`-arithmetic kit (Leaf 0, `c2669b3`,
`RigidityMatrix/Basic.lean`): `one_le_screwDim`, `two_le_screwDim` (needs the
`k ≥ 1`/body-bar dimension floor — `2 ≤ screwDim k` is FALSE at `k=0`, and
`omega` cannot discharge it after `unfold screwDim` because of the `choose 2`
integer division), `screwDim_sub_two_le_mul` (takes `2 ≤ m`; the `1 ≤ m` form is
false at `m=1`). Leaf 1a landed the duality-free rank-nullity core
`exists_linearIndependent_perp_of_normals` (PanelLayer; the triplicated proof in
`exists_two_perp_of_linearIndependent_normals`/`exists_three_perp`/
`exists_extensor_in_two_panels` collapsed into it). 23a-OD-A resolved NEGATIVE:
the extensor-bearing perp arity is the **extensor grade `k`** (`Fin k`/`Fin (k+1)`
tuples, Leaf 1b), not the ambient-only `Fin 2` the original recommendation
claimed (`ExtensorInPanel`, `Basic.lean:276`). 23a-OD-B (`span_omitTwoExtensor_eq_top`
squareness) ports clean via `omitTwoExtensor_linearIndependent_of_li`.

**Dispatch-only `⋀²ℝ⁴`-duality DROPPED to CHAIN** (left at `Fin 4` by 23a):
`exists_homogeneousIncidence_of_normals`, `exists_complementIso_ne_zero_of_homogeneousIncidence`,
`exists_hduality_witness_of_panel_incidence`, and the `Meet.lean` point-join↔panel-meet
chain (`extensor_join_eq_zero_of_complementIso_eq_zero_dotProduct` →
`complementIso_smul_eq_extensor_join`; consumers `exists_extensor_eq_panelSupportExtensor`).
The shared brick `linearIndependent_normals_of_algebraicIndependent`
(`CaseIII/Realization.lean:99`) was lifted (spine + dispatch both consume it).

**Green-modulo boundary 23a left (boundary (d) → CHAIN/ENTRY).** `case_III_realization`
/ `theorem_55_minimalKDof_k` carry the chain dispatch as an explicit
`hcand`/`hdispatch` hypothesis of the `case_III_hsplit_producer.hcand` shape (never
a `sorry`); the `d=3` line stays fully green via a `theorem_55_d3` wrapper filling
it from the existing `case_III_candidate_dispatch`. **As built, Leaf 5 was wider
than (d) anticipated:** `theorem_55_minimalKDof_k_all_k` takes **six** green-modulo
carries — the dispatch plus base/cut/Case-I/M4-forget producers (`d=3`-pinned →
CHAIN's `⋀^{d−1}(ℝ^{d+1})` duality) and the `6 ≤ bodyBarDim n` chain-extraction
floor (→ ENTRY). (a)'s claim that base/cut/Case-I "lift with the numeral pass" is
superseded by this.

**OD-2/OD-3 (secondary, ENTRY scoping):** KT Lemma 4.6 (chain-or-cycle / degree-2
vertex) exists as `exists_low_degree_vertex` + `exists_adjacent_degree_two_pair`
(`ReducibleVertex.lean`) + `exists_chain_data_of_noRigid` (`Reduction.lean`); KT
Lemma 4.8(i)/(ii) (split-off minimality) as `splitOff_removeVertex_minimalKDof`
(`Reduction.lean`) — but **only in fixed-tuple `d=3` form** (a fixed `v,a,b,c`
4-tuple, not a length-`d` chain). So the general-`d` chain producer is a NEW
ENTRY leaf, not subsumed (OD-2 answer: Phase-20 produces only the single degree-2
split). OD-1: no Lemma 5.4 short-cycle decl exists; `d=3` dodged 5.4 via the
triangle base `hasGenericFullRankRealization_of_triangle` (Arms) — whether
general-`d` can likewise dodge it stays open for ENTRY.

---

## CHAIN — recon verdicts (closed; full leaf-level detail in git)

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

### Closed-arc verdicts — the CHAIN detailed-build recon (23b CLOSED)

**Status: COLLAPSED.** Sub-phases (f)–(o‴) below were the detailed leaf-level recon + route
adjudications that built out CHAIN-3/4, CHAIN-2/2a/2c, and the `chainData_relabel_arm` `hρGv` route.
23b CHAIN is CLOSED; the live route is (A) (`(I.8.21)` onward, built on the §(o‴)(I.8.18)–(I.8.20)
refutation). The full blow-by-blow is in git + `notes/Phase23b.md` *Decisions made*; the reusable
lessons are lifted (DESIGN.md *Statement faithfulness to the source* — the ±r-row mis-targeting +
KT eq-6.44/6.66; FRICTION.md — the relabel/`funLeft`/`dualMap` idioms, the `Function.Injective (ℕ→α)`
over-`[Finite α]` and caller-satisfiability traps; model-exp Findings 2026-06-20/06-21). Below: the
verdicts the live route, the contract, and the cross-refs (`Phase23c.md`, `Phase23b.md`,
`model-experiment.md`) still resolve against — landed bricks kept by name, dead arcs to one-line
"why it died" pointers.

#### (f)/(g)/(h) CHAIN-3 — the `⋀^{d−1}W`-is-a-line duality — CLOSED

The CHAIN-3 finish recon **corrected the prior pin** (the d=3 `Φ̃ = dualAnnihilator` / `dim Φ̃ = 5`
route, `finrank_sup_range_wedgeFixedLeft` / `inf_range_wedgeFixedLeft` / `wedgeFixedLeft` /
`extensor_toDual_extensor_eq_zero_of_perp`, which is sound only because `dim Ω = C(d−1,2) = 1` at
`d=3` — these STAY as the green d=3 route, do NOT generalize). The route that generalizes: both the
point-join (the `(d−1)`-extensor of `d−1` points, KT p. 698) and the panel-meet
(`complementIso (k:=d−1)(j:=2)` of the **2** line-normals — `j=2`, NOT `j=d−1`; a line has exactly 2
normals at every `d`) are the Plücker coordinate of the same `(d−1)`-dim `W = {n_u,n'}^⊥`, both in
`⋀^{d−1}W` which is a line. The assembly **`extensor_join_proportional_complementIso_meet`** LANDED
(`MeetHodge.lean`) on the three landed `_grade` bricks (`extensor_mem_range_map_subtype_of_mem_grade`,
`exteriorPower_map_subtype_injective_grade`, `exists_smul_eq_of_mem_range_map_subtype_grade`,
`finrank_exteriorPower_self_eq_one`) + the OD-8 route-(α) chain (h-0…h-3). **OD-8** (the panel-meet
range-membership `complementIso_extensor_mem_range_map_subtype`): the in-hand annihilation
(`complementIso_toDual_eq_zero_of_wedgeProd_eq_zero`) does NOT directly give membership (that would need
the withdrawn `dim Φ` count); the genuine route is `complementIso`'s **O(n)-equivariance** (`complementIso`
is the Hodge `⋆` for the standard Euclidean structure), via (h-0) `screwAlgebraTopEquiv_map_eq_det_smul`,
(h-1) `complementIso_map_orthogonal_eq`, (h-2) `exists_orthogonal_map_span_pair_eq_coordPlane`, (h-3)
the target leaf (consuming the landed `exists_smul_extensor_eq_of_mem_span_range` +
`extensor_mem_range_map_subtype_of_mem_jgrade`), (h-4) the assembly. The d=3
`complementIso_smul_eq_extensor_join` stays the green wrapper (h-5). KT-faithfulness (coordinator-checked
vs KT pp. 697–698, eqs. 6.65–6.67): KT writes `C(Lᵢ)` agnostically as meet (6.66, rank side) AND join
(6.67, `D`-span side); the assembly formalizes the join=meet equality KT leaves implicit (a
BlueprintExposition-grade node) — the withdrawn `Φ̃`/`Ω` machinery is a d=3-only formalization artifact,
NOT in KT. (Hard core 2 of §1/§"CHAIN": built lazily at concrete grade — no general Hodge-star API.)

#### (i)/(j) OD-4 + CHAIN-4 — the `Fin (d+1)` incidence discriminator — CLOSED

**OD-4 RESOLVED: existence/homogeneous route, alg-independence NOT a new site.** The prior "forced" lean
followed KT's *affine* phrasing (p. 698: `d+1` affinely-independent points → `(d−2)`-flats in `⋃Πⱼ` →
alg-independence). The landed d=3 formalization never takes that route — it works homogeneously (§1.42
R1-affine), so eq.-(6.67)'s `dim = D` is driven by **linear** independence of `d+1` homogeneous vectors
(`span_omitTwoExtensor_eq_top`, already general, only hyp `LinearIndependent ℝ pbar`, via Lemma 2.1) —
no affine/alg independence, no `(d−j)`-flat fact. The row #106 cross-product construction + the
affine-route bricks (`exists_affineIndependent_of_det_polynomial_ne_zero`,
`exists_detPolynomial_of_pointPolynomial`, `exists_hduality_witness_of_panel_incidence`,
`omitTwoExtensor_homogenize_eq_extensor_kept`) are DEAD (zero live call sites; the live d=3 dispatch
consumes `exists_homogeneousIncidence_of_normals`, linear). Alg-independence stays live only at site (a)
(the nested seed-rank transfer, `case_III_nested_rank_lower`, `AlgebraicIndependence.md` row #107,
carrier-lifted, unchanged), NOT site (b)/eq.-(6.67). One build-time residual (the per-join panel-membership
must close combinatorially from the orthogonality hyps — join `{a,b}` ⊂ `Πᵢ` iff `i+1∈{a,b}`, the
`D = d + C(d,2)` split) — CONFIRMED at the CHAIN-4b build (no alg-independence resurfaced). (The
existence route the pre-22d precedents Claim 6.4/6.9 + the d=3 N3a used carries to general `d`.)

**CHAIN-4 LANDED** (the four `Fin (k+1)→Fin (k+2)` leaves, all `k:=2` wrappers keep d=3 green):
**4a** `exists_homogeneousIncidence_of_normals_gen` (the OD-4 sub-leaf, clean lift via
`LinearIndependent.rank_matrix` + `exists_ne_zero_dotProduct_eq_zero`); **4b**
`exists_line_data_of_homogeneousIncidence_gen` (8496d61; signature correction: needs `hpbar` for the
kept-points-LI conclusion; carries the §(i) residual, CONFIRMED at build) consuming the landed
`omitTwoExtensor_eq_extensor_kept_gen` + `exists_independent_perp_pair_gen`; **4c** `case_III_claim612_gen`
(the `D`-span existential, pure numeral lift on `span_omitTwoExtensor_eq_top` +
`eq_zero_of_annihilates_span_top`); **4d** `exists_complementIso_ne_zero_of_homogeneousIncidence_gen`
(the discriminator, `complementIso (k:=k)(j:=2)`, consuming CHAIN-3's (h-4)
`extensor_join_proportional_complementIso_meet`).

#### (k) OD-7 — the `hcontract_k` / four-producer fold — CLOSED

The four 23a-carried producers fold into CHAIN's tail (not a successor sub-phase): the M4-forget
`exists_extensor_eq_panelSupportExtensor` is the same `⋀²ℝ⁴` duality CHAIN-3 lifts, and
`hbase_k`/`hcut_k`/`hcontract_k` route through it. `hcontract_k` (the last open producer, the Case-I
dispatch) lifted in 5 leaves (LANDED 2026-06-18): `case_III_realization_all_k_gen` (verbatim numeral
pass), `case_I_realization_nonsimple_gen` (+ the `_perp_grade` swap), LEAF-0
`linearIndependent_normals_of_algebraicIndependent_triple` (the one genuinely-new piece — a fixed-3-row
LI at `Fin (k+2)`, since h65 has only 3 vertices so the `k+1`-vertex selector of `…_general` is
unavailable for `k≥3`), `case_I_realization_h65_gen` (KT Lemma 6.5, the all-contractions-non-simple arm),
`case_I_dispatch_gen`. No motive/IH change; the
`_all_k` name is the dof variable, not grade.

#### (l)/(m)/(n) CHAIN-2 + CHAIN-2a + CHAIN-2c — the `Fin d` candidate family — CLOSED

**§(c)'s framing corrected:** `caseIIICandidate` / `case_III_old_new_blocks` / `case_III_rank_certification`
are already general-`k` (under `variable {k}`), need no work; the only `d=3`-pinned `CaseIII/` surface is
the dispatch (CHAIN-5's target). CHAIN-2 = build the `Fin d`-indexed reduction LAYER on top of the
already-general (reused-verbatim) certification chain + the closed CHAIN-1 `ιc`-block augment. The
`ChainData` record landed (`Induction/Operations.lean`, the contract-C.1 `structure`; its `deg_two`
`Fin`-arithmetic settled — interior vertices guarded `0 < (i:ℕ)`, predecessor edge `edge ⟨(i:ℕ)−1,_⟩`).

**CHAIN-1 CLOSED** (the `ιc`-block candidate machinery, `RigidityMatrix/Basic.lean`):
`linearIndependent_sumElim_candidateBlock_swap` + `linearIndependent_sumElim_block_swap` (KT eq. 6.62);
`linearIndependent_sum_pinned_block_augment_block` + `linearIndependent_sum_augment_candidateRow_block`
(the `+|ιc|` count lift; the single-`Unit` forms re-derived as `ιc := Unit` corollaries).

**CHAIN-2a VERDICT: re-index, not construct-from-scratch.** The per-`i` candidate reduction is a
re-instantiation of the already-general arm closer `case_III_arm_realization` (which wraps the
`case_III_rank_certification` rank bound, KT eq. 6.29/6.64) at the interior split index `i`; the ~20
`ρ`/`w`/gate hyps are SUPPLIED by two already-general producer calls (W6b
`exists_candidateRow_bottomRows_of_rigidOn` + the CHAIN-4d discriminator + `case_III_nested_rank_lower_all_k`
for the eq.-(6.22) `h622lb` nested rank bound), NOT constructed per-`i`. Landed: `chainData_split_w6b_gates` (the W6b half),
`chainData_split_realization` (2a-ii, the per-`i` reduction = the `case_III_arm_realization` re-index,
consuming `htrans` as 2c's single-`i` slot). The d=3 `fin_cases u`-over-panels and the general-`d`
pick-a-candidate-`i` are NOT the same dispatch (the d=3 three-panel split is the `d=3` collapse of the
`d`-candidate disjunction); the family disjunction + discriminator-picks-`i` glue is CHAIN-2c.

**CHAIN-2c — ROUTE β LOCKED (user-adjudicated, KT-source-verified, model-exp row 242).** KT's `d`
candidates `(G,pᵢ)` are built from ONE base `(G₁,q₁)` (the `v₁`-split, eq. 6.46); the others are
index-shift iso-copies (eq. 6.55 "exactly the same framework") via `ρᵢ` (eqs. 6.54–6.56), NOT fresh
splits — refuting route α's per-`i`-splits premise. The single redundancy `r` (eq. 6.52) is carried
`= ±r` across all `d` panels (eq. 6.66, the degree-2 fact "similar to (6.44)"); `Mᵢ` fails full rank
⟺ `r ⊥ C(Lᵢ)`; eq. 6.67's `D`-span (Lemma 2.1) forces some `Mᵢ` full. So 2c is a `Fin d`-generalization
of `case_III_candidate_dispatch` off the single `v₁` base: one W6b, one discriminator (2c-i
`exists_chainData_discriminator_pick`, LANDED), then `Fin (k+1)`-case on `u` into the per-`i` arm. (The
±r chain eq. 6.66, the §(l) standalone leaf **CHAIN-2b**, folds into 2c under route β — the shared `ρ₀`
serves as the discriminator's `r` for every candidate panel, no separate `Mᵢ`-bottom-row lemma.) The
landed 2a-ii (`chainData_split_realization`) is reused only at the `i=1`/`M₀` candidate; interior
candidates reach the arm via the relabel arm (2c-ii). The dispatch `chainData_dispatch` (2c-iii) and the
CHAIN-5 `hdispatch` contract (C.3) are unchanged (2c-ii is infrastructure below the dispatch).
**Blueprint-clarity obligation (owner-flagged):** route β absorbs KT's isos (6.54–6.56) + ±r chain (6.66)
into the Lean relabel arm, so the `lem:case-III` general-`d` node prose must materialize the single-base
construction, the index-shift isos `ρᵢ`, the single ±-carried redundancy `r`, and the (6.67)
discriminator (tracked in BlueprintExposition; written at phase-close).

#### (o)/(o′)/(o″)/(o‴) CHAIN-2c-ii — the uniform relabel arm — the route-B foundations CLOSED, the per-body fold DEAD

**The uniform `Fin d` relabel arm is genuinely-new** (not a numeral pass over the d=3 M₂/M₃): KT's `ρᵢ`
is a `(i−1)`-cycle `v₁→…→vᵢ`, and the landed relabel-transport engine (`ofNormals_relabel` /
`hasGenericFullRankRealization_of_splitOff_relabel` / `splitOff_isLink_relabel`) is hard-wired to a single
involution `Equiv.swap a v` — it does NOT generalize uniformly. Foundations LANDED: **2c-ii-α**
`ChainData.shiftPerm` + action lemmas (`Operations.lean`, `List.formPerm`); **2c-ii-β**
`ofNormals_relabel_perm` (the general-`Equiv.Perm` framework-transport, `.symm`-placement forced — FRICTION
idiom). **(A)** the graph-iso brick `splitOff_isLink_shiftRelabel_iff` LANDED
(`Operations.lean`, the `(ρ,σ) = (shiftPerm i.castSucc, shiftEdgePerm i)` intertwiner).

**§(o′)(C) correction:** the landed d=3 M₃ (`case_III_arm_realization_M3`) does NOT route through
`ofNormals_relabel` — it builds `qρ := q ∘ swap a v` inline and instantiates `case_III_arm_realization`
by **row-span transport** of the shared `ρ₀`/`w`: `hρe₀`-slot via G4d-i
`acolumn_mem_hingeRowBlock_of_span_rigidityRows`, `hρGv`-slot via W9a
`funLeft_dualMap_sub_acolumn_mem_span_rigidityRows`, `hwmem`-slot via W9b `case_III_bottom_relabel`.
These are two distinct relabel mechanisms; route B uses the row-span one.

**§(o″) route adjudication — VERDICT: route B (M₃-style shared-`ρ₀` row-span), route A REJECTED.** Route A
(feed a relabel-transported framework as 2a-ii's `hsplitGP`) is unprovable: 2a-ii runs its OWN W6b on
`Gt` producing a candidate `ρᵢ` that is a `Classical.choice` preimage (via `Submodule.mem_map` off the
triple-existential `exists_redundant_panelRow_ab_lam_of_rigidOn`), with NO functional relationship to `ρ₀`
— so the eq.-(6.66) identity route A needs (`ρᵢ = shiftPerm`-image of `ρ₀`) equates two independent
existential witnesses, not a provable equation. KT does route B (one `r` off the base, the ±r chain recycles
it; verified KT p. 698, and the landed dispatch — one `ρ0` fed unchanged/negated to all three arms). This
**orphans `ofNormals_relabel_perm`** (built for route A, zero call sites — confirm-and-delete at the
2c-ii-arm build, but NOT pre-emptively; the graph-iso `splitOff_isLink_shiftRelabel_iff` is NOT orphaned).

**Route B's landed pieces (T-W9a span transport):** the genuinely-new crux. The fold core
`wstep_foldr_mem_span_rigidityRows` (graph-free over `BodyHingeFramework`, `wstep v a c := (funLeft (swap a
v)).dualMap − a-column subtraction`); the un-relabelled intermediate-framework chain
`ChainData.shiftBodyFramework` over `shiftBodyGraph s := G − vₛ₊₁` (NOT splits — the splits enter only at
the arm closer) with its per-step accessors (`shiftBody_{isLink_succ_edge,isLink_pred_edge,deg_two,…}`,
`shiftBodyGraph_{isLink_pred_edge,deg_two(_right),off_succ,isLink_of_off_body}`, `shiftBodyFramework_htrans`)
and the membership half `shiftBodyList_foldr_mem_span_rigidityRows` (transports `span (G−vᵢ)`-rows →
`span (G−v₁)`-rows for `2 ≤ i`, span-only; the relabel side `wstep_foldr_funLeft_eq` +
`shiftPerm_eq_prod_map_swap_shiftBodyList` is a separate bridge applied at the arm). The abstract eq.-(6.44) `±r` vector identity
`candidateRow_ac_eq_neg` (`Claim612.lean:1194`) is LANDED; its chain-step carry is the landed
`interior_group_eq_baseRedundancy` (`Relabel/ChainColumn.lean:465`), KT eq. 6.44/6.66. (No `redundancy_panel_carry`
decl exists in tree — it was LANDED (model-exp row 268) then DELETED as an ORPHAN (row 271: its `hcol`/`hrest`
unsuppliable at the chain step; the §(o‴)-rejected per-body block carry, the 4×-mis-pin trap). Coordinator-corrected
2026-06-23; the landed chain-carry is `interior_group_eq_baseRedundancy`, NOT this deleted bridge.)

**§(o‴) the per-body W9b fold is DEAD (machine-verified).** NO per-body fold — pinned-`Tag`, pure-span, or
accumulating-sum — carries the bottom-family `(ab)`-block disjunct, because that block row is not a
`(G−vᵢ)`-span member and its residual `hingeRow vₛ₊₂ b ρ` has no interior `e_b`-row home (the natural
successor edge `edge (s+1)` is incident to the removed vertex, so does not survive `removeVertex`). The
landed single-step `funLeft_dualMap_bottomTag_mem_rigidityRows` always *terminates* the `(ab)`-block into a
genuine `e_b`-row, so it cannot chain; the `bottomTag_foldr_mem_rigidityRows` chain (and the proposed
`funLeft_dualMap_pinnedBlock_carry` strengthened single-step) are orphaned. The honest global transport is
KT's (6.62) whole-relabel row correspondence (the cycle generalization of d=3 M₃'s genuine-row arm). §(o‴)
returned FLAG-DON'T-FORCE; the route then re-routed to the `hρGv`-slot decomposition (I.7/I.8).

#### (I.7)/(I.7.10)/(I.8.0)–(I.8.6) the `hρGv`-slot route — the bare-row / telescope decomposition

The (I.7) bare-row extraction decomposition + the (I.7.10) KT-source re-derivation (verdict: option (b),
engine slot KT-faithful, the missing leaf is the bare-row membership) settled the arm-wiring slot→brick
map before the I.8 sub-decomposition.

The arm `chainData_relabel_arm` discharges (I.8.0) the four engine bindings (`Gv = G − vᵢ`, the relabelled
selector `endsσρ`, `qρ := q₀ ∘ shiftPerm i.castSucc`, `(a,b) = (vᵢ₊₁, vᵢ₋₁)` in `chainData_bottom_relabel`'s
emit order). (I.8.1) Engine-slot → landed-brick map: `hwmem ← chainData_bottom_relabel`; `hρe₀ ←` G4d-i
(one application at `vᵢ`, `candidateRow_ac_eq_neg` STAYS for this); `htrans`/`hLn`/`hgab`/`hρgate`/… the M₃
template; **`hρGv ← wstep_foldl_freshEdge_slot_mem`** — the slot the wiring did NOT reach cleanly.

(I.8.2) **P1 (BLOCKER, fixed):** `wstep_foldl_freshEdge_slot_mem` / `wstep_foldl_hingeRow_telescope` were
stated over `(w : ℕ → α) (hw : Function.Injective w)`, un-instantiable under the arm's `[Finite α]`
(`Injective (ℕ→α)` ⟹ `False`) — FRICTION idiom; restated finite-range (over `cd.vtx`, `cd.vtx_inj`).
(I.8.3) **P2 (the real math):** each surviving summand `hingeRow (vtx s)(vtx s+1) ρ₀` needs
`ρ₀ ⊥ panel(qρ(vtx s, vtx s+1))` — NOT given by `hρe₀` (which only annihilates the base spliced panel).
This is KT eq. (6.62)+(6.66) (`r` is a genuine row at each surviving edge by the iterated eq.-(6.44)
degree-2 carry) — TRUE and KT-grounded but a genuinely-new Lean leaf. The two-edge column brick
`acolumn_mem_hingeRowBlock_sup_of_span_rigidityRows` LANDED (the honest two-block analogue of G4d-i: at an
interior degree-2 vertex with two surviving links, the `a`-column lands in `hingeRowBlock e_c ⊔ hingeRowBlock
e_d`; G4d-i's single-edge premise is provably FALSE at an interior vertex). De-risk
`i3_freshEdge_surviving_rows_mem_deRisk` localized the obstruction to the per-edge perps. (I.8.3.v) route (a)
(the iterated carry) discharges P2 gated on the iteration leaf (the originally-pinned closed form
`ρ₀_perp_interior_chain_edge` — see refutation below); route (b) (`chainData_bottom_relabel`) is circular for
P2. (I.8.4)–(I.8.6) the buildable sub-step sequence + clause-(ii) verdict (arm wiring NOT mechanical, the
`hρGv` slot the one un-clean piece).

#### (I.8.3.v)–(I.8.20) the all-`i` lift — route W, the `hφ` seam, the whole-matrix wall — DEAD

This is the long dead saga the live route (A) escapes; collapsed to the route-death verdicts
`Phase23c.md`/`model-experiment.md` reference. Lessons → DESIGN.md *Statement faithfulness* + model-exp
Findings; the FRICTION traps (vacuous lemmas passing the gates, member-mapping) are filed there.

- **(I.8.3.v-REFUTED)** the closed-form `ρ₀_perp_interior_chain_edge` "isolated `=⊤`" signature was REFUTED
  (row 321 adversarial build): the forward fold-value-as-span-member induction is vacuous. The landed bricks
  on this route that the live (A) route reuses or confirm-and-deletes: the perp leaves
  `chainData_freshEdge_perp_of_baseRedundancy` / `_of_witness` / `_transport_base_to_candidate` /
  `chainData_freshEdge_slot_perp`, `freshEdge_surviving_row_mem` / `_of_witness`, the panel-correspondence
  **(I.8.8-GENERAL)** `panelCorrespondence_supportExtensor` (LANDED axiom-clean) and the per-edge bridge
  **(I.8.8-BRIDGE)** (LANDED), the A-1 signature change **(I.8.9-A1)** (LANDED), the regroup column foundation
  **(I.8.9-COL)** + isolation core **(I.8.9-COL2)** `BodyHingeFramework.edgeIndexedCombination_comp_single_eq_incident`
  (LANDED), the chain-induction **(I.8.9-SETTLE)** leaves (`interior_group_eq_baseRedundancy` /
  `interior_group_acolumn_eq_neg_baseRedundancy` / `anchor_group_acolumn_eq_baseRedundancy` /
  `funLeft_dualMap_sub_acolumn_seedAdvance_mem_span_rigidityRows`).
- **(I.8.7) route fork → (I.8.7-RESULT) Route W FORCED** (the i=3 de-risk failed: the "vacuous `=⊤`"
  obstruction Lean-confirmed). **(I.8.8) Route W producer** (re-derive KT eq.-(6.24)'s redundancy; option (b) transport-the-witness REFUTED; option
  (a′) buildable). **(I.8.9)** producer-core: the witness-DATA regrouping was the unsolved crux ((a′)
  under-specified); the **(I.8.9-RECON)/(I.8.9-PAIR)** adversarial recons converged that the pinned leaf 2 was
  the wrong object.
- **(I.8.10) T-1/T-2/T-3** family-transport decomposition (`chainData_candidateRow_edgeGrouped_transport_comb`,
  the off-slot/per-body `±r` leaves) — **SUPERSEDED by (I.8.11)**: mis-targeted; the family transport is
  ELIMINATED, not built (the genuine `e_b`-row route supersedes; the T-1/T-2 leaves
  `funLeft_dualMap_*_acolumn_*` revive only if a later arm step needs them). **(I.8.12)** holistic recon: the
  `hφ` seam is REAL (the `funLeft σ⁻¹`-maps-the-member wall, `mem_span_…_relabel`); ROUTE β LIKELY-DEAD.
- **(I.8.13) ROUTE-α** (the central telescope-survival question) ANSWERED: the telescope survives
  (`wstep_foldl_hingeRow_telescope`), but **(I.8.14)** leaf 2 as stated is FALSE (the recon-or-spike mandated
  ran, NEGATIVE), and **(I.8.15)** the leaf-1-def re-design (OPTION B, the gate-compatible per-step edge
  accumulator) does NOT close — the gate's edge-support window (`{edge 1,…,edge i}`) excludes the fresh `e₀`
  + `edge 0` the member needs (PROBE C/D). **(I.8.16)** `hφ`-at-source scoping; **(I.8.17)** the B1 span
  re-derivation at `endsσρ` BLOCKED (both sanctioned B1 sources dead).
- **(I.8.18) ADJUDICATION: both local fold re-shapes are DEAD** — the member-mapping wall is the shared
  obstruction; the directions either use the gate (dead by the edge-support window) or abandon the fold for
  whole-relabel transport (the member-mapping wall). FLAG-DON'T-FORCE; the residue named was the whole-matrix
  re-shape (→ §I.8.19) or route B carry-to-ENTRY. **(I.8.19)/(I.8.20)** the whole-matrix attempt + its
  refutation are collapsed in the WHOLE-MATRIX section below (LEAF-C re-introduces the design-rejected Fix B;
  the column-op submatrix-containment is the relabel-IMAGE inclusion, KT (6.62), so it SHARES the
  member-mapping wall). **This is the wall option (A) (`(I.8.21)` onward) escapes** by re-shaping the rank
  certification to KT's `±r`/`Mᵢ`-block form (`hρe₀` only, NO `hρGv`). The seed-advancing `hφ`-spine
  (`chainData_freshEdge_slot_mem`, `shiftBodyListAsc_foldl_mem_span_rigidityRows`,
  `chainData_relabel_arm_hρGv`, `chainData_relabel_arm_h…`, the ROUTE-α leaf 1 `shiftEndsAdv`/`_zero`/`_succ`)
  is confirm-and-delete CANDIDATE at the route-settle commit; `chainData_relabel_arm_hρGv` stays a CORRECT
  carried-hypothesis lemma; d=3 M₃ (`i=2`, no `hφ` slot) zero-regression unaffected.

---

## WHOLE-MATRIX RE-ARCHITECTURE — refuted (§(o‴)(I.8.19)–(I.8.20)); the LIVE (A) route follows (§(I.8.21)–(I.8.24))

**Status: DEAD ARC (refuted; the live wall-escape is (A), `(I.8.21)` onward).** This was the
post-23b attempt to escape the `hρGv` member-mapping wall by re-shaping the eq.-(6.60→6.64)
realization to KT's whole-matrix form (`hφ` consumed at the BASE `(ends₀,q)` directly,
§(o‴)(I.8.18)). Full blow-by-blow in git; lesson lifted → DESIGN.md *Statement faithfulness*
(±r-row mis-targeting) + model-exp Findings 2026-06-21. Collapsed to the refutation verdicts the
open (A) route and `Phase23c.md` (which says "do NOT re-attempt §I.8.18–I.8.20") rest on.

**(I.8.19) WHOLE-MATRIX DESIGN-PASS — VERDICT RETRACTED (LEAF C unsound).** The original pass
(2026-06-21, opus, source-verified vs A-1 `exists_candidateRow_bottomRows_of_rigidOn`
`Candidate.lean:400`, the engine `case_III_arm_realization`/`case_III_rank_certification`, the d=3
`case_III_arm_realization_M3`, CHAIN-1 in `RigidityMatrix/Basic.lean`, KT §6.4.2 eqs. 6.59–6.67
pp. 694–698) proposed: drop the seed-advancing `hφ` fold and re-derive the candidate redundancy at
the candidate framework `(G−vᵢ, endsσρ, qρ)` by firing A-1 there (LEAF C
`chainData_relabel_arm_hρGv_wholeMatrix`), filling the engine's `hρGv`/`hwmem` slots with no
member-transport. Four source-facts F1–F4 grounded it: **F1** A-1 is parametric in `(Gab,Gv,ends,q)`;
**F2** the engine/rank-cert bind all slots at one `(Gv,ends,q)` and `hρGv`/`hwmem` byte-match A-1's
outputs; **F3** at d=3 M₃ moves the member by a single-step W9a
(`funLeft_dualMap_sub_acolumn_mem_span_rigidityRows`) + genuine `e_b`-row `sub_mem`; **F4** CHAIN-1
supplies the LI half (`columnOp` `col_a += col_v`, eqs. 6.14–6.16; `hingeRow_comp_columnOp_apply`;
`linearIndependent_sumElim_candidateBlock_swap`; `linearIndependent_sum_augment_candidateRow_block`),
NOT a span-membership submatrix identity (the redundancy transport eqs. 6.63→6.64). The leaf sequence was LEAF A
(`chainData_candidate_rigidOn`, member-free rigid-on transport, P=2), LEAF B
(`chainData_candidate_h622lb`, the rank-bound transport, the flagged P=3 crux), LEAF C (the
candidate-A-1 invocation), LEAF D (`chainData_bottom_relabel`, stays).

**(I.8.19)-ADDENDUM — LEAF C REFUTED (adversarial self-check, coordinator-verified vs the landed
dispatch).** The landed `case_III_candidate_dispatch` establishes a SINGLE shared `ρ₀` ONCE at the
base (A-1 fires once `:388–391`, normalized to `ρ0` `:404–411`), runs the discriminator ONCE on `ρ0`,
threads `ρ0` into every `fin_cases u` arm; the capstone
`exists_complementIso_ne_zero_of_homogeneousIncidence_gen` (`Claim612.lean:1462`) takes ONE `r`
(KT eq. 6.66 `±r` carry — single-`r` is structural). A-1's conclusion is `∃ρ, …`, so firing it fresh
at candidate `i` yields a `ρ_cand_i` NOT pinned to `ρ₀`; tying them needs either (a) the fixed-member
identity `hingeRow v₀v₂ ρ₀ ∈ span (candidate i)` = the dead member-mapping wall, or (b) a
`ρ_cand_i = ±ρ₀` carry = KT (6.66), the eq.-(6.44) chain-cancellation the `hφ`-spine perp/telescope
encodes. **LEAF C RELOCATES the seam, doesn't dissolve it** — structurally the design-rejected Fix B
(per-`i` re-seed). F1/F2 are necessary-not-sufficient (missed the discriminator's single-`r`
coupling); the §I.8.19(a) "no member-mapping transport" claim and the "CONFIRMED ORPHAN" map are
RETRACTED (downgraded to confirm-and-delete CANDIDATEs pending route-settle). LEAF A stays
independently fine; the single-step W9a stays (d=3 building block); d=3 M₃ (`i=2`) zero-regression
unaffected.

**(I.8.20) THE COLUMN-OP / WHOLE-MATRIX SPAN-INCLUSION QUESTION — ADJUDICATED: ROUTE DIES, IT IS THE
WALL** (2026-06-21, opus, re-derived from the landed bodies + KT pp. 696–698 read directly). The
(I.8.19)-ADDENDUM(C) open question — can the column-op carry the FIXED `ρ₀` membership where the fold
could not — is SETTLED AGAINST the route. KT's column-op submatrix-containment (6.60→6.64) is NOT a
fixed-`ρ₀` span-inclusion: KT (6.62) verbatim ("row `(v₀v₂)ᵢ∗` ⇔ row `(v₀v₁)ᵢ∗`", column
correspondence "follows from the isomorphism `ρᵢ`") is the relabel-IMAGE inclusion, which MOVES the
member off `hingeRow v₀v₂ ρ₀`. F4 re-confirmed (`linearIndependent_sumElim_candidateBlock_swap` /
`linearIndependent_sum_augment_candidateRow_block` conclude `LinearIndependent`, with `span` only in a
hypothesis; `hingeRow_comp_columnOp_apply` is the pure-`v`-column fact — none is a span-inclusion);
`chainData_bottom_relabel` (`Relabel.lean:1961`, the only landed base→candidate transport) re-confirmed
to MOVE the member. So the genuinely-new obligation `hingeRow v₀v₂ ρ₀ ∈ span (R(G,pᵢ).rigidityRows)`
for the fixed shared `ρ₀` is unreachable by the column-op; the whole-matrix route SHARES the
member-mapping wall §(o‴)(I.8.15)/(I.8.18) ruled dead in the fold form. The residue is route B (carry
`ρ₀`/`hφ@endsσρ` to ENTRY, flagged LIKELY-DEAD) or a fundamental rethink — re-pointed to that fork for
user adjudication. No Lean landed; tree byte-clean; `chainData_relabel_arm_hρGv` stays a CORRECT
carried-hypothesis lemma. **(This fork is what (A), `(I.8.21)` onward, resolves.)**

**(I.8.21) OPTION (A) FEASIBILITY RECON — VERDICT: (A) DOES NOT FEED THE EXISTING ENGINE; it is a
GENUINELY-NEW realization architecture (re-shape the rank-certification to KT's `rank Mᵢ + rank(base∖row)`
decomposition), NOT more churn on the dead fixed-member-transport paradigm — but its cost is SUBSTANTIAL and
its hardest leaf is genuinely-new. GO/NO-GO FOR THE USER (2026-06-21, opus design-pass; every load-bearing
claim re-derived from the landed `def`/`theorem` bodies AND KT pp. 696–698 read directly from the PDF, NOT
inherited from the prior pins or this recon's framing; docs-only, no Lean landed, tree byte-clean).** This
settles the prompt's make-or-break question (1) and the two sub-routes (2) + salvage map (3). Verified against
the engine `case_III_arm_realization` (`Arms.lean:72`, `hρGv` slot `:91`, the `hrank` call `:112–115`), the
rank-cert `case_III_rank_certification` (`Candidate.lean:1472`, `hρGv` `:1486`, **its SINGLE use of `hρGv`**
`:1606–1611`, conclusion = `D(|V(G)|−1) ≤ finrank (span (caseIIICandidate …).rigidityRows)` `:1495–1498`),
A-1 `exists_candidateRow_bottomRows_of_rigidOn` (`Candidate.lean:400`, the `ρ = ∑ⱼ lamAB j • rab j`
construction `:432`, `rab j ∈ hingeRowBlock e₀` `:431`), the d=3 M₃ arm `case_III_arm_realization_M3`
(`Relabel.lean:2537`, `hρGv` at the BASE `:2562`, the single-step W9a `:2699–2706`, the `sub_mem` recombine
`:2712–2724`), the single-step carrier W9a `funLeft_dualMap_sub_acolumn_mem_span_rigidityRows`
(`Relabel.lean:865`, `hφ` at the BASE `Fv` `:876`, conclusion at `Fva` `:877–880`), `hingeRow_sub_hingeRow_eq`
(`Basic.lean:565`), `screwDim k = (k+2).choose 2 = D` (`Basic.lean:87`), the slot core
`chainData_freshEdge_slot_mem` (`Relabel.lean:4158`, conclusion = the MOVED member `:4174`), the dispatch's
single-`ρ0` block (`Realization.lean:404–441`, M₃ arm at `:588–592` passing `hρ0Gv` UN-moved), the capstone
`exists_complementIso_ne_zero_of_homogeneousIncidence_gen` (`Claim612.lean:1462`, ONE `r`), and KT 2011 §6.4.2
eqs. (6.59)–(6.67) pp. 696–698 (`.refs/katoh-tanigawa-2011-molecular-conjecture.pdf`, pdf pp. 50–52, read
directly).

  *(0) THE DECISIVE SOURCE FACT — KT's abstract `r ∈ ℝ^D` IS the project's `ρ₀`, ALREADY; (A) is not "add an
  abstract `r`", it is "re-shape what consumes it".* Read directly (KT pp. 697–698): KT's `r := ∑ⱼ
  λ_(v₀v₂)ⱼ rⱼ(q(v₀v₂)) ∈ ℝ^D` (6.66 preamble) is the ONE redundancy vector tested against all `d` panels via
  (6.67). In the Lean, `ScrewSpace k` has `Module.finrank = D = screwDim k = (k+2).choose 2` (`Basic.lean:87`),
  and A-1 (`Candidate.lean:432`) builds `ρ₀ = ∑ⱼ lamAB j • rab j` with `rab j ∈ hingeRowBlock e₀` — *literally*
  KT's `r = ∑ⱼ λ_(v₀v₂)ⱼ rⱼ(q(v₀v₂))`, the `(v₀v₂)`-row's `λ`-combination of screw-level functionals. **So
  `ρ₀ : Module.Dual ℝ (ScrewSpace k)` IS KT's abstract `r`.** The project does not LACK the abstract `r`; it
  WRAPS it in a span-membership `hingeRow a b ρ₀ ∈ span(rigidityRows)` and consumes THAT. (A)'s "carry the
  abstract `r` + the `Mᵢ`-block FORM" therefore is NOT a new carrier — it is a re-shape of the *consumer* (the
  rank-certification) from "candidate-side span membership of `hingeRow a b ρ₀`" to KT's "`±r` equality of
  `ℝ^D` vectors inside `Mᵢ`, with the rank decomposition `rank Mᵢ + rank(base∖row)`".

  *(1) MAKE-OR-BREAK: DOES (A) ESCAPE THE WALL, OR DOES THE ENGINE SLOT FORCE THE FIXED-MEMBER MEMBERSHIP?
  VERDICT: the engine slot, AS LANDED, intrinsically requires the fixed-member span membership AT THE CANDIDATE
  — (A) cannot feed the existing engine; it MUST re-shape the rank-cert. But (A)'s re-shaped target genuinely
  escapes the wall (it carries `±r` as an ℝ^D equality, never a fixed-member transport). Both halves are
  source-forced.*
  - **The engine consumes `hρGv` as a FIXED-MEMBER candidate membership — re-confirmed at the SINGLE use
    site.** `case_III_rank_certification` uses `hρGv` exactly once (`Candidate.lean:1606–1611`): to place the
    collapsed candidate row `hingeRow v a ρ` in `span F₀` via `hingeRow v a ρ = hingeRow v b ρ − hingeRow a b
    ρ` (`hingeRow_sub_hingeRow_eq`, `Basic.lean:565`), where `hingeRow v b ρ` is a genuine `e_b`-row and
    `hingeRow a b ρ` is supplied by `hρGv` (lifted by `hFvle : span F_v ≤ span F₀`). The slot type is
    `hingeRow a b ρ ∈ span (ofNormals Gv ends q).rigidityRows` with `(a, b)` the candidate's degree-2 vertex's
    two neighbours and `Gv = G−vᵢ`, `ends = endsσρ`, `q = qρ` (F2; `Arms.lean:91`, FORCED by the `hrank` call
    `:112–115` whose `F₀ := caseIIICandidate G ends q …` is the CANDIDATE matrix). **This IS the fixed-member
    candidate membership the wall (§I.8.18/I.8.20) ruled has no source for `i ≥ 2`.** So feeding the EXISTING
    engine the (A)-carried data does NOT escape the wall — the engine's slot is the wall, re-stated.
  - **WHY d=3 is not a counterexample (the engine slot is satisfied there by a MOVED member, length-1 only).**
    At d=3 the M₃ arm takes `hρGv` at the BASE `ofNormals (G−v) ends₀ q` (`Relabel.lean:2562`, `(a,b)` = base
    vertices), applies ONE W9a step (`:2699–2706`) sending `hingeRow a b ρ ↦ hingeRow v b ρ` (member MOVED
    `a↦v`), and recombines with the genuine candidate `e_b`-row `hingeRow v b ρ` via `sub_mem` (`:2712–2724`).
    The single swap *is* KT's (6.62) at d=3, and the moved member lands as a genuine candidate row. The engine's
    `hρGv` slot for the M₃ arm is the BASE membership (the arm moves it internally) — so the engine slot does
    NOT demand a fixed candidate membership at d=3; the arm satisfies it by a length-1 move. The general-`d`
    fold cannot replicate this (the `(i−1)`-cycle is not a single adjacent swap, §I.8.18(a)), which is exactly
    why the wall is an emergent multi-step obstruction.
  - **WHY (A)'s re-shaped target ESCAPES the wall (the source-faithful decomposition).** KT does NOT certify
    the candidate's own rigidity rows span `D(|V|−1)` via a candidate-side `hingeRow a b ρ₀` membership. KT
    (6.61→6.65) exhibits `R(G,pᵢ)` after column-ops as the block matrix `(6.64)` whose **top-left `D×D` block is
    `Mᵢ`** and whose **bottom block is `R(G₁ ∖ {(v₀v₂)ᵢ∗}, q₁)`** — the BASE matrix minus the one redundant
    row — then concludes `rank R(G,pᵢ) ≥ rank Mᵢ + rank R(G₁∖row, q₁) = D + D(|V|−2) = D(|V|−1)` (6.65 tail).
    The redundancy enters ONLY as `Mᵢ`'s second row `∑ⱼ λ_(vᵢvᵢ₊₁)ⱼ rⱼ(q(vᵢvᵢ₊₁))`, which (6.66) proves equals
    `±r` (the ONE abstract `ℝ^D` vector) "due to `vᵢ` degree-two in `G₁`". **This `±r` is an EQUALITY of `ℝ^D`
    vectors — NOT a span membership, NOT a member transported across the relabel.** The member is allowed to
    move (KT's row is `(vᵢvᵢ₊₁)`, the candidate edge); only the abstract `r` is held fixed, and it is held fixed
    by the (6.44) degree-2 *cancellation* (the landed telescope/perp subtree's content, §I.8.20(d)), NOT by a
    transport. So KT's shape structurally never anchors a fixed dual-functional to a framework — it is exactly
    the escape the prompt's (A) describes. **CONCLUSION (1): (A) escapes the wall iff the rank-cert is re-shaped
    to KT's `rank Mᵢ + rank(base∖row)` decomposition; it CANNOT escape by feeding the existing engine, whose
    `hρGv` slot IS the wall.**

  *(2) THE TWO SUB-ROUTES.*
  - **Non-gate composition — VERDICT: DEAD / collapses back to route-1 (the wall), NOT distinct.** "Keep the
    telescope, re-anchor at the genuine base via a non-gate composition" was probed at §I.8.18(a): a per-step
    move that is NOT the `hends'_off` gate is not a fold-over-the-gate at all — it is a from-scratch
    span-transport of the relabel applied to a span membership, i.e. the whole-relabel transport of §I.8.18(2)
    /(I.8.20)(e), where the member-mapping wall lives. A "whole-cycle selector move in one shot" is precisely
    the fixed-member relabel-image transport `chainData_bottom_relabel` already supplies — and it MOVES the
    member (`Relabel.lean:1982–1994`, `(I.8.20)(b)`). A "different per-step invariant" that keeps the member
    fixed across the selector relabel has no source (the wall). **So the telescope+LEAVES-1–4 are reusable only
    in their CURRENT role — encoding the (6.44)/(6.66) `±r` cancellation that the `Mᵢ`-block re-shape (below)
    also needs — not as the basis of a new non-gate fold that escapes the wall.** Sub-route (2a) is not a third
    route; it is the dead fold paradigm.
  - **Matrix / abstract-`r` representation — VERDICT: this IS the live route, and it forces a MORE
    matrix-explicit representation than the basis-free `span` API supplies. This is the genuinely-new,
    cost-unknown part.** The project is basis-free: `rigidityRows` is a *set of dual functionals*, rigidity is a
    `finrank (span …)`. KT's `rank Mᵢ + rank(base∖row)` decomposition (6.64) needs the candidate matrix
    `R(G,pᵢ)` to be exhibited as a BLOCK matrix with the base submatrix (minus one row) in one block and `Mᵢ` in
    the corner — a *block-rank-additivity* statement (`rank ≥ rank(corner block) + rank(complementary block)`).
    The basis-free analogue is provable in principle (a span/`finrank` lower bound by exhibiting `D` rows whose
    images mod `span(base∖row)` are independent — the `Mᵢ` full-rank — plus the `D(|V|−2)` base rows), but it is
    a DIFFERENT certification shape from the landed `case_III_rank_certification` (which counts `D(|V|−1)` rows
    of the candidate directly via `hρGv`). The genuinely-new infra is: **(α)** a block-rank-additivity / quotient
    lower-bound lemma over the basis-free `rigidityRows` carrier (`rank(span A) ≥ dim(quotient corner) + rank(span
    B)` for `B ⊆ A`), **(β)** the `Mᵢ`-block as `D` rows of `R(G,pᵢ)` (the `r(Lᵢ)` rows + the `±r` row) whose
    quotient-independence is the discriminator's `r ⊥ C(Lᵢ)` fact (CHAIN-3/4, already landed as the
    discriminator, but re-aimed at the `Mᵢ` corner rather than the candidate-row membership), and **(γ)** the
    (6.66) `±r` equality `∑ⱼ λ_(vᵢvᵢ₊₁)ⱼ rⱼ(q(vᵢvᵢ₊₁)) = ±r` as an `ℝ^D`/`ScrewSpace`-vector identity — the
    (6.44) degree-2 cancellation the landed telescope already proves at the *membership* level, re-expressed at
    the *abstract-vector* level. **This is the matrix-explicit representation the prompt flagged as the
    cost-unknown part: it is real, and it touches the rank-certification architecture, not just one leaf.**

  *(3) SALVAGE / ORPHAN-CANDIDATE MAP (decided at a route-SETTLE commit, NOT here — per §I.8.20).*
  - **REUSE under (A) (high confidence):** the discriminator capstone
    `exists_complementIso_ne_zero_of_homogeneousIncidence_gen` (`Claim612.lean:1462`, the single-`r` (6.67) test
    — (A) keeps the single-`r` structure verbatim, it is the whole point); CHAIN-3/4 (the `⋀^{d−1}` duality +
    Claim 6.12); A-1 `exists_candidateRow_bottomRows_of_rigidOn` (the base redundancy + the `ρ₀ = ∑ λ • rab`
    abstract-`r` construction, fired ONCE at the base as the dispatch already does, `Realization.lean:388–391`);
    the dispatch's single-`ρ0` block (`Realization.lean:404–441`) UNCHANGED; the (6.44) degree-2 cancellation
    content of the telescope `wstep_foldl_hingeRow_telescope` + LEAVES 1–4 + the perp sub-tree (re-aimed from the
    membership level to the `±r` ℝ^D-equality level — sub-route (2b)(γ); likely a re-statement, not a rebuild);
    the d=3 M₃ arm + single-step W9a (`Relabel.lean:865`/`:2537`) UNCHANGED (zero-regression).
  - **ORPHAN-CANDIDATE under (A) (the seed-advancing `hφ`-spine, as §I.8.20 left it):** the slot core
    `chainData_freshEdge_slot_mem` (`:4158`), the seed-fixed fold `shiftBodyListAsc_foldl_mem_span_rigidityRows`
    (`:1807`), the seed-advancing gate (`:1201`), `chainData_relabel_arm_hρGv` (`:4647`) — these encode the
    MEMBERSHIP-level fold that (A) replaces with the `Mᵢ`-block rank decomposition. Their fate is the
    route-SETTLE commit's, not this recon's (§I.8.20 / `notes/CLAUDE.md` confirm-and-delete discipline). The
    ROUTE-α leaf 1 `shiftEndsAdv` + T-1/T-2 stay confirmed-orphan-candidates.
  - **MUST CHANGE under (A):** `case_III_rank_certification` (`Candidate.lean:1472`) — its `hρGv` slot and its
    `D(|V|−1)`-rows-of-the-candidate certification become the `rank Mᵢ + rank(base∖row)` decomposition; and
    `case_III_arm_realization` (`Arms.lean:72`) — its `hρGv` slot is replaced by the `Mᵢ`-block / `±r` inputs.
    **These are below the CHAIN↔ENTRY contract (C.0–C.6) and below the motive/IH** (re-verified: the rank-cert /
    arm are infrastructure beneath the dispatch C.3 and beneath the `ChainData` record C.1; the dispatch's
    `hdispatch` consume-shape and the 0-dof motive are untouched — §I.8.18 confirmed this, and the engine-slot
    re-shape does not move it because the dispatch threads ONE `ρ0` either way). **`d=3` M₃ (`i=2`) MUST stay
    zero-regression**, which constrains the re-shape: the new rank-cert must specialize to the d=3 M₃ arm's
    single-step-move shape, OR the d=3 wrapper keeps the *current* rank-cert and only the general-`d` arm uses
    the `Mᵢ`-block one (a fork in the rank-cert, the cleaner option to preserve zero-regression).

  *(VERDICT — GO/NO-GO, the honest cost band).* (A) is the ONE root-attacking route that is NOT the dead
  fixed-member-transport paradigm: it carries the abstract `r` (= the landed `ρ₀`) and re-shapes the
  rank-certification to KT's `rank Mᵢ + rank(base∖row)` block decomposition (6.64–6.65), where the redundancy is
  a `±r` ℝ^D-equality (6.66), never a fixed dual-functional transported across the relabel. **It genuinely
  escapes the wall — but it does NOT feed the existing engine; it requires re-shaping
  `case_III_rank_certification` + `case_III_arm_realization` (below the contract/motive, but the
  rank-certification architecture, not a leaf).** The genuinely-new infra is the basis-free block-rank-additivity
  lemma (2b)(α) + the `Mᵢ`-corner quotient-independence (2b)(β) + the (6.66) `±r` abstract-vector identity
  (2b)(γ); the discriminator, A-1, the single-`r` dispatch, and the (6.44) cancellation content survive (reuse,
  re-aimed). **HONEST COST BAND: a recon-first sub-phase, ~8–14 commits** — the block-rank-additivity infra
  de-risk spike (2–3, the genuinely-new + cost-unknown part: does the basis-free `finrank (span …)` carrier admit
  a clean quotient/block lower bound, or does the `ScrewSpace` `≃ₗ`/§38-defeq friction bite?), the `Mᵢ`-corner +
  the (6.66) `±r` identity re-statement (2–4), the rank-cert re-shape + the arm re-shape with d=3-fork
  preservation (2–4), the arm-shell + 2c-iii dispatch wire-up (1–2), the orphan confirm-and-delete (1) — PLUS the
  contingency that the block-rank-additivity de-risk fails (then the basis-free API genuinely cannot carry KT's
  decomposition without an explicit `Matrix`/coordinate model of `R(G,pᵢ)`, a much larger representation
  investment — STOP and escalate). **This is a deliberate go/no-go: (A) is well-motivated (root-attacking,
  KT-faithful, reuses the hard discriminator + cancellation machinery) but the rank-cert re-architecture is a
  substantial investment whose hardest leaf (basis-free block-rank-additivity) is genuinely-new and cost-unknown.
  The user/coordinator decides whether to open the (A) sub-phase (build the block-rank-additivity de-risk spike
  FIRST) or hold.** The residue if (A) is held or its de-risk fails is route B (carry `ρ₀`/`hφ@endsσρ` to ENTRY,
  flagged LIKELY-DEAD, §I.8.20) — but route B does not attack the root, so the real fork is **(A)-sub-phase
  (de-risk-first) vs. deliberate hold**.

  **CLAUSE (i) HONESTY.** Every load-bearing claim re-derived this pass from the landed bodies AND the KT PDF:
  the abstract-`r`-IS-`ρ₀` identification from A-1's actual `ρ = ∑ⱼ lamAB j • rab j` construction
  (`Candidate.lean:432`) + `screwDim = D` (`Basic.lean:87`) + KT's `r = ∑ λ rⱼ(q(v₀v₂))` (p. 698 read directly);
  the engine's SINGLE `hρGv` use from the rank-cert body (`Candidate.lean:1606–1611`, the
  `hingeRow_sub_hingeRow_eq` collapse, not a deeper consume); KT's `rank Mᵢ + rank(base∖row)` decomposition from
  (6.64)/(6.65)-tail read directly (the bottom block is `R(G₁∖row, q₁)`, NOT the candidate's rigidity rows — the
  structural divergence from the project's candidate-side certification); the `±r` ℝ^D-EQUALITY (not membership)
  from (6.66) read directly; d=3 zero-regression from the M₃ arm's BASE `hρGv` + single-step move
  (`Relabel.lean:2562/2699–2724`). **CLAUSE (ii) HONESTY.** This is a FLAG-DON'T-FORCE go/no-go: (A) is NOT
  declared buildable (its hardest leaf, basis-free block-rank-additivity, is named genuinely-new + cost-unknown
  with an explicit STOP-and-escalate-to-a-`Matrix`-model branch if the de-risk fails), and NOT declared dead (it
  is the one route that structurally escapes the wall, source-confirmed against KT's `Mᵢ`-block / `±r` shape). No
  buildable-looking signature is manufactured for the block-rank-additivity leaf — it is stated as the de-risk
  target. The make-or-break question (1) is answered precisely (the existing engine slot IS the wall; (A) needs
  the rank-cert re-shape to escape it). No Lean landed; tree byte-clean; no decl declared orphaned (confirm-and-
  delete fires at the route-SETTLE commit per §I.8.20); `d=3` unaffected.

**(I.8.22) (2b)(β) `Mᵢ`-CORNER LI-MODULO-BASE PIN — VERDICT: THE PROMPT'S (2b)(β) FRAME MIS-LOCATES THE WALL;
THE `Mᵢ` CORNER IS ALREADY LANDED (INLINE), AND THE GENUINELY-NEW PART OF (A) IS THE `±r` REDUNDANCY ROW'S
MEMBERSHIP-AT-THE-CANDIDATE = THE WALL — `finrank_span_rigidityRows_ge_of_corner` IS THE WRONG CONSUMER FOR
(A) AS LANDED, AND (2b)(β) IS NOT A SMALLEST-NEXT-COMMIT. FLAG-DON'T-FORCE STOP (2026-06-21, opus design-pass;
every load-bearing claim re-derived from the landed `def`/`theorem` bodies AND KT pp. 696–698 read directly
from the PDF — NOT inherited from the prior pins, the de-risk-spike framing, or this prompt's (2b)(β)/(γ)
spec; docs-only, no Lean landed, tree byte-clean).** This settles the prompt's recon items (1)–(3) and the
make-or-break question; it does NOT pin a buildable (2b)(β) signature, because the honest reading of the
landed cert is that (2b)(β) as posed is mis-targeted. Verified against `case_III_rank_certification`
(`Candidate.lean:1472`, the combined family `(sn ⊕ Unit) ⊕ ιb` `:1596–1599`, the SINGLE `hρGv` use
`:1606–1611`), its W6c assembler `case_III_full_family_restriction` (`Candidate.lean:1366`, the `sn`-block +
`Unit` candidate row + `ro`-bottom), the de-risk leaf `finrank_span_rigidityRows_ge_of_corner`
(`Candidate.lean:1661`), the discriminator `exists_complementIso_ne_zero_of_homogeneousIncidence_gen`
(`Claim612.lean:1462`, ONE `r`, ONE `u`), its dispatch consumer `case_III_candidate_dispatch`
(`Realization.lean:268`; A-1 once `:388–391`, discriminator once `:439–441`, `fin_cases u` → ONE arm
`:495–599`), the M₃ arm `case_III_arm_realization_M3` (`Relabel.lean:2537`, the `hρGv` `sub_mem` peel
`:2655–2724`), the telescope `wstep_foldl_hingeRow_telescope` (`Relabel.lean:3209`, a **`hingeRow`-level**
identity), and KT 2011 §6.4.2 eqs. (6.59)–(6.67), pp. 696–698 (`.refs/…`, pdf pp. 50–52, read directly).

  *(0) THE DECISIVE NEW SOURCE FACT — THE LANDED CERT ALREADY IS KT's `Mᵢ + base` DECOMPOSITION; THE `Mᵢ`
  CORNER IS NOT GENUINELY-NEW.* `case_III_rank_certification`'s `D(|V|−1)` bound is built from ONE combined LI
  family `fam = (sn ⊕ Unit) ⊕ ιb` (`Candidate.lean:1596–1599`, count `((D−1)+1) + D(m_v−1) = D·m_v`),
  whose three blocks **are exactly KT's (6.64) row groups**: `sn` = the `D−1` independent panel rows of the
  candidate `e_a`-hinge = KT's `r(Lᵢ)` (the `D−1` rows of `Mᵢ`); the `Unit` row `hingeRow v a ρ` = KT's `±r`
  redundancy row (the second `Mᵢ` row, eq. (6.64) `(v₀v₁)ᵢ∗`); `ιb` = the `D(m_v−1)` transported base rows =
  KT's `R(G₁∖{(v₀v₂)ᵢ∗}, q₁)`. The `Mᵢ`-full-rank ingredient — KT's "`r ∉ row-space r(Lᵢ)`, i.e.
  `r(C(Lᵢ)) ≠ 0`" (p. 698) — enters as `hρgate`/`hr` (`:1484`/`:1514`), the discriminator's `r ⊥ C(Lᵢ)`
  negation, threaded through W6c's `linearIndependent_sumElim_candidateRow_iff`. **So the project's basis-free
  cert ALREADY realizes KT's `rank Mᵢ + rank(base∖row)` decomposition — inlined into one LI family rather than
  factored through an abstract block-rank lemma.** This OVERTURNS the prior pins' premise that (A) must
  "re-shape the cert to KT's `Mᵢ`-block decomposition" via the new `finrank_span_rigidityRows_ge_of_corner`:
  the cert is not the wrong shape, it is the *right* shape with one slot (`hρGv`) wired wrong.

  *(1) MAKE-OR-BREAK (the prompt's q.1): DOES THE DE-RISK LEAF FEED A WORKING (A) ARM? VERDICT: NO — the
  prompt's (2b)(β) `g/ι/W/hLI` shape is MIS-LOCATED.* The prompt asks what `g, ι, W` are and whether the
  discriminator produces `hLI` for `finrank_span_rigidityRows_ge_of_corner`. Honest answer, source-grounded:
  - **`finrank_span_rigidityRows_ge_of_corner` proves a `finrank W + |ι| ≤ finrank(span F.rigidityRows)`
    bound for `W ≤ span F.rigidityRows` and `g` whose images mod `W` are LI.** To recover `D(|V|−1)` it would
    need `W` = `span(R(G₁∖row, q₁))` with `finrank W = D(|V|−2)` and `|ι| = D` corner rows LI mod `W`. But
    **`W` here would have to be a subspace of `span F.rigidityRows` for `F = the candidate`** — i.e. the base
    block must already sit *inside the candidate's own rigidity-row span as the relabel-image*. THAT inclusion
    (`span(base-rows-as-candidate-rows) ≤ span(candidate.rigidityRows)`) is the column-op / relabel-image
    submatrix-containment §(I.8.20) ADJUDICATED DEAD: KT's (6.62) maps the base rows to candidate rows by a
    member-*moving* correspondence, and the de-risk lemma's `hg : ∀ i, g i ∈ span F.rigidityRows` + `hWS : W ≤
    span F.rigidityRows` both DEMAND that relabel-image inclusion as an INPUT. **The de-risk leaf does not
    PRODUCE the inclusion; it CONSUMES it. The wall is upstream of the leaf, in establishing `hWS`/`hg`.**
  - **The `Mᵢ` corner's `hLI` is NOT the hard part and the discriminator already discharges its analogue.**
    The landed cert's `case_III_full_family_restriction` proves the `(sn ⊕ Unit)` block (= the `D` `Mᵢ` rows)
    LI relative to the bottom — that IS the `Mᵢ`-corner-LI-mod-base content, and it goes through on `hρgate`
    (the single discriminating panel). So even the genuinely-`Mᵢ`-corner half of (2b)(β) is **already landed
    inline** (not via the de-risk leaf, but it exists). The de-risk leaf `…_ge_of_corner` is a *generic
    restatement* of that same count in abstract block form — useful only if one re-factors the cert to consume
    `W = span(base∖row)` explicitly, which re-introduces the dead inclusion.

  *(2) THE SINGLE-PANEL DISCRIMINATOR IS NOT A CONCLUSION-SHAPE MISMATCH (the prompt's worry, REFUTED).* The
  prompt flags "the discriminator is a single-panel `∃u, r(C(Lᵤ))≠0`, not D-rows-LI." Source verdict: this is
  exactly right and exactly what KT needs — **no mismatch.** KT (6.65) requires "at LEAST ONE of
  `M₀,…,M_{d−1}` has full rank", and (6.67)/Lemma 2.1 supply it: `r` cannot be ⊥ to `⋃ᵢ C(Lᵢ)` (which spans
  `ℝ^D`), so SOME `C(Lᵤ)` is not ⊥ `r`, making `Mᵤ` full-rank. The dispatch realizes this by `fin_cases u` →
  ONE arm at the discriminating panel `Lᵤ`; **the other `Mᵢ` blocks are never built.** So (2b)(β)'s "exhibit
  the `Mᵢ` block as D rows … prove their images mod W LI" mis-states the obligation: KT/the engine need ONE
  full-rank `Mᵤ`, the discriminator selects it, and the *single chosen* `Mᵤ` corner is already the landed cert's
  `(sn ⊕ Unit)` block. **There is no D-rows-LI-for-all-`i` obligation to discharge.**

  *(3) WHERE THE GENUINELY-NEW WORK ACTUALLY IS — RE-CONFIRMED AS THE WALL, NOT (2b)(β).* The one slot of the
  landed cert wired wrong for general-`d` is `hρGv` (`Candidate.lean:1486`, used `:1606–1611`): the `±r`
  redundancy row `hingeRow a b ρ ∈ span(R(candidate-base-block))` at the relabelled candidate. The cert's `Unit`
  candidate row collapses (eq. (6.27)) to `hingeRow v b ρ − hingeRow a b ρ`, and the `hingeRow a b ρ` summand is
  supplied by `hρGv` (lifted `span F_v ≤ span F₀`). **This `hingeRow a b ρ`-membership-at-the-candidate is the
  member-mapping wall** (§I.8.18/I.8.20): for `i ≥ 2` no fixed-member transport reaches it, because KT's (6.62)
  MOVES the member (the `(v₀v₂)ᵢ∗ ⇔ (v₀v₁)ᵢ∗` correspondence). The de-risk leaf does not touch this slot. So:
  - **(2b)(β) as posed (`Mᵢ`-corner LI-mod-base feeding `…_ge_of_corner`) is NOT the smallest next commit, and
    is NOT even on the critical path:** the `Mᵢ` corner is landed; the leaf consumes (does not produce) the dead
    inclusion; the real obstruction is the `±r` row's candidate-membership = the wall.
  - **(2b)(γ) the `±r` ℝ^D-equality IS where KT escapes the wall, and it must come FIRST — but it is NOT "likely
    a re-statement of the telescope."** §I.8.21 guessed (2b)(γ) is "the (6.44) cancellation re-expressed at the
    abstract-vector level." Source check of the landed telescope `wstep_foldl_hingeRow_telescope`
    (`Relabel.lean:3209`): it is a **`hingeRow`-level (dual-functional-level) identity** — `wstep`-foldl applied
    to `hingeRow (w 0) (w 2) ρ₀` telescopes to `(∑ surviving hingeRows) + slot hingeRow`. KT's (6.66) `∑ⱼ
    λ_(vᵢvᵢ₊₁)ⱼ rⱼ(q(vᵢvᵢ₊₁)) = ±r` is a **`ScrewSpace`-vector (ℝ^D) equality** of the `Mᵢ` second row to `±r`,
    a DIFFERENT object: the telescope lives in `Module.Dual ℝ (α → ScrewSpace k)` (full hinge rows over all
    bodies), (6.66) lives in `Module.Dual ℝ (ScrewSpace k)` (one screw-functional, the `Mᵢ` row entry). The
    bridge from the hingeRow telescope to the `±r` scalar-row identity is **genuinely-new and unpinned** — it is
    the "read off the `vᵢ`-column entry of the telescoped row" step, which needs the degree-2 column-vanishing
    (eq. (6.52)) the telescope's `wstep_hingeRow_off`/`_frontier` lemmas encode but do not expose as a `ℝ^D`
    equality. **(2b)(γ) is a real leaf, not a re-statement; its cost is unknown.**

  *(VERDICT — FLAG-DON'T-FORCE, the honest gap).* (A)'s de-risk spike (2b)(α) LANDED a generic block-rank lemma,
  but the next leaf the prior pin named — (2b)(β) `Mᵢ`-corner LI-mod-base feeding `…_ge_of_corner` — is
  **mis-targeted**: the `Mᵢ` corner is already landed inline, the discriminator's single-panel output is
  correct (not a mismatch), and the de-risk leaf CONSUMES the dead relabel-image inclusion rather than producing
  anything new. **The genuinely-new, root-attacking work of (A) is (2b)(γ): the (6.66) `±r` ℝ^D-vector identity
  — the step that lets KT carry the redundancy as a fixed *abstract vector* `r` while the *member moves*, so the
  `Mᵢ` second row is `±r` WITHOUT a fixed-member candidate membership. That is what escapes the wall, and it is
  NOT a telescope re-statement (different carrier: ℝ^D screw-functional vs. full hinge-row dual).** So I do NOT
  pin a (2b)(β) `g/ι/W/hLI` signature (it would be a buildable-looking shape whose `hWS`/`hg` inputs are the
  dead inclusion — exactly the manufactured-signature failure clause (ii) forbids). **The corrected (A) leaf
  order is: (2b)(γ) FIRST** (the `±r` ℝ^D identity, which decides whether (A) can re-shape the cert at all),
  THEN a cert re-shape that consumes `±r` as the `Mᵢ` second row WITHOUT `hρGv` — only after (2b)(γ) is in hand
  is the cert-re-shape signature derivable. **(2b)(γ) is the smallest genuinely-advancing next commit; it is a
  recon-or-spike (does the hingeRow telescope's `vᵢ`-column read off as a clean ℝ^D `±r` equality, or does the
  degree-2 column-vanishing not localize at the abstract-vector level?), cost-unknown.** This is FLAG-DON'T-
  FORCE: (A) is NOT declared dead — (2b)(γ) is the live escape and is well-motivated — but its hardest
  remaining leaf is RE-IDENTIFIED (from the mis-targeted (2b)(β) to the genuinely-new (2b)(γ)), and no cert-
  re-shape signature is pinned until (2b)(γ) lands. The remaining cost band is unchanged (~6–11c), but its
  FIRST genuinely-new commit is (2b)(γ), not (2b)(β).

  **CLAUSE (i) HONESTY.** Every load-bearing claim re-derived this pass: the landed-cert-IS-`Mᵢ+base` finding
  from the actual `fam` assembly (`Candidate.lean:1596–1599`) cross-read against KT (6.64) row groups read
  directly (p. 697); the single-`hρGv`-use + eq.-(6.27) collapse from the cert body (`:1606–1611`); the
  single-panel `fin_cases u` → ONE arm from the dispatch body (`Realization.lean:495–599`) cross-read against KT
  (6.65)/(6.67) "at least one `Mᵢ` full-rank" (p. 697); the telescope's `hingeRow`-carrier vs. (6.66)'s ℝ^D-
  carrier divergence from the telescope statement (`Relabel.lean:3209–3216`, conclusion in `Module.Dual ℝ (α →
  ScrewSpace k)`) vs. KT (6.66) read directly (p. 698, `∈ ℝ^D`); the de-risk leaf's `hWS`/`hg` INPUT demands
  from its signature (`Candidate.lean:1664–1666`). **CLAUSE (ii) HONESTY.** No buildable (2b)(β) signature
  manufactured — it is named mis-targeted, with the `hWS`/`hg`-are-the-dead-inclusion reason spelled out. The
  hardest leaf is honestly re-identified (the prior pin's (2b)(β) was wrong; (2b)(γ) is the real one) and named
  genuinely-new + cost-unknown rather than pinned. No Lean landed; tree byte-clean; no decl orphaned; `d=3`
  unaffected; the de-risk leaf `…_ge_of_corner` is NOT declared dead (it is a correct generic lemma; it is just
  not the (A) consumer the prior pin expected — it may yet serve a future explicit-`Matrix` re-shape).

**(I.8.23) (2b)(γ) THE (6.66) `±r` ℝ^D-VECTOR IDENTITY — DE-RISK SPIKE VERDICT: POSITIVE, AND IT IS ALREADY
BUILT. The degree-2 column-vanishing DOES localize cleanly into a `Module.Dual ℝ (ScrewSpace k)` `±r` equality;
the localization mechanism is `hingeRow_comp_single_tail`/`_off` (the `f ↦ f.comp (single x)` column read-off);
and the (6.66) `±r` identity is realized — axiom-clean — by the 23b chain-induction subtree (LEAF 1–4), NOT by
the telescope. §I.8.22's "telescope re-statement / different carrier" framing CORRECTLY ruled out the telescope
route but MIS-LOCATED the actual `±r` realization, which is the separate chain induction.** GO/NO-GO ANSWERED
(2026-06-21, opus de-risk spike; every load-bearing claim re-derived from the landed `theorem` bodies AND KT
pp. 697–698 read directly from the PDF; **docs-only — no new Lean leaf, because the `±r` identity already
exists in tree** (`candidateRow_ac_eq_neg`, `interior_group_{eq,acolumn_eq_neg}_baseRedundancy`), and
manufacturing a wrapper would be the vacuous-pass failure the spike's clause forbids; tree byte-clean).
Verified against the telescope `wstep_foldl_hingeRow_telescope` (`Relabel.lean:3209`, conclusion in
`Module.Dual ℝ (α → ScrewSpace k)`), the column read-offs `hingeRow_comp_single_tail`/`_off`
(`Claim612.lean:953`/`:969`) + `hingeRow_comp_single_endpoint_flip` (`Relabel.lean:3862`), the abstract `±r`
core `candidateRow_ac_eq_neg` (`Claim612.lean:1194`, axiom-clean), the chain-induction LEAF 3/4
`interior_group_eq_baseRedundancy` (`Relabel.lean:3958`) / `interior_group_acolumn_eq_neg_baseRedundancy`
(`Relabel.lean:4039`, both axiom-clean: `propext`/`Classical.choice`/`Quot.sound`), the A-1 edge-grouped
output `hcombGv` (`Candidate.lean:444–445`), the cert's single `hρGv` use (`Candidate.lean:1606–1611`), the
d=3 `M₃` arm's `ρ̃ := -ρ` choice (`Relabel.lean:2530–2531`, the d=3 (6.66) instance), and KT 2011 §6.4.2
eqs. (6.52)/(6.64)/(6.66), pp. 697–698 (`.refs/…`, pdf pp. 51–52, read directly).

  *(0) THE DECISIVE SOURCE FACT — KT PROVES (6.66) "IN A MANNER SIMILAR TO THE PREVIOUS LEMMA (CF. (6.44))",
  AND THE PROJECT ALREADY FORMALIZED *THAT*.* KT p. 698 verbatim: "due to the fact that `vᵢ` is a vertex of
  degree two in `G₁` for all `2 ≤ i ≤ d−1`, we can easily show the following fact in a manner similar to the
  previous lemma (cf. (6.44)): `∑_{1≤j≤D−1} λ_(vᵢvᵢ₊₁)j rⱼ(q(vᵢvᵢ₊₁)) = ±r`." So (6.66) is **the same
  degree-2 column-vanishing argument as (6.44)**, iterated along the chain. The project formalized (6.44) as
  `candidateRow_ac_eq_neg` (the abstract two-edge form `∑ⱼ λac_j rac_j = −∑ⱼ λab_j rab_j`, the d=3 `M₃`
  candidate functional `= −r̂`), and iterated it along the chain in 23b as LEAF 1–4 (the chain induction
  `interior_group_acolumn_eq_neg_baseRedundancy`, concluding `(edge i-group).comp (single vᵢ) = −ρ₀` for
  every interior `2 ≤ i ≤ d−1`). **`ρ₀` IS KT's `r`** (§I.8.21(0): A-1's `ρ₀ = ∑ⱼ lamAB j • rab j`,
  `Candidate.lean:432`). Since the chain `edge i = (vᵢ, vᵢ₊₁)` (`cd.link`/`isLink_succ_edge`) and the `Mᵢ`
  second row is exactly that edge-group's `vᵢ`-column entry (KT (6.64)), `interior_group_acolumn_eq_neg_
  baseRedundancy` **IS** KT (6.66): the `Mᵢ` second row `= −ρ₀ = ±r` as a fixed `Module.Dual ℝ (ScrewSpace k)`
  vector, member-free. The `±` of KT's prose is the per-edge orientation artifact absorbed by the
  tail-column reading (`hingeRow_comp_single_endpoint_flip`).

  *(1) THE MAKE-OR-BREAK (the prompt's q.): DOES THE COLUMN READ-OFF LOCALIZE AT THE ABSTRACT-VECTOR LEVEL?
  VERDICT: YES, cleanly.* The column read-off is `f ↦ f.comp (LinearMap.single ℝ _ x)`, a linear map
  `Module.Dual ℝ (α → ScrewSpace k) → Module.Dual ℝ (ScrewSpace k)` — *exactly* the localization the prompt
  asked about. On a hinge row it is total: `(hingeRow u v ρ).comp (single x)` is `ρ` if `x = u`
  (`hingeRow_comp_single_tail`), `−ρ` if `x = v` (`_endpoint_flip`), `0` else (`hingeRow_comp_single_off`).
  There is **no defeq/`ScrewSpace ≃ₗ`/§38 friction**: these three are `LinearMap.ext fun x => …` one-liners
  over `Pi.single`, the carrier never unfolded. The cancellation localizes because at a degree-2 interior
  vertex `vᵢ` only the two incident edge-groups `(vᵢ₋₁vᵢ)` and `(vᵢvᵢ₊₁)` survive in `vᵢ`'s column
  (`edgeIndexedCombination_comp_single_eq_incident` + the deg-2 closure `deg_two_split`), and the eq.-(6.43)
  column-vanishing `g.comp (single vᵢ) = 0` (derived internally from `hcomb` + `hingeRow_comp_single_off`,
  since `r̂ = hingeRow (vtx 0)(vtx 2) ρ₀` is off `vᵢ` for `i ≥ 3`) forces the two surviving group-columns to
  negate — the per-step `P(i) → P(i+1)` of the chain induction. **So the abstract-vector `±r` equality holds;
  the degree-2 cancellation does NOT fail to localize.**

  *(2) WHY §I.8.22's "DIFFERENT CARRIER, telescope can't expose `±r`" WAS RIGHT ABOUT THE TELESCOPE BUT
  MIS-LOCATED THE `±r`.* §I.8.22 evaluated (2b)(γ) only against the telescope `wstep_foldl_hingeRow_telescope`
  (output `(∑_{s<m} hingeRow (wₛ)(wₛ₊₁) ρ₀) + hingeRow (w_m)(w_{m+2}) ρ₀` in `Module.Dual ℝ (α → ScrewSpace
  k)`). Re-confirmed: the telescope **cannot** expose `±r`, because the telescoped object is the *moved* base
  redundancy, supported on `{v₀,…,vᵢ₋₁, vᵢ₊₁}` — its `vᵢ = w_{m+1}` column is **`0`** (every summand: the slot
  `(w_m, w_{m+2})` is off `w_{m+1}`; each surviving `(wₛ, wₛ₊₁)`, `s ≤ m−1`, has both endpoints `≠ w_{m+1}`).
  That is KT (6.64)'s "by (6.52), all entries of the part associated with `V∖{vᵢ}` become zero" — the telescope
  is the *membership* tool (slot ∈ span), the wrong carrier for `±r`, exactly as §I.8.22 said. **The `±r`
  identity is a DIFFERENT decomposition**: the `Mᵢ` second row is the candidate-edge `(vᵢvᵢ₊₁)`-group of A-1's
  *edge-grouped-over-`G`-links* exposure `hcombGv`, read at the `vᵢ` column — the chain-induction object, NOT
  the telescoped object. §I.8.22 noted LEAF 3/4 "encode but do not expose" the cancellation; the source-read
  this pass shows LEAF 3/4 **do** expose it (`interior_group_acolumn_eq_neg_baseRedundancy`'s conclusion is
  literally `… = −ρ₀` in `Module.Dual ℝ (ScrewSpace k)`).

  *(3) THE PINNED `±r` ℝ^D-IDENTITY SIGNATURE (the cleanest equality the future cert re-shape consumes).* Two
  layers, both landed:
  - **Abstract two-edge core** (graph-free, the (6.44)/d=3 form): `candidateRow_ac_eq_neg` —
    `∑ⱼ lamAC j • rac j = −∑ⱼ lamAB j • rab j` in `Module.Dual ℝ (ScrewSpace k)`, given the degree-2 column
    vanishing `hcol`/`hrest` at the common tail body. With `ρ₀ = ∑ⱼ lamAB j • rab j`: the candidate-edge
    functional `= −ρ₀`.
  - **Chain-induction `Mᵢ`-row form** (the general-`d`, `ChainData`-keyed form the cert needs):
    `interior_group_acolumn_eq_neg_baseRedundancy` —
    `(∑_{evⱼ = edge i} cⱼ • hingeRow (uvⱼ)(vvⱼ)(rvⱼ)).comp (single (vtx i)) = −ρ₀`
    for `2 ≤ i < cd.d`, given A-1's edge-grouped exposure `hcomb` (`Candidate.lean:444–445`) + the deg-1 anchor
    `hdeg1`. This IS KT (6.66): the candidate `Mᵢ` second-row functional, read at `vᵢ`'s screw column, is the
    fixed abstract vector `−ρ₀`, **member-free** (no `hρGv`, no relabel transport). The future cert re-shape's
    `Mᵢ`-corner full-rank criterion `ρ_cand ⊥ C(Lᵢ)` becomes `ρ₀ ⊥ C(Lᵢ)` by this identity — discharged on the
    discriminator `hρgate` applied to the FIXED `ρ₀`, which is exactly the escape (A) describes.

  *(VERDICT — go/no-go, the honest finding).* **(A) is NOT dead — the wall-escape it rests on, the (6.66) `±r`
  abstract-vector identity, is BUILT and axiom-clean.** The spike's go/no-go question ("does the degree-2
  column-vanishing localize at the abstract-vector level?") is answered POSITIVE: it does, via
  `hingeRow_comp_single_tail`/`_off`, the same mechanism the landed (6.44)/d=3 `M₃` arm uses. The honest
  re-point: **(2b)(γ) is not a remaining genuinely-new leaf** — it was substantially delivered in 23b (LEAF
  1–4) and adversarially confirmed here against KT pp. 697–698. **No new Lean leaf is landed** (a wrapper
  re-exporting `interior_group_acolumn_eq_neg_baseRedundancy` with `ρ₀` substituted would be vacuous; the
  prompt's clause forbids a gate-clean-but-vacuous `±r` statement). The remaining (A) work is now **wholly the
  cert re-shape** (consume the landed `±r` as the `Mᵢ` second row + discharge the `Mᵢ`-corner LI-mod-`W` on
  `hρgate(ρ₀)` via the de-risk leaf `finrank_span_rigidityRows_ge_of_corner`, NO `hρGv`) + the arm re-shape +
  the 2c-iii dispatch + the orphan confirm-and-delete — all of which is the LATER work the spike explicitly
  scoped out. **The cert-re-shape signature is now derivable** (the prompt's gate: "only after (2b)(γ) lands is
  the cert-re-shape signature derivable"): the cert consumes `interior_group_acolumn_eq_neg_baseRedundancy`'s
  `−ρ₀` value for the `Mᵢ` row, NOT a candidate membership. **Revised cost band: ~5–9 commits** (the (2b)(γ)
  leaf, the prior band's first genuinely-new commit, is now closed by source-read; what remains is the cert/arm
  re-shape + wire-up + cleanup). **CLAUSE (i):** every claim re-derived from landed bodies + KT pp. 697–698
  read directly (the "in a manner similar to (6.44)" sentence; the (6.64) `Mᵢ` second row = `∑ λ_(vᵢvᵢ₊₁)j
  rⱼ(q1(vᵢvᵢ₊₁))`; the (6.66) `= ±r`); the three `±r` decls verified axiom-clean by `#print axioms`/lean_verify;
  the telescope `vᵢ`-column-is-`0` computed by hand against `hingeRow_comp_single_off`'s semantics. **CLAUSE
  (ii):** FLAG-DON'T-FORCE — (A) NOT declared dead (its escape is built), and NO vacuous wrapper manufactured;
  the honest outcome is "the `±r` leaf is already in tree, the spike re-points cost to the cert re-shape". `d=3`
  unaffected; no decl orphaned (confirm-and-delete still fires at the route-SETTLE commit per §I.8.20).

**(I.8.24) THE CERT-RE-SHAPE DESIGN PASS — VERDICT: (A) ESCAPES THE WALL, and the §I.8.22-vs-§I.8.23 tension
RESOLVES FAVORABLY. The de-risk leaf's `hWS`/`hg` are the **buildable relabel-IMAGE** inclusion (§I.8.20(e)) +
genuine candidate rows, NOT the dead **fixed-member** inclusion; the wall lives ONLY in the landed cert's
COLLAPSED `Unit` row (`hingeRow v a ρ` via eq. (6.27), needing `hρGv`), which the re-shape REPLACES with KT's
GENUINE candidate-edge `(vᵢvᵢ₊₁)ᵢ∗` row. Pinned: a FORKED general-`d` cert `case_III_rank_certification_chain`
+ arm `case_III_arm_realization_chain` consuming the `±r` value + the de-risk leaf, d=3 keeping the landed
`hρGv`-collapse engine verbatim (zero-regression). First build commit + ~5–9c band below. (2026-06-21, opus
docs-only design-pass; every load-bearing claim re-derived from the landed `def`/`theorem` bodies + KT pp.
696–698 read directly; NOT inherited from the prompt's framing or the prior pins; tree byte-clean.)** Verified
against the SHARED engine `case_III_rank_certification` (`Candidate.lean:1472`, the `fam` family `:1596–1599`,
the SINGLE `hρGv` use `:1606–1611`, the internal **same-selector** inclusion `hFvle` `:1551–1558`), the W6c
assembler `case_III_full_family_restriction` (`Candidate.lean:1366`, the `Unit` candidate row enters LI by
`hr` + the column-op, NO `hρGv` `:1417–1427`), the arm `case_III_arm_realization` (`Arms.lean:72`, parametric
in `(G,Gv,ends,q)`; its `Gv/ends/q` ARE the candidate base at the relabelled selector for general `d`), the
de-risk leaf `finrank_span_rigidityRows_ge_of_corner` (`Candidate.lean:1661`, `hWS`/`hg`/`hLI` inputs), the
`±r` identity `interior_group_acolumn_eq_neg_baseRedundancy` (`Relabel.lean:4039`, `= −ρ₀` member-free) + A-1's
edge-grouped `hcombGv` (`Candidate.lean:439–445`, links over genuine `G`), the relabel-image transport
`chainData_bottom_relabel` (`Relabel.lean:1961–1994`, genuine→genuine, member MOVING), the d=3 M₃ arm
`case_III_arm_realization_M3` (`Relabel.lean:2537`; it INSTANTIATES the shared engine `:2624` and produces the
candidate `hρGv` by a length-1 W9a move `:2655–2724`), the discriminator
`exists_complementIso_ne_zero_of_homogeneousIncidence_gen` (`Claim612.lean:1462`, ONE `r`), and KT 2011 §6.4.2
eqs. (6.59)–(6.67), pp. 696–698 (`.refs/…`, pdf pp. 50–52, read directly).

  *(0) THE LOAD-BEARING ARCHITECTURAL FACT THE PRIOR PINS BLURRED — the relabel lives in the ARM's ARGUMENTS,
  never inside the cert; the cert is selector-AGNOSTIC.* `case_III_rank_certification` (and its caller
  `case_III_arm_realization`) is **parametric in `(G, Gv, ends, q)`** with the SAME `ends`/`q` for the candidate
  `F₀ = caseIIICandidate G ends q …` and the candidate-base `Fv = ofNormals Gv ends q`. Its internal inclusion
  `hFvle : span Fv.rigidityRows ≤ span F₀.rigidityRows` (`:1551–1558`) is the **direct same-selector** map
  (`Gv`-link ↦ `G`-link via `hleG`, block-preserving) — member-PRESERVING and trivially buildable; it is NOT a
  relabel-image map. The relabel enters ONLY when the dispatch/arm INSTANTIATES `(Gv,ends,q)` at the *candidate
  base* `(G−vᵢ, endsσρ, qρ)` (verified: the M₃ arm does exactly this, `Relabel.lean:2624`, passing `Gv :=
  G−a`, `ends := ends₃`, `q := qρ`). So "the cert consumes the dead relabel-image inclusion" (§I.8.22) is
  imprecise: the cert consumes a **same-selector** inclusion; the relabel-image transport is the ARM's job, done
  ONCE to produce the cert's `hρGv` slot at the relabelled candidate base. The wall is in that ARM step (produce
  `hingeRow a b ρ ∈ span (G−vᵢ, endsσρ, qρ)`), and the cert's `hρGv` is its only consumer.

  *(1) THE MAKE-OR-BREAK, SETTLED PER-HYPOTHESIS — `hWS`/`hg`/`hLI` are each the BUILDABLE kind.* The re-shaped
  general-`d` cert applies `finrank_span_rigidityRows_ge_of_corner` to `F := the candidate` with:
  - **`W := span (relabel-image of the candidate-base block `R(G₁∖row, q₁)`)`**, and the obligation
    `hWS : W ≤ span F.rigidityRows`. This is the **relabel-IMAGE inclusion** `span ((funLeft (shiftPerm)⁻¹).dualMap
    '' (base rows)) ≤ span (candidate rows)` — §I.8.20(e) ADJUDICATED **BUILDABLE** (genuine base rows ↦ genuine
    candidate rows, member-MOVING, no member held fixed; it is the span-level form of `chainData_bottom_relabel`,
    `Relabel.lean:1982–1986`). It is the relabel-image, NOT the dead fixed-member inclusion (which §I.8.20(e)'s
    SECOND bullet named FALSE/unbuilt). **`hWS` is buildable.**
  - **`g := the `D` `Mᵢ` corner rows = the `D−1` candidate panel rows `r(Lᵢ)` of the candidate hinge `e_a` ⊕ the
    `±r` row = the genuine candidate-EDGE `(vᵢvᵢ₊₁)ᵢ∗` group`**, and `hg : ∀ j, g j ∈ span F.rigidityRows`. The
    `r(Lᵢ)` rows are genuine candidate panel rows (the landed cert's `sn` block, `F₀.panelRow_mem_rigidityRows`,
    `:1603` — free, no transport). The `±r` row is the **edge-`i` group `∑_{ev j = edge i} c j • hingeRow (uv j)
    (vv j)(rv j)`** of A-1's `hcombGv` (genuine `G`-links, `Candidate.lean:441`), transported to genuine candidate
    rows by the relabel-image map — `hg` for it is the SAME buildable relabel-image inclusion as `hWS`, **not** a
    fixed-member candidate membership. **`hg` is buildable. This is the decisive divergence from the landed cert,
    whose `Unit` row is the COLLAPSED `hingeRow v a ρ` (eq. (6.27)) needing the FIXED-member `hρGv` (`:1606–1611`)
    — the re-shape sources the `±r` row as KT's genuine candidate-edge row instead, killing the `hρGv` slot.**
  - **`hLI : LinearIndependent (W.mkQ ∘ g)`** — the `Mᵢ`-corner full rank MODULO the base block. KT (6.65): `Mᵢ`
    full-rank `⟺ r ∉ rowspace r(Lᵢ) ⟺ r(C(Lᵢ)) ≠ 0`. With the `±r` identity
    `interior_group_acolumn_eq_neg_baseRedundancy` (`= −ρ₀`, member-free), the `±r` row's class mod `W` is read at
    `vᵢ`'s column as `−ρ₀`, so the LI-mod-`W` reduces to `ρ₀ ⊥ C(Lᵢ)` discharged on the discriminator `hρgate`
    applied to the **FIXED `ρ₀`** (= KT's abstract `r`, §I.8.21(0)/§I.8.23(0)). **No fixed-member transport; `hLI`
    is the discriminator at `ρ₀` + the landed `±r` identity.** (The landed cert already proves the analogous
    `(sn ⊕ Unit)`-LI-mod-bottom inline via `hr` `:1417–1427`; the re-shape re-aims it through the de-risk leaf
    with `g`'s `±r` row sourced genuinely.)
  **VERDICT (1): the re-shaped cert genuinely uses ONLY the buildable relabel-image inclusion (`hWS`/`hg`) + the
  member-free `±r` value + the FIXED-`ρ₀` discriminator (`hLI`). NO `hWS`/`hg`/`hLI` smuggles in a fixed-member
  dependency. (A) escapes the wall.** The §I.8.22-vs-§I.8.23 tension RECONCILES exactly as the prompt's
  hypothesis predicted: §I.8.22 correctly said the de-risk leaf CONSUMES an inclusion, but mis-typed it — it is
  the buildable relabel-image kind (no member held fixed), not the dead fixed-member kind; §I.8.22's "dead"
  reading was an artifact of evaluating the leaf against the LANDED cert's collapsed-`Unit`-row sourcing (which
  DOES need the fixed `hρGv`), not the re-shaped genuine-`±r`-row sourcing §I.8.23 prescribes.

  *(2) THE d=3 FORK — pinned: FORK the cert; d=3 keeps the landed `hρGv`-collapse engine verbatim.* The engine
  `case_III_rank_certification`/`case_III_arm_realization` is SHARED across M₁/M₂/M₃ (M₃ instantiates it,
  `Relabel.lean:2624`). At d=3 the `(i−1)`-cycle is a single swap (M₃, `i=2`): the arm produces the candidate
  `hρGv` by ONE length-1 W9a move (`:2699–2724`), so the engine slot is satisfied with no wall — zero-regression
  REQUIRES leaving it untouched. The general-`d` `±r`-cert is a DIFFERENT certification shape (block-rank-
  additivity via the de-risk leaf, vs. the landed span-containment + `finrank_mono`). **The clean fork (§I.8.21(3)
  "the cleaner option"): NEW decls, the d=3 path unchanged.** Concretely:
  - **NEW `case_III_rank_certification_chain`** (`Candidate.lean`, after the de-risk leaf): the general-`d` cert.
    Drops `hρGv` + `hLn`/`hρe₀`-as-collapse-inputs; gains (i) `hWS : W ≤ span F₀.rigidityRows` (the relabel-image
    base block), (ii) the `±r`-row hypotheses — `g`'s `±r` member as a genuine candidate-edge group + its
    `−ρ₀`-column value (consuming `interior_group_acolumn_eq_neg_baseRedundancy`), (iii) `hρgate(ρ₀)` (UNCHANGED,
    the discriminator at the fixed `ρ₀`). Conclusion identical: `screwDim k * (V(G).ncard − 1) ≤ finrank (span
    candidate.rigidityRows)`, now via `finrank_span_rigidityRows_ge_of_corner` (`finrank W + D ≤ …` with
    `finrank W = D(m_v−1)`) instead of `finrank_mono`.
  - **NEW `case_III_arm_realization_chain`** (`Arms.lean`, beside the engine): consumes `case_III_rank_
    certification_chain`; the rest of the arm (W6a–W6f good-`t` shear, GAP-2/3, the realization assembly) is
    SHARED and lifts verbatim (it operates on the rank bound, agnostic to how it was certified).
  - **d=3 UNTOUCHED:** `case_III_arm_realization_M3` + `case_III_arm_realization` + `case_III_rank_certification`
    stay byte-identical (the dispatch keeps routing M₁/M₂/M₃ through them). The 2c-iii general-`d` dispatch
    `chainData_dispatch` routes the interior candidates `2 ≤ i < d` through `case_III_arm_realization_chain` and
    keeps the d=3 floor on the landed engine — the C.4 zero-regression wrapper is preserved.

  *(3) BUILDABLE-LEAF DECOMPOSITION (signatures + order + first build + estimate). REUSE vs. CHANGE vs. ORPHAN.*
  - **REUSE (no change):** the de-risk leaf `finrank_span_rigidityRows_ge_of_corner` (`:1661`); the `±r` identity
    `interior_group_acolumn_eq_neg_baseRedundancy` + LEAF 1–4 chain (`Relabel.lean:3958/4039`); A-1
    `exists_candidateRow_bottomRows_of_rigidOn` (the `hcombGv` edge-grouped exposure, `:439–445`); the
    relabel-image transport `chainData_bottom_relabel` (`:1961`); the discriminator capstone (`Claim612.lean:1462`);
    the dispatch's single-`ρ0` block + A-1-once (`Realization.lean:388–441`); the SHARED arm-realization tail
    (W6a–W6f). All consumed as-is by the new chain cert/arm.
  - **CHANGE (new decls):** `case_III_rank_certification_chain`, `case_III_arm_realization_chain` (above), + the
    2c-iii `chainData_dispatch` routing interior `i` through the chain arm.
  - **ORPHAN-CANDIDATE (confirm-and-delete at the route-SETTLE commit, NOT here — §I.8.20):** the seed-advancing
    `hφ`-spine (`chainData_freshEdge_slot_mem` `:4158`, the gate `:1201`, `chainData_relabel_arm_hρGv` `:4647`,
    the fold `shiftBodyListAsc_foldl_mem_span_rigidityRows`); the telescope `wstep_foldl_hingeRow_telescope`
    (its `vᵢ`-column-is-`0` content is the *membership* tool the dead route used — UNUSED by (A), which sources
    the `±r` row genuinely). These die because (A) replaces the membership-fold with the genuine-candidate-row +
    block-rank-additivity shape. The `±r` chain induction (LEAF 1–4) STAYS (it is the `hLI` ingredient).
  - **NAMED FIRST BUILD COMMIT (smallest genuinely-advancing):** land `case_III_rank_certification_chain` —
    re-state the cert to consume `(hWS, the `±r` `g`-row + its `−ρ₀` value via `interior_group_acolumn_eq_neg_
    baseRedundancy`, hρgate ρ₀)` through `finrank_span_rigidityRows_ge_of_corner`, NO `hρGv`. This is the make-
    or-break Lean step; the de-risk leaf + the `±r` identity are landed, so it is a *re-statement that consumes
    landed bricks*, not a genuinely-new leaf — but it is the commit that proves (1) holds in Lean (the
    `W`/`g`/`hLI` shapes type-check against the actual de-risk leaf signature). **The one residual UNKNOWN to
    surface honestly:** establishing `hWS` (the relabel-image base block as a subspace `W` of the candidate span
    with the right `finrank W = D(m_v−1)`) is the `chainData_bottom_relabel`-over-the-whole-base-block step — its
    span-level map is buildable (§I.8.20(e)), but packaging it as a SUBSPACE `W` with a known `finrank` (so
    `finrank W + D` lands on `D(m_v−1) + D = D(m_v)`) may take 1–2 supporting leaves (the relabel-image of an LI
    base family is LI with the same card — `LinearIndependent.map'` on the injective `funLeft`-dualMap, the
    pattern the M₃ arm already uses for `w` at `Relabel.lean:2629`). This is plausibly mechanical (the injective
    `(funLeft σ⁻¹).dualMap` preserves LI + card), NOT a wall, but it is the one part not yet in tree as a packaged
    subspace; flag it as the first build's sub-risk.
  - **ESTIMATE: ~5–9 commits** (UNCHANGED from §I.8.23) — (1c) `case_III_rank_certification_chain` + the `hWS`
    subspace-packaging leaf(s); (1–2c) `case_III_arm_realization_chain`; (1–2c) the 2c-iii `chainData_dispatch`
    + CHAIN-5 wire-up; (1c) orphan confirm-and-delete; (1–2c) cleanup/exposition. ENTRY + ASSEMBLY remain later
    sub-phases (codes).

  **CLAUSE (i) HONESTY.** Every load-bearing claim re-derived this pass from the landed bodies + KT: the cert's
  same-selector `hFvle` from `Candidate.lean:1551–1558` (NOT a relabel-image map); the SINGLE `hρGv` use + the
  eq.-(6.27) collapse from `:1606–1611`; the W6c LI-without-`hρGv` from `case_III_full_family_restriction:1417–1427`;
  the relabel-in-the-arm-arguments fact from the M₃ instantiation `Relabel.lean:2624` + the candidate `hρGv` W9a
  move `:2655–2724`; `hWS`-is-buildable from §I.8.20(e)'s FIRST bullet + `chainData_bottom_relabel`'s genuine→genuine
  conclusion `:1982–1986`; the `±r` row's `−ρ₀` value + member-freeness from `interior_group_acolumn_eq_neg_
  baseRedundancy:4039–4067`; the three load-bearing decls re-verified axiom-clean (`#print axioms`:
  `propext`/`Classical.choice`/`Quot.sound`). **CLAUSE (ii) HONESTY.** FLAG-DON'T-FORCE: the tension is settled
  per-hypothesis (each of `hWS`/`hg`/`hLI` typed as buildable-or-dead against the actual de-risk-leaf signature +
  §I.8.20(e), NOT hand-waved); the ONE not-yet-in-tree piece (the `hWS` base-block-as-subspace packaging) is named
  as the first build's sub-risk with its plausible `LinearIndependent.map'` route, NOT pinned as trivially closed;
  no buildable-looking signature is manufactured whose `hWS`/`hg` are secretly the dead fixed-member inclusion
  (the LEAF-C trap) — the re-shape's `±r` row is sourced as KT's GENUINE candidate-edge row, which is the precise
  reason it escapes. No Lean landed; tree byte-clean; `d=3` forked-off untouched; the orphan `hφ`-spine stays
  confirm-and-delete-at-route-SETTLE per §I.8.20.

**(I.8.24)(4) THE CHAIN-ARM LEAF DECOMPOSITION — `case_III_arm_realization_chain` broken into named,
buildable sub-leaves with EXACT signatures + build order; the (b) crux ISOLATED as its own standalone lemma.
(2026-06-21, opus docs-only; every signature pinned against the LANDED `def`/`theorem` bodies — the chain cert
`case_III_rank_certification_chain` `Candidate.lean:1770`, the engine `case_III_arm_realization` `Arms.lean:310`
+ shared tail `case_III_realization_of_rank` `Arms.lean:63`, the M₃ template `case_III_arm_realization_M3`
`Relabel.lean:2537`, the de-risk leaf `:1661`, the carrier packaging leaf `:1691`, the (a) leaf
`linearIndependent_mkQ_panelRow_of_edge` `:1720`, the append-one criterion + `_of_comp`
`Constructions.lean:269/297`, the `±r` identity `interior_group_acolumn_eq_neg_baseRedundancy` `Relabel.lean:4039`,
A-1's `hcombGv` `Candidate.lean:439–445`, the relabel transport `chainData_bottom_relabel` `Relabel.lean:1961`,
the d=3 dispatch `case_III_candidate_dispatch` `Realization.lean:388–540` — NOT inherited from the §I.8.24(1)–(3)
prose.) The §I.8.24(3) named-first-build (`case_III_rank_certification_chain`) is LANDED; this is the leaf
decomposition of the SECOND build it teed up.**

  *(4.0) THE FACT THAT MAKES THE ARM ATOMIC, AND THE CUT.* The arm `case_III_arm_realization_chain` must, like
  the engine, (i) produce the cert's corner data `(W, hWS, hWcard, ι/hιcard, g, hg, hLI)`, (ii) apply
  `case_III_rank_certification_chain` to get `hrank`, (iii) `exact case_III_realization_of_rank …` (the SHARED
  tail, landed; consumes only `hrank` + split/seed data — `Arms.lean:63`, verified the engine `:346–353`
  literally does `case_III_rank_certification …; exact case_III_realization_of_rank …`). The ONLY genuinely-new
  content over the d=3 M₃ arm is `(W, hWS, hWcard, hg, hLI)` — and within `hLI`, the `±r`-row half (b). The cut
  isolates (b) as its own lemma so the arm body is then mechanical wiring (relabel-image transport + the two
  landed `hLI` halves + the count). The arm consumes the dispatch's `hgate : ρ₀(panelSupportExtensor na n') ≠ 0`
  (verified: the dispatch fires the discriminator ONCE on the shared `ρ₀` and passes `hgate` into the matched
  arm, `Realization.lean:439–441/501`; so `hgate` at the FIXED `ρ₀` enters the chain arm as a HYPOTHESIS, the
  `u`↔candidate-index match being the future 2c-iii `chainData_dispatch`'s job, NOT the arm's).

  *(4.1) THE (b) CRUX — its own standalone lemma `BodyHingeFramework.notMem_span_mkQ_pmR_row_of_gate`* (the
  genuine genuinely-new step; KT 2011 (6.65) `Mᵢ` full-rank `⟺ r ∉ rowspace r(Lᵢ)`, via the eq.-(6.66) `±r`
  column read-off). It says: the `±r` row's class mod the base block `W` is NOT in the span of the candidate
  panel rows' classes. Stated abstractly over the candidate carrier so the arm supplies the concrete pieces:
  ```
  theorem BodyHingeFramework.notMem_span_mkQ_pmR_row_of_gate [DecidableEq α]
      (F : BodyHingeFramework k α β) {ends : β → α × α} {e : β} {vᵢ : α}
      (hv : (ends e).1 = vᵢ) (hev : (ends e).2 ≠ (ends e).1)
      {n_u n' : Fin (k + 2) → ℝ} {ρ₀ : Module.Dual ℝ (ScrewSpace k)}
      (hsupp : F.supportExtensor e = panelSupportExtensor n_u n')   -- C(Lᵢ) at the candidate hinge
      (hgate : ρ₀ (panelSupportExtensor n_u n') ≠ 0)                -- the discriminator at the FIXED ρ₀
      {s : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)}
      (hs : ∀ i ∈ s, (i : β × _ × _).1 = e)
      {W : Submodule ℝ (Module.Dual ℝ (α → ScrewSpace k))}
      (hW : ∀ φ ∈ W, φ.comp (LinearMap.single ℝ (fun _ : α => ScrewSpace k) vᵢ) = 0)
      {rRow : Module.Dual ℝ (α → ScrewSpace k)}
      (hrCol : rRow.comp (LinearMap.single ℝ (fun _ : α => ScrewSpace k) vᵢ) = -ρ₀) :  -- the (6.66) value
      W.mkQ rRow ∉ Submodule.span ℝ
        (Set.range (W.mkQ ∘ (fun i : s => F.panelRow ends (i : β × _ × _))))
  ```
  *Proof shape (all ingredients in tree, no new math):* by contradiction. If `W.mkQ rRow ∈ span (W.mkQ ∘ panel
  rows)`, then `rRow − ∑ⱼ cⱼ • panelRowⱼ ∈ W` (`mem_span_range` + `W.mkQ`-kernel `= W`). Precompose with
  `single vᵢ` (the column read-off): `W`-side `→ 0` (`hW`), `rRow`-side `→ −ρ₀` (`hrCol`), and each
  `panelRowⱼ.comp (single vᵢ)` `= annihRow (C(Lᵢ)) …` (the `single (ends e).1` column form, `hv` + the
  `hingeRow_apply`/`screwDiff` step inside `linearIndependent_panelRow_comp_single_of_edge:516–525`, here used
  as an *equality* not for LI). So `−ρ₀ = ∑ⱼ cⱼ • annihRow(C(Lᵢ))ⱼ ∈ (span C(Lᵢ))^⊥`, hence `ρ₀(C(Lᵢ)) = 0`
  (`annihRow_apply_self`/`mem_dualAnnihilator` + `hsupp`) — contradicting `hgate`. **CLAUSE (ii) HONESTY ON (b):
  this does NOT reduce to a single landed lemma** — it is the assembly of the column read-off (`hrCol`, supplied
  by `interior_group_acolumn_eq_neg_baseRedundancy = −ρ₀`), the panel-row column form (the `annihRow` content of
  `linearIndependent_panelRow_comp_single_of_edge`, re-used as an equality), the `W`-annihilation (`hW`), and the
  `(span C(Lᵢ))^⊥` membership → `hgate` contradiction. Each *piece* is in tree; the *assembly* is the genuine
  leaf. It does cleanly follow from the column identity + `hgate` (the read-off localizes at the single column
  `vᵢ`, where `W` vanishes and the panel rows expose their annihilator block) — NOT flagged as needing a
  motive/IH change or new math. The one build-time latitude: the exact `Finsupp`/`mem_span_range` bookkeeping of
  "in the span ⟹ difference in `W`" through `W.mkQ` (mechanical; `Submodule.mkQ`-kernel + `sub_mem`).

  *(4.2) THE (a) HALF — already a landed consume-leaf, the arm supplies `hW`/`hindep`.* The `D−1` candidate panel
  rows are LI mod `W` via the LANDED `BodyHingeFramework.linearIndependent_mkQ_panelRow_of_edge` (`Candidate.lean:1720`,
  signature verified). The arm supplies: `hindep : LinearIndependent ℝ (fun i : s => F.panelRow ends i)` (the
  candidate fresh hinge `e_a`'s panel-row independence — from the candidate's extensor nonvanishing, the M₃ arm's
  `hane`/`hr` pattern) and `hW : ∀ φ ∈ W, φ.comp (single vᵢ) = 0` (the relabel-image base block's off-`vᵢ`
  vanishing — its rows are `hingeRow x y r` with `x, y ≠ vᵢ`, killed by `single vᵢ` via `hingeRow_comp_single_off`,
  the M₃ `htransport`-genuine-branch pattern `Candidate.lean:1576`). **Both `hW` and `hindep` are shared with the
  (b) lemma's `hW`/`hsupp`** — the arm proves them once.

  *(4.3) THE `g` / `hg` / `hLI` ASSEMBLY (arm-internal, post-(b)).* With (a) + (b) lemmas in hand:
  - **`g := Sum.elim (fun i : s => F₀.panelRow ends i) (fun _ : Unit => rRow)`** over `ι := s ⊕ Unit`, where `s`
    is the `D−1`-card candidate-`e_a`-panel-row index (`hιcard : Fintype.card (s ⊕ Unit) = screwDim k` from
    `Nat.card s = D−1` + `Fintype.card_sum`), and `rRow` is the `±r` row.
  - **`rRow := the edge-`i` group `∑_{ev j = cd.edge i} cGv j • hingeRow (uvGv j) (vvGv j) (rvGv j)`** of A-1's
    `hcombGv` (`Candidate.lean:441–445`), transported to a candidate row by the relabel-image map. Its `−ρ₀`
    column value is `interior_group_acolumn_eq_neg_baseRedundancy` (`Relabel.lean:4039`, signature verified:
    consumes the A-1 `hcomb`/`hlink` + the chain `cd`/`h3`/degree-2 data, concludes `(edge-i group).comp
    (single (vtx i)) = −ρ₀`). **NOTE — the column value is read at the BASE rows (`hcombGv` is over `Gv`-links);
    the transported candidate row's column at `vᵢ` is the same `−ρ₀` because the relabel `(funLeft σ⁻¹).dualMap`
    is the member-MOVING map that sends the `vtx 1`-base column to the `vtx i`-candidate column (the
    `chainData_bottom_relabel` content). The arm derives `hrCol` for the *candidate* `rRow` by composing the
    base `−ρ₀` value with the relabel's column-naturality — flagged (4.5) as the one not-yet-isolated arm step.**
  - **`hg`** — the `s`-panel rows are free candidate rows (`F₀.panelRow_mem_rigidityRows_of_link` at `e_a`,
    `Pinning.lean:166`); the `±r` `rRow` is in `span F₀.rigidityRows` by the SAME relabel-image inclusion as
    `hWS` (the genuine→genuine `chainData_bottom_relabel`, NOT a fixed-member membership).
  - **`hLI : LinearIndependent ℝ (W.mkQ ∘ g)`** — `Submodule.linearIndependent_mkQ_sumElim_unit_of_notMem_span`
    (`Constructions.lean:269`, landed) fed by (a)'s `LinearIndependent (W.mkQ ∘ panel rows)` (its `hf`) and (b)'s
    `notMem_span` (its `hx`). Type-checks directly: `g = Sum.elim (panel rows) (fun _ : Unit => rRow)`.

  *(4.4) THE `W` / `hWS` / `hWcard` HALF (arm-internal).* Apply the LANDED carrier packaging leaf
  `BodyHingeFramework.exists_le_finrank_span_rigidityRows_eq_card_of_injective_map` (`Candidate.lean:1691`,
  signature verified) at `L := (funLeft (cd.shiftPerm i.castSucc)⁻¹).dualMap` (injective — `dualMap` of a
  surjective `funLeft`, the M₃ `hw` route `Relabel.lean:2729–2731`), `f := the base LI bottom family` of card
  `D·(m_v − 1)` (`m_v = |V(G − vᵢ)|`), `hS := chainData_bottom_relabel`'s span-level genuine→genuine transport
  (`:1961`). Returns `W ≤ span F₀.rigidityRows` with `finrank W = D·(m_v−1)` (= `hWcard`). The arm still supplies
  the concrete `f`/`hf`/`hS` against the chain data (the bottom family + its LI + the per-member transport) —
  arm wiring, no wall.

  *(4.5) BUILD ORDER + THE TWO ARM-INTERNAL STEPS NOT YET ISOLATED.* Order:
  1. **`notMem_span_mkQ_pmR_row_of_gate`** (the (b) crux, §(4.1)) — `Candidate.lean`, beside
     `linearIndependent_mkQ_panelRow_of_edge`. THE genuinely-new leaf; the FIRST commit of this build. *This is
     where Phase23c's Hand-off now points.*
  2. **`case_III_arm_realization_chain`** (the arm, §(4.0)) — `Arms.lean`, beside `case_III_arm_realization`.
     Consumes (1) + the landed (a)/append-one/carrier/`±r`-identity leaves; produces `(W,hWS,hWcard,g,hg,hLI)`,
     applies `case_III_rank_certification_chain`, `exact case_III_realization_of_rank`.
  3. **2c-iii `chainData_dispatch`** + CHAIN-5 wire-up; then orphan confirm-and-delete (the `hφ`-spine; LEAF 1–4
     STAYS).
  **CLAUSE (ii) — the two arm-internal steps flagged NOT-yet-isolated, possibly each its own sub-leaf at build:**
  (α) deriving `hrCol` for the *candidate-transported* `rRow` from A-1's *base* `−ρ₀` value — needs the relabel's
  column-naturality (`funLeft`-dualMap commutes the `single vᵢ`-column with the `single (vtx 1)`-column under the
  cycle); plausibly mechanical (`hingeRow_funLeft_dualMap` + the M₃ `:2708–2710` `acolumn` pattern), but it is the
  step that BRIDGES the landed base-side `±r` identity to the candidate-side `hrCol` the (b) lemma wants, and the
  d=3 M₃ arm does its analogue at length 1 (`:2699–2724`, `hw9a` then `hingeRow_comp_single_tail`); at general `i`
  the cycle-relabel naturality is the genuinely-new bridge — **if it does NOT factor cleanly through
  `hingeRow_funLeft_dualMap`, it is a real sub-leaf, not hand-waved.** (β) the bottom family `f`/`hf` for §(4.4):
  the chain's "bottom rows" family at the candidate base — the M₃ arm gets it pre-packaged from the dispatch as
  `w`/`hw`/`hwmem`; at general `d` the chain dispatch must build it (the OD-7 reduction producers + the relabel),
  which is partly the 2c-iii dispatch's job, partly the arm's. **Neither (α) nor (β) is a wall** (both are
  member-MOVING relabel transport, §I.8.20(e) buildable), but both are arm wiring whose exact factor-into-leaves
  is a build-time call, NOT pinned here. **No motive/IH change; the (b) reduction follows cleanly from the column
  identity + `hgate`; no signature manufactured with secretly-unsatisfiable hypotheses — `hrCol`/`hgate`/`hW` are
  each discharged by the dispatch's `ρ₀`/`hgate` + the landed `±r` identity + the off-`vᵢ` base vanishing.**

  *(4.6) PRE-BUILD CORRECTIONS to (4.0)–(4.5) — file location + the "pure assembly" framing (2026-06-21,
  opus, docs-only; verified against the import DAG + the landed cert/leaf/template bodies).* Two pins in
  (4.0)–(4.5) are wrong as stated; correct them before the arm build:

  - **FILE: the chain arm lives in `CaseIII/Relabel.lean`, NOT `Arms.lean`** (corrects (4.5).2 / the (3) NEW
    bullet / the Phase23c Hand-off). The import DAG is `Arms ⊂ Relabel ⊂ Realization` (verified:
    `Relabel.lean:6` `import …CaseIII.Arms`; `Realization.lean:11` `import …CaseIII.Relabel`).
    `case_III_arm_realization_chain` consumes the chain-relabel leaves `chainData_bottom_relabel`
    (`Relabel.lean:1961`) and `funLeft_dualMap_interior_group_acolumn_eq_neg_baseRedundancy`
    (`Relabel.lean:4086`) — both *downstream* of `Arms.lean`, so it CANNOT compile there. Its only viable home
    is `Relabel.lean` (where the chain leaves + the `M₃` arm template already live), upstream of the future
    2c-iii `chainData_dispatch` in `Realization.lean`. (Relabel.lean is already 4776 lines, past the ~1500-LoC
    tripwire — the chain arm + dispatch likely force a `Relabel/` split before or at this build; flag at build.)
  - **"PURE ASSEMBLY" UNDERSTATES THE ARM: it must CONSTRUCT its candidate as a `caseIIICandidate`, not bridge
    to one** (sharpens (4.0)/(4.3)/(4.4)). `case_III_rank_certification_chain` is stated over
    `caseIIICandidate (G−vᵢ) endsσρ qρ e_fresh e_repro (q(a,·)) n' n_b 0` (`Candidate.lean:1886–1906`); there is
    **no** `caseIIICandidate ↔ ofNormals` bridge lemma in tree (grep-confirmed), and the chain leaves produce
    membership in `ofNormals (G−vᵢ) endsσρ qρ`. So the arm does what the *engine* does (`case_III_arm_realization`
    builds `F₀ := caseIIICandidate G ends q e_a e_b na n' nb 0` and the SHARED tail handles the off-`{e_a,e_b}`
    seed coincidence via `caseIIICandidate_supportExtensor_of_ne`): the chain arm INSTANTIATES `caseIIICandidate`
    at the relabelled split, identifying `e_fresh`/`e_repro` with the candidate-`i` split's two overridden hinges,
    then routes the chain-leaf memberships (stated over `ofNormals`) into the `caseIIICandidate` rigidity rows
    via the same off-the-two-slots seed-coincidence step. This is genuine arm-internal wiring, NOT "wire landed
    brick B into slot C". It IS the same *kind* of wiring the engine + shared tail already do — so it is buildable,
    member-MOVING, no wall, no motive change — but it is a real arm body (comparable to the ~200-line `M₃` arm),
    NOT a thin instantiation. The (α) `hrCol` step must be stated for the SPECIFIC `±r` `rRow` the arm puts in
    `g` (the relabel-image of A-1's edge-`i` group at the candidate `caseIIICandidate`); the landed
    `funLeft_dualMap_interior_group_acolumn_eq_neg_baseRedundancy` gives the `−ρ₀` *column value at `ofNormals`*,
    and bridging it to the `caseIIICandidate` row's column is the (α) sub-leaf. (β) the bottom family stays a
    hypothesis (the dispatch supplies it).

  **Consequence for the build order:** the arm is one larger commit (in `Relabel.lean`), or — preferred under the
  scope-to-fit discipline — split: first land the (α) `hrCol`-at-`caseIIICandidate` sub-leaf + the candidate
  `±r`-row `hg` membership (the relabel-image of A-1's edge-`i` group ∈ `span caseIIICandidate.rigidityRows`,
  both via `chainData_bottom_relabel` + the seed-coincidence), THEN the arm assembling those + the carrier `W`
  + the `hLI` corner leaf + the SHARED tail. No motive/IH/contract change; the wall stays gone (selector-agnostic
  cert, `±r` as a genuine candidate-edge row).

  *(4.7) CORRECTION to (4.3)/(4.6) — the `±r`-row `hg` is a REPRODUCED-SLOT member, NOT off-slot; the landed
  GROUP leaf is mis-targeted (2026-06-21, opus docs-only, VERIFIED against the landed bodies).* (4.3)/(4.6)
  framed the candidate `±r`-row `hg` as "the relabel-image of A-1's edge-`i` group routed via the OFF-slot
  seed-coincidence row bridge" — and the GROUP leaf landed in commit 44d7b73
  (`funLeft_dualMap_pmR_group_mem_span_caseIIICandidate` + per-summand brick) implements exactly that off-slot
  route, demanding `htransport` = a surviving genuine `(G−vᵢ).IsLink f' u' w'` with `f' ∉ {e_c,e_r}`. **This is
  wrong for the `±r` row.** Traced through the landed bodies: A-1's `±r`-group is its `ev j = cd.edge i` group
  (`interior_group_acolumn_eq_neg_baseRedundancy`, `Relabel.lean:4140`); `edge i` links `vᵢ — vᵢ₊₁`
  (`ChainData.link`); under `(shiftPerm i.castSucc)⁻¹` (`vᵢ` top-of-cycle ↦ `vᵢ₋₁`, `vᵢ₊₁` off-cycle fixed) the
  endpoints become `{vᵢ₋₁, vᵢ₊₁}` = **the candidate fresh pair** = the wrap-edge `Or.inr` branch of
  `chainData_bottom_relabel` (`:2032`/`:2045`) = the candidate's **reproduced slot `e_r`** (`caseIIICandidate`
  overrides exactly `{e_c, e_r}`, `Candidate.lean:944`). No `G`-edge links `vᵢ₋₁—vᵢ₊₁` (only the fresh `e₀ ∉
  E(G)`), so the off-slot `htransport` is UNSATISFIABLE. The `±r` row IS a candidate member — via the
  **reproduced-slot route**: the M₃ arm (`Relabel.lean:2756`, `d=3 i=2`) shows it — the `(a,b)`-block tag
  relabels to the genuine `e_r`-row because `ρ₀ ⊥ candidate.supportExtensor e_r` (the dispatch's `hρe₀`). So the
  next concrete commit is a NEW reproduced-slot `hg` leaf `funLeft_dualMap_pmR_group_mem_span_caseIIICandidate_
  reproduced` (signature pinned in `notes/Phase23c.md` *Hand-off*: `hcollapse` = relabel image lands on the
  `e_r`-tag, `hperp` = `ρ₀ ⊥ reproduced extensor`; `subset_span` of the `mem_hingeRowBlock_iff` /
  `caseIIICandidate_supportExtensor_reproduced` row). The landed off-slot GROUP leaf is RETAINED (it correctly
  serves the OFF-slot genuine bottom-family members of the `hWS` W-block, where the endpoints DO survive as
  genuine `(G−vᵢ)` links). **CLAUSE (ii):** this is one more genuinely-new leaf, member-MOVING, no wall, no
  motive/IH change — flagged, not forced; the off-slot framing in (4.3)/(4.6) for the `±r` corner is superseded
  by this entry.

  *(4.8) BLOCKED — the `±r`-row sourcing seam does NOT close from the landed leaves: a verified
  column-index/object mismatch between the `hg` route and the `hrCol` route (2026-06-21, opus docs-only;
  every claim re-derived from the landed `def`/`theorem` bodies — A-1 `Candidate.lean:400`, the cert
  `:1922`, the discriminator `:1798`, the `hrCol` leaf `Relabel.lean:4240`, the reproduced-slot `hg` leaf
  `:2212`, the off-slot GROUP leaf `:2157`, T-2 `:4693`, `chainData_bottom_relabel` `:1961`, the M₃ template
  `:2691`, `caseIIICandidate` `Candidate.lean:939`, `shiftPerm` `Operations.lean:1468`).* The §(4.7)
  reproduced-slot leaf landed (commit `b675317`), but assembling the arm exposes that **no single `±r`-row
  object grounds BOTH the cert's `hg` AND the discriminator's `hrCol` from the landed leaves.** This is the
  clause-(ii) FLAG-DON'T-FORCE stop; a 4th pin on this seam needs a genuinely-new corrected leaf, named below.

  **The two demands, and the body they read at (verified):**
  - The candidate framework for chain candidate `i` re-inserts body `vᵢ = vtx i` (`chainData_bottom_relabel`
    removes `cd.vtx i.castSucc`; the M₃ instance `i=2` maps the engine's re-inserted `v := a = vtx 2 = vtx i`,
    `Relabel.lean:2778–2779`). The candidate hinge `e_a` links `vtx i — vtx (i+1)` (engine `hG_ea`/`hends_ea`
    `Arms.lean:68–69`; M₃ `e_a := e_c`), so the discriminator `notMem_span_mkQ_pmR_row_of_gate`'s `hv :
    (ends e_a).1 = vᵢ = vtx i` pins the **panel-row tail at `vtx i`**, and its `hrCol : rRow.comp (single vᵢ)
    = −ρ₀` reads the `±r` row's column at **`single (vtx i)`** (`Candidate.lean:1799–1809`).
  - The LANDED `hrCol` leaf `funLeft_dualMap_interior_group_acolumn_eq_neg_baseRedundancy` (`Relabel.lean:4240`)
    establishes `= −ρ₀` at **`single (cd.vtx ⟨i−1⟩)`** (line 4257), for the `±r` object = the relabel image
    `(funLeft (shiftPerm ⟨i⟩)⁻¹).dualMap (∑_{ev j = edge i} …)` of A-1's **FILTERED** edge-`i` group. Its
    docstring (`:571`) even names `vtx (i−1)` "the re-inserted candidate body" — a convention that **conflicts**
    with `chainData_bottom_relabel`'s `vtx i` removal. **The column is at the wrong body (`vtx (i−1)`, not
    `vtx i`).**

  **Route (b) — `±r` = the filtered edge-`i` group (the §(4.7)/`hrCol`-leaf object): `hg` UNSATISFIABLE.**
  The filtered group `∑_{ev j = edge i} cⱼ • hingeRow (uvⱼ)(vvⱼ)(rvⱼ)` is a **multi-row sum**; the
  `interior_group_acolumn_*` machinery characterizes only its *column values* (`.comp (single …)`), never an
  equality to a single `hingeRow`. So the reproduced-slot leaf's `hcollapse : (relabel image) = hingeRow
  (endsσρ e_r).1 (endsσρ e_r).2 ρ₀` (`:2222–2225`) is **unsatisfiable from landed leaves** (a many-row sum
  agreeing with one row only at selected columns ≠ that row). And the off-slot GROUP leaf's `htransport`
  (`:2167`) is also unsatisfiable: the filtered summands' relabelled endpoints are `(shiftPerm ⟨i⟩)⁻¹ {vtx i,
  vtx (i+1)} = {vtx (i−1), vtx (i+1)}` — the candidate **fresh pair**, NOT a surviving off-`{e_c,e_r}` link.
  (This is the prior row-393/394 finding, here re-confirmed at the object level.)

  **Route (a) — `±r` = A-1's FULL combination single-row via T-2: `hg` OK, `hrCol` FAILS.** T-2
  `chainData_candidateRow_edgeGrouped_transport_comb` (`:4693`, currently orphaned) relabels A-1's full row
  `hingeRow x y ρ = ∑_{ALL j} …` to `hingeRow ((shiftPerm ⟨i⟩)⁻¹ x)((shiftPerm ⟨i⟩)⁻¹ y) ρ`. With `(x,y) =
  (vtx 0, vtx 2)` (the spliced edge `e₀`, A-1's `(ends e₀)`, `hab₁/hab₂` `:4202`) and `(shiftPerm ⟨i⟩)⁻¹`
  fixing `vtx 0` + sending `vtx 2 ↦ vtx 1`, the image is the **single genuine row `hingeRow (vtx 0)(vtx 1) ρ`**
  — `hg`-routable via the off-slot bridge IF `edge 0 = v₀v₁` survives `removeVertex vᵢ` (`i ≥ 2`, TRUE). **But
  its `vtx i`-column is `0`** (`hingeRow_comp_single_off`, `vtx i ∉ {vtx 0, vtx 1}` for `i ≥ 2`), **not `−ρ₀`**
  — so the discriminator cannot fire (`hrCol` demands `−ρ₀` at `vtx i`).

  **DIAGNOSIS (the incompatibility).** The only object reading `−ρ₀` (the filtered group's relabel image) reads
  it at the **wrong body `vtx (i−1)`** and does **not** collapse to a single row (so no `hg`); the only objects
  with a clean single-row `hg` (the full-combination images) read **`0`** at `vtx i`. KT eq. (6.66) wants the
  `±r` row to be a candidate row **incident to `vᵢ = vtx i`** whose `vtx i`-column is `±ρ₀` — which is the
  candidate's **reproduced slot `e_b`**, linking `{vtx (i−1), vtx i}` (M₃: `e_b := e_a` the chain shared edge,
  links `vtx (i−1)—vtx i`, `Relabel.lean:2779`; this is the row the M₃ engine itself builds, `hingeRow v c ρ`
  /`hvb_row` `:2866`, incident to the re-inserted body). The landed `hrCol` leaf reads the *other* endpoint
  `vtx (i−1)` of that same edge (so its `−ρ₀` is `hingeRow_swap`-consistent with a row `hingeRow (vtx i)(vtx
  (i−1)) ρ₀`, but the swap relocates the value to `+ρ₀` at `vtx i`).

  **THE GENUINELY-NEW LEAF NEEDED (the FIX, FLAGGED not forced).** A `±r`-row sourcing that is (i) a single
  candidate **reproduced-slot** row `hingeRow (vtx i)(vtx (i−1)) ρ₀` (incident to `vᵢ = vtx i`), with (ii) `hg`
  via the reproduced slot (`caseIIICandidate_supportExtensor_reproduced` + `hperp`, the §(4.7) mechanism — but
  for the `{vtx i, vtx (i−1)}` edge, NOT the unsatisfiable filtered-group `hcollapse`), and (iii) a CORRECTED
  `hrCol` leaf reading that row's column at `single (vtx i)` (the re-inserted body) = `±ρ₀`, sign reconciled.
  Candidate signature (pin at build):
  ```
  theorem Graph.ChainData.reproducedSlot_pmR_acolumn_eq_baseRedundancy …
      (hcomb : hingeRow (vtx 0)(vtx 2) ρ₀ = ∑ j, c j • hingeRow (uv j)(vv j)(rv j)) … :
      (hingeRow (cd.vtx ⟨i⟩) (cd.vtx ⟨i−1⟩) ρ₀).comp (single (cd.vtx ⟨i⟩)) = ρ₀    -- at vᵢ = vtx i
  ```
  together with a reproduced-slot `hg` for the SINGLE row `hingeRow (vtx i)(vtx (i−1)) ρ₀` (not the group). The
  **open decision**: whether the `±r` row's identity `hingeRow (vtx i)(vtx (i−1)) ρ₀ ∈ span (candidate rows)`
  follows from A-1 + the relabel (the M₃ `hvb_row` route reads it directly from `hρe₀` as a genuine reproduced
  row; the cycle generalization must show the **transported redundancy lands on the `{vtx i, vtx (i−1)}` edge**,
  not the `{vtx (i−1), vtx (i+1)}` fresh pair the filtered-group relabel produces). This is the substantive
  KT-(6.66) step the current leaves miss — it is the SAME math the dead `hρGv`-spine's
  `chainData_freshEdge_slot_mem` route was attacking (the slot row `hingeRow vᵢ₋₁ vᵢ₊₁ ρ₀ ∈ span (G−vᵢ)`,
  §(I.8.0)–(I.8.3)), which suggests the wall-escape is **less complete than (4.7) claimed**: the reproduced-slot
  `hg` leaf landed, but its `hcollapse` input is the unbuilt piece.

  **CLAUSE (ii) HONESTY.** STOP here, do NOT pin a 4th leaf whose hypothesis is unsatisfiable. Fate of the
  current leaves: the **reproduced-slot `hg` leaf** (`:2212`, `b675317`) is RETAINED but its `hcollapse` is
  not dischargeable for the filtered group — it needs to be re-aimed at a single reproduced-slot row (above) or
  superseded; the **off-slot GROUP leaf** (`:2157`) is RETAINED for the genuine off-slot `hWS` bottom family
  (its correct use); the **`hrCol` leaf** (`:4240`) is RETAINED as the base-side `−ρ₀`-at-`vtx (i−1)` fact but
  is **NOT** the discriminator's `hrCol` (wrong body) — the corrected `vtx i`-column leaf is new; **T-2**
  (`:4693`) is the right TRANSPORT primitive for the full-combination single row but route (a) shows the full
  row reads `0` at `vtx i`, so T-2 alone does not source the `±r` row either — REVIVE only if the corrected
  sourcing routes through it. No motive/IH/contract change is forced; this is machinery below the contract. The
  smallest unblocking commit is the corrected `vtx i`-column `hrCol` leaf + the single-reproduced-row `hg`,
  with the `hingeRow (vtx i)(vtx (i−1)) ρ₀ ∈ span` identity as the named open decision.

  *(4.9) RESOLVED — the `±r` corner row is the DIRECT genuine reproduced-slot `e_b`-row; the
  graph-endpoints-vs-overridden-support DECOUPLING grounds BOTH `hg` and `hrCol` with no `hρGv`
  (2026-06-22, opus; adjudicated by an adversarial recon pair + independent source verification, then
  BUILT clean). The (4.8) open decision is answered: the `±r` row is NOT a relabel-image / filtered-group
  object (those land on the candidate fresh pair, which OMITS `vᵢ`, and read `0` at `single vᵢ`). It is
  the candidate's **reproduced hinge `e_b`** read off its own GENUINE `G`-link, oriented through `vᵢ`.*

  The KEY DISTINCTION the 4 prior attempts missed: at chain candidate `i`, the reproduced slot `e_b`'s
  GRAPH-link endpoints (the chain edge through the re-inserted body `vᵢ`) are DECOUPLED from its OVERRIDDEN
  support panel (the fresh pair, which omits `vᵢ`). `caseIIICandidate.graph = G` (`Candidate.lean:943`) so
  the slot keeps its genuine link; only `supportExtensor` is overridden at `{e_a, e_b}`
  (`caseIIICandidate_supportExtensor_reproduced`, `:971`). So ONE genuine row `hingeRow u vᵢ ρ₀` (with
  `G.IsLink e_b u vᵢ`, `vᵢ` the head) grounds both demands:
  - **`hg` (membership)** reads the OVERRIDDEN support: `ρ₀ ∈ r(p(e_b))` of the candidate `⟺ ρ₀ ⊥
    panelSupportExtensor (n_u + t • n') n_r` = the dispatch's `hρe₀` — VERBATIM the `d=3` M₃ `hvb_row`
    mechanism (`Relabel.lean:2866`), `Submodule.subset_span ⟨e_b, u, vᵢ, hlink, ρ₀, hblock, rfl⟩`. USES
    ONLY `hρe₀`, NEVER `hρGv`. → leaf `hingeRow_mem_caseIIICandidate_rigidityRows_reproduced`.
  - **`hrCol` (column)** reads the GRAPH link at `single vᵢ`: `hingeRow u vᵢ ρ₀` has `vᵢ` as head, so
    `hingeRow_swap` + `hingeRow_comp_single_tail` gives `−ρ₀` — exactly the discriminator's `hrCol`. →
    leaf `reproducedSlot_pmR_acolumn_eq`. (`vᵢ ∈ {u, w}` because the link includes the re-inserted body;
    the support panel omitting `vᵢ` is what makes the membership perp `hρe₀` not `hρGv`.)

  Both leaves landed (`Candidate.lean`, after `linearIndependent_mkQ_corner_of_gate`), abstract over the
  `caseIIICandidate` params + the genuine link + `hperp`, axiom-clean, build/lint warning-clean. The
  SATISFIABILITY gate passes: the arm orients `e_b`'s genuine link with `vᵢ` as head, so the SAME object
  `hingeRow u vᵢ ρ₀` is the cert's `g`-corner `±r` member (`hg`), the discriminator's `rRow` (`hrCol`),
  and reads `−ρ₀` at `vᵢ` — no two-object mismatch (the (4.8) defect). Option (A) escapes the wall AT THE
  ARM: the `±r` row's membership is `hρe₀`-only; no `hρGv`, no member-mapping wall, no motive/IH change.

  **Fate of leaves (updated from (4.8)):** the mis-targeted reproduced-slot GROUP leaf
  `funLeft_dualMap_pmR_group_mem_span_caseIIICandidate_reproduced` (`b675317`) is **DELETED** — its
  `hcollapse` (filtered group = single row) is unsatisfiable AND it was stated over `G.removeVertex vᵢ`
  (the cert is over full `G`); grep-confirmed consumed nowhere. The off-slot GROUP leaf
  `…_caseIIICandidate` (`:2157`) is **KEPT** (genuine off-slot `hWS` bottom family). The base-side `hrCol`
  leaf `funLeft_dualMap_interior_group_acolumn_eq_neg_baseRedundancy` (reads `vtx (i−1)`) and T-2 are NOT
  the `±r` sourcing — the genuine `e_b`-row route supersedes them; revive only if a later arm step needs
  them. **Hand-off re-pointed** to the arm assembly `case_III_arm_realization_chain` (now genuine wiring:
  construct candidate over full `G`, assemble `(W,hWS,hWcard,g,hg,hLI)` with `±r` = these leaves, apply
  the cert, `exact case_III_realization_of_rank`).

  *(4.10) CHAIN-2c-iii `chainData_dispatch` — DECOMPOSITION INTO COMMIT-SIZED LEAVES, RANKED, with the
  HARD CORE named (2026-06-23, opus docs-only design-pass; every load-bearing claim re-derived from the
  LANDED `def`/`theorem` bodies after the `Relabel/` split — the assembly `case_III_arm_corner_assembly`
  + spine `case_III_arm_realization_chain` `Relabel/ForkedArm.lean:136/59`, the chain cert
  `case_III_rank_certification_chain` `Candidate.lean:1988`, the carrier leaf
  `exists_le_finrank_span_rigidityRows_eq_card_of_injective_map` `Candidate.lean:1727` + its mirror
  `Submodule.exists_le_finrank_eq_card_of_injective_map` `Mathlib/.../Constructions.lean:246`, the (α)
  bridge `funLeft_dualMap_comp_single` `Basic.lean:576`, `chainData_bottom_relabel` `Relabel/Chain.lean:316`,
  the W6b gate producer `chainData_split_w6b_gates` `Realization.lean:771`, the LANDED per-`i` reduction
  `chainData_split_realization` `Realization.lean:954`, the discriminator-pick
  `exists_chainData_discriminator_pick` `Realization.lean:1144` + capstone `…_gen` `Claim612.lean:1462`,
  the d=3 dispatch `case_III_candidate_dispatch` `Realization.lean:268`, the per-`i` candidate template
  `case_III_arm_realization_M3` `Relabel/Arm.lean:54`, the `ChainData` interior accessors
  `Operations.lean:1392–1462`, the C.3 dispatch contract — NOT inherited from the prior pins' prose.)*

  **THE ARCHITECTURAL FACT THAT SETS THE CUT (re-confirmed, route β §(l)/(m)/(n)).** The dispatch fires
  the redundancy producer + discriminator **ONCE** off the single shared base (the `v₁`-split), getting one
  `ρ₀` (= KT's abstract `r`) and one discriminating panel `u`; it then routes `u`'s matched candidate `i`
  to an arm. There are TWO arm routes, already both landed:
  - the **base candidate `i=1`** (the `v₁`-split's own genuine framework — `hρGv` IS a genuine base
    membership, no relabel) and the **d=3 floor**: the LANDED OLD engine `case_III_arm_realization`, reached
    via the LANDED per-`i` reduction `chainData_split_realization` (which already fires
    `chainData_split_w6b_gates` once + feeds the old engine, taking the discriminator slot as `htrans`);
  - the **interior candidates `2 ≤ i < d`** (the relabel-image candidates, KT 6.54–6.56): the option-(A)
    `case_III_arm_corner_assembly` (NO `hρGv`, the `±r` block decomposition).

  So the dispatch is NOT a from-scratch composer — it is a **discriminator-pick + Fin-case router** over two
  already-landed arm routes, PLUS the production of the corner-assembly's RAW inputs for the interior route.
  The HARD CORE is exactly that production: `hgate`/`hρe₀` (the discriminator outputs threaded to the matched
  `i`), and `W`/`hWS`/`hWcard`/`hW` (the relabel-image base block as a CONCRETE subspace).

  **THE ONE GENUINE DESIGN DECISION — the `W`/`hW` threading (clause (ii), FLAGGED).** This is the prompt's
  flagged wrinkle, and it is a REAL (small) decision, not mechanical threading: `case_III_arm_corner_assembly`
  takes `hW : ∀ φ ∈ W, φ.comp (single v) = 0` on a *specific* `W`, but the LANDED carrier leaf
  `exists_le_finrank_span_rigidityRows_eq_card_of_injective_map` returns an **EXISTENTIAL** `W` (its body is
  `⟨span (range (L ∘ f)), …⟩` but the `∃` hides it — `Mathlib/.../Constructions.lean:251`). You CANNOT prove
  `hW` on a `Classical.choice`-obtained opaque `W`. **VERDICT (does NOT need the coordinator/user — it is below
  the contract/motive, a leaf-shape choice):** the dispatch must NOT consume the existential leaf; it sets
  `W := Submodule.span ℝ (Set.range (L ∘ f))` **concretely** and proves the three facts on it directly. This
  is one genuinely-new small leaf (LEAF-2 below), a concrete-`W` carrier variant exposing the body the
  existential leaf hides. `hWcard = finrank_span_eq_card (hf.map' L …)`; `hWS = span_le.mpr …`; `hW` by
  `Submodule.span_induction` over `range (L ∘ f)` + the (α) bridge `funLeft_dualMap_comp_single`
  (`Basic.lean:576`): `(funLeft σ⁻¹).dualMap (f j) ).comp (single v) = (f j).comp (single (σ v))`, and the base
  rows `f j` (genuine `(G−vᵢ)`-rows over old bodies) vanish at `single (σ v)` since `σ v ∉ {their endpoints}`.
  **This is NOT a motive/IH/contract change** (re-confirmed: the cert/arm are below C.0–C.6); it is a
  return-shape mismatch between a landed leaf and its actual consumer, fixed by one new leaf.

  **THE OTHER FLAGGED GAP — the bottom-family `hS` disjunction (clause (ii), the §(4.4)(β) flag, RE-CONFIRMED
  as real arm-internal wiring, not a wall).** The carrier leaf's `hS : ∀ j, L (f j) ∈ span F₀.rigidityRows`
  is supplied by `chainData_bottom_relabel` — but that lemma's CONCLUSION is itself a DISJUNCTION (genuine
  candidate row OR a `(vᵢ₊₁,vᵢ₋₁)`-block tag), and the input `hwmem` (from `chainData_split_w6b_gates`) is
  ALSO a disjunction (genuine `Gv`-row OR `(ab)`-block tag). So `hS` is NOT a single application: it is a
  per-member case-split routing the genuine images via the off-slot GROUP leaf
  `funLeft_dualMap_pmR_group_mem_span_caseIIICandidate` (`Relabel/Chain.lean:512`, KEPT for exactly this) +
  the row-routing bridge `hingeRow_mem_caseIIICandidate_rigidityRows_of_ofNormals_link`, and the block-tag
  images via the reproduced-slot membership. **This is member-MOVING relabel transport (§I.8.20(e)
  buildable), no wall, no motive change — but it is genuine wiring with a non-trivial case-split, NOT a
  one-liner.** It is the bulk of LEAF-4 below.

  **THE LEAVES (commit-sized, ranked EASY→HARD; the hard core flagged so a build cannot peel an easy one and
  defer the hard).** Home: a fresh `Relabel/Dispatch.lean` importing `Relabel/ForkedArm` (the `Relabel/` split
  is DONE; do NOT grow `Realization.lean`). All signatures below are over `{k} {α β} [Finite α] [Finite β]
  [DecidableEq α] [DecidableEq β]`, `{G : Graph α β} {n : ℕ} (cd : G.ChainData n)`.

  - **LEAF-1 (EASIEST — pure combinatorial setup, ~½ commit). The interior-split `endsσρ`/`qρ` candidate
    framework + the four `case_III_arm_corner_assembly` graph/seed hyps NOT already on the accessors.** At an
    interior `i` (`0 < i`), the accessors (`Operations.lean:1392–1462`) already give `hvVc`/`haVc`/`hbVc`
    (the three `removeVertex` memberships), `hG_ea`/`hG_eb` (`isLink_succ_edge`/`isLink_pred_edge`), `heab`
    (`pred_edge_ne`), `hva`/`hvb` (`castSucc_ne_succ`/`castSucc_ne_pred_castSucc`), `hsplitG`
    (`isLink_eq_succ_or_pred_or_removeVertex`), and `hleG` is `removeVertex_isLink.mp ·.1`. LEAF-1 supplies
    the per-candidate selector `endsσρ`/seed `qρ` (the `(shiftPerm i.castSucc)⁻¹`-shifted ones, exactly
    `chainData_bottom_relabel`'s target framework `Relabel/Chain.lean:337–341`) and the remaining hyps
    `hends_ea`/`hends_eb` (the override selector at the two re-inserted hinges, the `Function.update` pattern
    of `case_III_candidate_dispatch:444`), `hends_Gv`/`hne_Gv` (the off-slot link-recording + general-position
    support nonvanishing, verbatim from `chainData_split_realization:1079–1092`), `hVone`/`hVcard`
    (`Graph.vertexSet_removeVertex` + `Set.ncard_diff_singleton_of_mem (cd.vtx_mem _)`), `hLn`/`hgab` (the seed
    pairwise-LI from the split realization's `IsGeneralPosition`). Signature (a `def` producing the framework +
    a bundling `lemma`, or inline in LEAF-4):
    ```
    -- the candidate-i selector/seed (no new theorem; a def, mirrors chainData_bottom_relabel's target):
    def ChainData.candidateEnds (cd : G.ChainData n) (i : Fin cd.d) (ends₀ : β → α × α) : β → α × α
    def ChainData.candidateSeed (cd : G.ChainData n) (i : Fin cd.d) (q : α × Fin (k+2) → ℝ) :
      α × Fin (k+2) → ℝ := fun p => q (cd.shiftPerm i.castSucc p.1, p.2)
    ```
    No new math. **Risk: none.** It is bookkeeping; its only subtlety is matching `chainData_bottom_relabel`'s
    exact `endsσρ`/`qρ` shape so LEAF-4 can chain them.

  - **LEAF-2 (EASY-MODERATE — the concrete-`W` carrier variant, ~½–1 commit). The genuinely-new leaf the
    `W`/`hW` threading decision forces** (see the design decision above). A concrete-`W` companion to
    `exists_le_finrank_span_rigidityRows_eq_card_of_injective_map`, exposing the `span (range (L ∘ f))` body
    plus the off-`v` column-vanishing `hW`. Home: `Candidate.lean`, beside the existential leaf. EXACT
    signature:
    ```
    theorem BodyHingeFramework.span_relabelImage_le_and_finrank_and_acolumn_vanish
        [DecidableEq α] (F : BodyHingeFramework k α β) {ιb : Type*} [Fintype ιb] {v : α}
        {f : ιb → Module.Dual ℝ (α → ScrewSpace k)} (hf : LinearIndependent ℝ f)
        {σ : Equiv.Perm α}
        (hS : ∀ j, (LinearMap.funLeft ℝ (ScrewSpace k) σ).dualMap (f j)
          ∈ Submodule.span ℝ F.rigidityRows)
        (hvanish : ∀ j, (f j).comp (LinearMap.single ℝ (fun _ : α => ScrewSpace k) (σ.symm v)) = 0) :
        ∃ W : Submodule ℝ (Module.Dual ℝ (α → ScrewSpace k)),
          W ≤ Submodule.span ℝ F.rigidityRows ∧
          Module.finrank ℝ W = Fintype.card ιb ∧
          (∀ φ ∈ W, φ.comp (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v) = 0)
    ```
    with `W := span (range ((funLeft σ).dualMap ∘ f))`. `hWS`/`hWcard` reuse the existential leaf's body
    (`span_le` + `finrank_span_eq_card (hf.map' …)`); `hW` is the new content — `span_induction` over the
    range, base case the LANDED `funLeft_dualMap_comp_single` (`Basic.lean:576`, signature re-verified):
    `((funLeft σ).dualMap (f j)).comp (single v) = (f j).comp (single (σ.symm v))`, which `hvanish` kills.
    **(The `hvanish`-at-`σ.symm v` direction is FORCED by that bridge's `σ.symm w` conclusion, not a free
    choice — the (4.8)-class column-index trap; pinned exactly to avoid a confident-wrong signature.)**
    BUILD-TIME LATITUDE (flag, not a wall): which concrete `σ` (`shiftPerm i.castSucc` itself, whose `.symm` is
    `chainData_bottom_relabel`'s `(shiftPerm i.castSucc)⁻¹`) is passed — i.e. whether the leaf is instantiated
    at `σ = shiftPerm i.castSucc` (then `σ.symm = (shiftPerm i.castSucc)⁻¹` matches the relabel's
    `(funLeft (shiftPerm i.castSucc).symm).dualMap` — so the `f j` images live in the candidate span via
    `chainData_bottom_relabel`, and `hvanish` reads `(shiftPerm i.castSucc) v`). `hvanish` is then discharged
    in LEAF-4 from "base rows over old bodies don't touch `(shiftPerm i.castSucc) v`". **Risk: low** —
    `span_induction` + one landed bridge; the only friction is the perm-direction bookkeeping (a TACTICS-QUIRKS
    `.symm`-placement candidate).

  - **LEAF-3 (MODERATE — the discriminator→candidate plumbing, ~1 commit). Fire the single redundancy +
    discriminator off the shared base and EXPOSE `ρ₀`/`hgate`/`hρe₀` at the matched interior candidate `i`.**
    This is the `Fin (k+1)` family glue CHAIN-2c-i (`exists_chainData_discriminator_pick`, LANDED) wrapped to
    return, for the candidate `i` the discriminator's panel `u` matches, the assembly's discriminator slots:
    `hgate : ρ₀ (panelSupportExtensor (q(a,·)) n') ≠ 0` and `hρe₀ : ρ₀ (panelSupportExtensor (q(a,·)) (q(b,·)))
    = 0`, where `ρ₀` is the W6b functional from `chainData_split_w6b_gates` (fired ONCE) and `n'` is the
    transversal. The d=3 template is `case_III_candidate_dispatch:435–441` (the discriminator region) + `:501`
    (`hgate`/`hρ0e₀` passed to the arm); `chainData_split_realization` already does exactly this for the OLD
    engine via its `htrans` slot, so LEAF-3 is the SAME wiring re-aimed at the assembly's `hgate`/`hρe₀` shape.
    Sketch signature (a producer the dispatch consumes; `i` ranges over interior candidates, `u`↔`i` matching
    is the OD-arithmetic the candidate selector `cand : Fin (k+1) → α` fixes):
    ```
    theorem ChainData.exists_shared_redundancy_and_discriminator …
        (the base seed + IH context) :
        ∃ (q : … ) (ends : …) (ρ₀ : Module.Dual ℝ (ScrewSpace k)) (i : Fin cd.d) (hi : 0 < (i:ℕ)) (n' : …),
          ρ₀ ≠ 0 ∧
          ρ₀ (panelSupportExtensor (q(cd.vtx i.succ,·)) n') ≠ 0 ∧                     -- hgate
          ρ₀ (panelSupportExtensor (q(cd.vtx i.succ,·)) (q(cd.vtx ⟨i-1⟩.castSucc,·))) = 0 ∧  -- hρe₀
          (the W6b ρ₀/w bundle at the base, for LEAF-4's bottom family)
    ```
    **BUILD-TIME LATITUDE (flag):** the panel-index `u : Fin (k+1)` ↔ chain-candidate `i : Fin cd.d` match (the
    `cand` injective selector of `exists_chainData_discriminator_pick`) is the `Fin` arithmetic C.3 leaves to
    build-time. **Risk: moderate** — no new linear algebra (the discriminator is LANDED general-`k`), but the
    candidate-selector arithmetic and threading the W6b base bundle through to LEAF-4 is real plumbing.

  - **LEAF-4 (THE HARD CORE — ~1–2 commits; this is where a build MUST NOT scope-to-fit away). The interior
    base-block `W`/`hWS`/`hWcard`/`hW` production over the chain bottom family + the `hS` disjunction
    routing.** Given the matched interior `i`, `ρ₀`, the W6b base bottom family `w`/`hw`/`hwmem` (LEAF-3's
    bundle), produce the four corner inputs `case_III_arm_corner_assembly` consumes and CALL it. The body:
    (a) the LI base family `f := w` (card `D·(m_v−1)`, `hf := hw`); (b) `L := (funLeft (cd.shiftPerm
    i.castSucc)⁻¹).dualMap`, injective (M₃ `hw` route, `dualMap` of surjective `funLeft`); (c) `hS` — the
    per-member case-split over `hwmem`: genuine images via `chainData_bottom_relabel`'s `Or.inl` →
    off-slot GROUP leaf / row-routing bridge into `caseIIICandidate.rigidityRows`; block-tag images via
    `Or.inr` → reproduced-slot membership; (d) `hvanish` — base rows over old bodies vanish at `single (σ v)`;
    (e) apply LEAF-2 to get `W`/`hWS`/`hWcard`/`hW`; (f) `exact case_III_arm_corner_assembly … hgate hρe₀ hWS
    hWcard hW hdef`. **WHY THIS IS THE HARD CORE:** (c) is the §(4.4)(β) flag — `chainData_bottom_relabel` and
    `hwmem` are BOTH disjunctions, so `hS` is a real per-member router (genuine vs block-tag, each into the
    candidate span), NOT a single rewrite; and it must align the framework `chainData_bottom_relabel` produces
    (`ofNormals (G−vᵢ) endsσρ qρ`) with the assembly's `caseIIICandidate (G) endsσρ qρ e_a e_b …` over full
    `G` (the row-routing bridge `hingeRow_mem_caseIIICandidate_rigidityRows_of_ofNormals_link`, the
    off-the-two-slots seed coincidence). This is the substantive composer the last two dispatches scoped AWAY
    from. **Risk: the highest of the four**, but bounded — every ingredient is landed (`chainData_bottom_relabel`,
    the GROUP leaf, the reproduced-slot membership, the row-routing bridge, LEAF-2); it is assembly + a
    case-split, no new linear algebra and NO wall (member-MOVING throughout, the cert is `hρGv`-free).
    Sketch:
    ```
    theorem ChainData.case_III_chain_arm_at_interior (cd : G.ChainData n) (i : Fin cd.d) (hi : 0 < (i:ℕ)) …
        (the LEAF-3 ρ₀/hgate/hρe₀ + W6b w/hw/hwmem bundle, the LEAF-1 framework hyps) :
        PanelHingeFramework.HasGenericFullRankRealization k n G
      := …; exact PanelHingeFramework.case_III_arm_corner_assembly G (G.removeVertex (cd.vtx i.castSucc))
            endsσρ … hgate hρe₀ hWS hWcard hW hdef
    ```

  - **LEAF-5 (MODERATE — the router + d=3 floor, ~1 commit). `ChainData.chainData_dispatch` proper.** The
    top-level dispatch: from `cd`/base-seed/IH context, fire LEAF-3 to get the matched `i`/`ρ₀`/gates; CASE on
    the candidate: `i=1` (base) and the **d=3 floor** route to the LANDED `chainData_split_realization` (the
    OLD engine, zero-regression — its `htrans` slot filled from the SAME discriminator); interior `2 ≤ i < d`
    route to LEAF-4. Produces `HasGenericFullRankRealization k n G` from the C.3 inputs. **BUILD-TIME LATITUDE
    (flag):** the precise routing predicate (`i=1` vs `d=3∧i=2` vs general interior) and the `d=3`
    zero-regression check (the C.4 adapter must keep `case_III_candidate_dispatch` byte-reachable) is settled
    at build; the prompt's "`d=3` floor (`i=2`) → landed engine" is the zero-regression invariant. **Risk:
    moderate** — the routing/`Fin`-arithmetic is the work; both arm routes are landed. CHAIN-5 (wiring
    `chainData_dispatch` into `case_III_realization_all_k`'s `hdispatch` via the C.4 4-tuple adapter) is the
    NEXT sub-step after, plus the orphan confirm-and-delete (the `hφ`-spine; LEAF 1–4 STAYS).

  **RANKING + HARD-CORE FLAG (the anti-scope-to-fit gate).** EASIEST→HARDEST: LEAF-1 (combinatorial setup) <
  LEAF-2 (concrete-`W` carrier, one `span_induction`) < LEAF-3 (discriminator plumbing) < LEAF-5 (router) <
  **LEAF-4 (the base-block `W` production + `hS` disjunction routing) — THE HARD CORE.** A build that lands
  LEAF-1/2/3 but defers LEAF-4 as "too big" has peeled the easy shell and left the actual composer
  undone — LEAF-4 is the §(4.4)(β) flag made concrete, the piece the last two dispatches scoped away from.
  The **FIRST commit-sized leaf to land is LEAF-2** (the concrete-`W` carrier variant: it is the genuinely-new
  leaf the `W`/`hW` threading decision forces, it unblocks LEAF-4's `hW`, and it is small + self-contained —
  the rows-384/389 "land the genuinely-new small piece first" pattern). **CLAUSE (ii):** no motive/IH/contract
  change is forced; the one design decision (concrete vs existential `W`) is below the contract and is RESOLVED
  here (concrete `W`, new LEAF-2 — does NOT need coordinator/user); the two flagged gaps (the `W`/`hW` shape,
  the `hS` disjunction) are named as real wiring, not hand-waved; `d=3` stays a zero-regression wrapper.

  *(4.11) LEAF-3 DISCRIMINATOR-INDEX GAP — VERIFIED, FROZEN-CONTRACT DECISION REQUIRED (BLOCKED; 2026-06-23,
  opus docs-only design-pass, both halves of clause (i) verified: the LANDED `def`/`theorem` bodies AND KT
  §6.4.2 read end-to-end from `.refs/katoh-tanigawa-2011-molecular-conjecture.pdf` pp. 692–698, eqs. 6.46–6.67.)*

  **A build BLOCKED on LEAF-3.** The (4.10) pin treated "the panel-`u`↔candidate-`i` match" as build-time `Fin`
  arithmetic (line ~2086). It is NOT: it is a frozen-contract decision. The gap is an INDEX-SET mismatch between
  two LANDED objects, and KT's argument forces the equation that closes it.

  **The two LANDED objects (source-verified).**
  - `exists_chainData_discriminator_pick` (`Realization.lean:1144`) takes `cand : Fin (k+1) → α` (injective) and
    returns a PANEL index `u : Fin (k+1)`. Its capstone `exists_complementIso_ne_zero_of_homogeneousIncidence_gen`
    (`Claim612.lean:1462`) is likewise `Fin (k+1)`-indexed (`n : Fin (k+1) → …`, returns `u : Fin (k+1)`). BOTH
    discriminators in the tree are `Fin (k+1)`-indexed; neither is `Fin cd.d`-indexed.
  - `case_III_arm_corner_assembly`'s `hgate`/`hρe₀` (`Relabel/ForkedArm.lean:155–156`) are stated at a SINGLE
    matched interior `i : Fin cd.d` (normals `q(cd.vtx i.succ,·)`, `q(cd.vtx ⟨i−1⟩.castSucc,·)`). The arm + spine
    are `cd.d`-agnostic — they take one already-chosen `i`. So the ENTIRE index gap is concentrated in LEAF-3:
    to route `u : Fin (k+1)` to a chain candidate `i : Fin cd.d`, AND to even FORM `cand : Fin (k+1) → α` over the
    chain's candidate vertices, the dispatch needs `cd.d = k+1`.
  - `ChainData.d` (`Operations.lean:1286`) is a FREE `ℕ` field with only `hd : 1 ≤ d`. The frozen CHAIN↔ENTRY
    dispatch contract C.3 (below) takes `cd : G.ChainData n` with NO `cd.d = k+1` hypothesis. C.1/C.4 NOTE
    `d = k+1` only in record-field COMMENTS (`d : ℕ -- = body-bar dim index (d = k+1)`; C.4 table `d=3 (= k+1 at
    k=2)`) — not as a hypothesis anywhere on the frozen interface.

  **KT §6.4.2 — `d = k+1` is STRUCTURAL, candidate-`i` IS selected by the panel discriminator, and `d`/`k` are
  NOT independent (the answer to the prompt's question 1, primary-source-verified).** KT's `d` is the **ambient
  Euclidean dimension** ("a nonparallel panel-hinge realization `(G,p)` in `Rᵈ`", p. 692). The chain `v₀v₁…v_d`
  has length `d`. KT builds **`d` candidate frameworks** `M₀,M₁,…,M_{d−1}` (p. 692 "consider d distinct
  frameworks"; eq. 6.65 lists exactly `M₀..M_{d−1}`) and **`d` panels** `Π₀,…,Π_{d−1}` (eq. 6.67: `Π₀=Π(v₀)`,
  `Πᵢ=Π(v_{i+1})` for `1≤i≤d−1`). **The candidate index and the panel index are the SAME set of size `d`**: `Mᵢ`
  fails full rank ⟺ `r ⊥ C(Lᵢ)` for `Lᵢ⊂Πᵢ` (eq. 6.66 + the line below 6.67). The winning candidate IS selected
  by the panel discriminator — there is NO separate `⋀^{d−1}`-duality / `ρ₀`-redundancy selector (KT's redundancy
  `r` is the SAME `±r` for every panel, eq. 6.66, so it cannot discriminate; the ONLY selection is eq. 6.67). And
  the dimension count is forced: `dim span(6.67) = (d+1 choose d−1) = (d+1 choose 2) = D` by Lemma 2.1 (p. 698).
  Since the project's `D = screwDim k = (k+2 choose 2)`, `(d+1 choose 2) = (k+2 choose 2)` ⟹ `d+1 = k+2` ⟹
  **`d = k+1`**. Equivalently via the standing `hn : bodyBarDim n = screwDim k` (`n(n+1)/2 = (k+2)(k+1)/2` ⟹
  `n = k+1`) and KT's "chain of length `d` = ambient dim `n`" (Lemma 4.6): `d = n = k+1`. So `d = k+1` is a
  structural identity of the argument; option (c) "candidate-`i` selected by mechanism X, no contract change" is
  **NOT available** — KT offers no `cd.d`-free selector.

  **`cd.d = k+1` is NOT derivable below the contract.** `hn` pins `n = k+1`, not `cd.d`. `cd.d` is whatever ENTRY's
  extractor produced; KT Lemma 4.6 guarantees the chain has length = ambient dim, but THAT guarantee is a property
  of the produced chain — it must be CARRIED on `cd` (a record field) or asserted on the dispatch (a hypothesis).
  Both are on the frozen interface (C.1 record, C.3 signature). **This is a frozen-contract change → FLAG-DON'T-FORCE
  fires; STOP.**

  **The seed-reconciliation sub-question (prompt question 3) is NOT the blocker — it is ROUTINE (verified).** The
  assembly is fed `candidateSeed i q = q∘(shiftPerm i.castSucc on body coord)` (`Operations.lean:2723`), i.e. the
  base seed `q₁` read through the index-shift iso `ρᵢ`. By KT eq. 6.55 `(Gᵢ,qᵢ)` is "exactly the same framework as
  `(G₁,q₁)`" via `ρᵢ`, so `candidateSeed`'s candidate-`i` normals ARE the base normals at the `ρ`-image vertices —
  `panelSupportExtensor(candidateSeed(a,·), n')` is a base-`q₁` extensor under a known reindexing, with `ρ₀` the
  FIXED abstract redundancy. This is functional-on-a-FIXED-extensor (the member fixed, the extensor relabelled) =
  the eq.-6.66 `±r` shape on the LANDED `candidateEnds`/`candidateSeed` = `chainData_bottom_relabel`-target
  machinery — it is NOT the `hρGv` member-mapping wall (§I.8.18–8.20, which transported a fixed *functional*
  `φ@endsσρ` and is `hρGv`-only; the (A) cert is `hρGv`-free). The block flagged it "wall-adjacent"; it is on the
  buildable side. It is downstream of the index gap (no matched `i` exists until the index gap closes).

  **THE OPTIONS (for coordinator/user adjudication; (a) recommended).**
  - **(a) Add `d_eq : cd.d = k + 1` to the `ChainData` record (C.1) — or, equivalently, to the CHAIN-5 dispatch
    signature (C.3).** *Consequence:* one new field/hypothesis on the frozen interface; the dispatch forms
    `cand : Fin (k+1) → α` by transporting `cd.vtx` across `d_eq`, and matches `u : Fin (k+1)` to `i : Fin cd.d`
    by `d_eq`. d=3 zero-regression holds (`3 = 2+1`, the C.4 wrapper sets it by `rfl`/`decide`). ENTRY later
    discharges `cd.d = k+1` from KT Lemma 4.6 (chain length = ambient dim = `n = k+1` via `hn`) — that proof is
    ENTRY's, not 23c's. This is the structurally-faithful, minimal change. *Rough estimate:* the contract edit +
    re-thread of the C.0 lockstep trio (record/producer/consumer) + d=3 wrapper ≈ **1 commit**; it then UNBLOCKS
    LEAF-3/4/5 to proceed on the prior ~5–7 band.
  - **(b) Re-express both discriminators over `Fin cd.d` instead of `Fin (k+1)`.** *Consequence:* re-states the
    two LANDED axiom-clean capstones (`exists_chainData_discriminator_pick`, `…_homogeneousIncidence_gen`, +
    CHAIN-4c/4b `case_III_claim612_gen`/`exists_line_data_…_gen`) over `Fin cd.d`. But the capstone's `D`-span
    finish (eq. 6.67, Lemma 2.1) needs the panel count `cd.d` to span `D = (cd.d+1 choose 2)`, which equals
    `screwDim k` ONLY when `cd.d = k+1` — so re-indexing does NOT avoid the equation, it merely relocates it into
    the CHAIN-4 count and re-opens green capstones. Strictly worse than (a). *Rough estimate:* **~3–5 commits**,
    re-opens landed axiom-clean CHAIN-4, higher regression risk; STILL needs `cd.d = k+1`.
  - **(c) Candidate-`i` selected by a separate mechanism, no contract change.** **NOT AVAILABLE** — KT's only
    selector is the `(k+1)`-panel discriminator (eq. 6.67); the redundancy `±r` is shared across panels and cannot
    select. Recorded for completeness; ruled out by the primary source.

  **What would unblock:** a coordinator/user decision on (a) vs (b) (recommendation: (a)). On (a), the 23c plan is
  otherwise intact — LEAF-1/LEAF-2 stay LANDED; LEAF-3 gains the `d_eq`-backed `cand`/`u↔i` match; LEAF-4/LEAF-5
  proceed as pinned. The CHAIN↔ENTRY contract gains exactly one field/hypothesis (C.1 or C.3); C.0/C.2/C.4–C.6 and
  the 0-dof motive/IH are untouched (the rank-cert/arm are `cd.d`-agnostic below the dispatch).

  **RESOLVED → (a) (2026-06-23, user-approved); the `d_eq : d = n` field is LANDED** (2026-06-23,
  `Induction/Operations.lean` `ChainData` RECORD, after `hd`; build/lint/axiom-clean; purely additive, no
  `ChainData` value constructions exist yet so nothing downstream to fix). Adjudication grounded by a diverse-lens recon PAIR
  (constructive + adversarial-refute, opus×opus, read-only) that CONVERGED on "`d=k+1` structural +
  ENTRY-dischargeable", with the coordinator independently PDF-verifying the two load-bearing KT statements
  (Prop 1.1 `D = C(d+1,2)`, p.648/p.5; Lemma 4.6 "chain … of length `d`", p.18; §6.4.2 "`d` distinct
  frameworks", p.46). **Refinement adopted: state the field as `d_eq : d = n` on the `ChainData` RECORD**
  (the chain length = the dof-regime index `n`), not `cd.d = k+1` — `n` is a record parameter and `k` is not,
  so `d = n` keeps the field record-local; `d = k+1` then follows at use sites from `hn : bodyBarDim n =
  screwDim k` (⟹ `n = k+1`). It is a **constructive record field** (set when ENTRY builds the chain to length
  `k+1`, KT-4.6's truncation = the constructor), *not* a dispatch hypothesis — which is what keeps it off the
  satisfiability trap (a hypothesis asserted but not dischargeable, rows 392/394). Two downstream risks both
  recon members flagged (non-blocking for this decision): the ENTRY KT-4.6 chain-extraction leaf (23d,
  genuinely-new combinatorial) and the eq-6.66 `±r`-shared-across-all-interiors step (KT's most compressed:
  "easily show … cf. 6.44"; lands in LEAF-4/CHAIN bookkeeping). The contract-encoding lesson this episode
  yields (a known parameter identity left unencoded = a latent gap surfacing at the first consumer) is lifted
  to `DESIGN.md` *Frozen contracts must encode the invariants relating their parameters* + the
  `coordinate-phase` step-1 trigger / design-pass clause (iii); model-exp rows 407–410.

  *(4.12) WHERE THE MATCHED-INTERIOR `hρe₀` + `hgate` COME FROM — RESOLVED; THE INTERIOR `hρe₀` IS A
  GENUINELY-NEW eq-6.66 `±r`-ANNIHILATION LEAF (NOT a transport, NOT a per-candidate W6b firing); IT
  is MACHINERY BELOW THE CONTRACT, so NOT BLOCKED — but it is the conjecture-crux leaf the next two
  build steps must NOT scope away from. (2026-06-23, opus docs-only design-pass; clause (i): every
  load-bearing claim re-derived from the LANDED `def`/`theorem` bodies — `case_III_arm_corner_assembly`
  `ForkedArm.lean:136`, `chainData_split_w6b_gates` `Realization.lean:771`,
  `exists_chainData_discriminator_pick` `Realization.lean:1173`, `chainData_split_realization`
  `Realization.lean:983`, the d=3 dispatch `case_III_candidate_dispatch` `Realization.lean:268–599`,
  the `hcand` contract `Arms.lean:853–863`, the cert `case_III_rank_certification_chain`
  `Candidate.lean:2039`, the corner `hLI` `notMem_span_mkQ_pmR_row_of_gate` `Candidate.lean:1849`,
  the `±r` sourcing `hingeRow_mem_caseIIICandidate_rigidityRows_reproduced` `Candidate.lean:1975` +
  `reproducedSlot_pmR_acolumn_eq` `Candidate.lean:2003`, and `interior_group_acolumn_eq_neg_baseRedundancy`
  `Relabel/ChainColumn.lean:546` — AND KT §6.4.2 eqs. (6.64)–(6.67) pp. 697–698 read directly from
  the PDF. Resolves the recon's questions A/B/C + the internal (4.10)-vs-(4.11) inconsistency.)*

  **THE INTERNAL INCONSISTENCY THIS PASS RESOLVES.** (4.10)'s LEAF-3 sketch (signature at ~2078–2084)
  returns the interior `hρe₀` as a LEAF-3 conjunct rated "moderate"; (4.11)'s resolution (~2237)
  defers "the eq-6.66 `±r`-shared-across-all-interiors step" to LEAF-4/CHAIN bookkeeping. **(4.11) is
  right and (4.10)'s LEAF-3 sketch was wrong** about where (and how) the interior `hρe₀` is produced —
  the corrected boundary is pinned below.

  **(B) `hgate` IS LANDED, lands at the matched candidate directly (no transport needed for the gate
  itself).** `exists_chainData_discriminator_pick` (`Realization.lean:1173`, general-`k`) returns, for
  the matched panel `u`, the gate `ρ₀ (panelSupportExtensor (fun j => q (cand u, j)) n') ≠ 0` — at the
  candidate VERTEX `cand u` read off the BASE seed `q` (the selector `cand` picks the vertex; `q` is the
  ambient base normal family). With `cand u = vtx i.succ` via the LANDED `candidateVtx_succ_eq`, this
  is *verbatim* the consumer's `hgate : ρ₀ (panelSupportExtensor (q(a,·)) n') ≠ 0` at `a = vtx i.succ`
  (`ForkedArm.lean:155`). So **the discriminator's narrative "transporting `ρ` to that candidate's role
  is the deferred step 4" (Realization.lean:1147–1156) refers to the seed/`hρe₀` side, NOT the gate** —
  the gate is already at the candidate vertex's panel in base coordinates. **Caveat (the one transport
  the gate side DOES need): the consumer framework `F₀` uses the CANDIDATE seed `candidateSeed i q`
  (`Operations.lean:2733`, `= q ∘ shiftPerm i.castSucc` on the body coord), while the discriminator's
  gate is stated against the BASE seed `q`.** They are NOT defeq — `candidateSeed i q (a,·) = q(shiftPerm
  i.castSucc a, ·) ≠ q(a,·)` in general. So the dispatch either (i) feeds the discriminator the seed it
  will hand the consumer (run the discriminator at `candidateSeed`'s base-image vertices — the `cand`
  selector already lets you choose which vertices, and `candidateSeed i q (vtx i.succ,·)` vs.
  `q(shiftPerm(vtx i.succ),·)` is a `shiftPerm`-image bookkeeping the `candidateSeed_apply`/`shiftPerm_*`
  simp set handles), or (ii) transports the gate across the `shiftPerm` relabel. Either way the gate
  side is **`shiftPerm`-image bookkeeping on the LANDED selector/seed machinery, not a wall** — it is the
  (4.11) "functional-on-a-FIXED-extensor, member fixed, extensor relabelled" shape, the buildable side.
  This is real LEAF-3 plumbing, low-moderate risk.

  **(A) THE MATCHED-INTERIOR `hρe₀` IS A GENUINELY-NEW LEAF — option (b), NOT (a) (a transport) and NOT
  a per-candidate W6b firing. Here is the decisive source chain.**

  1. *The consumer's `hρe₀` slot (re-confirmed shape).* `case_III_arm_corner_assembly` (`ForkedArm.lean:156`)
     takes `hρe₀ : ρ₀ (panelSupportExtensor (q(a,·)) (q(b,·))) = 0` at the FIXED `ρ₀`, with `(a,b) =
     (vtx i.succ, vtx (i−1).castSucc)` the INTERIOR candidate's two chain neighbours. It is consumed ONLY
     by the `±r` row's membership `hingeRow_mem_caseIIICandidate_rigidityRows_reproduced` (`Candidate.lean:1975`,
     `hperp`, `t=0` reducing the reproduced-slot support to `panelSupportExtensor (q(a,·)) (q(b,·))`). It
     is the KT eq-(6.66) second-`Mᵢ`-row-is-`±r` fact: `ρ₀` (`= r`) annihilates the reproduced edge
     `(vᵢvᵢ₊₁)`'s support panel.

  2. *Why it is NOT a per-candidate W6b firing (the decisive satisfiability fact, the rows-392/394 trap
     applied here).* The natural-looking route — fire `chainData_split_w6b_gates` (`Realization.lean:771`)
     at the INTERIOR split `(v,a,b) = (vtx i.castSucc, vtx i.succ, vtx (i−1).castSucc)`, whose conclusion
     `:801` is `ρ (panelSupportExtensor (q(a,·)) (q(b,·))) = 0` at *exactly* the interior `(a,b)` —
     **is UNAVAILABLE to the dispatch.** `chainData_split_w6b_gates` requires `hsplitGP :
     HasGenericFullRankRealization k n (G.splitOff v a b e₀)` for THAT split (`:788`). But the dispatch's
     contract `hcand`/`hdispatch` (`Arms.lean:853–863`, frozen C.3) is handed an IH-generic realization
     of ONLY the **base `v₁`-split-off** `G.splitOff v a b e₀` for the spine-chosen base body `v`
     (`Arms.lean:910–913`) — there is NO interior-candidate split realization in scope, and producing one
     would need the IH at the interior split (which the dispatch does not call). This is *precisely* the
     §(o″) Route-A refutation (~931–937) re-confirmed: a per-candidate W6b produces a `Classical.choice`
     witness `ρᵢ` with NO functional relationship to the base `ρ₀`, whereas the cert needs ONE `ρ₀`
     (the gate, the membership, and the base block `W`'s relabel-image all read the same `F₀`). So
     **`chainData_split_realization` (`Realization.lean:983`, which DOES fire W6b at the interior split via
     its own `hsplitGP` hypothesis) is reusable ONLY at the base candidate `i=1` + the d=3 floor**
     (where the base split IS the only split, zero-regression) — NOT at general interior `i`. The (4.10)
     LEAF-3 sketch's "fire `chainData_split_w6b_gates` once off the shared base then expose `hρe₀` at the
     matched interior `i`" conflated two things: the ONE firing produces `hρe₀` at the BASE `(v₀v₂)`
     panel, never at the interior `(vᵢvᵢ₊₁)` panel.

  3. *Why it is NOT a transport of the base `hρe₀` (option (a) ruled out), and what landed object is the
     near-miss.* The base firing gives `ρ₀ (panelSupportExtensor (q(v₀,·)) (q(v₂,·))) = 0`. The interior
     `hρe₀` is at a DIFFERENT panel `(vᵢvᵢ₊₁)`. KT eq-(6.66) is the equation `∑ⱼ λ_(vᵢvᵢ₊₁)ⱼ rⱼ(q(vᵢvᵢ₊₁))
     = ±r` (p. 698, "we can easily show … in a manner similar to (6.44)", the degree-2 fact) — i.e. the
     interior reproduced-slot panel's redundancy combination EQUALS the base `±r`, so `r ⊥ C(Lᵢ)` ⟺ `r ⊥`
     the interior panel. This is NOT `simp`/`rw` of the base annihilation; it is the iterated eq-(6.44)
     degree-2 carry along the chain. The LANDED `interior_group_acolumn_eq_neg_baseRedundancy`
     (`Relabel/ChainColumn.lean:546`) is the CLOSEST landed object but is the **WRONG SHAPE**: it gives a
     COLUMN value `(∑ edge-i-group).comp (single (vtx i)) = −ρ₀` (a `Module.Dual ℝ (ScrewSpace k)`-valued
     screw-column read at body `vtx i`), the dual-functional/row-level `±r` carry the dead `hρGv` route's
     `hrCol` consumed — NOT a panel annihilation `ρ₀ (panelSupportExtensor …) = 0`. The §I.8.3-P2 finding
     (~978–981), reached independently on the dead `hρGv` route, says exactly this: "each surviving
     summand needs `ρ₀ ⊥ panel(qρ(vtx s, vtx s+1))` — NOT given by `hρe₀` … This is KT (6.62)+(6.66) …
     TRUE and KT-grounded but a genuinely-new Lean leaf." **That finding survives the route change
     verbatim: the option-(A) consumer needs the SAME genuinely-new fact, now as its `hρe₀` slot.**

  4. *Is it BLOCKED (a contract/motive/IH change) or buildable below the contract? — BUILDABLE BELOW THE
     CONTRACT, NOT BLOCKED.* The cert `case_III_rank_certification_chain` (`Candidate.lean:2039`) is
     `hρGv`-FREE and selector-agnostic; `notMem_span_mkQ_pmR_row_of_gate` (`Candidate.lean:1849`) shows the
     corner `hLI` needs ONLY `hgate` + `hW` (W vanishes at `single vᵢ`) + `hrCol = −ρ₀` — it does NOT
     require `ρ₀` to be the base redundancy by any TYPING constraint. So the interior `hρe₀` is not a
     frozen-interface field and forces NO motive/IH/C.0–C.6 change (contrast (4.11)'s `d_eq`, which WAS a
     contract field). It is a NEW LEMMA over the chain machinery, KT-grounded, whose ingredients exist
     (the iterated eq-6.44 degree-2 carry: `candidateRow_ac_eq_neg` in
     `Claim612.lean` is the abstract `±r` vector identity; the `interior_group_eq_baseRedundancy`/
     `interior_group_acolumn_*` chain-induction subtree in `Relabel/ChainColumn.lean` carries the
     constant-along-the-chain value). **The genuinely-new content is the bridge from those `hingeRow`-level
     / column-level facts to the `ρ₀ (panelSupportExtensor (q(vtx i.succ,·)) (q(vtx (i−1).castSucc,·))) = 0`
     panel-annihilation shape** — the "read the `±r` carry as a panel-meet perp" step the §I.8.22-(3)
     finding (~1345–1356) named as cost-unknown for the `hρGv` route and which is NOW the live leaf for
     option (A) (where it is the ONLY remaining `±r` obligation, the `hrCol`/`hρGv` ones being discharged
     by the genuine reproduced-slot decoupling, (4.9)).

     Named signature (a producer the dispatch/LEAF-4 consumes; the SHARED base `ρ₀`, the interior index
     `i`):
     ```
     theorem ChainData.baseRedundancy_perp_interior_reproduced_panel
         (cd : G.ChainData n) (i : Fin cd.d) (hi : 1 < (i:ℕ))   -- interior, i ≥ 2 (the ±r-carry range)
         {ρ₀ : Module.Dual ℝ (ScrewSpace k)} {q : α × Fin (k+2) → ℝ}
         (hbase : ρ₀ (panelSupportExtensor (q(cd.vtx 2,·)) (q(cd.vtx 0,·))) = 0)  -- the base (v₀v₂)
           -- annihilation in `chainData_split_w6b_gates`/`chainData_bottom_relabel`'s emit order
           -- `(vtx 2, vtx 0)`; the `(a,b)`-vs-`(b,a)` order is `panelSupportExtensor_swap`/`map_neg`-free
           -- for `= 0`
         (… the eq-6.52 λ-grouped (ab)-edge witness ρ₀ = Σⱼ λ • rab j, from chainData_split_w6b_gates
            at the BASE split, + the degree-2 closures cd.deg_two at vtx i …) :
         ρ₀ (panelSupportExtensor (q(cd.vtx i.succ,·)) (q(cd.vtx ⟨i-1⟩.castSucc,·))) = 0
     ```
     Ingredients (all KT-faithful, all on the chain machinery, NO `hρGv`, NO relabel-IMAGE/member-mapping
     wall): the base `ρ₀ = Σⱼ λ_(v₀v₂)ⱼ rⱼ(q(v₀v₂))` witness (the eq-6.52 grouping, an output of
     `chainData_split_w6b_gates` at the base split, `Realization.lean:813–815`); the iterated degree-2
     eq-6.44 carry `candidateRow_ac_eq_neg` (`Claim612.lean:1194`, the d=3 abstract identity); the chain-induction value subtree
     (`interior_group_eq_baseRedundancy` family, `Relabel/ChainColumn.lean`). **This is the conjecture's
     redundancy-carry seam at the panel-annihilation level — the project's single most-reverted lemma
     family's heir.** It is the leaf the prior two opus build dispatches scoped AWAY from by shrinking to
     `candidateVtx`/`candidateVtx_succ_eq` (the selector + the `u↔i` match), which are real but are the
     INDEX plumbing, not this annihilation.

  **(C) THE CORRECTED LEAF-3-vs-LEAF-4 BOUNDARY.** LEAF-3 does NOT produce the interior `hρe₀`. LEAF-3
  produces `(matched i, ρ₀, hgate-at-candidate, n', and the base-split W6b ρ₀/w/hw/hwmem bundle)` — i.e.
  it fires `chainData_split_w6b_gates` + the discriminator at the **BASE split** ONCE, gets the shared
  `ρ₀` (with the base `(v₀v₂)` annihilation), fires the discriminator over `cand = candidateVtx ∘ Fin.cast
  d_eq_kAdd.symm` to get the matched panel `u`/candidate `i`/`hgate`/`n'`, and threads the W6b base bottom
  family for LEAF-4's base block `W`. The interior `hρe₀` is produced **in LEAF-4** (or as the standalone
  leaf above, called from LEAF-4) via `baseRedundancy_perp_interior_reproduced_panel`, fed the base `ρ₀`
  bundle from LEAF-3. Corrected LEAF-3 producer signature (replacing the (4.10) ~2078–2084 sketch — drop
  the interior-`hρe₀` conjunct, keep the base bundle):
  ```
  theorem ChainData.exists_shared_redundancy_and_matched_candidate (cd : G.ChainData n) … :
      ∃ (q : …) (ends : …) (ρ₀ : Module.Dual ℝ (ScrewSpace k)) (i : Fin cd.d) (hi : 1 < (i:ℕ)) (n' : …),
        ρ₀ ≠ 0 ∧
        ρ₀ (panelSupportExtensor (q(cd.vtx 0,·)) (q(cd.vtx 2,·))) = 0 ∧                      -- BASE hρe₀
        ρ₀ (panelSupportExtensor (candidateSeed-image of cd.vtx i.succ) n') ≠ 0 ∧            -- hgate
        (the W6b ρ₀/w/hw/hwmem base bundle for LEAF-4's W) ∧
        (the eq-6.52 λ-grouped witness ρ₀ = Σ λ • rab, feeding the (4.12) interior-hρe₀ leaf)
  ```
  Then LEAF-4, given the matched `i` + this bundle, calls `baseRedundancy_perp_interior_reproduced_panel`
  to GET `hρe₀` at the interior `(vtx i.succ, vtx (i−1).castSucc)`, builds the base block `W` from the
  bottom family via `chainData_bottom_relabel` + LEAF-2, and `exact case_III_arm_corner_assembly … hgate
  hρe₀ hWS hWcard hW hdef`. (The base `i=1` candidate + the d=3 floor route to `chainData_split_realization`,
  zero-regression, where the interior `hρe₀` leaf is NOT needed — the base split IS the split.)

  **VERDICT (clause (ii) honesty).** NOT BLOCKED: no contract/motive/IH change (the cert is `hρGv`-free
  and `ρ₀`-agnostic; the interior `hρe₀` is a leaf below the frozen interface). The route is the
  genuinely-new leaf `baseRedundancy_perp_interior_reproduced_panel` (named, signature + ingredients
  pinned, KT eq-6.66-grounded). Clause (iii): the leaf's satisfiability is traced to ground — its
  hypotheses (base `ρ₀`/`λ`-witness + degree-2 closures) ARE produced by `chainData_split_w6b_gates` at
  the base split (the dispatch's available realization), so unlike the rows-392/394 trap its premises are
  dischargeable for the real consumer object; the WRONG route (per-candidate W6b at the interior) is
  ruled out by the unavailable interior `hsplitGP`. **Anti-scope-to-fit gate: a build that lands LEAF-3
  (the base bundle + `hgate` + the matched `i`) but defers the interior-`hρe₀` leaf has peeled the index
  plumbing and left the conjecture-crux undone — the interior `hρe₀` leaf is THE hard core, on par with
  LEAF-4's `hS` disjunction (it may BE the bulk of LEAF-4).** No Lean landed; tree byte-clean.

  **COORDINATOR ROUTE-VERIFICATION FLAG (2026-06-23, added after the recon).** The recon's INGREDIENT pin
  for this leaf originally cited `redundancy_panel_carry` as a LANDED chain-carry — it is NOT: it was landed
  (row 268) then DELETED as an ORPHAN (row 271, `hcol`/`hrest` unsuppliable at the chain step; the
  §(o‴)-rejected per-body block carry, the 4×-mis-pin trap). Corrected above to the genuinely-landed
  `candidateRow_ac_eq_neg` (d=3 abstract identity) + `interior_group_eq_baseRedundancy` (the chain-carry
  that REPLACED the orphan). **The structural verdict (interior-`hρe₀` genuinely-new, no contract change,
  LEAF-4, `hgate`-direct, LEAF-3 produces the base bundle) is coordinator-source-verified and stands — but
  the leaf's INTERNAL ROUTE (how `interior_group_eq_baseRedundancy` + the base witness bridge to the
  `panelSupportExtensor`-annihilation shape for option (A), without re-treading the killed degree-2-carry
  route) is NOT yet independently verified.** Given this seam's history (4× mis-pin + an orphan + §(o‴)
  rejections), the interior-`hρe₀` leaf should get a DEDICATED route recon (likely a diverse-lens pair) at
  the LEAF-4 boundary, BEFORE a build burns on it — diff the route against the §(o‴)/row-271 orphan verdict.
  This does NOT block the next commit: the LEAF-3 producer (base bundle + matched `i` + `hgate`) does not
  touch the interior-`hρe₀` route.

  *(4.13) THE LEAF-4 ROUTE RECON FIRED — DIVERSE-LENS PAIR (read-only, opus×opus, OPUS-ONLY, 2026-06-24)
  RE-ROUTED the interior-`hρe₀` leaf: §(4.12)'s structural verdict STANDS, but its INTERNAL route pin
  (`interior_group_eq_baseRedundancy`) is WRONG-SHAPE; the corrected live core is
  `candidate_perp_two_incident_panels`, fed the eq-6.52 ALL-edge redundancy (a below-contract LEAF-3
  widening). NOT a wall / NOT a killed-route re-tread — buildable, but the conjecture crux.*

  **What the pair found (both members + coordinator source-verification of the pivotal lemma bodies).**
  - **`interior_group_eq_baseRedundancy` / `_acolumn_eq_neg_baseRedundancy` (`Relabel/ChainColumn.lean:465/546`)
    are WRONG-SHAPE for this leaf** — they conclude a *column value* (`(edge-group).comp (single …) = −ρ₀`,
    `Module.Dual`-valued, the dead `hρGv` `hrCol` shape), NOT the scalar *panel annihilation*
    `ρ₀(panelSupportExtensor …) = 0` the consumer's `hρe₀` slot needs. Both members converged on this; it is
    the §(4.12) ingredient pin's error (beyond the deleted-orphan citation already corrected). Do NOT route
    the leaf through the `interior_group_*` column subtree.
  - **The corrected live core is `BodyHingeFramework.candidate_perp_two_incident_panels` /
    `_supportExtensors` (`Relabel/Chain.lean:918/950`, axiom-clean, the eq-6.44 two-edge perp carry, built
    as the `hρGv` P2 A-2 de-risk).** Coordinator-source-confirmed: at a **degree-2 body** `a` it proves the
    candidate vector `r̂ := ∑ⱼ λ_(ab)ⱼ rab j` annihilates **both incident panels** `supportExtensor e_c`
    (`= ab`) and `supportExtensor e_d` (`= ac`) — directly at the panel-annihilation level (the
    `mem_hingeRowBlock_iff` bridge, `Claim612.lean:823`, IS the `ρ₀ ⊥ panel ⟺ ρ₀ ∈ hingeRowBlock`
    correspondence; the §(4.12) "column→panel bridge is genuinely-new" worry dissolves — the live core is
    already at the annihilation level). It is SOUND (KT eq-6.66) and runs at the BASE, NOT the killed
    per-body `hρGv` route (member B could not refute; the killed route's cut-successor-edge failure mode
    does not recur).
  - **THE NEW REQUIREMENT (source-confirmed by reading `candidate_perp_two_incident_panels`'s hyps).** Its
    `hcol` is the **FULL redundancy combination's** column-vanishing at body `a`:
    `((∑ λ_ab • hingeRow a b (rab j)) + (∑ λ_ac • hingeRow a c (rac j)) + grest).comp (single a) = 0` — the
    eq-6.43/6.52 ALL-edge data (with `grest` the rest beyond the `ab`/`ac` blocks), plus per-edge
    `hrab`/`hrac` block memberships at BOTH incident edges. **LEAF-3 / `chainData_split_w6b_gates` currently
    emits only the `(ab)`-block λ-witness `ρ₀ = ∑ λ_ab • rab` — NOT the full eq-6.52 decomposition.** So the
    leaf needs the W6b/LEAF-3 output bundle **WIDENED** to emit the all-edge eq-6.52 redundancy (member A:
    the W6b producer computes a `Gv`-edge-grouped form internally, `Candidate.lean:439–445` — extract it, do
    NOT invent it at LEAF-4). This is a **below-contract internal-API widening** (no motive/IH/C.0–C.6
    change — both members confirm the cert is `hρGv`-free + `ρ₀`-agnostic).
  - **THE REMAINING BUILD-TIME DE-RISK (members split here — settle at the build).** The core gives perp to
    the panels *through* the degree-2 split body `vᵢ` (`(vᵢ,vᵢ₊₁)`, `(vᵢ,vᵢ₋₁)`); the consumer's `hρe₀` is
    at the **reproduced-slot / neighbour-neighbour "shortcut" panel** `(vtx i.succ, vtx (i−1).castSucc)`.
    Member A: the seed-relabel correspondence `panelCorrespondence_supportExtensor` (`Relabel/Arm.lean:834`,
    edge `s` ↔ base `shiftEdgePerm i (edge s)`) + `caseIIICandidate_supportExtensor_reproduced`
    (`Candidate.lean:971`) transport the incident-panel perp to the reproduced slot (KT eq-6.56). Member B:
    the core reaches the incident panels, not obviously the shortcut panel — confirm the transport composes.
    Coordinator: `panelCorrespondence_supportExtensor` is an EDGE-level transport (verified); the
    reproduced-slot panel identity under `candidateSeed` is the precise claim to nail at the build (read
    `caseIIICandidate_supportExtensor_reproduced`'s body + KT eq-6.56).

  **REVISED LEAF-4 BUILD ORDER (replacing the §(4.12)/(4.10) LEAF-4 sketch's `interior_group_*` route).**
  (i) **Widen LEAF-3 / `chainData_split_w6b_gates`** (or a sibling extractor) to emit the eq-6.52 ALL-edge
  redundancy data (`grest` + per-edge `λ`/`r` witnesses + the full-combination column-vanishing `hcol`) —
  the data `candidate_perp_two_incident_panels` consumes. (ii) **Build the interior-`hρe₀` leaf** via
  `candidate_perp_two_incident_supportExtensors` at the degree-2 split body + the
  `panelCorrespondence_supportExtensor` / `caseIIICandidate_supportExtensor_reproduced` transport to the
  reproduced-slot panel. (iii) the base block `W` + `exact case_III_arm_corner_assembly` (the §(4.12) (ii)
  half, unchanged). The seam stays the conjecture crux — a build that closes (i)+(ii) should be rated by the
  eq-6.52 widening + the panel-match transport, not the `W`-block plumbing.

  *(4.14) THE LEAF-4 DECOMPOSITION + SETTLE PASS (docs-only, source-verified against the LANDED bodies,
  2026-06-24). NET: sub-step (1) the eq-6.52 REGROUPING is SETTLED-SATISFIABLE with an exact data flow;
  sub-step (2) the REPRODUCED-SLOT TRANSPORT is **FLAGGED — the §(4.13) route as pinned does NOT reach the
  consumer's actual `hρe₀` panel** (a clause-(ii) flag, not a confident re-pin: the §(4.13) verdict "SOUND, runs
  at the base, buildable" stands at the KT-math level, but its Lean route via `candidate_perp_two_incident` +
  `panelCorrespondence` lands on the WRONG panel). The leaf is below the contract either way; the open decision
  is which of two corrected routes carries the shortcut-panel annihilation. This pass pins the buildable parts
  and names the single remaining genuinely-new step.)*

  **VERIFIED LOAD-BEARING FACTS (clause (i), each read off the LANDED `def`/`theorem` body, not prior prose).**
  - **The consumer's `hρe₀` is the SHORTCUT `(a,b)`-panel annihilation, NOT an incident `v`-panel.**
    `case_III_arm_corner_assembly` (`Relabel/ForkedArm.lean:136`, LANDED) takes
    `hρe₀ : ρ₀ (panelSupportExtensor (q(a,·)) (q(b,·))) = 0` and uses it at exactly one place
    (`ForkedArm.lean:200–202`): the reproduced-slot membership
    `hingeRow_mem_caseIIICandidate_rigidityRows_reproduced` (`Candidate.lean:1975`), whose `hperp` slot is
    `ρ₀ (panelSupportExtensor (n_u + t•n') n_r) = 0`, instantiated at `t=0`, `n_u=q(a,·)`, `n_r=q(b,·)`
    (`zero_smul, add_zero`). At the interior dispatch split (`Operations.lean:1313` `deg_two` +
    `:1340–1362` accessors) the roles are `v = vtx i.castSucc` (the degree-2 split body, REMOVED), `a = vtx
    i.succ`, `b = vtx (i−1).castSucc` — the **two NEIGHBOURS of `v`**. So `hρe₀` is `ρ₀ ⊥` the panel-meet of
    the neighbour-neighbour line `(a,b)`, in the SHARED base seed `q` (NOT a `qρ`-relabel). Confirmed: three
    distinct lines pass through `{v,a,b}` — `(v,a)`, `(v,b)`, `(a,b)` — and the consumer needs the third.
  - **`candidate_perp_two_incident_supportExtensors` (`Relabel/Chain.lean:950`, LANDED) reaches the two
    INCIDENT panels through the degree-2 body, NOT the shortcut.** Its conclusion is `(∑ λab • rab) ⊥
    F.supportExtensor e_c ∧ ⊥ F.supportExtensor e_d` where (its hyps `hrab`/`hrac`) `e_c`/`e_d` are the body's
    two incident edges. With the degree-2 body `= v`, those are `(v,a)` and `(v,b)`. Perp-to-`(v,a)` ∧
    perp-to-`(v,b)` does **not** imply perp-to-`(a,b)` without a Grassmann–Cayley collinearity step.
  - **`panelCorrespondence_supportExtensor` (`Arm.lean:923`, LANDED) is a GENUINE-CHAIN-EDGE transport, not a
    shortcut-edge one.** It equates the candidate-`i` framework's `supportExtensor (edge s)` to the base
    framework's `supportExtensor (shiftEdgePerm i (edge s))` for a surviving chain edge `s+1 < i`. The shortcut
    `(a,b) = (vtx i.succ, vtx (i−1).castSucc)` is the candidate's REPRODUCED FRESH slot `e_b` — it is **not** a
    chain `edge s` of `G − vtx i`, so this lemma does not range over it. (Its `i = 3` de-risk
    `i3_panelCorrespondence_supportExtensor_deRisk` confirms the same: both conjuncts are at `edge 0`/`edge 1`,
    genuine chain edges.) So §(4.13)'s "transport the incident-panel perp to the reproduced slot via
    `panelCorrespondence` + `caseIIICandidate_supportExtensor_reproduced`" does not type-check at the panel the
    consumer needs.
  - **`caseIIICandidate_supportExtensor_reproduced` (`Candidate.lean:971`, LANDED) is a `Function.update`
    unfold, not a meet identity.** It states `(caseIIICandidate … e_c e_r n_u n' n_r t).supportExtensor e_r =
    panelSupportExtensor (n_u + t•n') n_r` — i.e. it *names* the reproduced slot's overridden support as the
    `(a,b)`-line at `t=0`. It does NOT relate that panel to the incident panels; it is the slot-definition, the
    very thing telling us the target panel is the shortcut `(a,b)` line.
  - **The d=3 M₃ floor does NOT exercise this carry — it gets `hρe₀` for free.** In
    `case_III_arm_realization_M3` (`Relabel/Arm.lean:54`) the consumer's `hρe₀ : ρ ⊥ panelSupportExtensor
    (q(a,·)) (q(b,·))` is an *input hypothesis*, fed straight from the BASE W6b annihilation
    (`chainData_split_w6b_gates:801`) because at d=3 the M₃ split body's neighbours ARE the base split's
    `(a,b)`. The separate `hρ_ac` (`Arm.lean:121`, perp to a THIRD panel `C(q(ac))`) is derived by the
    **ONE-edge column projection** `acolumn_mem_hingeRowBlock_of_span_rigidityRows` (`Chain.lean`) +
    `hingeRow_comp_single_tail`, and feeds the CANDIDATE's own `hρe₀` slot inside `case_III_arm_realization`
    (after the `(a v)` relabel) — NOT the M₃ consumer's `hρe₀`. So there is **no landed precedent** for the
    general-`d` interior carry of `ρ₀` to a neighbour-neighbour panel ≠ the base one.

  **SUB-STEP (1) — THE eq-6.52 REGROUPING: SETTLED-SATISFIABLE (clause (iii) index check passes).** The
  consumer `candidate_perp_two_incident_supportExtensors` consumes a TWO-GROUP + remainder bundle
  (`lamAB`/`rab ∈ block e_c`, `lamAC`/`rac ∈ block e_d`, `grest`, `hcol` the full-combination `v`-column
  vanishing, `hrest`). The LANDED widening (`chainData_split_w6b_gates`, the `hedgeGv` conjunct
  `:825–831`, re-exposed from `Candidate.lean:439–445`) supplies the FLAT all-edge form
  `hingeRow a b ρ = ∑_{j : Fin nGv} cGv j • hingeRow (uvGv j) (vvGv j) (rvGv j)` over **every `G − base-v`
  link**, each summand carrying its link (`hlinkGv`) + block row (`hrvGv`). **The flat-sum IS sufficient to
  reconstruct the two-group + remainder shape** at the interior degree-2 vertex `vᵢ = vtx i.castSucc` (which
  SURVIVES `G − base-v`, being a distinct vertex): partition `Fin nGv` by the degree-2 closure
  (`ChainData.deg_two`, `Operations.lean:1316`) — `{j | evGv j = edge i}` → the `e_c = (v,a)` group, `{j | evGv
  j = edge (i−1)}` → the `e_d = (v,b)` group, the rest → `grest`; `hrab`/`hrac` are the `hrvGv` memberships
  reindexed onto the two groups; `hcol` is `freshEdge_interior_acolumn_sup` (LANDED, `Relabel/Arm.lean:556`,
  projecting the `vᵢ`-column of `hingeRow a b ρ ∈ span` into `block (edge i) ⊔ block (edge (i−1))`, strict
  boundary `s+2 < i` so both neighbours survive). The existing single-vertex precedent
  `freshEdge_surviving_row_mem_of_witness` (`Arm.lean:702`, LANDED, zero-blast) wires this exact bundle through
  `candidate_perp_two_incident_supportExtensors` already — confirming the data flow type-checks. **Index
  cardinalities line up** (clause (iii)): the flat index is `Fin nGv`; the two-group + remainder is a
  `Finset.filter` partition of `Finset.univ : Finset (Fin nGv)`, not a re-typed `ιab`/`ιac` (the consumer's
  `ιab`/`ιac` are `Type*` with `Fintype`, so the filtered subtypes `{j // evGv j = edge i}` instantiate them
  directly). Caveat (the load-bearing one): the widening fires at the **BASE** split (`hedgeGv` is over
  `G − base-v`), so the regrouping is at an interior vertex of the BASE candidate row — which is exactly what
  the dispatch needs, since the discriminator picks ONE candidate `i` against the BASE `ρ₀`.

  **SUB-STEP (2) — THE REPRODUCED-SLOT TRANSPORT: FLAGGED (the one genuinely-new step; the §(4.13) route is
  wrong-panel).** What sub-step (1) delivers is `ρ₀ ⊥ supportExtensor (v,a)` AND `ρ₀ ⊥ supportExtensor (v,b)`
  (the two INCIDENT panels at the degree-2 split body `v`). What the consumer needs is `ρ₀ ⊥ panelSupportExtensor
  (q(a,·)) (q(b,·))` (the SHORTCUT `(a,b)` panel). **These are not the same panel, and neither the §(4.13) route
  nor any LANDED leaf bridges them.** The KT-math IS sound (eq-6.66: the single redundancy `r` is shared `±r`
  across all `d` panels, and the `(a,b)` shortcut is the reproduced spliced edge — KT's whole device), but the
  bridge is the genuinely-new content the leaf must supply. **Two candidate routes, FLAG-not-FORCE — the build
  must pick one (both buildable in principle; neither is a wall; both below the contract):**

  - **Route A (preferred — the M₃ one-edge precedent, made degree-2-aware via the candidate framework).** Do
    NOT read the column at the REMOVED body `v` (degree-2 → SUP of two blocks → no single-panel pin, the
    `freshEdge_interior_acolumn_sup` SUP shape, which is exactly why §(4.13)'s incident route stalls). Instead
    read it at a NEIGHBOUR. KT's mechanism (M₃ precedent, `hρ_ac`): in the candidate framework where the
    shortcut edge `(a,b)` IS present as the reproduced slot, the body `b` (or `a`) has the shortcut as one of
    its incident edges; the column of the candidate row at that body lands (one-edge form) in the shortcut's
    block ⇒ `ρ₀ ⊥` the shortcut panel. The genuinely-new piece: showing the shortcut edge is the relevant body's
    SOLE surviving edge in the right sub-framework (degree-1 there, as in M₃) — or, if it is degree-2 there too,
    the eq-6.44 `⊓`-form (`candidate_perp_two_incident_panels` gives `r̂ ∈ block e_c ⊓ block e_d`) pins it.
    This needs a new leaf `baseRedundancy_perp_interior_reproduced_panel` whose body reads the column at the
    neighbour, NOT at `v`. **OPEN: which body, and is it degree-1 there?** — answer at the build by reading the
    candidate framework's link set at `a`/`b`.
  - **Route B (the Grassmann–Cayley collinearity step — genuinely-new math).** Prove the meet identity: at the
    degree-2 vertex `v` with neighbours `a,b`, if `ρ₀ ⊥ panelSupportExtensor (q(v,·)) (q(a,·))` and `ρ₀ ⊥
    panelSupportExtensor (q(v,·)) (q(b,·))`, then `ρ₀ ⊥ panelSupportExtensor (q(a,·)) (q(b,·))`. This is FALSE
    in general (three independent lines) — it holds only because `ρ₀` is the SHARED redundancy `r` and the
    three panels meet KT eq-6.66's incidence (the `±r` carry is a *linear* relation among the three panel
    extensors, not a generic implication). Formalizing it would route through `Meet.lean`/`MeetHodge.lean`'s
    duality (the N3b / Claim-6.12 line-in-panel-union machinery) and is the harder route.

  **VERDICT + REVISED BUILD ORDER for LEAF-4.** (i′) widening ✓ LANDED. (i-col) `freshEdge_interior_acolumn_sup`
  ✓ LANDED (it is the SUP-shape `hcol` input for sub-step (1), NOT a single-panel pin — keep it). (i-leaf) the
  interior-`hρe₀` leaf `baseRedundancy_perp_interior_reproduced_panel`: build via **Route A** (read the
  candidate row's column at a neighbour body, one-edge/`⊓`-form, to land in the shortcut block ⇒ shortcut-panel
  perp), falling back to Route B only if the neighbour body is degree-2 in every available sub-framework. (ii)
  the base block `W` + `exact case_III_arm_corner_assembly` — unchanged from §(4.13). **Do NOT** pin the leaf to
  `candidate_perp_two_incident` alone (it stops at the incident panels), do NOT route the shortcut through
  `panelCorrespondence_supportExtensor` (chain edges only), and do NOT revive the `interior_group_*` column
  subtree (column value, §(4.13)). The seam remains THE conjecture crux; rate a build by the
  incident-panel→shortcut-panel bridge (Route A's neighbour-column lemma), not the regrouping (settled) or the
  `W`-plumbing.

  **Why this is a flag, not a re-pin (clause (ii) honesty).** The §(4.12) pin was wrong-shape (column value);
  §(4.13) corrected the level (annihilation) but landed on the wrong PANEL (incident, not shortcut). A third
  confident single-pass pin here would repeat the ~50%-wrong history of this zone. The buildable facts are
  pinned (sub-step 1 + the `W`-block); the one undischarged genuinely-new step (incident→shortcut) is named with
  two concrete routes and the satisfiability check that decides between them at the build (the neighbour body's
  degree in the candidate framework). No motive/IH/contract change either way (the cert is `hρGv`-free +
  `ρ₀`-agnostic; this is machinery below the contract, §I.8.21).

  *(4.15) THE LEAF-4 INTERIOR-hρe₀ BRIDGE — DIVERSE-LENS RECON PAIR, CONVERGED (read-only, opus×opus,
  OPUS-ONLY, 2026-06-24; coordinator-adjudicated; SUPERSEDES §(4.14)'s Route A).* The §(4.14) flag named route A
  (degree-1 neighbour-column) vs route B (`Meet.lean`) for the genuinely-new incident→shortcut step, deferring the
  choice to a build-time discriminator (the neighbour body's degree in the candidate framework). The 2-leaf
  trigger fired (the i′ widening + the column-sup brick fed the not-yet-built crux core) → a diverse-lens recon
  PAIR settled the discriminator BEFORE a build. The pair CONVERGED.

  **KILLED — Route A as pinned (degree-1 neighbour-column) fails for general interior `i ≥ 2`.** Both members
  source-traced the discriminator: the neighbour `b = vtx (i−1).castSucc` is ITSELF an interior chain vertex
  (`0 < i−1` for `i ≥ 2`), hence **degree-2 in `G`** by `ChainData.deg_two` (genuine incident edges `edge (i−2)`
  and `e_b = edge (i−1)`). `caseIIICandidate.graph = G` (`rfl`), so reading `b`'s column in the consumer's
  framework `F₀` lands in the two-block SUP `block (edge (i−2)) ⊔ block e_b`, NEVER isolating the shortcut block.
  The shortcut `(a,b)` is **not a graph edge at all** — it is `e_b`'s OVERRIDDEN support in `F₀`
  (`caseIIICandidate_supportExtensor_reproduced` at `t=0` = `panelSupportExtensor (q(a,·)) (q(b,·))`), so no
  `G`-column-projection can land in it. `deg_two` constrains only split bodies `vtx j.castSucc`, never the
  neighbours — so the discriminator is degree-2 generically and Route A's degree-1 premise is FALSE. (M₃'s
  `hρ_ac` precedent is degree-1 only because it derives FROM `hρGv` at the base `v₁`-split, where the removed
  apex shears off the predecessor edge — `hρGv`-based, the exact slot (A) eliminated, so NOT the general model.)

  **CORRECTED ROUTE (converged) — the iterated degree-2 panel-perp carry (KT eq-6.66; the §I.8.3-P2 heir).** The
  one genuinely-new sub-lemma is `ChainData.baseRedundancy_perp_chain_edge`: carry `ρ₀`'s panel-perp from the
  BASE annihilation (LEAF-3 `chainData_split_w6b_gates`'s `(ab)` perp at the base spliced panel) ALONG the chain
  to the interior off-slot chain edge `(vtx (i−2), vtx (i−1))`, by induction on `s` (depth `O(i)`), each step via
  `candidate_perp_two_incident_supportExtensors` (`Chain.lean:950`, the eq-6.44 two-edge perp carry, `hρGv`-free)
  with the per-step `hcol` regrouped from the LEAF-4 widening's flat edge-sum at each interior vertex via the
  just-landed `freshEdge_interior_acolumn_sup` (the two-block SUP IS the right per-step `hcol` shape — the brick
  is ON-ROUTE, keep it). **The FINAL step is Lean-checked** (member A, `lean_multi_attempt` → no goals): apply
  `candidate_perp_two_incident_supportExtensors` at body `b` in `F₀` — `b`'s two incident edges are `e_b` (support
  overridden → the shortcut) and `edge (i−2)` (off-slot, genuine chain panel); given `ρ₀ ⊥` the off-slot
  predecessor chain panel (from the carry) + the `rab`-decomposition + `hcol`/`hrest` at `b`, the lemma transfers
  the perp to `e_b`'s overridden support = the shortcut = the consumer's `hρe₀`. So the leaf = the carry + this
  final application; NO column-projection at a degree-1 neighbour is needed.

  **Route B (Grassmann–Cayley meet via `Meet.lean`) = FALLBACK** only if a per-step `hcol` proves unsatisfiable
  (member B's adversarial hedge; not expected — the per-step `hcol` is the landed `freshEdge_interior_acolumn_sup`
  SUP shape). Below the contract either way (cert `hρGv`-free + `ρ₀`-agnostic; no motive/IH/C.0–C.6 change). d=3
  floor needs NONE of this (matched `i` = base split, base `(a,b)` = consumer `(a,b)`; the dispatch feeds the
  same `hρe₀` to all three arms).

  **Build order (NEXT):** build `ChainData.baseRedundancy_perp_chain_edge` (the conjecture-crux inductive
  sub-lemma — `ρ₀ ⊥ base panel` + the eq-6.52 `λ`-witness + `deg_two` ⟹ `ρ₀ ⊥` every chain edge `≤ i`, by
  induction on `s`); rate a build by IT, not the final application (Lean-checked) or the `W`-plumbing. Then
  assemble the interior-`hρe₀` leaf (carry at `s = i−2` + the final application at body `b`); then step (ii) the
  base block `W` (`chainData_bottom_relabel` + LEAF-2) + `exact case_III_arm_corner_assembly`. **Do NOT** pin to
  a degree-1 neighbour-column projection (shortcut isn't a graph edge), to `candidate_perp_two_incident` at `v`
  (reaches incident panels only), to `panelCorrespondence_supportExtensor` (chain-edge transport only), or to the
  M₃ `hρ_ac` (`hρGv`-based).

  *(4.16) THE CARRY DECOMPOSE+SETTLE PASS — VERDICT: the landed per-step `baseRedundancy_group_acolumn_perp`
  (b23e50e) is the WRONG SHAPE to drive the carry value-free, AND the ρ₀-tie via it FORCES the forbidden
  column-value read. The right per-step is the 23b `candidate_perp_two_incident_supportExtensors`, but it
  re-opens the 23b FLAG-AND-STOP (the per-vertex eq-6.52 witness has no landed producer). A clause-(ii) FLAG,
  not a confident re-pin (docs-only, opus, source-verified + Lean-checked against the LANDED bodies, 2026-06-24).*

  **What this pass verified (clause (i), against the actual `theorem` bodies + a Lean probe).** The carry's
  two open questions, settled by reading the landed signatures and a `lean_multi_attempt`/diagnostic probe at
  the candidate framework `Fva = ofNormals (G − vtx i) endsσρ qρ`:

  - **THE ρ₀-TIE (Q1) — the landed per-step does NOT tie to ρ₀ value-free.** `baseRedundancy_group_acolumn_perp`
    (`Relabel/ChainColumn.lean:429`, b23e50e) concludes a perp of the **GROUP COLUMN**
    `((∑_{evⱼ=edge i} cⱼ•hingeRow uvⱼ vvⱼ rvⱼ).comp (single vᵢ)) (Fva.supportExtensor (edge i)) = 0` — the object
    annihilating the panel is the `vᵢ`-column of the `edge i`-group (a `Dual ℝ (ScrewSpace k)`), **NOT** `ρ₀`.
    Lean-confirmed: feeding `hstep.1` where `ρ₀ (Fva.supportExtensor (edge i)) = 0` is expected gives a
    type-mismatch (the LHS functional is the group column, not `ρ₀`). The ONLY bridge `group column → ρ₀` in the
    project is `group column = −ρ₀` — i.e. the **forbidden value read** `interior_group_acolumn_eq_neg_baseRedundancy`
    (the `interior_group_*` subtree §(4.12)/(4.13) the cert was built to avoid). So `baseRedundancy_group_acolumn_perp`
    cannot deliver the carry's `ρ₀ ⊥ panel` without reviving the value read. **The landed b23e50e per-step is correct
    but OFF the carry's critical path** (the high-value (4.10) clause-(ii) outcome — it is a group-column annihilation,
    not the redundancy-carry step).

  - **THE VALUE-FREE TIE EXISTS — via a DIFFERENT, already-landed per-step.**
    `candidate_perp_two_incident_supportExtensors` (`Relabel/Chain.lean:950`, 23b) concludes
    `(∑ⱼ lamABⱼ•rabⱼ) (F.supportExtensor e_c) = 0`, which IS `ρ₀ ⊥ panel` after the eq-6.52 rewrite
    `ρ₀ = ∑ⱼ lamABⱼ•rabⱼ` — a **value-free** tie (`ρ₀` is the witness sum, NOT a column value). Lean-probe
    PROBE B compiled clean: `rwa [hρ] at (…).1`. So the §(4.15) route's per-step pin should be
    `candidate_perp_two_incident_supportExtensors`, **not** `baseRedundancy_group_acolumn_perp`.

  - **THE INDUCTION (Q2) — the value-free per-step re-opens the 23b FLAG-AND-STOP.**
    `candidate_perp_two_incident_supportExtensors` CONSUMES `hperp_ab : ∀ j, rab j (F.supportExtensor e_c) = 0`,
    `hperp_ac : ∀ j, rac j (F.supportExtensor e_d) = 0` (the **per-WITNESS-ROW** perps of the two incident-edge
    groups) plus the eq-6.43 column vanishing `hcol`/`hrest`. The carry's IH gives a **ρ₀-perp** (a SUM perp
    `ρ₀ ⊥ panel(prev)`), which does NOT yield the per-row `rab j`/`rac j` perps — and the W6b producer
    (`exists_candidateRow_bottomRows_of_rigidOn` / `chainData_split_w6b_gates`) guarantees the witness rows
    `rab j ∈ hingeRowBlock e₀` ONLY at the **base spliced panel** `e₀`, not the chain-edge panels. Supplying the
    per-vertex eq-6.52 witness `(lamAB, rab, lamAC, rac, grest)` AT EACH INTERIOR VERTEX is exactly **Route W**,
    which the 23b de-risk `i3_freshEdge_interior_acolumn_sup_deRisk` (`Relabel/Arm.lean:479–481`) already
    FLAGGED-AND-STOPPED as having **no landed producer** (the single-vertex consumers
    `freshEdge_surviving_row_mem_of_witness` + `candidate_perp_two_incident_*` STAND as Route W's building blocks,
    but the per-vertex witness producer does not exist).

  **The genuine open decision (FLAG, clause (ii)).** The §(4.15) carry needs ONE of:
  (A) the **value read** — discharge the per-edge `ρ₀ ⊥ panel(edge s)` from the candidate-framework edge-grouped
      base redundancy via the LANDED `chainData_freshEdge_perp_of_baseRedundancy` (`ChainColumn.lean:1076`,
      which uses `interior_group_acolumn_eq_neg_baseRedundancy` = the `interior_group_*` value read §(4.12)).
      This route IS landed and produces the per-edge ρ₀-perp the carry wants — but the cert/route was scoped
      `interior_group_*`-FREE, so reviving it for the redundancy-carry seam **reverses the §(4.12)–(4.13)
      scope-out decision** and needs coordinator/user adjudication (it does NOT touch the cert's `hρGv`-freedom;
      it is below the contract — but it is the exact subtree the last three reroutes ruled out); OR
  (B) a **genuinely-new per-vertex eq-6.52 witness producer** (Route W) — supply
      `(lamAB, rab, lamAC, rac, grest)` with the per-row perps at each interior vertex from the candidate
      rigidity-row span. This is the 23b FLAG-AND-STOP's unbuilt producer — a genuinely-new, non-trivial leaf
      (KT eq-6.66's per-vertex redundancy decomposition), the conjecture-crux content proper; OR
  (C) the **Meet.lean Grassmann–Cayley fallback** (§(4.15) Route B) — if a value-free per-step `hcol` route
      through the projective duality exists. Not yet scoped at the per-step level.

  **Recommendation (FLAG-DON'T-FORCE): route (A) is the shortest path and is LANDED, but it reverses a
  thrice-affirmed scope-out — surface it for adjudication before building.** The decision is: *is the
  redundancy-carry seam allowed to read the interior edge-group column as `−ρ₀`?* The §(4.12)/(4.13)/(4.15)
  reroutes all said NO for the cert + the column-projection bricks; but `chainData_freshEdge_perp_of_baseRedundancy`
  shows the value read is the only LANDED way to get the per-edge `ρ₀`-perp the carry's per-step needs (the
  value-free `candidate_perp_two_incident_supportExtensors` needs a witness with no producer = route (B)). The
  cert stays `hρGv`-free either way (no motive/IH/C.0–C.6 change); the value read is a property of the
  redundancy-carry leaf's INTERNALS, not the contract.

  **What this pass RULED OUT.** (1) Driving the carry from the landed b23e50e per-step value-free — Lean
  type-mismatch, the conclusion is a group-column perp. (2) Deriving the per-row witness perps `hperp_ab`/`hperp_ac`
  from the carry's ρ₀-perp IH — a sum vanishing on a panel does not make each `rab j` vanish on it; the witness
  rows are perp only to `e₀` (base), per the W6b producer. (3) The §(4.15) claim that the carry is "the
  conjecture-crux inductive sub-lemma, rate a build by IT" stands at the KT-math level, but its Lean realization
  is NOT "chain `baseRedundancy_group_acolumn_perp`" — that per-step is the wrong shape; the carry is route (A)'s
  value-read closure OR route (B)'s unbuilt witness producer.

  **Structural invariants traced (clause (iii)).** `vtx : Fin (cd.d+1) → α` (`v₀…v_d`),
  `edge : Fin cd.d → β`, `cd.d = n` (`d_eq`); `cd.deg_two` holds ONLY at interior `vtx i.castSucc` for `0 < i`
  (i.e. `v₁…v_{d−1}`); the endpoints `v₀`, `v_d` are not degree-2. The candidate `i : Fin cd.d` removes `vtx i`;
  surviving chain edges are those of index `< i` (both endpoints `< i`, so `≠ vtx i` by `vtx_inj`). The FINAL
  step's target panel is `e_b`'s OVERRIDDEN support `panelSupportExtensor (q(a,·)) (q(b,·))` (the shortcut, NOT a
  graph edge; `caseIIICandidate_supportExtensor_reproduced` at `t=0`), reached via the per-step at body `b`
  (incident edges `e_b` = shortcut + `edge (i−2)` = genuine off-slot). The d=3 floor (`i = 2` = base split)
  needs NONE of the carry — matched `i` = base, base `(a,b)` = consumer `(a,b)`, `hρe₀` = LEAF-3's base
  annihilation directly (zero-regression).

  **Build order (REVISED, pending the (A)-vs-(B) adjudication).** If (A): (i) wrap
  `chainData_freshEdge_perp_of_baseRedundancy` into the carry `baseRedundancy_perp_chain_edge` (it already
  produces the per-edge ρ₀-perp; the "carry" is then a thin assembly + the final step at body `b` via
  `candidate_perp_two_incident_supportExtensors` fed the chain-edge perps as `hperp`), (ii) the base block `W`
  + `exact case_III_arm_corner_assembly`. If (B): build the per-vertex witness producer first (the genuinely-new
  leaf), then the carry over it. **Do NOT** build the carry over `baseRedundancy_group_acolumn_perp` (wrong shape,
  Q1) regardless.

  *(4.17) THE `hWS` WRAP-EDGE-TAG MEMBERSHIP — VERDICT: BLOCKED AS SHAPED. The forked cert's `W = bare
  relabel-image span` cannot route the relabelled wrap-edge tag into the candidate span; re-shape `W` to the
  d=3 engine's column-op / off-`v`-restriction OPERATED frame (option A; user-adjudicated 2026-06-24,
  feasibility-pass-first). Compiler-checked SPIKE, read-only, opus / OPUS-ONLY, 2026-06-24, agentId
  `a6fb2b975b3b7ead2` (resumable). This is the SEPARATE `hWS` half of LEAF-4 step (ii) — the interior `hρe₀`
  half closed at §(4.16)→rows 426–428.*

  **Trigger.** The LEAF-4 (c) `hS` router `bottomRelabel_image_mem_span_caseIIICandidate` (2878600) LANDED
  gate-/axiom-clean, but the coordinator's shape check (satisfiability trace, the rows-392/394 corollary)
  found its REPRODUCED branch mis-targeted; a read-only spike kernel-confirmed it.

  **The contradiction (kernel-checked — a `False`-deriving `example` compiled).** `chainData_bottom_relabel`'s
  wrap-edge Or.inr tag is `hingeRow (vtx i.succ) (vtx (i−1).castSucc) ρ'` — endpoints `(a,b) = (vtx_{i+1},
  vtx_{i−1})`, which OMIT `vᵢ = vtx_i`. Routing it through `hingeRow_mem_caseIIICandidate_rigidityRows_reproduced`
  forces the row endpoints to be `e_b`'s genuine link, so the router carries `hG_eb_cand : G.IsLink e_b
  (vtx i.succ) (vtx (i−1).castSucc)`. That contradicts the consumer's REQUIRED `hG_eb : G.IsLink e_b v b`
  (`v = vtx i.castSucc`): same `e_b` + shared endpoint `vtx_{i−1}` ⟹ (`IsLink.right_unique` + `vtx_inj`)
  `vtx_i = vtx_{i+1}`, False. The leaf type-checks only because `hG_eb_cand` is a CARRIED hypothesis — it is
  unsatisfiable for the dispatch.

  **The only viable route (telescope) + its unprovable residual.** `hingeRow a b ρ' = hingeRow a v ρ' −
  hingeRow b v ρ'` (through `vᵢ = v`; `hingeRow_sub_hingeRow_eq`). The `b–v` summand LANDS (reproduced `e_b`
  at the GENUINE `(v,b)` link, perp `ρ' ⊥ panel(qρ a, qρ b)` supplied by the tag). The `a–v` summand lands
  via the fresh `e_a` slot ONLY GIVEN the extra perp `ρ' ⊥ panelSupportExtensor (qρ a) n'` — kernel-checked:
  the full membership compiles given BOTH perps, residual = exactly this one. It is NOT in dispatch data and
  is geometrically FALSE: the bottom-family `ρ'` only annihilates the `(ab)`-panel (`hingeRowBlock e₀`), while
  `n'` is the FREE transversal the discriminator gates `ρ` NON-perp to (`hgate`). Route (B)
  `candidate_perp_two_incident` is for the structured shared `ρ̂`, not the arbitrary per-member `ρ'`.

  **Root cause (the real finding — traced to landed decls).** The forked cert
  `case_III_rank_certification_chain` consumes `hWS : W ≤ span F₀.rigidityRows` as a bare relabel-image span —
  its carrier `exists_le_finrank_span_rigidityRows_eq_card_of_injective_map` (`Candidate.lean:1727`) demands
  every image (incl. the Or.inr tags) DIRECTLY in the candidate span. The d=3 engine
  `case_III_rank_certification` (`Candidate.lean:1614`) NEVER needs this: it certifies `W`'s rank in a
  column-op / off-`v`-restriction OPERATED frame (`case_III_full_family_restriction` +
  `hingeRow_comp_columnOp_comp_offProj` `Claim612.lean:881`), where the tag is only an IMAGE. The `W`-shape
  divergence (the §(4.10) LEAF-2 decision) is the bug; the LEAF-4(c) plan ("block-tag → reproduced-slot
  membership") is its source.

  **Decision (user-adjudicated 2026-06-24).** LEAF-4 step (ii) `hWS` is blocked as shaped. Fix = option (A):
  re-shape the chain cert's base block to the operated frame (carry `hingeRow v b ρ'` as the actual span
  member, eliminating the unprovable perp) — re-opens the LANDED cert + carrier + LEAF-2
  `span_relabelImage_le_and_finrank_and_acolumn_vanish`. Option (B) (a per-Or.inr-member perp on the W6b
  producer) is geometrically dead. **Path: an (A)-feasibility pass FIRST** — does the d=3 operated-frame
  `W`-certification COMPOSE with the forked `±r`-block cert? — before re-opening settled machinery.

  **Salvageability.** The router 2878600's GENUINE branch (off-slot survivors via
  `hingeRow_mem_caseIIICandidate_rigidityRows_of_ofNormals_link`) is sound + reusable. The REPRODUCED branch
  is dead — to be replaced when `hWS` is re-shaped (do not patch in place; no buildable leaf closes it with
  current data).

  **Clause (iii) invariants traced.** `vtx : Fin (cd.d+1) → α` injective; interior split `e_b = edge (i−1)`
  links `(v,b) = (vtx_i, vtx_{i−1})` (`isLink_pred_edge`); the wrap-edge tag's `(vtx_{i+1}, vtx_{i−1})` omit
  `vᵢ`. `caseIIICandidate.graph = G` (no graph splice). d=3 floor (`i=2`=base) needs none of this
  (zero-regression).

  *(4.18) THE OPTION-(A) FEASIBILITY PASS — VERDICT: INFEASIBLE. Re-shaping the forked chain cert's base
  block `W` to the d=3 operated frame does NOT exist as posed: the block-additivity `W` must satisfy
  `hWS` (⊆ candidate span) ∧ `hWcard` (full rank `D·(m_v−1)`) ∧ `hW` (off-`vᵢ`-vanishing) simultaneously,
  and the redundancy carry is inherently a row THROUGH `vᵢ`, so no such `W` exists. The `hρGv`
  member-mapping wall was RELOCATED to the interior-arm `W`-production, not escaped. Compiler-checked SPIKE,
  read-only, opus / OPUS-ONLY, 2026-06-24, agentId `a6adfeb0dff230bc1` (resumable). User-adjudicated
  2026-06-24 → investigate option (B′) next.*

  **The impossibility (kernel-checked).** The corner `hLI` mechanism `notMem_span_mkQ_pmR_row_of_gate`
  (`Candidate.lean:1849`, KT eq. 6.16 block-triangular split) FUNDAMENTALLY requires
  `hW : ∀ φ ∈ W, φ ∘ₗ single vᵢ = 0` — it precomposes with `single vᵢ`, the `W`-side dies (`hW`), and the
  `±r` row gives `−ρ₀ ≠ 0` (gate). But `hWcard` forces `W` to contain the redundancy member's direction (the
  relabelled bottom family is LI, the wrap-edge member among it), and that member's ONLY candidate-span
  representative is the operated transport `hingeRow vᵢ B ρ₀` — a row THROUGH `vᵢ`, whose `single vᵢ`-column
  is `±ρ₀ ≠ 0` (kernel-checked: any `W` containing it AND satisfying `hW` forces `ρ₀ = 0`, contradicting the
  gate `hgate`). The off-`vᵢ`-vanishing alternative (the bare wrap-tag, endpoints OMIT `vᵢ`) satisfies `hW`
  but is not a candidate row (breaks `hWS` — the §(4.17) block). So `hWS ∧ hWcard ∧ hW` are jointly
  unsatisfiable on the redundancy member.

  **Why the d=3 engine works without this (clause i, read end-to-end).** `case_III_rank_certification`
  (`Candidate.lean:1508`) builds ONE flat LI family `fam` over `(sn ⊕ Unit) ⊕ ιb` and bounds the candidate
  span via `finrank_span_eq_card` + `finrank_mono` — there is **no submodule `W`**. The base rows `wtil` are
  OPERATED transports: each `wtil j ∈ span F₀.rigidityRows`, and `((wtil j) ∘ Φ) ∘ Pv = w j` (`Φ = columnOp`,
  `Pv =` off-`v` projection); LI is established only in the operated `Φ∘Pv` frame (`case_III_full_family_
  restriction`). The redundancy enters as `wtil j = hingeRow v b ρ'` (through `v`, a genuine candidate
  `e_b`-row, `t=0`, no `hρGv`). The WALL is the `Unit` corner row `hingeRow v a ρ` collapse (eq. 6.27,
  `:1642–1647`): the `hingeRow a b ρ` summand needs `hρGv : hingeRow a b ρ ∈ span (ofNormals Gv …).rigidityRows`
  (`hFvle hρGv` at `:1646`) — the member-mapping wall. So the basis-free analogue of KT's "column-op THEN
  block-triangular" (6.61→6.65) is the FLAT OPERATED FAMILY, not a static submodule `W ≤ span F₀.rigidityRows`.

  **What survives (not the problem).** The corner cert — `hg`/`hLI`/`hrCol`, the `±r` reading via the genuine
  reproduced-`e_b` row (`hperp = hρe₀`, never `hρGv`) — is sound and `W`-INDEPENDENT. The block-additivity
  cert `case_III_rank_certification_chain` (`Candidate.lean:2039` → `finrank_add_card_le_of_linearIndependent_mkQ`)
  is correct; the obstruction is solely the joint existence of a `W` with `hWS ∧ hWcard ∧ hW`.

  **The two genuinely-new options (both below contract/motive — no C.0–C.6/IH change; d=3 zero-regression;
  NEITHER a re-shape of the three landed leaves cert/carrier/LEAF-2).**
  - **(A′)** re-derive the chain cert in the d=3 flat operated frame, producing the `hρGv` slot at the
    relabelled candidate base via a general-`d` analogue of the M₃ length-1 W9a move — the genuinely-new
    conjecture-crux rank-certification content KT's argument requires (the eq. 6.66 `±r` ℝ^D-vector identity,
    §I.8.24(2)(2b)(γ)); the LANDED crux `baseRedundancy_perp_interior_reproduced_panel` is plausibly a building
    block. This IS the wall, confronted generically.
  - **(B′) [CHOSEN to investigate next]** a column-op-aware block-rank lemma `finrank S ≥ finrank W + D` where
    `W` holds the OPERATED transports (through `vᵢ`) and the `hW`-analogue tests the OPERATED composite
    `(φ ∘ Φ ∘ Pv) ∘ single vᵢ = 0` (AFTER the column op, where `Pv` kills `single vᵢ`). Because the corner is
    the `±r` block (sources via `hρe₀`, no `hρGv`), B′ may combine option-(A)'s `±r` wall-escape WITH the d=3
    operated frame — potentially sidestepping BOTH the `hWS∧hW` impossibility and the wall. Genuinely-new
    abstract LA (block-rank relative to a column operation); needs its own feasibility check (the next spike).

  **Decision (user-adjudicated 2026-06-24).** (A) is infeasible. Investigate (B′) via a compiler-checked
  feasibility spike (does the operated-frame block-rank lemma compose with the `±r` corner?) before building;
  fall back to (A′) if B′ does not compose. The router 2878600 and LEAF-2/cert/carrier stay landed but their
  `hWS`/`hW`/`W`-block role is now under re-design.

  *(4.19) THE OPTION-(B′) FEASIBILITY PASS — VERDICT: INFEASIBLE. The operated-frame block-rank route does
  not separate the `±r` corner from the operated base block. With (A) AND (B′) refuted, the three feasibility
  reconnaissance passes CONVERGE: the `±r`-corner wall-escape — the central bet of the 23c (A) architecture —
  does NOT extend to the general-`d` RANK CERTIFICATION; the `hρGv` member-mapping wall is unavoidable.
  Compiler-checked SPIKE, read-only, opus / OPUS-ONLY, 2026-06-24, agentId `a895196401fd4cb15` (resumable).
  A USER-DECISION POINT: (A′) confront the wall generically, or a broader reconsideration.*

  **Why B′ fails (kernel-checked, PROBES 1–5).** The proposed `hW`-analogue tests the OPERATED composite
  `(φ∘Φ∘Pv)∘single vᵢ`. (A) `Pv ∘ single vᵢ = 0`, so the test is TRIVIAL for every row including the corner —
  the `single vᵢ` separation collapses. (B) The discriminator relocates to `single a` and SURVIVES for the
  corner: `Φ` moves col_v into col_a, so `hingeRow u v ρ₀` reads `−ρ₀ ≠ 0` at the operated `single a`. (C, the
  make-or-break) but the operated base is NOT controlled at `single a`: each transport satisfies
  `(wtil∘Φ)∘Pv = w`, so the operated base's `single a`-column = the BARE `w∘single a`, nonzero (an `a`-incident
  `G_v`-row reads `r'≠0`; the redundancy carry `hingeRow a b ρ'` reads `ρ'≠0`) — both collide with the
  corner's `−ρ₀` in the same column, so no block-triangular separation. (D) The d=3 separator
  `linearIndependent_sum_restriction_block` (`RigidityMatrix/Basic.lean:1189`) needs the top block
  pure-`v`-column (`htopvanish`), but the genuine `±r` corner `hingeRow u v ρ₀` reads `ρ₀(S u − S a) ≠ 0` at
  `S v = 0` (PROBE 5) — it is NOT pure-`v`, so it CANNOT join the d=3 top block. The d=3 separation is
  structurally tied to the COLLAPSED corner `hingeRow v a ρ` (pure-`v`), the one that needs `hρGv`. So
  `htopvanish` for the `±r` corner is REFUTED by a counterexample (not a sorry'able gap).

  **The convergence (the durable finding).** The `±r`-corner reformulation escapes `hρGv` at the ARM/corner
  level (the corner ROW's membership `hg` via `hρe₀` + its LI `hLI` — all sound, `W`-independent, LANDED). But
  it does NOT escape the wall in the general-`d` RANK CERTIFICATION: the genuine `±r` row (KT eq. 6.66) is
  geometrically a row THROUGH `vᵢ` that is not pure-`vᵢ`-column after the column op — incompatible with both
  the static-`W` block-additivity (A, §(4.18)) and the operated-frame separation (B′). The basis-free analogue
  of KT's "column-op THEN block-triangular" that DOES certify the rank is the d=3 FLAT OPERATED FAMILY with the
  COLLAPSED corner + `hρGv` (the wall). So the only remaining route is **(A′): re-derive the chain cert in the
  d=3 flat operated frame, producing `hρGv` generically via a general-`d` analogue of the M₃ length-1 W9a
  move** — the genuinely-new conjecture-crux content (the wall §I.8.18–20 called intrinsic to KT, proved for
  `d=3` only via W9a; the LANDED crux `baseRedundancy_perp_interior_reproduced_panel` may be a building block).

  **Caveat on (A′)'s own feasibility (FLAG).** (A′) requires producing the collapsed-corner `hρGv` at the
  interior candidate. The design's §(o″) Route-A characterized firing W6b (the base `hρGv`/realization
  producer) PER-INTERIOR-SPLIT as a dead end (the interior split's general-position precondition `hsplitGP` is
  unavailable). Whether the M₃ W9a `hρGv` proof GENERALIZES by a route that sidesteps per-interior W6b is OPEN
  — it may be tractable (the W9a move's structure, not a fresh W6b firing) or it may be blocked like §(o″), in
  which case 23c's whole approach needs reconsideration. **This is why (A′) warrants a tractability recon
  before a build commitment.**

  **Decision point (surfaced to the user 2026-06-24).** Both `±r`-corner wall-escape routes (A, B′) are
  refuted; (A′) confronts the wall and may itself be blocked. Options: (1) recon (A′)'s tractability (does the
  W9a `hρGv` proof generalize without per-interior W6b?); (2) build (A′) directly; (3) pause / broader
  reconsideration of the 23c approach. The corner cert + the LANDED leaves stay in tree; the `W`-block /
  rank-certification layer is the open re-design.

  *(4.20) THE OPTION-(A′) TRACTABILITY PASS — VERDICT: INFEASIBLE, it IS the member-mapping wall (§I.8.18–20),
  kernel-confirmed. With (A), (B′), AND (A′) all refuted, the general-`d` interior-`hρGv` route is exhausted —
  23c's rank-certification layer needs a FUNDAMENTAL RECONSIDERATION (the design's surfaced option (3)).
  Compiler-checked SPIKE, read-only, opus / OPUS-ONLY, 2026-06-24, agentId `a22d7811559060d3b` (resumable).*

  **The reduction (PROBE 1, kernel-clean) — the W9a generalization is LANDED; the wall is ONLY the `hφ` slot.**
  The interior `hρGv` is exactly the conclusion of the LANDED `chainData_relabel_arm_hρGv`
  (`Relabel/ChainColumn.lean:1390`). Instantiating it reduces the interior `hρGv` to a SINGLE residual = its
  `hφ` slot: `hingeRow (vtx 0)(vtx 2) ρ₀ ∈ span (ofNormals (G − vtx 1) endsσρ q).rigidityRows` — the base
  redundancy `hingeRow v₀v₂ ρ₀` held MEMBER-FIXED, at the base `G − v₁` framework but the RELABELLED selector
  `endsσρ`. Everything else (`hlink`/`hrv`/`hcomb`/`hdeg1`/`hρe₀` + the general-`d` W9a-fold transport
  `chainData_freshEdge_slot_mem` + `wstep_foldl_freshEdge_slot_mem`) is LANDED — the W9a *generalization* is
  NOT the obstruction.

  **Why `hφ` has no source (PROBES 2–3, kernel-clean) — the member-mapping wall.** `hφ` is a span MEMBERSHIP
  at the relabelled selector. The dispatch's base bundle fires W6b ONCE at the base `v₁`-split (its only
  `hsplitGP`, `Realization.lean:1300`) → the base `hρGv'` at the UN-relabelled selector. The only mechanism
  moving a membership into `span(endsσρ)` is the relabel-image transport `(funLeft (shiftPerm i.castSucc)⁻¹).
  dualMap` — and it is MEMBER-MOVING: PROBE 2 = it sends `hingeRow (vtx0)(vtx2) ρ₀ ↦ hingeRow (vtx0)(vtx1) ρ₀`
  (`σ⁻¹` fixes `vtx0` off-cycle, sends `vtx2 ↦ vtx1` interior) for `i ≥ 3`; PROBE 3 (False-witness) =
  `hingeRow (vtx0)(vtx1) ρ₀ = hingeRow (vtx0)(vtx2) ρ₀` forces `ρ₀ = 0` (read both at `single (vtx2)`),
  contradicting the gate. So the transported member is provably NOT the member-fixed `hφ`. This IS KT's (6.62)
  relabel correspondence mapping the FIXED dual functional — the §I.8.18–20 member-mapping wall, intrinsic
  (the four route families dead). At `d=3`/`i=2`, `shiftPerm 2 = (v₁v₂)` is a single swap and M₃ W9a closes —
  the masking degeneracy that made `d=3` look generalizable.

  **No framework-free escape (the decisive structural difference from the `hρe₀` crux).** The interior `hρe₀`
  dissolved because it is an ANNIHILATION `ρ₀(panel) = 0`, reading only the seed `q` (framework-free value-read;
  `baseRedundancy_perp_interior_reproduced_panel` LANDED). `hφ` is a span MEMBERSHIP in `rigidityRows` —
  intrinsically framework-dependent, with NO value-read form; pushing it per-summand still routes through the
  member-moving genuine-row transport. So the spike-and-land that beat the `hρe₀` mis-pins does NOT apply.

  **Bottom line.** The `±r`-corner reformulation genuinely escapes `hρGv` at the arm/corner level (`hg`/`hLI`
  via `hρe₀`, LANDED, sound) but CANNOT certify the general-`d` rank without the member-fixed base-redundancy
  membership `hφ`, which the cycle relabel provably moves. (A), (B′), (A′) are all refuted; the interior-`hρGv`
  route is exhausted. **23c needs a fundamental reconsideration — surfaced to the user 2026-06-24 (a phase
  STOP).** Candidate directions (the user's call, likely needing a fresh KT-§6.4.2 rank-argument recon): a
  rank-counting cert that never tracks an individual member-fixed row (KT's "whole-matrix bookkeeping with the
  member moving"); re-reading KT's actual rank argument for a route the row-membership decomposition missed;
  or pausing the conjecture-crux step and advancing ENTRY/ASSEMBLY / other program phases that do not depend on
  it. ALL LANDED leaves stay in tree (sound; reusable under a re-architected rank cert).

  *(4.21) THE KT-§6.4.2 RANK-ARGUMENT SOURCE RECON — VERDICT: the §(4.20) STOP is UPHELD and SHARPENED. KT's
  paper certifies the rank by whole-matrix bookkeeping with the member MOVING (NOT row-membership) — so the
  project's row-membership frame is not KT's literal shape — BUT KT's "member moves" is realized IN LEAN
  exactly as the relabel-image submatrix containment, which IS the wall. There is NO missed KT route; the
  fundamental reconsideration is to BUILD the §I.8.21(α) matrix-level block-rank-additivity-over-a-relabel
  infra. Source-verification recon (read-only, primary KT PDF, opus / OPUS-ONLY, 2026-06-24, agentId
  `a781cadcbac15592a`). HIGH confidence (grounded in KT eqs. 6.44/6.51/6.62–6.67, Claim 6.11, printed
  pp. 685/690–691/696–698).*

  **KT's rank mechanism (pinned to the source).** (b) a block RANK-ADDITIVITY count + (c) a union-DIMENSION
  argument — NOT (a) row-by-row span membership. Per-candidate (6.64–6.65): column+row ops reduce `R(G,pᵢ)` to
  a `D×D` block `Mᵢ` over `R(G₁∖(v₀v₂)ᵢ∗, q₁)`, then `rank R(G,pᵢ) ≥ rank Mᵢ + rank R(G₁∖…) = D + D(|V|−2)`
  (block-triangular additivity; the bottom block's rank is the SAME `D(|V|−2)` for every `i` by the IH on the
  ONE base `v₁`-split, 6.46/6.51, transported by the index-shift isos 6.54–6.56). "At least one `Mᵢ` has full
  rank" (6.65) is the contrapositive union-dimension count (6.67) closed by Lemma 2.1 (`(d+1 choose d−1)=D`).
  The redundant covector `r` is carried `=±r` across panels (6.66, the degree-2 two-edge cancellation, `d=3`
  model 6.44) — `r` re-expressed via a DIFFERENT edge's rows, the member MOVING. Eq. (6.62) (the relabel
  correspondence) is used to identify which candidate row plays the moved redundant role
  (`(v₀v₂)ᵢ∗ ⟷ (v₀v₁)ᵢ∗`) and to make `R(G,pᵢ)` CONTAIN `R(G₁,q₁)` as a submatrix (the precondition of the
  6.64 additivity) — it never pins the FIXED base row into the candidate's span.

  **Why this does NOT supply a missed Lean route (the adversarial half).** KT's moving-member bookkeeping is
  realized in Lean precisely as the relabel transport `(funLeft (shiftPerm)⁻¹).dualMap` — KT's (6.62)
  correspondence IS an index relabelling, and §(4.20) PROBE 2 confirmed the transport moves `vtx2 ↦ vtx1`.
  KT's block rank-count (6.64) is valid ONLY because (6.62) gives the relabelled-submatrix containment; KT's
  paper hides this as a one-line "it is not difficult to see" (the 6.61 sentence), but in Lean the
  submatrix-containment-under-relabelling is the WHOLE content. The design's own §(4.18) (B′) operated-frame
  block-rank IS KT's column-op-then-block-count, and §(4.20) (A′) IS KT's member-moving genuine-row transport —
  both kernel-confirmed DEAD. So KT's argument hits the SAME step; the wall is genuinely KT's once a
  Lean-checkable witness is demanded for each "not difficult to see."

  **The genuinely-new idea (the sharpened reconsideration).** Build an ABSTRACT block-rank-additivity lemma
  that consumes the (6.62) correspondence as a single relabel-ISOMORPHISM of matrices and concludes
  `rank R(G,pᵢ) ≥ rank Mᵢ + rank R(G₁,q₁)` WITHOUT extracting an individual fixed row's span membership — i.e.
  formalize KT's "submatrix containment" (6.61) as a MATRIX-LEVEL rank-preserving block embedding (induced by
  `ρᵢ` + the column op), reading `±r` (6.66) off as a covector identity in `ℝ^D` (§I.8.23 notes this is
  structural / single-`r`), so the union-dimension finish (6.67) is the only per-`Mᵢ` analysis. This is the
  design's §I.8.21(α) "block-rank-additivity / quotient" infra (a genuinely-new, cost-unknown abstract-LA
  piece). Precedent + the gap: the §(4.18) de-risk LANDED a GENERIC block-rank lemma
  (`Submodule.finrank_add_card_le_of_linearIndependent_mkQ`) but it consumes a SCALAR fixed-member membership
  (`hWS`/`hW`) at the single rank-cert use site (`Candidate.lean:1606–1611`), which forces the wall; the new
  lemma must instead carry the whole base matrix as a BLOCK (never forming that membership). **Verdict: the
  reconsideration is NOT "find KT's missed route" (there is none) but "build the matrix-block-rank infra that
  lets Lean count the rank the way KT counts it on paper." A fresh-session design+build of the §I.8.21(α)
  infra — cost-unknown — is the next concrete direction; ALL LANDED leaves stay in tree (reusable).**

  *(4.22) THE A1 §I.8.21(α) FEASIBILITY SPIKE — VERDICT: INFEASIBLE (the §(4.21) "build the
  matrix-block-rank infra" direction has NO feasible route in hand; the FEASIBLE first pass was
  WITHDRAWN). Read-only compiler-checked spike + a construct-or-concede resume, opus / OPUS-ONLY,
  2026-06-24, agentId `a8d70da3d32f07ca3` (resumable). → option (C)/(D); user adjudication pending.*

  **First pass returned FEASIBLE — and it was UNSOUND (a route-COMPOSITION verdict mis-read as a
  dischargeability one).** The spike pointed at the LANDED static-`W` cert
  `case_III_rank_certification_chain` (`Candidate.lean:2039`) + the router's reproduced branch and built
  two scratch lemmas: SPIKE 1 produced `W`/`hW` "sorry-free", SPIKE 2 closed the full interior arm with
  "only a `G.deficiency n = 0` residual". But BOTH carried the load-bearing data —
  `f, hf, hvanish, hG_eb_cand, hdisj` (SPIKE 1) and `W, hWS, hWcard, hW` (SPIKE 2) — as HYPOTHESES,
  never discharged; the lone residual was the spine-level deficiency, NOT evidence the corner data is
  satisfiable. So the pass only re-proved that the already-landed `case_III_arm_corner_assembly`
  TYPE-CHECKS, and confirmed the (already-known, §(4.18)-agreed) ROW/membership escape — it did NOT
  touch the actual wall (`W`-existence / dischargeability for the real interior carry).

  **The construct-or-concede resume CONCEDED, with two NEW sorry-free kernel re-derivations** (built
  green, deleted): `concede_hG_eb_cand_unsatisfiable` re-derives §(4.17) for the REAL dispatch slot
  `e_b = cd.edge ⟨i−1⟩` (its landed link `isLink_pred_edge : G.IsLink e_b (vtx i.castSucc)
  (vtx (i−1).castSucc)` = `(v,b)` vs. the router's required `(vtx i.succ, vtx (i−1).castSucc)` = `(a,b)`
  ⟹ `IsLink.left_unique` + `vtx_inj` ⟹ `False`); `concede_through_v_row_breaks_hW` re-derives §(4.18)
  (the redundancy member's only candidate-span rep is the through-`vᵢ` row `hingeRow B vᵢ ρ₀`, `single
  vᵢ`-column `−ρ₀` by `reproducedSlot_pmR_acolumn_eq`; in `W` + `hW` ⟹ `ρ₀ = 0` ⊥ `hgate`). **No third
  route:** the only two landed candidate-span hinge-row membership lemmas are `_of_ofNormals_link`
  (genuine survivor, both endpoints off `vᵢ` — cannot carry a through-`vᵢ` row) and `_reproduced` (needs
  the unsatisfiable `hG_eb_cand`). Off-`vᵢ` wrap-tag ⟹ breaks `hWS`; through-`vᵢ` rep ⟹ breaks `hW`. So
  `hWS ∧ hWcard ∧ hW` are jointly unsatisfiable on the redundancy member — kernel-confirmed a THIRD time.

  **A1's matrix-level-infra question (the §(4.21) "genuinely-new idea"): NO feasible route in hand.** A
  static-`W` cert is dead (§(4.18), re-confirmed). The flat-OPERATED-frame analogue that DOES certify the
  rank either (i) keeps the genuine `±r` corner — already kernel-refuted by §(4.19) (B′): the `±r` row is
  not pure-`vᵢ`-column after `Φ`, a counterexample to `htopvanish`, not a sorry'able gap — or (ii)
  reintroduces the collapsed corner `hingeRow v a ρ` + `hρGv` = (A′) = the wall, §(4.20) found intrinsic
  to KT. So the §I.8.21(α) infra would have to escape BOTH the static-`W` impossibility AND the
  `±r`/`htopvanish` counterexample at once; none is in hand, and every route adjacent to it (A/B′/A′) is
  kernel-refuted.

  **Decision (verdict; user adjudication pending).** A1 = INFEASIBLE. The rank-cert obligation cannot be
  discharged for the general-`d` interior carry with current machinery. → option **(C)** (land general-`d`
  Theorem 5.5 conditional on the rank-cert obligation as an explicit top-level `h…` hypothesis,
  documenting the wall as the frontier; concrete + buildable, lets ASSEMBLY proceed) or **(D)** (broader
  reconsideration / external input; no route in hand). The parallel-safe **ENTRY** sub-phase is available
  for green-node momentum regardless (frozen contract, rank-cert-independent). ALL landed leaves stay in
  tree (sound, reusable). **Lesson** (Findings 2026-06-24; the satisfiability corollary already in
  DESIGN.md *Constructibility recon*): a compiler-checked SPIKE answers a route-COMPOSITION question, NOT
  a dischargeability one — a type-checking composition with the crux carried as hypotheses can report a
  single residual and still be unsound; the discriminating test is CONSTRUCT-OR-CONCEDE (produce the
  actual object, or concede), and resuming the SAME spike armed with the prior kernel-impossibilities is
  the cheapest decisive settle.

  *(4.23) THE §I.8.21(α) MATRIX-LEVEL (ROW-OPERATION) FEASIBILITY SPIKE — VERDICT: INFEASIBLE; the wall
  is intrinsic to KT's row operation ITSELF, NOT an artifact of the span-membership formalization. Confirms
  §(4.20)/(4.21)/(4.22) from the orthogonal row-operation angle (the one §(4.20) flagged as not-yet-spiked).
  Read-only design+spike, opus / OPUS-ONLY, 2026-06-24, agentId `a7e3f98e6ca6914cd` (resumable). → (C).*

  **The question (the coordinator's rework hypothesis, user-authorized).** KT (Lemma 6.13, §6.4.2,
  eqs. 6.60–6.67, read end-to-end from the primary PDF) certifies the rank by rank-preserving COLUMN + ROW
  operations, NOT span membership: column-op (6.61) → bottom sub-block = `R(G₁,q₁)` via the relabel (6.62);
  row-op (6.63–64) ZEROES the redundant `(v₀v₂)ᵢ*` row's `V∖vᵢ` part, moving it into the pure-`vᵢ` corner
  `Mᵢ`; bottom block becomes `R(G₁∖redundant)` (still rank `D(|V|−2)`). Hypothesis: place the redundant row
  in the CORNER (row-opped to pure-`vᵢ`), keep the BOTTOM block = genuine base rows only (LANDED transport,
  no wall) → escape the `hρGv`/`hWS` membership. The coordinator believed the wall might be a span-membership
  *formalization artifact*.

  **DISPROVEN at the kernel — the row operation IS the span membership (the scissors).** KT's pure-`vᵢ`
  corner `Σλ rⱼ(q₁(vᵢvᵢ₊₁))` is the Lean object `hingeRow vᵢ a ρ₀`; to enter `span F₀.rigidityRows`
  (required by the cert's `hg`/`hmem`, `Candidate.lean:1636–1648`/`2052`), the collapse `hingeRow vᵢ a ρ₀ =
  hingeRow vᵢ b ρ₀ − hingeRow a b ρ₀` (6.27) reduces to the GENUINE `hingeRow vᵢ b ρ₀` (via `hρe₀`, no wall)
  PLUS the residual `hingeRow a b ρ₀ ∈ span` = `hρGv` = the wall (SPIKE 3b leaves EXACTLY this one `sorry`).
  The SCISSORS (SPIKE 2b/4a/4b): the pure-`vᵢ` corner (`vᵢ` first) DOES satisfy `htopvanish` (the
  coordinator's bet was right about this) — but converting the block separator's LI to the SPAN bound
  `D(|V|−1) ≤ finrank(span)` (`finrank_mono`, `:1666`) needs the corner ⊆ span, forcing `hingeRow a b ρ₀ ∈
  span` again; the genuine corner (`vᵢ` second) enters via `hρe₀` but is NOT pure-`vᵢ` (§(4.19)). The two
  corners differ by exactly `hingeRow a b ρ₀` — the wall.

  **Clause-(i) confirmation against the LANDED Phase-22g code.** The project ALREADY documents the
  equivalence: `exists_redundant_panelRow_ab_decomposition` (`Candidate.lean:191`) gives the redundant row
  `r i* = wGv + wOther` with `wGv ∈ span(R(G_v,q)-rows)`, and the `r̂ := Σⱼ λ_{(ab)j} rⱼ` doc (`:230`) states
  `r̂` "IS the `G_v`-row part `wGv`." So KT's row operation `Σλ rⱼ` and the `hρGv` membership are the SAME
  mathematical fact (§(4.21)'s adversarial finding, now from the row-op angle). Why it cannot dissolve like
  `hρe₀`: `hρe₀` is an ANNIHILATION (framework-free value-read); `hingeRow a b ρ₀ ∈ span` is a
  framework-dependent MEMBERSHIP with no value-read form.

  **Verdict.** The member-mapping wall is intrinsic to KT — FOUR independent kernel confirmations (§(4.18)
  static-W, §(4.20) member-mapping, §(4.21) KT primary-source, §(4.23) row-operation) + the A1 concede + the
  project's own Phase-22g docs. No re-architecture of the rank cert escapes it; **(D) would need a
  genuinely-NEW idea beyond KT's argument** (escaping the scissors), none in hand. ALL landed leaves stay in
  tree (sound, reusable). **→ option (C)** (honest-conditional general-`d` Theorem 5.5; the landed
  `case_III_arm_realization_chain` already carries the rank-cert obligation as hypotheses, so this is wiring
  + ASSEMBLY, not new rank-cert math) + ENTRY in parallel. No motive/IH/contract change (the wall is below
  the contract).

  *(4.24) THE GEOMETRY-AWARE-TRANSPORT SCOPING RECON — VERDICT: RELOCATES-TO-WALL; the project's transport
  is ALREADY geometry-aware (corrects the "remembers only σ" diagnosis), and a LINEARITY IMPOSSIBILITY closes
  the whole dual-span transport class. The user-proposed "remember the geometry" transport is built (for
  genuine rows) and provably cannot reach the redundant row. 5th independent kernel confirmation. Read-only
  design+spike, opus / OPUS-ONLY, 2026-06-24, agentId `ae987b45e0e8d9414` (resumable). → (C).*

  **The transport is already geometry-aware (corrects §(4.20)–(4.23)'s "generic σ" framing).** `shiftPerm i`
  IS KT's `ρᵢ` (6.54; `Induction/Operations.lean:1552`, doc-confirmed); `qρ = q ∘ shiftPerm i` IS KT's config
  relation (6.55/6.56/6.59; `Arms.lean:92`, `ChainColumn.lean:1434`); and `rigidityRow_relabel_to_genuine`
  (`Relabel/Basic.lean:308`, LANDED) absorbs KT's per-edge reproduction (6.59) as the abstract hypothesis
  `hsupp` — exactly the "absorb 6.61's entrywise grind into an abstract property" the rework bet hoped for.
  It WORKS for genuine rows. So σ IS ρᵢ and the config relation IS encoded; the transport layer is correct.

  **The redundant row is closed by LINEARITY, not a missing abstraction (the decisive new test).** The bet:
  decompose the base redundancy `hingeRow v₀v₂ ρ₀ = Σⱼ cⱼ·(genuine rows)` (A-1), transport each genuine
  summand faithfully, recombine. SPIKE 3 (kernel): for ANY linear `T`, `T(Σcⱼ gⱼ) = Σcⱼ T(gⱼ)` — so the
  decomposed route lands the redundant row at the SAME image as the un-decomposed row, namely its `ρᵢ`-image
  `hingeRow (σ⁻¹v₀)(σ⁻¹v₂) ρ₀` = the MOVED member (interior `σ⁻¹v₂ = v₁ ≠ v₂`; KT (6.62) `(v₀v₂)ᵢ∗ ⟷
  (v₀v₁)ᵢ∗`), ≠ the member-fixed `hφ` (PROBE 3: equal ⟹ `ρ₀=0` ⊥ gate). The redundant row has no genuine
  `G₁`-edge to anchor `hsupp` to (`(v₀,v₂)` is the redundant COMBINATION, not an edge), so the
  faithful-transport property cannot apply to it. d=3 closes only because `shiftPerm 2 = (v₁v₂)` is a single
  swap landing the moved member directly on a genuine `e_b`-row (the masking degeneracy, re-confirmed).

  **The only escape is a non-linear / explicit-`Matrix` object — = the §I.8.21(α) infra, no route in hand.**
  Any future transport must be non-linear-in-the-carrier or operate on explicit `Matrix` coordinates (6.61 as
  a rank-preserving block embedding WITHOUT extracting the row's membership) — the §I.8.21(α) re-architecture
  that §(4.22)/(4.23) kernel-confirmed has no feasible route (must escape the static-`W` impossibility AND the
  `±r`/htopvanish counterexample at once; a transport `Ψ` would CONSUME, not produce, the containment). A
  large multi-phase representation investment, not made feasible by any transport. **Verdict: (D) needs a
  genuinely-new idea beyond KT (and beyond the dual-span entirely); none in hand. → option (C)** (the landed
  `case_III_arm_realization_chain` carries the rank-cert obligation as hypotheses: wiring + ASSEMBLY, not new
  rank-cert math) + ENTRY. **Nothing to rework** — the transport layer is CORRECT (it faithfully transports
  exactly the genuine rows; the redundant row's relocation is intrinsic, not a transport defect). No
  motive/contract change.

  *(4.25) THE ROUTE-B (genuine-basis) ARCHITECTURE PASS — VERDICT: B-WORKS at the two decisive kernel
  spikes; the UNCONDITIONAL crux is RESOLVABLE via an architectural inversion faithful to KT (6.64),
  **pending the one carried hypothesis LEAF-B1** (genuine-basis extraction). SUPERSEDES the §(4.20)–(4.24)
  "(C)-only" recommendation. Read-only architecture design+spike, opus / OPUS-ONLY, 2026-06-24, agentId
  `ad8dafc55bcaf21e3` (resumable). User-directed (tackle the faithful re-architecture, no skipping a key
  step).*

  **The architectural inversion (why all 5 prior walls were the WRONG object).** §(4.18)–(4.24) all forced
  the base REDUNDANT row into the base block `W` (→ through-`vᵢ`, breaks `hW`) or transported it as a covector
  (→ linearity-moved, §(4.24)). KT (6.64) does NEITHER: the bottom block is `R(G₁ ∖ (v₀v₂)ᵢ*, q₁)` — the base
  with the redundant row DELETED (still rank `D(|V|−2)`, since it is redundant) — and the redundant row's
  reproduction sits in the CORNER `Mᵢ`. Route B follows KT: `W` = GENUINE rows ONLY (off-`vᵢ`, where the
  transport provably WORKS — §(4.24) conceded this; card `D(|V|−2)`); corner = `D−1` fresh panel rows + the
  `±r` row (`hρe₀`-sourced, NEVER `hρGv`). `W` + corner = `D(|V|−2)+D = D(|V|−1)`. §(4.24)'s linearity
  impossibility does NOT apply because route B **never transports the redundant row** (it is a direct corner
  row via `hρe₀`, not a transported covector); the transport acts ONLY on genuine rows. The §(4.19)
  `htopvanish`/§(4.23) scissors does NOT apply because the chain cert `case_III_rank_certification_chain` (via
  `finrank_span_rigidityRows_ge_of_corner`) needs the corner only independent-mod-`W`, NOT pure-`vᵢ`.

  **Q1 + Q2 kernel-spiked (sorry-free, `#print axioms`-clean, CONSTRUCTED not hypothesized).** Q1 (reproduction
  = a provable column EQUALITY, KT 6.66): `q1A_corner_value_equality_constructed` on the LANDED
  `interior_group_eq_baseRedundancy` — no membership/transport. Q2 (the bound assembles for the GENUINE-only
  block): Q2-A the cert composes; Q2-B deleting the redundant row preserves the base span (genuine rows attain
  rank `D(|V|−2)` — the satisfiability §(4.18) called impossible *for the redundant-INCLUDING block*); Q2-C
  each genuine row transports (`rigidityRow_relabel_to_genuine`); Q2-D the genuine-only `W` satisfies `hW`
  (genuine rows have both endpoints `≠ vᵢ`).

  **Representation verdict: a LIGHT rank-cert REFORMULATION, not a `Matrix` rebuild.** Bare-dual-vector
  representation kept verbatim; `Meet`/`MeetHodge`, the ±r identity, the union-dimension, the carrier all
  untouched. The ONE rework: LEAF-2 / the `W`-production builds `W` from a GENUINE-only basis (card `D(|V|−2)`)
  instead of the full relabelled bottom family (which forced the redundant member → the wall); the §(4.17)-dead
  reproduced router branch is dropped.

  **The one carried hypothesis = the crux + top risk: LEAF-B1 (genuine-basis extraction).** From the IH's rank
  realization (`HasGenericFullRankRealization k n G₁`, rank `D(|V|−2)`), extract an LI family of GENUINE
  `R(G₁,q₁)` rows (redundant member excluded) of card `D(|V|−2)` spanning `span(R(G₁∖redundant))`, carrying the
  per-member genuine-link data `rigidityRow_relabel_to_genuine` consumes. Standard basis-from-spanning-set (Q2-B
  gives the span) over the edge-indexed genuine rows — but must produce a concrete `ιb` of card `D(|V|−2)` +
  recoverable genuine-link data; if not recoverable, may need the IH to deliver a genuine-row basis directly (a
  small motive-adjacent strengthening, BELOW the frozen contract). **DE-RISK by constructing it at the kernel
  before committing the full build** (it is the structural twin of this session's two carried-hypothesis false
  FEASIBLEs — treat it as the discriminating test).

  **Plan (≈3–4 sub-phases to close the rank cert, then ENTRY/ASSEMBLY):** LEAF-B1 (genuine-basis extraction,
  the crux) → LEAF-B2 (genuine-only `W` producer, rework of LEAF-2) → LEAF-B3 (corner producer, mostly landed)
  → LEAF-B4 (interior-arm rewire, drop the dead reproduced branch) → CHAIN-2c-iii dispatch / CHAIN-5, then
  ENTRY + ASSEMBLY (parallel-safe). Route A (full concrete `Matrix`, KT transfers literally but heavy) is the
  documented fallback IF LEAF-B1 proves intractable; B's diagnosis tells A exactly how to slot the redundant
  row. **Verdict: 23d's rank-cert reconsideration is RESOLVABLE (an A2-equivalent build via route B), NOT
  (C)/(D) — pending the LEAF-B1 de-risk.**

  *(4.26) ROUTE-B INTERIOR `hS` GAP — the dispatch's interior-arm `hS` is NOT satisfiable as LEAF-B2 is
  architected. Read-only compiler-checked dispatch recon, opus, 2026-06-24. VERDICT: BLOCKED at the
  interior `hS`; flagged not forced.*

  **The kernel facts (all against LANDED `def`/`theorem`, not prose).** The dispatch's interior arm calls
  `case_III_arm_corner_assembly_via_leafB2`, whose `hS` slot demands LEAF-B2's universal transport: **every**
  base rigidity row `φ ∈ Fbase.rigidityRows` (`Fbase = ofNormals (G − vtx 1) ends q`) has its cycle-relabel
  image `(funLeft σ.symm).dualMap φ ∈ span (caseIIICandidate G endsρ qρ (edge i) (edge (i−1)) (qρ(a,·)) n'
  (qρ(b,·)) 0).rigidityRows`, with `a = vtx i.succ`, `b = vtx (i−1).castSucc`. LEAF-B2
  (`exists_genuine_relabelImage_base_block`, `Candidate.lean:1844`) instantiates `hS` at the members of an
  **arbitrary** genuine basis `f` of `span(rigidityRows ∖ {rhat})` (LEAF-B1) — so `hS` must hold for *every*
  genuine base row, including rows at the **wrap edge `edge i`** (a genuine `G − vtx 1` link for `i ≥ 2`).

  **The wrap-edge row's image is the dead `(a,b)`-block tag, NOT a candidate-span member.**
  `chainData_bottom_relabel` (`Chain.lean:382–409`) classifies a base genuine row at the wrap edge `edge i`
  into the `Or.inr` branch — the reproduced-slot tag `hingeRow (vtx i.succ) (vtx (i−1).castSucc) ρ'` (bodies
  = the PANEL pair `(vtx (i+1), vtx (i−1))`). The `hS` router
  `bottomRelabel_rigidityRows_mem_span_caseIIICandidate` (`ForkedArm.lean:544`) routes that tag through
  `hingeRow_mem_caseIIICandidate_rigidityRows_reproduced` (`Candidate.lean:2061`), which requires
  `hG_eb_cand : G.IsLink e_b (vtx i.succ) (vtx (i−1).castSucc)` — i.e. the candidate's reproduced hinge
  `e_b = edge (i−1)` must genuinely link `vtx (i+1)`–`vtx (i−1)`. **This is provably FALSE** (kernel-checked:
  `cd.isLink_pred_edge` pins `edge (i−1)` to link `vtx i`–`vtx (i−1)`; `IsLink` functionality + `vtx_inj` +
  `omega` close `False`). Since `rigidityRows = {hingeRow u v r | G.IsLink e u v, r ∈ block e}`
  (`Basic.lean:638`) and `caseIIICandidate.graph = G`, the only `G`-edge candidate for the tag's
  body-support `{vtx (i+1), vtx (i−1)}` is the chain triangle through `w = vtx i` (the unique common
  neighbour): `hingeRow (vtx(i+1)) (vtx(i−1)) ρ' = hingeRow (vtx(i+1)) (vtx i) ρ' − hingeRow (vtx(i−1)) (vtx
  i) ρ'` (difference-collapse `hingeRow_sub_hingeRow_eq`), whose first summand needs `ρ' ∈ block(edge i)` =
  `ρ'(C(qρ(a,·), n')) = 0` — but `ρ'` (= the base row's `r`, or `−r`) only annihilates `C(qρ(a,·),qρ(b,·))`
  (the reproduced panel), never the candidate panel `C(qρ(a,·), n')`. So the tag is NOT in the candidate
  span.

  **The project ALREADY documents this as the wall.** `funLeft_dualMap_pmR_group_mem_span_caseIIICandidate`
  (`Chain.lean:491–499`) states verbatim: the collapsed `hingeRow vᵢ₊₁ vᵢ₋₁ (−ρ₀)` form "would force
  `ρ₀ ⊥ panelSupportExtensor`, contradicting the discriminator `hgate`, which is exactly why it is the
  independent `D`-th row" — i.e. the wrap-edge content is the **independent `±r` corner row**, NOT a
  base-block row. Option A escaped by transporting the wrap edge as a GROUP (`∑_{evⱼ=edge i} cⱼ•hingeRow…rvⱼ`)
  whose *sum* is the corner row; route B's LEAF-B2, by demanding each genuine basis row transport
  *individually* into the candidate span, re-introduces exactly the member-mapping wall §(4.18)–(4.24)
  documented. The conditional rank-cert composition (Q1/Q2 of §(4.25)) is sound; the GAP is that its `hS`
  premise is **unsatisfiable** for the real interior dispatch (the "deferred-hypothesis unsatisfiable for the
  consumer" trap, DESIGN.md *Constructibility recon* — the same shape as the §(4.22) false-FEASIBLE).

  **Root cause: wrong base-block target framework.** KT (6.62)'s bottom block `R(G₁∖(v₀v₂)ᵢ*, q₁)` maps under
  ρᵢ to the candidate's *seed* rigidity rows `R(Gᵢ, qᵢ) = ofNormals (G − vᵢ) endsρ qρ` — the UN-overridden
  framework. `caseIIICandidate` OVERRIDES the support extensor at `e_c = edge i` and `e_r = edge (i−1)` (the
  corner slots), so a base `edge i` row's image is a genuine *seed* row but lands on the candidate's overridden
  `e_c` slot, where its block condition is against the wrong (corner) panel. LEAF-B2 hardcodes
  `Fcand = caseIIICandidate`; the base block `W` should target the seed framework `ofNormals (G − vᵢ) endsρ
  qρ` (and the rank cert relate that to `caseIIICandidate`'s span only on off-slot rows).

  **Candidate fix routes considered (none is a clean buildable re-route at this layer):**
  1. *Re-route the tag via the genuine `(b,v)` slot.* Fails: the reproduced slot can only produce
     `hingeRow (vtx i) (vtx (i−1)) ρ'` (edge (i−1)'s genuine bodies), not the tag's `(vtx(i+1),vtx(i−1))`
     bodies; they are different rows.
  2. *Difference-collapse through `w = vtx i`.* Fails: needs `ρ' ∈ block(edge i)`, = the discriminator gate
     condition that is generically violated (the whole point of `hgate`).
  3. *Weaken LEAF-B2's `hS` to basis members only.* Fails: LEAF-B1 produces an arbitrary basis; the span of
     `R(G−vtx1)∖{rhat}` genuinely requires `edge i` rows (each edge contributes independent rows), so no basis
     avoids them.
  4. *Re-target the base block to the seed framework `ofNormals (G − vᵢ) endsρ qρ` (the KT-faithful fix).*
     This is the real fix but is NOT a wiring change: it re-architects LEAF-B2's `Fcand` + the corner cert's
     `W ≤ span(candidate)` relation (the corner block must be independent-mod-`W` where `W` lives in the seed
     span, not the overridden candidate span). A genuine rank-cert re-statement — phase-direction work, not a
     dispatch leaf.

  **Unblock = adjudicate route 4 (seed-framework base block) vs. the option-A GROUP transport (the landed
  `funLeft_dualMap_pmR_group_mem_span_caseIIICandidate`, which already lands the wrap edge as the corner `±r`
  GROUP, no individual-row `hS`).** The option-A group leaf is LANDED and wall-free; the route-B LEAF-B2
  individual-row `hS` is the regression. The cheapest exit may be to NOT use LEAF-B2's universal `hS` for the
  interior arm at all and instead route the base block through the seed framework + the landed group leaf for
  the `±r` corner — i.e. interior arm uses the option-A `case_III_arm_corner_assembly` (engine `hwmem` slot),
  not `case_III_arm_corner_assembly_via_leafB2`. That is a coordinator/phase decision. **[The (4.27)
  scoping below CORRECTS this "cheapest exit" hope: the option-A engine route's `hwmem`/`hρGv` bottom block
  ALSO walls at general `d`; the seed-framework re-architecture is the real wall-free route.]**

  *(4.27) OPTION-A `W`-PRODUCTION SCOPING — VERDICT (B): the bottom-block `W` does NOT escape wall-free via
  the option-A engine route; the SEED-FRAMEWORK re-architecture (route 4) is the wall-free route, and its
  one new leaf is the general-`d` relabel SET-image equality. Read-only compiler-checked scoping recon,
  opus, 2026-06-24.*

  **The crux the (4.26) "cheapest exit" missed.** The chain cert `case_III_rank_certification_chain`
  (`Candidate.lean:2125`, `hρGv`-FREE) needs a bottom block `W` with: `W ≤ span(caseIIICandidate …)`,
  `finrank W = D·(|Gv|−1)`, `hW : ∀ φ ∈ W, φ ∘ single vᵢ = 0`. The option-A *group* transport
  `funLeft_dualMap_pmR_group_mem_span_caseIIICandidate` handles the `±r` CORNER row only; it does NOT
  produce `W`. The two ways to produce `W`:
  - **Engine route** (`case_III_arm_realization` → `case_III_rank_certification`, `Arms.lean:310`): takes
    `hρGv : hingeRow a b ρ ∈ span R(G − vᵢ)` as a HYPOTHESIS. At a general interior `i` with the SHARED `ρ₀`
    this is exactly the member-mapping wall — `interior_group_acolumn_eq_neg_baseRedundancy` is the wrong
    shape (a column value, not a panel/row membership), the fresh-edge telescope (`Arm.lean:259–760`) walls.
    Even the `d=3` M₃ arm (`case_III_arm_realization_M3`, `Arm.lean:54`) discharges `hρGv` via W9a and stays
    on the engine route. **Engine route WALLS at general `d`.**
  - **Per-`i` `chainData_split_realization`** (`Realization.lean:1046`, which DOES fire W6b at the interior
    split): needs the IH at the interior split `G.splitOff vᵢ …`, NOT in scope (the frozen C.3 contract hands
    only the BASE `v₁`-split realization), AND a per-`i` W6b gives a `Classical.choice` `ρᵢ` unrelated to the
    shared `ρ₀` the cert/gate/corner all read (the §(o″)/(2305–2317) Route-A refutation). **WALLS.**

  **The wall-free route — the candidate's OWN seed rows as `W` (kernel-verified).** Probe `probe3_seed_W`
  (reverted): take `W := span (ofNormals (G − vᵢ) endsρ qρ).rigidityRows` (the candidate's seed framework,
  un-overridden). Then `hWS` (every seed `Gvᵢ`-row is a candidate rigidity row — the off-slot bridge
  `hingeRow_mem_caseIIICandidate_rigidityRows_of_ofNormals_link`, all `Gvᵢ`-edges are `≠ e_a, e_b`) and `hW`
  (every seed row is a `G − vᵢ` link, so vanishes off `single vᵢ` — `ofNormals_removeVertex_rigidityRow_comp_
  single_self`) BOTH close mechanically, NO `hS`, NO `hρGv`. The ENTIRE residual is `hWcard = hseedrank`:
  `finrank (span R(G − vᵢ, q∘σ)) = D·(|Gv|−1)` — the candidate seed framework's rigidity rank.

  **`hseedrank` IS wall-free — it is the relabel rank-iso, NOT `hρGv`.** The relabel `funLeft σ`
  (`σ = shiftPerm i.castSucc`) is a bijective linear automorphism; its `dualMap` carries
  `span R(base seed) → span R(candidate seed)` ISOMORPHICALLY, so `finrank` is preserved = base seed rank
  `D·(|Gv|−1)` (the base IH, in scope). The wrap-edge concern that killed the corner-OVERRIDDEN transport
  does NOT arise at the bare seed: at `d=3` `rigidityRows_ofNormals_relabel` (`Relabel/Basic.lean:648`,
  `hρGv`-FREE, 173-line proof) gives the SET equality `R(splitOff-relabelled seed) = (funLeft swap).dualMap ''
  R(splitOff base seed)` for the SPLITOFF frameworks (the short-circuit edge carries the wrap-edge image as a
  GENUINE seed row). The wall was an artifact of LEAF-B2 transporting into the corner-overridden candidate;
  at the seed level the relabel is a clean bijection.

  **VERDICT (B): option A does NOT escape wall-free; route 4 (seed-framework base block) is the real
  wall-free route.** It is NOT a "fall back to landed option A" — it is the rank-cert re-architecture: replace
  LEAF-B2's `Fcand`-transport `W` with the candidate's own seed-row span, sourcing its rank from a NEW
  general-`d` relabel SET-image leaf.

  **COST ESTIMATE (route 4):**
  - **NEW LEAF 1 (the one genuinely-new piece): general-`d` `rigidityRows_ofNormals_relabel`** — the chain
    generalization of the `d=3` `Relabel/Basic.lean:648` SET-image equality from `Equiv.swap a v` /
    `Equiv.swap e_b e₀ * Equiv.swap e₁ e_c` to `shiftPerm i.castSucc` / `shiftEdgePerm i`. Bricks LANDED:
    `ofNormals_supportExtensor_relabel_perm`, `blockRow_relabel_perm`, `rigidityRow_relabel_to_genuine`,
    `removeVertex_genuine_shiftRelabel`, and `chainData_bottom_relabel` already prove the per-row
    correspondence in BOTH directions; the new leaf packages them as a bijective SET equality. Est. ~1 leaf
    (~150–250 LoC, mirroring the `d=3` proof shape), MEDIUM risk (the cycle `σσ = id` analog of `hσσ` and the
    splitOff-vs-removeVertex graph bookkeeping need care). **This is the de-risk target before the build.**
  - **NEW LEAF 2: the seed-`W` producer** — package `probe3_seed_W` (kernel-verified, ~25 LoC, LOW risk) +
    `hseedrank` from LEAF 1 + the base IH rank. Replaces `case_III_arm_corner_assembly_via_leafB2`.
  - **Reused (landed):** the corner via `funLeft_dualMap_pmR_group_mem_span_caseIIICandidate` (the `±r` row),
    the panel rows, `linearIndependent_mkQ_corner_of_gate`, `interior_hρe₀_of_baseWidening`, the spike's
    mechanical `hgate`/`hρe₀`/`heab_off` discharges.
  - **Then:** the `chainData_dispatch` `Fin cd.d` router (base/`d=3` via `chainData_split_realization` + its
    `htrans`; interior via the new seed-`W` producer) + the `ends`-orientation override (GAP 2) + CHAIN-5.
  - **Total ≈ 2 new leaves + the dispatch + CHAIN-5** (vs. the prior "dispatch is a build" estimate). The
    one real risk is NEW LEAF 1; the seed-`W` reduction (probe-verified) de-risks everything downstream.
  - **Alternative if LEAF 1 walls:** the deeper reconsideration (route A full `Matrix`, or honest-conditional
    (C)). But LEAF 1 is the chain analog of a LANDED `d=3` `hρGv`-free leaf, so it is plausibly buildable.

  *(4.28) ROUTE 4-BARE WALLS — `hseedrank` is PROVABLY FALSE for the BARE seed; the §(4.27) verdict erred
  (bare vs splitOff). Make-or-break NEW LEAF 1 build, fresh opus, 2026-06-24, BLOCKED (recon-before-build,
  nothing written).*

  **The kernel fact (against the landed bricks).** §(4.27) claimed `W := span (ofNormals (G − vᵢ) endsρ
  qρ).rigidityRows` has rank `D·(|Gv|−1)` via the relabel rank-iso. FALSE for the BARE seed. The base wrap
  edge `edge i` (link `vtx i`–`vtx (i+1)`, both `≠ vtx 1` so a genuine `G − vtx 1` rigidity row) relabels
  under `σ = shiftPerm i.castSucc` (`σ⁻¹(vtx i) = vtx (i−1)`, `σ⁻¹(vtx (i+1)) = vtx (i+1)` off-cycle) to a
  row on the pair `(vtx (i−1), vtx (i+1))` — the `Or.inr` WRAP branch of the LANDED
  `removeVertex_genuine_shiftRelabel` (`Relabel/Chain.lean:249`), NOT a genuine `G − vᵢ` link. There is **no
  `G`-edge** on `(vtx (i−1), vtx (i+1))` (interior `deg_two` closure), so `R(G − vᵢ)` is MISSING the
  wrap-edge image; the relabel is not a row-set bijection and `finrank (span R(G − vᵢ)) < D·(|Gv|−1)`. The
  "`funLeft σ` is a linear automorphism ⟹ preserves finrank" fallback (§(4.27) Blockers) does NOT rescue it:
  `funLeft σ` preserves the finrank of the *image* span `(funLeft σ).dualMap '' span R(base)`, but the
  bare-seed span is a STRICT subspace of that image (missing the `(vtx(i−1),vtx(i+1))` row). KEY: the landed
  `d=3` `rigidityRows_ofNormals_relabel` (`Relabel/Basic.lean:648`) is stated for **splitOff** frameworks
  (`ofNormals (G.splitOff a v c e₁) …` ↔ `(funLeft swap).dualMap '' ofNormals (G.splitOff v a b e₀) …`),
  where the FRESH short-circuit edge `e₀`/`e₁` carries the wrap-edge image as a genuine row — exactly what
  the bare seed lacks.

  **VERDICT: route 4-bare WALLS — the wrap-edge member-mapping wall, a THIRD appearance** (option-A `hρGv`
  §(4.18)–(4.24); route-B `hS` §(4.26); now route-4-bare `hseedrank`). Route 4 *moved* the wall from
  LEAF-B2's `hS` to `exists_seed_base_block`'s `hseedrank`; the BARE seed does not escape it. **NEW LEAF 2
  `exists_seed_base_block` (LANDED 057a86e) is a sound lemma with an UNSATISFIABLE `hseedrank` for the bare
  seed it hardcodes** — a dead conditional unless re-targeted. The §(4.27) `probe3_seed_W` verified only
  `hWS`/`hW` (true for the bare seed); it ASSERTED `hseedrank` from a relabel iso that holds only for
  splitOff — the gap the coordinator's acceptance of §(4.27) missed (lesson: verify a "generalization of a
  landed lemma" against the landed lemma's ACTUAL framework form — splitOff vs bare — before accepting).

  **Candidate fix = route 4-SPLITOFF (LEAF-1 unblock-1), viability UNVERIFIED:** re-target `W` to the
  candidate SPLITOFF seed `ofNormals (G.splitOff vᵢ a b e₀') endsρ qρ` (wrap-absorbing: the relabel iso DOES
  hold splitOff↔splitOff, generalizing `Relabel/Basic.lean:648` to `shiftPerm`/`shiftEdgePerm`), and re-state
  the rank cert's `W ≤ span(caseIIICandidate)` to carry the extra `e₀'` short-circuit row (is it a candidate
  row? — an OPEN obligation) — a genuine rank-cert re-statement, NOT a leaf. Open risks: (a) the splitOff↔
  splitOff relabel iso at the non-involutive cycle `σ` (the `d=3` proof's `hσσ`/`hρρ` involution facts fail);
  (b) the `e₀'`-row's candidate-span membership; (c) a 4th wrap-edge surfacing. **Given §(4.27) already erred
  on bare-vs-splitOff, a verify-first compiler-checked spike on route 4-splitOff is prudent before a build.**
  Fallback if route 4-splitOff walls: route A (full `Matrix`) / honest-conditional (C). **Phase-direction
  decision owed to the user.**

  *(4.29) ROUTE 4-SPLITOFF WALLS at the `e₀'`-row containment (a 4th wrap-edge wall) — Q1 (rank) is wall-free
  and verified sorry-free, but Q2 (the splitOff seed's fresh short-circuit row ∈ candidate span) FAILS by the
  same discriminator-gate obstruction. Read-only compiler-checked verify-first spike (all probe edits
  reverted, tree clean), fresh opus, 2026-06-24.*

  **Q1 (rank `hseedrank_ss`): WALL-FREE, verified end-to-end sorry-free + warning-clean.** The splitOff↔
  splitOff SET-image equality at the NON-involutive cycle `σ = shiftPerm i.castSucc` / `shiftEdgePerm i`
  builds cleanly: `R(ofNormals (G.splitOff vᵢ vᵢ₊₁ vᵢ₋₁ e₀') endsρ qρ) = (funLeft σ.symm).dualMap '' R(base
  v₁-split)`. The `d=3` proof's `hσσ`/`hρρ` are NOT load-bearing — they were artifacts of stating the equality
  with `ρ`/`σ` on BOTH sides (forcing `ρ(ρ·)=·`); the clean statement uses `ρ.symm`/`σ` asymmetrically. Both
  directions reduce to LANDED involution-free bricks: `⊇` (image ⊆ target) = `rigidityRow_chainData_relabel`
  (`Relabel/Basic.lean:460`); `⊆` (target ⊆ image) = `rigidityRow_relabel_perm` (`Relabel/Basic.lean:203`)
  at the INVERSE iso `(splitOff_isLink_shiftRelabel_iff).symm` (+ `apply_symm_apply` cleanup) and the
  dualMap-composition identity `(funLeft σ.symm).dualMap ((funLeft σ).dualMap φ) = φ`. The finrank corollary
  is then `Submodule.span_image` + `funLeft σ.symm` a `LinearEquiv` (`LinearEquiv.funCongrLeft`/`.dualMap`) +
  `LinearEquiv.finrank_map_eq`, giving `finrank (span R(Fss)) = finrank (span R(base split)) = D·(|Gv|−1)`
  (the base = v₁-split IH). The crux fact: `hingeRow_funLeft_dualMap` (`RigidityMatrix/Basic.lean:549`,
  docstring "No involution on `ρ` is needed") makes the whole dual-map layer involution-free. (The two probe
  theorems built green: `PROBE_rigidityRows_chainData_relabel_setimage` + `PROBE_finrank_seed_ss`, ~40 LoC.)

  **Q2 (containment `hWS`): WALLS — the splitOff seed's fresh `e₀'` short-circuit row is NOT a
  `caseIIICandidate` span member.** The cert `case_III_rank_certification_chain` (`Candidate.lean:2196`)
  requires `hWS : W ≤ span(caseIIICandidate G endsρ qρ e_a e_b (qρ(vᵢ₊₁,·)) n' (qρ(vᵢ₋₁,·)) 0).rigidityRows`
  for the FULL `W = span Fss.rigidityRows`. `Fss = ofNormals (G.splitOff vᵢ vᵢ₊₁ vᵢ₋₁ e₀') endsρ qρ` includes
  a row at the FRESH short-circuit edge `e₀'` (link `vᵢ₊₁`–`vᵢ₋₁`, support `C(qρ(vᵢ₊₁,·), qρ(vᵢ₋₁,·))`,
  block functional `ρ' ⊥ C(vᵢ₊₁,vᵢ₋₁)`). This row is NON-redundant in the isostatic splitOff (drops `W` below
  `D·(|Gv|−1)` if removed). The off-slot bridge `hingeRow_mem_caseIIICandidate_rigidityRows_of_ofNormals_link`
  does NOT carry it: it requires `G.IsLink e₀' u v`, but `e₀' ∉ E(G)` (`caseIIICandidate.graph = G`). The only
  other route is the difference-collapse through the common neighbour `vᵢ` (`hingeRow_sub_hingeRow_eq`):
  `hingeRow vᵢ₊₁ vᵢ₋₁ ρ' = hingeRow vᵢ₊₁ vᵢ ρ' − hingeRow vᵢ₋₁ vᵢ ρ'`. The 2nd summand is a candidate
  `e_b = edge(i−1)` row (its overridden support at `t=0` is `C(qρ(vᵢ₊₁,·), qρ(vᵢ₋₁,·))` =
  `caseIIICandidate_supportExtensor_reproduced`, which `ρ'` annihilates — ✓). BUT the 1st summand
  `hingeRow vᵢ₊₁ vᵢ ρ'` is a candidate `e_a = edge i` row ONLY IF `ρ' ⊥ C(qρ(vᵢ₊₁,·), n')`
  (`caseIIICandidate_supportExtensor_candidate`, the OVERRIDDEN candidate slot) — and the discriminator
  transversal `n'` is chosen precisely so `ρ₀(C(qρ(vᵢ₊₁,·), n')) ≠ 0` (`hgate`), with the `±r` corner `ρ₀`
  the `e₀'`-redundancy direction. A generic `e₀'`-row `ρ'` annihilating `C(vᵢ₊₁,vᵢ₋₁)` does NOT annihilate
  `C(vᵢ₊₁, n')`. So the `e₀'` row is NOT in the candidate span.

  **VERDICT: route 4-splitOff WALLS — a 4th wrap-edge appearance** (option-A `hρGv` §(4.18)–(4.24); route-B
  `hS` §(4.26); route-4-bare `hseedrank` §(4.28); now route-4-splitOff `hWS`). The wall is invariant under
  base-block re-targeting: it is the discriminator-gate condition `ρ₀ ⊥̸ C(vᵢ₊₁, n')` (the very thing making
  the `±r` corner the independent `D`-th row) re-surfacing wherever the wrap-edge content tries to enter the
  candidate span — `hρGv` (A), `hS` (B), `hseedrank` (4-bare, missing), `hWS` (4-splitOff, present-but-uncontainable).
  Q1's resolution shows the relabel iso is NOT the obstacle (it's clean splitOff↔splitOff); the obstacle is
  that `caseIIICandidate` OVERRIDES the `e_a = edge i` slot to `C(vᵢ₊₁, n')`, so ANY row through bodies
  `{vᵢ₊₁, vᵢ}` (which the wrap content always reduces to) must clear the gate. Q3 is moot: the cert's `hWS`
  demands the full `W` (incl. `e₀'`) in the candidate span, which Q2 blocks.

  **Consequence: the rank-cert reconsideration via a seed/genuine base-block `W ≤ span(caseIIICandidate)` is
  closed to all routes in hand** (A-engine, B-individual, 4-bare, 4-splitOff). The decision moves to: **route A**
  (full concrete `Matrix` model of the `Mᵢ`-block — the wrap row enters as a literal matrix row, not a span
  member, so the gate never gates a *membership*; KT transfers literally but heavy), or **honest-conditional
  (C)** (carry the wrap-redundancy as an explicit hypothesis to the consumer, document the residual). The
  invariant (the gate obstruction is intrinsic to the `caseIIICandidate` override architecture, NOT to any
  one base-block choice) is the load-bearing finding: no further base-block re-targeting escapes it. Lesson:
  Q1 being clean while Q2 walls is the precise diagnostic — the relabel/rank machinery generalizes fine; the
  block is the candidate's own slot-override meeting the discriminator, one layer above the seed.

  *(4.30) ROUTE-A FEASIBILITY SCOPING — VERDICT: ROUTE A IS A GENUINELY-DIFFERENT, FEASIBLE PATH (NOT
  the refuted §(4.22)/(4.23) work), but it is a LARGE multi-leaf sub-phase (a from-scratch concrete
  `Matrix R(G,p)` model + the `Matrix.rank`↔span bridge + a per-`Mᵢ` matrix-block-additivity rebuild),
  NOT a light reformulation. The decision is A-vs-(C) on COST, not on feasibility: A is buildable and
  KT-faithful but expensive; (C) is cheap and leaves one named gap. Read-only recon, all probe queries
  reverted / tree clean, opus, 2026-06-24. Every load-bearing claim re-derived from the LANDED
  `def`/`theorem` + KT §6.4.2 (6.60–6.67) read directly from the primary PDF.*

  **(1) ROUTE A IS NOT THE REFUTED §(4.22)/(4.23) WORK — the prior refutation was option (i)
  (dual-space maneuvers), route A is option (ii) (a literal `Matrix`).** The §(4.21)→(4.23) "§I.8.21(α)
  matrix-level block-rank infra" the spikes refuted was, on its own framing (§I.8.21(2b)(α), lines
  1196/1239–1240): "a block-rank-additivity / quotient infra" — an ABSTRACT `finrank`/`Submodule` lemma
  consuming the EXISTING `rigidityRows`/span representation. It LANDED, as
  `Submodule.finrank_add_card_le_of_linearIndependent_mkQ` (`Mathlib/.../Dimension/Constructions.lean:214`,
  carrier-agnostic `finrank` over any field `V` — NOT a `Matrix`), and IS the kernel of the chain cert
  `case_III_rank_certification_chain`. §(4.22) refuted it because it "consumes a SCALAR fixed-member
  membership (`hWS`/`hW`) at the single use site, which forces the wall"; §(4.23) confirmed "the row
  operation IS the span membership." **Both refuted the dual-space span model's expression of KT's
  (6.61) submatrix-containment as a span MEMBERSHIP.** Route A is a *different object*: a genuine
  mathlib `Matrix R(G,p)` (rows = `(edge, hinge-block-index)`, columns = `(body, screw-coord) = α × Fin D`,
  entry = the doc-comment's literal "`r` in `u`'s `D` columns, `−r` in `v`'s", `Basic.lean:480–489`),
  where rank = `Matrix.rank`, KT's (6.61) column op = an explicit right-multiply by a unit-det matrix,
  and (6.64) block-triangular additivity = a literal block-matrix-rank fact. §(4.24) line 3102 EQUATED
  "explicit-`Matrix` object" with "= the §I.8.21(α) infra, no route in hand" — that equation is the
  source of the doc's internal tension and it is **imprecise**: it was written imagining a `Matrix`
  *transport* `Ψ` that "would CONSUME, not produce, the containment" (line 3106) — i.e. a hybrid still
  bottoming out in the dual-space cert's membership. A *standalone* `Matrix` cert (the rank computed by
  matrix operations, never re-entering the span-membership layer) is NOT what §(4.24) refuted. **So
  route A is option (ii); §(4.22)/(4.23) refuted only option (i). Route A is LIVE.**

  **(2) ROUTE A DOES DISSOLVE THE GATE WALL — confirmed against the wall's exact source.** The wall
  (§(4.18)–(4.29)) is NOT the gate `ρ₀(C(vᵢ₊₁, n')) ≠ 0`; the gate is KT's (6.65)/(6.66)/(6.67) full-rank-
  of-`Mᵢ` certification, a value-read the project ALREADY proves cleanly and soundly
  (`notMem_span_mkQ_pmR_row_of_gate` / `linearIndependent_mkQ_corner_of_gate`, `Candidate.lean:2006/2082`,
  + the union-dim finish `interior_hρe₀_*` closed by Phase-17 `omitTwoExtensor_linearIndependent`). The
  wall is the OTHER half of KT's argument: (6.64)'s block additivity needs `R(G,pᵢ)` to CONTAIN
  `R(G₁,q₁)` as a submatrix (the (6.61) column op + (6.62) ρᵢ-relabel row correspondence), and in the
  *dual-space span* model that "submatrix containment" is forced to be "every base/seed row ∈
  `span(caseIIICandidate.rigidityRows)`" — where `caseIIICandidate` genuinely OVERRIDES the `e_c = edge i`
  hinge's support extensor to the free `va`-line `C(vᵢ₊₁, n')` (`caseIIICandidate` def
  `Candidate.lean:939–947`; the override is the realized candidate framework `pᵢ`'s actual geometry, not
  an artifact). The wrap content always reduces to a row through bodies `{vᵢ₊₁, vᵢ}` = the overridden
  `e_c` slot, so its membership must clear the gate (§(4.29) line 3388–3390) — the membership and the
  gate collide. **In a literal `Matrix`, KT's (6.61) "submatrix containment" is a structural EQUALITY of
  matrix entries after an explicit invertible column operation (`Matrix.rank_mul_eq_right_of_isUnit_det`,
  CONFIRMED in mathlib), NOT a span membership.** The redundant/wrap row is a literal matrix row that the
  (6.64) row operation transforms IN PLACE; its `±r` value (6.66) is a literal entry computation
  (`interior_group_eq_baseRedundancy` already gives this as a column equality). No membership is ever
  formed, so the override-meets-gate collision never arises — the override just IS the top-left block
  `r(Lᵢ)` of `Mᵢ`, and the gate `r(C(Lᵢ)) ≠ 0` certifies `rank Mᵢ = D` via a `D×D` minor. **Route A
  genuinely avoids the membership obstruction. CONFIRMED, not hoped.**

  **(3) BUT ROUTE A IS HEAVY — and the bridge to the honest statement, while real, is itself a leaf
  family.** What must be built (NEW, from scratch — the project has NO `Matrix`-valued rigidity matrix
  anywhere; `R(G,p)` is exclusively `rigidityRows : Set (Dual ℝ (α → ScrewSpace k))`, kernel-confirmed):
  - **A1. The concrete `Matrix R(G,p)`** — `Matrix (Σ e, Fin (D−1)) (α × Fin D) ℝ` (plus the
    trivial-motion rows, or the pinned form), entries from the hinge-row blocks. NEW def + the basic API
    (row/column accessors, the `(edge,j)` ↔ `hingeRow` correspondence). MEDIUM, ~1 leaf.
  - **A2. The `Matrix.rank`↔`finrank (span rigidityRows)` bridge** — `Matrix.rank (R Q) = finrank (span
    Q.rigidityRows)` via the LANDED-in-mathlib `Matrix.rank_eq_finrank_span_row` (CONFIRMED) + the
    coordinate iso `α → ScrewSpace k ≅ (α × Fin D → ℝ)`. This is the clause-(iii) anchor: it connects
    `Matrix.rank` to the honest `HasGenericFullRankRealization` target (`PanelHinge.lean:1035`, which is
    literally `finrank (span rigidityRows) = D·(|V|−1) − def`), NOT a weaker matrix fact. But the
    coordinate iso must commute with the `ScrewSpace` carrier — `ScrewSpace k` is a `def` of dim `D`
    over `ℝ`, opaque (Phase 22l), so the iso + its naturality is real work, MEDIUM, ~1–2 leaves.
  - **A3. The matrix-block-additivity rebuild** — `rank (column-opped R(G,pᵢ)) ≥ rank Mᵢ + rank(bottom)`.
    mathlib has the two primitives (`Matrix.rank_mul_eq_right_of_isUnit_det` for the column op,
    `Matrix.det_fromBlocks_zero₂₁` for the block-triangular det) + the project's `Rank.lean` submatrix-det
    witnesses (`exists_submatrix_det_ne_zero_of_linearIndependent_rows`), but there is NO off-the-shelf
    `Matrix.rank` block-additivity-as-INEQUALITY lemma — it must be assembled (block-triangular full-rank
    minor + the IH's bottom-block rank). MEDIUM–HIGH, ~2–3 leaves; this is route A's analog of the
    landed `finrank_add_card_le_of_linearIndependent_mkQ`, re-done at the `Matrix` level.
  - **A4. The (6.61) column op + (6.62) ρᵢ-relabel realized on the matrix** — the explicit unit-det
    column-operation matrix (add `vᵢ`'s columns to `vᵢ₊₁`'s) + the ρᵢ row/column permutation; prove the
    result equals the block form (6.61) entrywise. This is the "not difficult to see" step KT compresses
    and the project's own §(4.21) flags as "the WHOLE content"; at the matrix level it is an entrywise
    computation, tractable but laborious. MEDIUM–HIGH, ~2–3 leaves.
  - **A5. Re-aim the gate/union-dim cert at the matrix `Mᵢ`** — `rank Mᵢ = D ⟺ r(C(Lᵢ)) ≠ 0` (6.65/6.66)
    + the (6.67) union-dim finish. The CONTENT is LANDED (the gate value-read, `interior_group_eq_base
    Redundancy` for `±r`, `omitTwoExtensor_linearIndependent` for Lemma 2.1); A5 re-states it against the
    `D×D` matrix minor instead of the `mkQ` quotient. LOW–MEDIUM, ~1–2 leaves (mostly re-wrap of landed).
  - **A6. The dispatch + spine wiring** — the `Fin cd.d` router over the matrix arms + CHAIN-5, then the
    honest Theorem 5.5 assembly via the A2 bridge. Same shape as the (C)/route-4 dispatch. MEDIUM.
  - **Reusable verbatim (LANDED, sound):** the entire upstream stack — the carrier `ScrewSpace`, the
    discriminator/gate value-reads, `interior_group_eq_baseRedundancy` (the `±r` column equality),
    `interior_hρe₀_of_baseWidening`, Phase-17 Lemma 2.1, the `ChainData` contract (C.0–C.6, frozen, NO
    motive/IH change — the wall is below the contract, confirmed), the Q1 relabel rank-iso (§(4.29),
    `rigidityRow_chainData_relabel` + `LinearEquiv.finrank_map_eq`, the matrix analog of (6.62)). The
    `mkQ`-quotient block cert (`case_III_rank_certification_chain` + `finrank_add_card_le_of_linear
    Independent_mkQ`) is SUPERSEDED for the interior arm but stays for `d=3`/the base arm.
  - **NOT reusable:** there is no existing `Matrix` rigidity infra to extend — A1–A4 are from scratch.

  **COST ESTIMATE: a dedicated sub-phase, ≈ 9–14 leaves across A1–A6** (the same order as a full
  realization-layer phase like 22h/22i, not a 2–3-leaf reformulation). The two genuinely-new high-risk
  pieces are **A3** (matrix block-additivity-as-inequality) and **A4** (the entrywise (6.61) column-op
  proof); the others are bridge/re-wrap work. A `d=3` zero-regression discipline must be kept (the matrix
  arm specializes to the existing `mkQ` arm, or the dispatch routes `d=3` to the LANDED engine).

  **VERDICT (decisive).** Route A is a **GENUINELY-DIFFERENT, FEASIBLE path** — it is option (ii) (a
  literal `Matrix`), NOT the option-(i) dual-space work §(4.22)/(4.23) refuted, and it DOES dissolve the
  override-meets-gate membership wall (the wrap row enters as a literal matrix row; (6.61) containment is
  an entrywise column-op equality, never a span membership). The clause-(iii) bridge (`Matrix.rank` ↔
  `finrank (span rigidityRows)` ↔ the honest `HasGenericFullRankRealization`) is real and lands on the
  honest statement, not a weaker fact. **But route A is a HEAVY, multi-leaf sub-phase** (≈9–14 leaves; A3
  + A4 genuinely-new), NOT the "light reformulation" the route-B/route-4 family hoped to be. So the
  user's decision is **A-vs-(C) on COST**, with real data: **(A)** unconditional honest general-`d`
  Theorem 5.5, ~a full realization-phase of work, KT-faithful, no named gap; **(C)** honest-conditional
  (carry the wrap-redundancy membership as one explicit `h…` hypothesis to the consumer), ~1 leaf +
  wiring, leaves a single documented gap that is exactly KT's (6.61) "it is not difficult to see"
  submatrix containment. ENTRY + ASSEMBLY are parallel-safe under either. **Flag-don't-force:** the one
  residual uncertainty NOT settled in this read-only recon is the *constant factor* on A1/A2 — whether
  the `ScrewSpace`-opacity coordinate iso (A2) and the entrywise column-op (A4) compose without a
  `maxHeartbeats`/`whnf` blow-up at general `d` (the Phase-22l opacity concern). A 1–2-day compiler-checked
  spike building A1 + A2 (the matrix def + the rank bridge at `d=3`, reverted) would settle the constant
  factor before a full A commitment; it would NOT change the feasibility verdict (the math is KT-literal
  and the mathlib primitives are confirmed present), only sharpen the leaf count. This spike is the
  recommended de-risk IF the user leans toward A.

  *(4.31) THE A5 ROUTE-COMPOSITION SPIKE — VERDICT: A5 IS DISCHARGEABLE BUT NEEDS ONE PRECEDING
  RE-COORDINATIZATION LEAF (A4.5 — a PRODUCT-column rigidity matrix). The column op IS expressible
  over a coordinatized matrix (no abstract span membership — route A's escape holds at the kernel),
  but `hblock`'s `D×D` corner block split is NOT dischargeable over the existing flat `dualCoordEquiv`
  matrix — its arbitrary `finBasis` columns do not factor as `α × Fin D`. The fix is a product-column
  matrix `rigidityMatrixProd`, same rank, columns `α × Fin D`. Compiler-checked spike (5 probes,
  all SORRY-FREE except the residual `hblock` block-fill); scratch reverted, tree clean; opus,
  2026-06-24. Every load-bearing claim re-derived from the LANDED `def`/`theorem` (`dualCoordEquiv`
  `Concrete.lean:72`, `rigidityMatrix` `:130`, `rigidityMatrix_row` `:156`, the A4 bridge
  `rank_ge_of_isUnit_mul_reindex_fromBlocks` `Rank.lean:376`, `rigidityMatrix_mul_rank` `:282`,
  `columnOp` `Basic.lean:998`) + KT §6.4.2.*

  **(1) THE COORDINATOR'S CONCERN IS CONFIRMED AT THE KERNEL: the flat `rigidityMatrix` columns
  (`Fin (finrank ℝ (Dual ℝ (α → ScrewSpace k)))`, an ARBITRARY `Module.finBasis` of the dual,
  `dualCoordEquiv`) do NOT factor as `α × Fin D`, so `hblock`'s `D×D` corner column split has no
  natural realization on it.** The dimension is right (PROBE 1, SORRY-FREE: `finrank ℝ (Dual ℝ
  (α → ScrewSpace k)) = card α · screwDim k`, by `Subspace.dual_finrank_eq` + `Module.finrank_pi_fintype`
  + `screwSpace_finrank` — `rw [Subspace.dual_finrank_eq, Module.finrank_pi_fintype]; simp
  [screwSpace_finrank]`), so `N = D·|V|`. But the `D×D` corner `Mᵢ` lives on the `D` columns of body
  `vᵢ₊₁`, and the arbitrary flat basis mixes all bodies' coordinates — there is **no column subset =
  "body `vᵢ₊₁`'s `D` columns"**. The `Concrete.lean:276` doc-comment ("an explicit invertible matrix
  on the `D·|V|` columns") and the `rigidityMatrix`/`rigidityMatrix_mul_rank` `α × Fin D` prose are
  **dimension-correct but index-imprecise**: the literal column index is the flat arbitrary basis, not
  the product `α × Fin D`. **A5-build fixes that prose (one leaf-side doc edit).**

  **(2) BUT THE COLUMN OP ITSELF IS EXPRESSIBLE OVER A COORDINATIZED MATRIX — route A's "(6.61) is a
  column-op, never a span membership" escape holds at the kernel (PROBE 2b, SORRY-FREE).** For ANY
  primal `Φ : (α → ScrewSpace k) ≃ₗ[ℝ] (α → ScrewSpace k)` (KT's `columnOp` is exactly such an equiv,
  `Basic.lean:998`), the matrix `U = (toMatrix' (flatColumnOpEquiv Φ))ᵀ` — where `flatColumnOpEquiv Φ
  := dualCoordEquiv.symm.trans (Φ.symm.dualMap.trans dualCoordEquiv)` — satisfies
  `(rigidityMatrix * U).row p = dualCoordEquiv (Φ.symm.dualMap (rigidityRowFun p))`, i.e. the
  right-multiply realizes "precompose every row functional with `Φ`". Proof (lifts verbatim): row of
  `M * Uᵀ` = `vecMul (M.row p) Uᵀ` = `U.mulVec (M.row p)` (`Matrix.vecMul_transpose`) = `flatColumnOpEquiv
  Φ (M.row p)` (`LinearMap.toMatrix'_mulVec`) = `dualCoordEquiv (Φ.symm.dualMap (rigidityRowFun p))`
  (`rigidityMatrix_row` + `LinearEquiv.symm_apply_apply` through the `.trans`). **`IsUnit U.det` is a
  4-line fact** (PROBE 2c, SORRY-FREE): `IsUnit.of_mul_eq_one _ ?h; rw [← Matrix.det_mul,
  ← LinearMap.toMatrix'_comp]; simp` (det of `g · g⁻¹` = det 1 = 1). **No `ScrewSpace` unfolding
  anywhere** — the op enters as conjugation-by-`coordEquiv` of the abstract `Φ.symm.dualMap`, not a
  per-coordinate manipulation. So the wall (span membership of the wrap row) genuinely never forms.

  **(3) THE RESOLUTION: A PRODUCT-COLUMN RIGIDITY MATRIX `rigidityMatrixProd` (one new re-coordinatization
  leaf, A4.5), feeding the SAME A4 bridge.** The A4 bridge `rank_ge_of_isUnit_mul_reindex_fromBlocks`
  takes ANY `M : Matrix p q K`; instantiate it not with the flat matrix but with
  `rigidityMatrixProd : Matrix (β × Fin (D−1)) (α × Fin D) ℝ`, whose columns factor as `α × Fin D` so
  `en : (α × Fin D) ≃ n₁ ⊕ n₂` is the obvious product split (`n₁ = {vᵢ₊₁} × Fin D`, the `D` corner;
  `n₂` = the rest). Built (PROBE 3, all SORRY-FREE) from a per-vertex screw basis:
  `dualProductCoordEquiv := (Pi.basis (fun _ => screwBasis k)).dualBasis.equivFun.trans (funCongrLeft …
  sigmaEquivProd.symm)` (needs `haveI : DecidableEq (Σ _ : α, Fin D) := Classical.decEq _` in the def
  body). Its rank bridge is the SAME carrier-agnostic argument as `Matrix.rank_of_dualCoord`
  (`rank_eq_finrank_span_row` + `Submodule.span_image` + `LinearEquiv.finrank_map_eq`), so
  `rigidityMatrixProd.rank = finrank (span (range rigidityRowFun)) = finrank (span rigidityRows)` (lands
  on the honest target, **no `ScrewSpace` reach-in**). The column op realizes on it identically
  (PROBE 4, SORRY-FREE: `prodColumnOpEquiv`, same conjugation proof, now needs `[DecidableEq α]` for the
  `α × Fin D` `toMatrix'`). The entrywise content (PROBE 5): `dualProductCoordEquiv φ (body, j) =
  φ (Pi.single body (screwBasis k j))` (pure `Basis.dualBasis`/`Pi.basis` API), so `hingeRow u v r`'s
  support (only bodies `u, v`) makes the block-zero structure **entrywise-visible** — the residual
  `hblock` block-fill is a finite support computation, NOT a span argument.

  **(4) THE CORRECTED A5 LEAF DECOMPOSITION (EXACT SIGNATURES; supersedes the §(4.30) A5 sketch).** A5
  splits into A4.5 (the re-coordinatization, the genuinely-new piece this spike surfaced) + A5-proper
  (the gate re-wrap + `hblock` block-fill). Signatures (`F : BodyHingeFramework k α β`, `D := screwDim k`,
  `Dr := finrank ℝ (ScrewSpace k) = D` by `screwSpace_finrank`; all bankable fragments below verified
  SORRY-FREE in the spike — quote them on build-resume):
  - **A4.5a — `screwBasis`** (LOW, ~0.3 leaf): `noncomputable def screwBasis (k) : Basis (Fin (finrank ℝ
    (ScrewSpace k))) ℝ (ScrewSpace k) := Module.finBasis ℝ (ScrewSpace k)`.
  - **A4.5b — `dualProductCoordEquiv`** (LOW–MED, ~0.5 leaf): `[Fintype α] : Dual ℝ (α → ScrewSpace k)
    ≃ₗ[ℝ] (α × Fin (finrank ℝ (ScrewSpace k)) → ℝ)` := `haveI : DecidableEq (Σ _ : α, Fin …) :=
    Classical.decEq _; ((Pi.basis (fun _ : α => screwBasis k)).dualBasis.equivFun).trans (funCongrLeft
    ℝ ℝ (sigmaEquivProd α (Fin …)).symm)`.
  - **A4.5c — `rigidityMatrixProd`** (LOW, ~0.3 leaf): `[Fintype α] (F) (ends) (hgp) : Matrix
    (β × Fin (D−1)) (α × Fin (finrank ℝ (ScrewSpace k))) ℝ := Matrix.of fun p => dualProductCoordEquiv
    (F.rigidityRowFun ends hgp p)`.
  - **A4.5d — `rigidityMatrixProd_rank_eq_finrank_span_rigidityRows`** (LOW–MED, ~1 leaf): `[Fintype α]
    [Finite β] (hends) : (rigidityMatrixProd F ends hgp).rank = finrank (span F.rigidityRows)`. Compose
    the carrier-agnostic `rank_eq_finrank_span_row`-route (quoted SORRY-FREE in spike PROBE 3) with the
    LANDED `span_range_rigidityRowFun` (`Concrete.lean:199`). **Best refactor: GENERALIZE
    `Matrix.rank_of_dualCoord` (`Concrete.lean:84`) to take an arbitrary coordinatizing `coordEquiv :
    Dual ℝ M ≃ₗ[ℝ] (κ → ℝ)` instead of the hard-wired `dualCoordEquiv`** — then both the flat
    `rigidityMatrix_rank` and the product `rigidityMatrixProd_rank` are one-line instances, no proof
    duplication.
  - **A5a — `prodColumnOpEquiv`** + **the column-op-as-right-multiply** (MED, ~1–1.5 leaf): the unit-det
    `U := (toMatrix' (prodColumnOpEquiv Φ))ᵀ` (`IsUnit U.det` via the PROBE-2c 4-liner) and the row
    identity `(rigidityMatrixProd F ends hgp * U).row p = dualProductCoordEquiv (Φ.symm.dualMap
    (rigidityRowFun p))` (PROBE-4 proof, SORRY-FREE). `[Fintype α] [DecidableEq α]`.
  - **A5b — the gate re-wrap** (LOW–MED, ~1–2 leaf, content LANDED): `Mᵢ`-full-rank via
    `interior_group_eq_baseRedundancy` + `omitTwoExtensor_linearIndependent`, re-stated as
    `LinearIndependent (Mᵢ).row` for the A3/A4 `hA`.
  - **A5c — the `hblock` block-fill** (MED–HIGH, ~1.5–2.5 leaf, the residual crux): construct `em`/`en`
    (the `en : (α × Fin D) ≃ ({vᵢ₊₁} × Fin D) ⊕ rest` product split), and prove
    `(rigidityMatrixProd F endsᵢ hgpᵢ * U).reindex em en = fromBlocks Mᵢ B 0 (R(G₁,q₁))` ENTRYWISE — each
    entry is `dualProductCoordEquiv (Φ.symm.dualMap (hingeRow u v r)) (body, j) = (Φ.symm.dualMap …)
    (Pi.single body (screwBasis j))` (PROBE 5), so the lower-left zero = "wrap rows vanish off the
    `vᵢ₊₁` columns after the op" is a `Function.update`/`Pi.single`-support computation (KT's `columnOp`
    moves `vᵢ`'s content to `vᵢ₊₁`; `hingeRow_comp_columnOp_apply` `Basic.lean:1070` is the operated-row
    value). This is the "not difficult to see" entrywise step KT compresses and §(4.21) flags as the
    WHOLE content — now genuinely entrywise, NOT a span membership.
  - **A6 — dispatch + spine** (MED, unchanged from §(4.30)) — fire `rank_ge_of_isUnit_mul_reindex_fromBlocks
    (rigidityMatrixProd …) U hU em en hblock hA hD`, get `D·|V| ≤ rank`, bridge to the honest target via
    A4.5d, route the `Fin cd.d` arms.

  **LEAF COUNT (sharpened): A4.5 ≈1.5–2 leaves (the new re-coordinatization) + A5b/A5c ≈3–4 + A6 ≈1–2 =
  ≈6–8 for A5+A6** (was §(4.30) "A5 ~2–3, A6 ~1–2"; the spike found A5 needs a preceding A4.5 leaf, so
  the count rises by the re-coordinatization, but A4.5a–d are mostly mechanical and A5c is the only
  MED–HIGH residual). The §(4.30) total (≈9–14 for the whole route-A sub-phase) is unchanged in order.

  **VERDICT (decisive, kernel-checked).** A5 as the §(4.30) sketch posed it — discharge `hblock` for the
  flat `rigidityMatrix` — is **NOT directly dischargeable**: the flat arbitrary-basis columns don't
  factor as `α × Fin D`. **But the route is sound and needs only a re-coordinatization leaf (A4.5), NOT
  a motive/IH change and NOT genuinely-new math beyond it** — the A4 bridge accepts any `M`, the
  product matrix has the same honest rank by the same opacity-clean argument, and the column op + block
  structure are entrywise over `α × Fin D`. **No phase-direction decision is owed** (this is within
  route A, which the user already chose; A4.5 is a sub-leaf of the §(4.30) A5 scope, not a new route).
  The only judgment call is the A4.5d refactor (generalize `rank_of_dualCoord` vs duplicate) — a
  build-time call, recommend generalize. Fall-back (C) is unaffected.*

  *(4.32) THE A5c-ASSEMBLY + A6 CHAIN-DATA INTEGRATION SPIKE — VERDICT: THE A6 COMPOSITION
  SKELETON IS SORRY-FREE AGAINST THE ACTUAL `caseIIICandidate` ARM, **but the A4.5d/A2 honest-rank
  bridges are mis-leveled** — `rigidityMatrix(Prod)` rows are indexed by ALL of `β` and the bridges
  require `hgp`/`hends` TOTAL over `β`, jointly UNSATISFIABLE on the real arm (`β` has non-edges,
  `e₀ ∉ E(G)`). The fix is one un-surfaced leaf: a row-RESTRICTED product matrix indexed by
  `{e // e ∈ E(G)} × Fin (D−1)` (kernel-confirmed the bridge generalizes to a `Subtype` row index).
  NOT a motive/IH change, NOT a frozen-contract change, NOT genuinely-new math — a re-indexing leaf
  (A4.5e) the §(4.31) decomposition missed. The `Fin cd.d` dispatch match rests on the STATED
  `d_eq_kAdd` (the `d = n` field), NOT coincidence — the 23c precedent gap is fixed in the record.
  Compiler-checked spike (3 scratch files, 6 probes; PROBE 1/2/3/5/6 SORRY-FREE; scratch reverted,
  tree clean); opus, 2026-06-24. Every load-bearing claim re-derived from the LANDED `def`/`theorem`
  (`Concrete.lean` A1–A5c, `Rank.lean:376` the A4 bridge, `caseIIICandidate` `Candidate.lean:939`,
  `case_III_arm_realization` `Arms.lean:310`, `case_III_rank_certification(_chain)`
  `Candidate.lean:1508/2196`, `rigidityRows` `Basic.lean:638`, `toBodyHinge` `PanelHinge.lean:87`,
  `ChainData` + `d_eq`/`d_eq_kAdd` `Operations.lean:1285`/`Realization.lean:980`).*

  **(1) THE A6 COMPOSITION SKELETON IS SORRY-FREE (PROBE 2).** Against the ACTUAL `caseIIICandidate G
  ends q e_a e_b na n' nb 0` framework `F₀`, the route-A `hrank` (= the
  `case_III_rank_certification` target `screwDim k · (|V(G)|−1) ≤ finrank (span F₀.rigidityRows)`)
  is produced by the landed A4 + A4.5d bridges with NO new lemma:
  ```
  have hbound := Matrix.rank_ge_of_isUnit_mul_reindex_fromBlocks
    (F₀.rigidityMatrixProd ends hgp₀) U hU em en hblock hA hD     -- A4: #m₁+#m₂ ≤ rank
  rw [hm₁, hm₂] at hbound                                          -- #m₁=D, #m₂=D·(|V|−2)
  rw [F₀.rigidityMatrixProd_rank_eq_finrank_span_rigidityRows ends hgp₀ hends₀] at hbound  -- A4.5d
  -- arith: D + D·(|V|−2) = D·(|V|−1);  exact hbound
  ```
  So the §(4.31) plan's CORE (fire the A4 bridge on `rigidityMatrixProd`, bridge via A4.5d) is
  kernel-correct: the seam where route A plugs into the live arm is the `hrank` step of
  `case_III_arm_realization` (`Arms.lean:346–353`) / the `case_III_rank_certification_chain` call in
  `case_III_arm_realization_chain` (`ForkedArm.lean:90`). Route A REPLACES `case_III_rank_certification`
  /`_chain` (the `mkQ`-quotient cert reading the `hWS`/`hg`/`hLI` span MEMBERSHIPS — the
  §(4.18)–(4.30) wall) with a NEW `case_III_rank_certification_matrix` (this PROBE-2 body); the
  downstream `case_III_realization_of_rank` tail is route-agnostic (`Arms.lean:343` comment),
  consumed verbatim.

  **(2) THE `em`/`en` SPLIT IS CONSTRUCTIBLE (PROBE 3, SORRY-FREE).** `en : (α × Fin D) ≃
  ({x // x = a} × Fin D) ⊕ ({x // x ≠ a} × Fin D)` via `(Equiv.prodCongr (Equiv.sumCompl (· = a)).symm
  (Equiv.refl _)).trans (Equiv.sumProdDistrib …)` (needs `[DecidableEq α]`); `#({x // x = a} × Fin D)
  = D` by `Fintype.card_prod`/`card_subtype`/`simp`. The corner column block IS body `a`'s `D` columns
  — `a = vtx i.succ`, KT's `vᵢ₊₁`. NO level-mismatch at the COLUMN split (the §(4.31) PROBE-3 product
  factoring was the fix and it holds). The corner ROW block `m₁` (`= D = (D−1) panel rows of `e_a` +
  1 reproduced `e_b`-row), the bottom `m₂` (`= D·(|V|−2)` IH rows), are CHOSEN SUBFAMILIES, fed to
  `em` as a partition — but see (3): the row index `β × Fin (D−1)` is the wrong universe.

  **(3) THE LEVEL-MISMATCH (the analogue of the flat-vs-product mismatch §(4.31) caught, one level
  up): `hgp₀` and `hends₀` are JOINTLY UNSATISFIABLE on the real arm.** `rigidityMatrix`/
  `rigidityMatrixProd` (`Concrete.lean:187`/`401`) are indexed by **ALL `β × Fin (D−1)`** (every
  label `e : β`, edge or not — `Matrix.of fun (p : β × Fin (D−1)) => …`), and STRUCTURALLY require
  `hgp : ∀ e, supportExtensor e ≠ 0` TOTAL over `β` (the def calls `blockBasis hgp p.1`, which needs
  `finrank_hingeRowBlock (hgp e) : finrank (hingeRowBlock e) = D−1` for EVERY label). The A4.5d/A2
  honest-rank bridges (`*_rank_eq_finrank_span_rigidityRows`) additionally require
  `hends : ∀ e, G.IsLink e (ends e).1 (ends e).2` (every label is a `G`-link). On the actual Case-III
  arm `β` has **non-edges** (`e₀ ∉ E(G)`, `e₀_fresh`), so:
  * `hends` is FALSE for `e = e₀` (a non-edge is not a link);
  * `hgp` for a non-edge depends on `ends e`: `supportExtensor e = panelSupportExtensor (q(ends e).1)
    (q(ends e).2)`, which is `0` when `ends e = (x,x)` (PROBE 5, SORRY-FREE: `panelSupportExtensor n n
    = 0`). A non-edge with distinct ends keeps `hgp` but then `hends` is even more false.
  The two cannot BOTH hold over all `β` once a non-edge exists. **CONFIRMED against the LANDED arm**:
  every existing arm general-position hypothesis is the **edge-RESTRICTED** form `∀ e, G.IsLink e … →
  supportExtensor e ≠ 0` (`Arms.lean:126/246/705`, `case_III_arm_realization.hne_Gv`,
  `case_III_arm_corner_assembly.hne_Gv`), NEVER total — and the A4.5d/A2 capstones have **ZERO callers
  anywhere** (grep: only the scratch). They were landed as "the honest target" but never wired to a
  framework with `β = E(G)`; the total-`hgp` mismatch was latent.

  **(4) THE FIX — A4.5e, a row-RESTRICTED product matrix (the un-surfaced leaf the §(4.31)
  decomposition missed). NOT a motive/IH/contract change, NOT new math.** The carrier-agnostic
  `Matrix.rank_of_coordEquiv` (`Concrete.lean:97`) takes ANY `[Finite ι]` row index and ANY family
  `w : ι → Dual ℝ M` — PROBE 6 (SORRY-FREE) confirms it fires on a `Subtype`-indexed family
  `{e // e ∈ E(G)} × Fin (D−1) → Dual ℝ (α → ScrewSpace k)`. So the route-A matrix is
  `rigidityMatrixEdge F ends hgp : Matrix ({e // e ∈ E(G)} × Fin (D−1)) (α × Fin D) ℝ`, rows
  `dualProductCoordEquiv (rigidityRowFun ends hgp ⟨e.1, j⟩)` for `e ∈ E(G)` only, with `hgp` /
  `hends` quantified over edges only (`∀ e ∈ E(G), …` — satisfiable, the existing edge-restricted
  form). Its rank bridge re-proves the span identity for the restricted range (the
  `span_range_rigidityRowFun` argument restricted to edges — straightforward; the off-edge labels
  contribute nothing to `span rigidityRows` since `rigidityRows` is already edge-only,
  `Basic.lean:638`). This is ≈1–1.5 leaf. The A5c operated-entry facts
  (`rigidityMatrixProd_mul_columnOp_apply(_eq_zero_of_ne)`) carry over verbatim (they are entrywise,
  index-agnostic on rows). **The §(4.31) A5/A6 decomposition stands EXCEPT it must re-target every
  matrix to the edge-restricted row index.**

  **(5) `hblock` (the `fromBlocks` equality) IS STILL THE RESIDUAL CRUX (MED–HIGH), but now over the
  edge-restricted matrix.** After the row restriction, `em : ({e // e ∈ E(G)} × Fin (D−1)) ≃ m₁ ⊕ m₂`
  partitions the EDGE rows: `m₁` = the corner (the `e_a` panel rows + the `e_b` `±r` reproduced row),
  `m₂` = the IH bottom (`G₁ ∖ row` edges). The lower-left `0` block reads off the landed
  `rigidityMatrixProd_mul_columnOp_apply_eq_zero_of_ne` (`Φ = (columnOp hva).symm`, `v = vᵢ₊₁ = a`'s
  corner body): the operated wrap rows vanish off body `a`'s `D` columns. This is the genuine
  remaining work; the entry-zero fact is landed, the assembly into a `fromBlocks` matrix equality is
  the ~1.5–2-leaf residual §(4.31) already named (now over the restricted index).

  **(6) THE `Fin cd.d` DISPATCH MATCH RESTS ON A STATED CONTRACT (question d, no 23c-style gap).**
  The corner row count `m₁` needs `D = screwDim k` (grounded in `screwSpace_finrank`, `Basic.lean:209`);
  the candidate index match `Fin cd.d ↔ Fin (k+1)` is the STATED `Graph.ChainData.d_eq_kAdd`
  (`Realization.lean:980`, derived from the record FIELD `d_eq : d = n` + `hn`), consumed by
  `candidatePanel`/`exists_chainData_discriminator_pick`. The 23c LEAF-3 latent `d = n` gap is FIXED
  in the record (`Operations.lean:1298`, a structural field set by ENTRY). The bottom `m₂ = D·(|V|−2)`
  is the IH rank on `G₁` (`|V(G₁)| = |V|−1`), `D·(|V(G₁)|−1)`. All three cardinalities rest on stated
  facts, NOT coincidence. **Question (b) (corner `Mᵢ` row-LI via `linearIndependent_rigidityMatrixProd
  _row_iff` + `omitTwoExtensor_linearIndependent` / `interior_group_eq_baseRedundancy`)** sits at the
  edge-restricted object level once A4.5e lands; the A5b iff is row-index-agnostic, so it re-wraps to
  the restricted matrix unchanged. **Question (c) (GAP 2, `ends`-orientation via `Function.update`)**
  is NOT hit by this spike — the arm builds `ends₁` via `Function.update` already
  (`Realization.lean:1159`, `chainData_split_realization`); the route-A matrix consumes that same
  `ends₁`, no new override.

  **CORRECTED LEAF DECOMPOSITION (supersedes §(4.31)(4)'s A5c/A6, exact signatures).** `F :
  BodyHingeFramework k α β`, `D := screwDim k`:
  - **A4.5e — `rigidityMatrixEdge` + its honest-rank bridge** (NEW, the spike's surfaced leaf;
    LOW–MED, ~1–1.5 leaf): `noncomputable def BodyHingeFramework.rigidityMatrixEdge [Fintype α]
    (F) (ends) (hgp : ∀ e ∈ E(F.graph), F.supportExtensor e ≠ 0) : Matrix ({e // e ∈ E(F.graph)} ×
    Fin (D−1)) (α × Fin D) ℝ` (rows `dualProductCoordEquiv (rigidityRowFun … ⟨e.1, j⟩)`, edge-only),
    `theorem …_rank_eq_finrank_span_rigidityRows [Fintype α] [Finite β] (hends : ∀ e ∈ E(F.graph),
    F.graph.IsLink e (ends e).1 (ends e).2) : (F.rigidityMatrixEdge ends hgp).rank = finrank (span
    F.rigidityRows)` via `Matrix.rank_of_coordEquiv` (PROBE 6) + the edge-restricted
    `span_range_rigidityRowFun`. (Equivalently: re-state A1's `rigidityMatrix(Prod)` themselves over
    `{e // e ∈ E(G)}` — a build call; the cleanest is a fresh edge-indexed def reusing the landed
    `rigidityRowFun`/`blockBasis`.)
  - **A5c — `case_III_rank_certification_matrix`** (the PROBE-2 body + the `hblock` residual; MED–HIGH,
    ~2–3 leaf): `theorem PanelHingeFramework.case_III_rank_certification_matrix [DecidableEq β]
    [DecidableEq α] [Finite α] [Finite β] (G Gv : Graph α β) (ends) {q} {v a b} {e_a e_b}
    (hvVc … hVcard …) (the `case_III_rank_certification` arm context, MINUS `hρGv`/`hwmem` + PLUS the
    edge-restricted `hgp`/`hends` for `caseIIICandidate` and the chain-geometry `em`/`en`/`U`/`hblock`/
    `hA`/`hD`) : screwDim k · (|V(G)|−1) ≤ finrank (span (caseIIICandidate … 0).rigidityRows)`. Body =
    PROBE 2 (the A4 + A4.5e composition); the open content is constructing `U := (toMatrix'
    (prodColumnOpEquiv (columnOp hva).symm))ᵀ`, `em`/`en` (PROBE 3), and proving `hblock` entrywise off
    `rigidityMatrixProd_mul_columnOp_apply(_eq_zero_of_ne)`.
  - **A6 — re-route `case_III_arm_realization`'s `hrank`** (MED, ~1 leaf): swap the
    `case_III_rank_certification` call (`Arms.lean:350`) / `case_III_rank_certification_chain`
    (`ForkedArm.lean:90`) for `case_III_rank_certification_matrix`; the rest of the arm + the
    `Fin cd.d` dispatch (`chainData_split_realization` / `chainData_dispatch`) is unchanged.
  **BANKABLE SORRY-FREE FRAGMENTS (lift on build-resume):**
  - the A6 composition core (PROBE 2 body, quoted in (1) above — fires verbatim once A4.5e replaces
    A4.5d and `em`/`en`/`hblock` are supplied);
  - `en := (Equiv.prodCongr (Equiv.sumCompl (· = a)).symm (Equiv.refl (Fin D))).trans
    (Equiv.sumProdDistrib _ _ _)` with `Fintype.card ({x // x = a} × Fin D) = D` by
    `rw [Fintype.card_prod, Fintype.card_fin]; simp` (PROBE 3, needs `[DecidableEq α]`);
  - `panelSupportExtensor n n = 0` (PROBE 5: `by_contra; (panelSupportExtensor_ne_zero_iff n n).mp;
    .injective` of `![n,n]`) — the lemma confirming the `hgp`-failure mechanism (file it as a small
    mirror if the restricted bridge needs a non-edge extensor-zero fact).

  **VERDICT (decisive, kernel-checked).** The route-A A5c/A6 integration is **dischargeable as a
  mechanical re-indexing**, NOT walled and NOT requiring a motive/IH/contract change — but the §(4.31)
  decomposition is **OFF BY ONE LEAF**: it targeted the all-`β`-row `rigidityMatrixProd`, whose honest-
  rank bridge cannot fire on the real arm (`hgp`/`hends` total-over-`β` jointly unsatisfiable with
  non-edges). The corrected NEXT LEAF is **A4.5e** (the edge-restricted matrix + its honest-rank
  bridge), the smallest buildable commit; A5c (`case_III_rank_certification_matrix`, the `hblock`
  crux) and A6 (the arm re-route) follow. No phase-direction decision is owed (within route A). The
  fall-back (C) is unaffected. Three scratch files / 6 probes; PROBE 1/2/3/5/6 SORRY-FREE; tree clean.*
  **[SUPERSEDED by §(4.33): the §(4.32) corner index map is garbled — corner pin is `v`, not `a`,
  and the `…_apply_eq_zero_of_ne` per-row-keyed op is the wrong vanishing for the `0` block. §(4.33)
  carries the corrected map AND surfaces a deeper cert-shape obstruction the §(4.32) skeleton hid.]**

  *(4.33) THE CORRECTED-`hblock` SPIKE — VERDICT: the §(4.32) index map is GARBLED (corner pin is the
  re-inserted body **`v`**, not `a`; `en := columnSplit v`), and once corrected, a DEEPER obstruction
  surfaces: **the landed matrix cert `case_III_rank_certification_matrix`'s `fromBlocks A B 0 D` shape
  — a TOTAL row bijection `em` with BOTH diagonal blocks full-row-LI — is UNSATISFIABLE on the real
  isostatic arm for `D ≥ 3` (all general `d`).** Three corrected index-map bricks LANDED sorry-free
  into `Concrete.lean` (PROBE A/C/D below); the `hblock` ASSEMBLY itself is BLOCKED on the cert-shape
  mismatch, which forces a cert-kernel reshape (option 4b′) — a FLAG, not a unilateral pick.
  Compiler-checked spike (one scratch file, PROBE A/C/D SORRY-FREE → landed; scratch deleted, tree
  clean); opus, 2026-06-25. Every load-bearing claim re-derived from the LANDED `def`/`theorem`
  (`columnOp`/`columnOp_apply_single`/`hingeRow_comp_columnOp_apply` `Basic.lean:998/1036/1070`,
  `rigidityMatrixEdge_mul_columnOp_apply(_eq_zero_of_ne)` `Concrete.lean`, `case_III_rank_certification
  _matrix` `Candidate.lean:2265`, `finrank_span_rigidityRows_ge_of_corner`/`case_III_rank_certification`
  `Candidate.lean:1698/1509`, the A3/A4 kernel `Rank.lean:376`, `caseIIICandidate` `Candidate.lean:940`,
  deficiency count `Deficiency.lean:236`) + KT §6.4.2.*

  **(1) THE §(4.32) CORNER INDEX MAP IS GARBLED — corner pin is `v`, not `a`.** §(4.32) wrote
  `en := columnSplit a` and read the `0` block off `rigidityMatrixEdge_mul_columnOp_apply_eq_zero_
  of_ne`. Both are wrong:
  * **Corner pin = `v = (ends e_b).1`** (the re-inserted degree-2 body), NOT `a`. Confirmed against the
    dual-space cert's new-block pin (`Candidate.lean`, the `sn` block "stays independent through
    `v = (ends e_b).1`'s screw column") + `columnOp` (`Basic.lean:998`: `Φ.symm = columnOp hva`
    turns the corner rows `hingeRow v a/b ρ` into pure-`v`-column rows, `hingeRow_comp_columnOp_apply`).
    So **`en := columnSplit v`, not `columnSplit a`** — with `columnSplit a` the corner rows
    `hingeRow v a r (columnOp hva (single a s))` would read off `a`'s column, which after the op is
    NOT pinned (the op moves `a`'s content onto `v`), giving a wrong/degenerate corner block.
  * **`…_apply_eq_zero_of_ne` is the WRONG `0`-block lemma.** It keys the column op `Φ = (columnOp
    hva).symm` on **each row `p`'s OWN endpoints** (`hva : (ends p.1.1).1 ≠ (ends p.1.1).2`) and
    vanishes the entry off *that row's* first endpoint — a per-row op, not the one FIXED op the
    `fromBlocks` block needs. The lower-left `0` block needs the BOTTOM rows (general `G₁ = G ∖ {v}`
    links, endpoints `≠ v`) vanishing at the FIXED pin body **`v`**'s columns, under ONE op keyed on
    the corner edge's `(v, a)`. (`…_apply_eq_zero_of_ne` stays in tree — it is sound and additive.)

  **(2) THREE CORRECTED BRICKS LANDED SORRY-FREE** (`Concrete.lean`, build/lint/warning/axiom-clean,
  `[propext, Classical.choice, Quot.sound]` only):
  - **PROBE A — `BodyHingeFramework.rigidityMatrixEdge_mul_columnOp_apply_pin_zero`**: for a FIXED pin
    `v ≠ a` (NOT the row's endpoints), `(rigidityMatrixEdge ends hgp * U) p (v, c) = 0` when the row's
    endpoints `(ends p.1.1).1, .2` both `≠ v`. Proof: `…_mul_columnOp_apply` + `columnOp_apply_single
    hva` (`columnOp hva (Pi.single v s) = Pi.single v s`, since `(single v s) a = 0`) ⟹
    `hingeRow u w r (single v s) = r(0 − 0) = 0` (`Pi.single_eq_of_ne` both endpoints). The corrected
    lower-left-`0`-block read — the FIXED-pin replacement `…_apply_eq_zero_of_ne` couldn't serve.
  - **PROBE C — `…_apply_corner`**: for a CORNER row whose endpoints ARE `(v, a)`, the operated entry
    at `(v, c)` is `(blockBasisOn hgp _ j) (finScrewBasis k c)` — the panel functional on the screw
    basis (the `a`-column cancels, `hingeRow_comp_columnOp_apply`). The `hA` content: the `D × D`
    corner is the panel functionals on `v`'s `D` columns, row-LI = `omitTwoExtensor_linearIndependent`
    / `interior_group_eq_baseRedundancy` (via the A5b iff).
  - **PROBE D — `…_reindex_toBlocks₂₁_eq_zero`**: with `en := columnSplit v` and ANY row split `em`
    whose bottom rows avoid `v`, `((reindex em (columnSplit v)) (rigidityMatrixEdge * U)).toBlocks₂₁
    = 0`. Each entry is PROBE A (the `columnSplit v` `Sum.inl` corner column is a `(v, c)` column).
    So `hblock = fromBlocks (toBlocks₁₁) (toBlocks₁₂) 0 (toBlocks₂₂)` is a `Matrix.fromBlocks_toBlocks`
    rewrite **provided** the bottom `m₂` rows avoid `v`.

  **(3) THE DEEPER OBSTRUCTION — the cert's total-bijection `fromBlocks` shape is UNSATISFIABLE
  (`D ≥ 3`).** PROBE D's `hbot` hypothesis (`m₂` rows avoid `v`) CANNOT be met by a total `em`
  bijection, and the cert demands a total bijection:
  * The cert needs `em : ({e // e ∈ E(G)} × Fin (D−1)) ≃ m₁ ⊕ m₂` (a BIJECTION of ALL edge-rows,
    `Rank.lean:376` — `Equiv`, not an injection), with `#m₁ = D`, `#m₂ = D·(|V_Gv|−1)`, summing to
    `D·(|V(G)|−1)`. For minimal-0-dof `G` the count is ISOSTATIC: `(D−1)·|E(G)| = D·(|V(G)|−1)`
    (deficiency formula `def_{G̃}(V) = D(|V|−1) − (D−1)|E| = 0`, `Deficiency.lean:236`), so the
    counts match and `em` IS a total bijection — every edge row is used.
  * The `v`-incident rows are exactly `e_a`'s + `e_b`'s = `2(D−1)` rows. The corner `m₁` holds `D` of
    them; the surplus `2(D−1) − D = D−2` `v`-incident rows are FORCED into `m₂`. For `D ≥ 3` (every
    general `d`; at `d=3`, `D=6`, surplus `= 4`) this is nonempty.
  * After the op, those surplus `v`-rows are pure-`v`-column (`hingeRow_comp_columnOp_apply`): ZERO on
    the `n₂` (non-`v`) columns, NONZERO on `n₁` (`v`-columns). So in `m₂` they make `toBlocks₂₂` have
    **zero rows** (⟹ `hD : LinearIndependent toBlocks₂₂.row` FALSE) AND `toBlocks₂₁` **nonzero**
    (⟹ PROBE D's `hbot` unmeetable, `hblock`'s `0` block FALSE). Both `fromBlocks` conditions break.
  * **Why:** KT's (6.64) block-additivity is a SUBSPACE statement (`D` independent corner rows +
    `D·(|V_Gv|−1)` independent bottom rows, the surplus `D−2` rows IGNORED) — which is exactly why
    the dual cert uses `finrank_span_rigidityRows_ge_of_corner` (= `finrank_add_card_le_of_linear
    Independent_mkQ`, a `W`-subspace + `g`-family + `mkQ`, NO row partition). The matrix cert's
    `fromBlocks A B 0 D` with a TOTAL `em` + both blocks full-row-LI is a STRICTLY STRONGER shape that
    demands the WHOLE edge matrix be full-row-rank at `F₀` — FALSE, since `R(G,p₁)` at the `t=0`
    shear has `D−2` dependent surplus rows (the redundancy KT Claim 6.11 exploits, the same surplus).

  **(4) `hD` / `hA` DIFFICULTY VERDICT (the recon's crux question).** The route-A cert is stated for a
  SINGLE generic split `(v,a,b)` with `Gv = G.removeVertex v` (the IH base — NOT a chain-relabelled
  candidate; the interior-`i` chain relabel `chainData_bottom_relabel` is handled UPSTREAM by
  `chainData_dispatch`, the separate item-2 leaf). So for THIS cert **the bottom block needs NO
  matrix-relabel**: the bottom rows are `F₀`'s own `Gv`-edge rows (endpoints `≠ v`, so unaffected by
  the `v`-seed override — identical to `R(Gv,q)`'s rows), and their row-LI is the IH `Gv`-realization
  full-rank, a gate fact via the A5b iff `linearIndependent_rigidityMatrixProd_row_iff` ⟸ unit-det `U`
  + zero-off-`v`-block + reindex (all LI-preserving). `hA` likewise = the `D`-corner panel functionals
  LI = `omitTwoExtensor`/`interior_group` (PROBE C content). **BUT** both `hD` and `hA` are dischargeable
  ONLY in the SUBSPACE/row-SUBSET shape (corner = `D` chosen rows; bottom = the `Gv`-rows, surplus
  ignored) — NOT in the cert's total-`em`-bijection `fromBlocks` shape, per (3). So the `hD`/`hA`
  *content* is ~1–1.5 mechanical leaves each (gate facts, NO hard relabel); the BLOCKER is the cert
  SHAPE, not `hD`'s difficulty.

  **(5) OPTIONS (FLAG — no phase-direction picked).** The corrected index map is settled and the three
  bricks are banked; the `hblock` ASSEMBLY is blocked on the cert-shape mismatch. Three honest routes:
  - **(4b′) — reshape the matrix cert to row-SUBMATRIX block-additivity (RECOMMENDED, ~2–3 leaves).**
    Mirror the dual cert's subspace approach AND A3's existing column-submatrix step (`Rank.lean:344`,
    `N = M.submatrix id c`): add a ROW-submatrix variant of A3/A4 taking `em : m₁ ⊕ m₂ ↪ rows` (an
    INJECTION, not `≃`) — pick the `D` corner rows + the `D·(|V_Gv|−1)` `v`-clean `Gv`-bottom rows,
    IGNORE the `D−2` surplus. Then PROBE D's `hbot` IS meetable (`m₂` = `Gv`-rows only, all `≠ v`),
    `hD`/`hA` are the gate facts of (4), and the bricks A/C/D feed it directly. The reshape is
    cert-kernel-local (A3 `rank_fromBlocks_zero₂₁_…` already proves `#m₁+#m₂ ≤ rank` via a SUBMATRIX
    minor — generalize its row side from the implicit `em`-bijection to an explicit row injection).
    No motive/IH/contract change; `d=3` dual cert untouched.
  - **(4a) — `D := R(G₁,q₁)` the relabelled IH matrix (~3–5 leaves, HARD).** Take the bottom block as
    the literal IH matrix, forcing the matrix-model analogue of `chainData_bottom_relabel` (the
    `(funLeft σ).dualMap` member-move) NOW. Genuinely-hard + duplicates the upstream-`dispatch` relabel
    work. NOT recommended.
  - **(C) — documented fallback** (carry the rank-cert obligation as one hypothesis, ~1 leaf + wiring;
    gap = KT's own (6.61) "not difficult to see"). Unaffected; available if (4b′) walls.

  **VERDICT (decisive, kernel-checked).** The §(4.32) index map is corrected (corner at `v`,
  `columnSplit v`) and the three corrected bricks (PROBE A/C/D) are LANDED sorry-free. The `hblock`
  assembly is **BLOCKED on a cert-SHAPE obstruction** (the total-`em`-bijection `fromBlocks` cannot
  hold for `D ≥ 3` — the `D−2` surplus `v`-rows break both `toBlocks₂₁ = 0` and `hD`), NOT on `hD`'s
  difficulty (`hD`/`hA` are ~1-leaf gate facts, NO hard relabel, in the right SUBSPACE shape). The fix
  is a cert-kernel reshape to a row-submatrix (option 4b′, ~2–3 leaves) — a FLAG for the coordinator/
  user, no phase-direction picked. No motive/IH/contract change. Fall-back (C) unaffected.*

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

### (4.34) THE A6 ARM-ASSEMBLY RECON + ARM-SPINE LANDING — VERDICT: arm composes sorry-free; `hA`/`hD` are TWO genuinely-new dual-space→matrix-row LI bridges (NOT the (4.33)/row-473 ~1-leaf gate facts)

**Compiler-checked spike (session #34), then the deliverable landed.** The recon
built the route-A `case_III_rank_certification_matrix` application at the arm seam
in a scratch `.lean`, `sorry`'d each gap, and read the kernel residuals. Verdict:
**NEEDS-X resolved to ARM-SPINE-FIRST** (coordinator decision, within carry-the-crux;
no motive/IH/contract change). The arm spine
`PanelHingeFramework.case_III_arm_realization_matrix` is now **LANDED** sorry-free
(`CaseIII/Relabel/ForkedArm.lean`, build/lint/warning/axiom-clean, `[propext,
Classical.choice, Quot.sound]` only) — the route-A sibling of
`case_III_arm_realization_chain`, same split-data/count/`q`-normal signature
(+ `[Fintype α] [DecidableEq α]`), carrying `(m₁, m₂, hm₁, hm₂, re, hbot, hA, hD)`
as hypotheses and CONSTRUCTING `U`/`hU`/`en`/`hblock` in-body off the landed bricks.

**The arm SHAPE is constructible (confirmed sorry-free).** All four block-data
pieces build in-body with no carry beyond the row selection:
* `U := Matrix.transpose (toMatrix' (prodColumnOpEquiv (columnOp hva).symm).toLinearMap)`;
  `hU` via `prodColumnOpEquiv_transpose_toMatrix'_det_isUnit`.
* `en := (columnSplit v).symm`.
* `hblock`: `conv_lhs => rw [← fromBlocks_toBlocks M]; rw [hz]` where `hz : M.toBlocks₂₁ = 0`
  is the landed `rigidityMatrixEdge_mul_columnOp_submatrix_toBlocks₂₁_eq_zero` (needs `hbot`:
  `re ∘ Sum.inr` bottom rows avoid `v`). Pins `A := M.toBlocks₁₁`, `D := M.toBlocks₂₂`.
The carried row-selection `(m₁, m₂, re, hbot)` is the genuine A6 construction (the
dispatch's burden, item 2), exactly as `_chain` carries `(W, g)`.

**EXACT kernel-read residual goals** (`M := (F₀.rigidityMatrixEdge ends hgp * U).submatrix re (columnSplit v).symm`):
* `hA ⊢ LinearIndependent ℝ M.toBlocks₁₁.row` — unfolds to
  `LinearIndependent ℝ (of fun i j ↦ (rigidityMatrixEdge*U) (re (Sum.inl i)) ((columnSplit v).symm (Sum.inl j)))`
  (corner rows × body-`v` columns).
* `hD ⊢ LinearIndependent ℝ M.toBlocks₂₂.row` (bottom `Gv`-rows × `body ≠ v` columns).

**Why `hA`/`hD` are NOT ~1-leaf (correcting (4.33)/row-473).** All landed LI content
is **dual-space** (`LinearIndependent ℝ` over `Dual ℝ (α → ScrewSpace k)` functionals:
`omitTwoExtensor_linearIndependent`, `exists_independent_rigidityRows_of_edge`,
`linearIndependent_mkQ_corner_of_gate`); the residuals are **matrix-row** LI (vectors
in `n₁ → ℝ`). The only landed bridge `linearIndependent_rigidityMatrixProd_row_iff`
(A5b) is for the **full** matrix's `.row`, NOT a column-operated, row-restricted,
`v`-column-projected `toBlocks`. Grep-confirmed: NO landed `submatrix.toBlocks.row` LI
lemma. Two NEW bridges needed:
* **`hD`** — ✅ LANDED 2026-06-25 as `linearIndependent_toBlocks₂₂_row_of_off_pin`
  (`Concrete.lean`). **The design's `rank_eq_finrank_span_row` + `linearIndependent_rows_iff_
  rank_eq_card` Gram route was NOT needed** — a cleaner op-invariance route: the column op
  `Φ.symm = columnOp hva` only updates body `v`'s coordinate, invisible to a `Gᵥ`-row whose
  endpoints avoid `v`, so the operated bottom block `toBlocks₂₂` IS the un-operated `R(Gᵥ,q)`
  submatrix (`submatrix_columnOp_toBlocks₂₂_eq`, entrywise off `rigidityMatrixEdge_mul_columnOp_
  apply_off_pin` + `rigidityMatrixEdge_apply`). So `hD` is a pure submatrix-restriction of the
  IH row-LI: the bridge takes `hIH : LinearIndependent ℝ ((rigidityMatrixEdge).submatrix
  (re ∘ Sum.inr) ((columnSplit v).symm ∘ Sum.inr)).row` (the IH `R(Gᵥ,q)` full-rank restricted
  to the matched rows/cols — the dispatch's burden, item 2) and rewrites through the equality.
* **`hA`** — ✅ LANDED 2026-06-25 as `linearIndependent_toBlocks₁₁_row_of_corner_gate`
  (`Concrete.lean`). **The design's "port `linearIndependent_mkQ_corner_of_gate`" route was NOT
  needed** (no `mkQ`/quotient detour): the corner block IS the coordinate matrix of the corner
  block-basis functional family against the screw dual basis `(finScrewBasis k).dualBasis`, so its
  row-LI ⟸ the dual-space corner LI by the **dual-space→matrix-row coordinate re-wrap**
  (`Matrix.linearIndependent_row_of_coordEquiv`, the A5b core). The bridge takes the corner rows'
  `(v,a)`-endpoint records (`hc1`/`hc2`, supplying `rigidityMatrixEdge_mul_columnOp_apply_corner` to
  rewrite each entry to `coordEquiv (blockBasisOn …) j`) + the dual-space corner block-basis-functional
  LI `hLI` (the `D = (D−1)+1` corner independence, the dispatch's burden item 2). `coordEquiv :=
  (finScrewBasis k).dualBasis.equivFun` reindexed across the singleton `v`-column index
  `{body//body=v}×Fin D ≃ Fin D` (`Equiv.uniqueProd` + `LinearEquiv.funCongrLeft`); the singleton
  column reduces `(columnSplit v).symm (Sum.inl (⟨v,rfl⟩,c)) = (v,c)` by `rfl` after `subst`.
  **The §38 whnf guard HELD** — the `coordEquiv` is a `LinearEquiv` (kernel ⊥), so the carrier never
  unfolds (no `simp`/`whnf` on `F₀`); cleaner than a `linearIndependent_row_of_coordEquiv` on the raw
  candidate. Same `[propext, Classical.choice, Quot.sound]` axiom set as the `hD` leaf.

**NEXT** = leaf 1 (`hD` bridge) ✅ LANDED 2026-06-25; leaf 2 (`hA` bridge) ✅ LANDED 2026-06-25 — BOTH
arm-carried LI hypotheses now have producing leaves. NEXT = the dispatch (item 2) discharges
`(re, hbot, hA, hD)` and wires the arm. No phase-direction or contract change; `_chain` stays in tree
(parallel, sound).

### (4.35) THE ROUTE-A DISPATCH SPIKE — VERDICT: the interior arm composes; the wrap-edge wall DOES NOT re-surface (kernel-probed); GAP-2 resolved; 5-leaf decomposition (2 mechanical generalizations + 2 genuinely-new MATRIX-SHAPE bridges + wiring)

**Read-only compiler-checked spike (session #34, row 480).** Built a `chainData_dispatch`
interior-arm skeleton calling `case_III_arm_realization_matrix` at an interior matched candidate
`i` (`2 ≤ i < d`) of `cd : G.ChainData n`, with the split tuple
`(v,a,b,e_a,e_b) = (vtx i.castSucc, vtx i.succ, vtx (i−1).castSucc, edge i, edge (i−1))` read off
the landed `ChainData` accessors and the GAP-2 override
`ends₁ := Function.update (Function.update ends e_a (v,a)) e_b (v,b)`; `sorry`'d each gap and read
the kernel residuals. **The arm typechecks.** Cardinalities forced/consistent
(`m₁ = Fin (screwDim k)`, `m₂ = Fin (screwDim k·(|V(Gᵥ)|−1))`). No commit; scratch deleted.

**Make-or-break — the wrap-edge wall DOES NOT re-surface (kernel-probed).** Route A's `hgp` is a
**general-position** statement (`supportExtensor e ≠ 0` from `hLn`/`hgab`), never a span membership.
The probe `spike_probe_eb_corner` (compiled clean) confirmed the `e_b` reproduced `±r` row's operated
corner entry at `(v,c)` reads `(blockBasisOn hgp _ _)(finScrewBasis k c)` — **identical form to the
`e_a` rows** (because `columnOp hva (Pi.single v s)` updates `v↦s`, leaves `b↦0`). So the `±r`/wrap
content enters as a **member of the corner block `A`** (a literal matrix row), NOT as a span-membership
of the corner-overridden candidate. The discriminator gate intrinsic to the dual-space
`caseIIICandidate` slot-override (§(4.18)–(4.29)) never forms in the literal-`Matrix` model. The one
genuinely-hard residual is the corner `hLI` (= KT eq. 6.66 `±r` row + Lemma 2.1), KT's real content,
not the wall.

**GAP-2 RESOLVED.** The `ends`-orientation pins are the `Function.update` override `ends₁` — exactly
the pattern the landed base/`d=3` router `chainData_split_realization` already uses
(`Realization.lean:1159`); `hends_ea`/`hends_eb` close by `Function.update_self`/`_of_ne heab`. No
motive/contract change.

**Per-obligation verdict** (`F₀ := caseIIICandidate G ends₁ q e_a e_b (q(a,·)) n' (q(b,·)) 0`;
`re : Fin (screwDim k) ⊕ Fin (screwDim k·(m−1)) → {e//e∈E(G)}×Fin (screwDim k−1)`):
* `re` — (b) NEEDS-NEW-LEAF: corner half (`Sum.inl`, `D` rows) = `e_a`'s `D−1` panel rows **+ 1**
  `e_b` `±r` row (`e_a` alone has only `D−1` slots); bottom half (`Sum.inr`) = `D·(m−1)` `Gᵥ`-edge
  rows from the IH.
* `hbot` — (a): falls out of the `re` builder (`Gᵥ`-links avoid `v` by `removeVertex_isLink` +
  `cd.removeVertex_isLink_edge_succ_pred_off` + `ends₁`-off rewrite).
* `hc1` — (a): both corner edges record `v` first (`hends_ea`/`hends_eb`).
* `hc2` — (b) NEEDS-NEW-LEAF: the landed `hA` leaf demands `(ends).2 = a` for ALL corner rows, but the
  `e_b` row has `.2 = b ≠ a`. Corner math is sound (probe-confirmed); only the hypothesis is too
  strict → corrected form `hc2' : ∀ i, (ends (re (Sum.inl i)).1.1).2 ≠ v`.
* `hLI` — (b) NEEDS-NEW-LEAF (the crux): the `D×D` corner full-rank `blockBasisOn`-family LI in the
  **full screw-dual**. The landed `linearIndependent_mkQ_corner_of_gate` proves the SUM family LI in
  the **`W`-quotient**, not this. = KT eq. 6.66 + Lemma 2.1 (`omitTwoExtensor_linearIndependent`).
* `hD`-input `hIH` — (b) NEEDS-NEW-LEAF: `LinearIndependent ℝ ((F₀.rigidityMatrixEdge ends₁ hgp).submatrix
  (re∘Sum.inr) ((columnSplit v).symm∘Sum.inr)).row` — a **row-LI submatrix of the un-operated edge
  matrix**, NOT the dual-space `finrank/span` shape `chainData_bottom_relabel` produces for `_chain`.
* geometric `hgp`/`hends`/`hendsGv`/`hneGv`/`hm₁`/`hm₂` — all (a): `hgp` via the `d=3` engine's
  `hne_F₀` model (`Arms.lean:126`, `caseIIICandidate_supportExtensor_*` + `panelSupportExtensor_ne_zero_iff`);
  rest trivial off `ends₁`/`hends_Gv`/`Fintype.card_fin`.

**THE LOAD-BEARING CORRECTION (clause ii).** The hand-off's "`hA`/`hD` inputs come from
`exists_independent_rigidityRows_of_edge` + Lemma 2.1 / the IH" is true in spirit but **the landed
bridges produce the WRONG SHAPE**: all are **dual-space `finrank/span/mkQ-quotient`** facts (built for
`_chain`); route-A `hA`/`hD` need **row-LI of concrete edge-matrix submatrices / `blockBasisOn`
families** (no quotient, no span). Leaves 3+4 are genuinely-new matrix-shape bridges, NOT re-uses —
the corner `hLI` (leaf 3) is the dispatch's hardest single obligation, on par with the `hA`/`hD`
leaf-1/leaf-2 effort.

**Ordered leaf decomposition for `chainData_dispatch`'s interior arm:**
1. **Generalize** `rigidityMatrixEdge_mul_columnOp_apply_corner`: replace `hv2 : (ends p.1.1).2 = a`
   with `hv2 : (ends p.1.1).2 ≠ v` (keep `hv1 : .1 = v`). Proof = `simp [Function.update_of_ne,
   Pi.single_eq_of_ne]` (probe kernel-verified). *P≈1.*
2. **Generalize** `linearIndependent_toBlocks₁₁_row_of_corner_gate`: drop `hc2 : .2 = a` →
   `hc2' : ∀ i, (ends (re (Sum.inl i)).1.1).2 ≠ v`; reuse leaf 1 in the `hmeq` `ext`. *P≈1–2.*
3. **`dispatch_corner_blockBasis_linearIndependent`** (genuinely-new, the crux): from the
   discriminator gate `ρ₀(panelSupportExtensor (q(a,·)) n') ≠ 0`, `hρe₀`, and Lemma 2.1, produce
   `LinearIndependent ℝ (fun i:Fin (screwDim k) => blockBasisOn hgp (re(Sum.inl i)).1.2 (re(Sum.inl i)).2)`
   for the `re` selecting `e_a`'s `D−1` block rows + the `e_b` `±r` row. *Bridges the landed dual-space
   gate to the screw-dual `blockBasisOn` family. P≈3.*
4. **`dispatch_bottom_rowLI_of_IH`** (genuinely-new): from the IH `HasGenericFullRankRealization k n Gᵥ`,
   build the bottom injection `re∘Sum.inr` and prove `hIH` (the row-LI submatrix of the un-operated edge
   matrix). *Matrix-shape analogue of the span-shaped `chainData_bottom_relabel`. P≈3.*
5. **`chainData_dispatch`** interior-arm wiring: `obtain` LEAF-3's bundle at the base `v₁`-split, set
   `ends₁`, build `re` (leaf 4 bottom + the explicit corner injection), read `hρe₀` off
   `interior_hρe₀_of_baseWidening`, discharge `hgp`/`hends`/etc. via the `d=3` `hne_F₀` pattern, supply
   `hA`/`hD` via leaves 2/3/4, call `case_III_arm_realization_matrix`. The full router case-splits
   `(i:ℕ)`: `i≤1` → `chainData_split_realization` (landed floor); `2≤i` → this arm. *P≈2 once 1–4 land.*

**No phase-direction / motive / IH / contract change.** Route A confirmed end-to-end through the
dispatch modulo leaves 1–5; the wrap-edge wall is escaped, GAP-2 resolved. NEXT = leaf 1.
