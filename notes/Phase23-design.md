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
the `rigidityRows` membership predicate `Basic.lean:603–604`; the perp is genuinely-new.] **De-risk —
DONE 2026-06-20** (`i3_freshEdge_surviving_rows_mem_deRisk`, `Relabel.lean`, axiom-clean): the concrete
`span (G−v₃)` gate the abstract `i3_freshEdge_slot_mem_deRisk` deferred. **Finding: the `link`/membership
half discharges CLEANLY at the concrete level** (`cd.link` + `vtx_inj` survival of `removeVertex (vtx 3)`
+ `hingeRow_mem_rigidityRows` + `mem_hingeRowBlock_iff`), so the two surviving rows reach the concrete
candidate span **conditional on** their per-edge perps `hperp0`/`hperp1`. **The perp half remains the
genuinely-new obstruction the gate ISOLATES** (it does NOT follow from `hρe₀`, which only gives
`ρ₀ ⊥ C(q(v₀v₂))`): so the H.11 gate localizes the obstruction to the per-edge perp (route (a) degree-2
carry off `candidateRow_ac_eq_neg`, or route (b) off `chainData_bottom_relabel`) rather than failing —
the build proceeds (no STOP), with the remaining P2 step = the perp derivation, now the only un-landed half.

**(I.8.3.v) PERP-ROUTE VERDICT — the P2 perpendicularity obligation IS derivable (route (a)), but needs
ONE genuinely-new sub-lemma; route (b) is circular (recon-before-build, 2026-06-20, opus).** Settles the
two candidate routes (I.8.3) flagged, verified against **KT 2011 §6.4.2 eqs. (6.50)–(6.66)** (read
end-to-end, p. 692–697) AND the **landed `def`/`theorem` bodies** (file:line). The obligation, restated
exactly: for each surviving interior chain edge `s < (i:ℕ)−1`, prove
`ρ₀ ((ofNormals (G−vᵢ) ends qρ).toBodyHinge.supportExtensor (cd.edge s)) = 0`
(`= ρ₀ ⊥ panel(qρ(vtx s, vtx (s+1)))`, equivalently `ρ₀ ∈ hingeRowBlock (edge s)` by
`mem_hingeRowBlock_iff`, `Claim612.lean:823`). It is **NOT** discharged by `hρe₀` — confirmed against the
engine: `hρe₀` (`Arms.lean:90`) is `ρ ⊥ panel(q(a,·), q(b,·))` at the **candidate fresh pair**
`(a,b) = (vᵢ₊₁, vᵢ₋₁)`, NOT the intermediate chain panels.

  *(Q1 — what KT 6.62/6.66 actually asserts about the redundancy `r`'s perpendicularity, deciding lines.)*
  KT does **NOT** prove "`r ⊥` each intermediate chain panel" as a standalone perp. KT's mechanism (the
  deciding lines, p. 695–697): eq. (6.61) converts `R(G,pᵢ)` so its **bottom block is literally
  `R(G₁,q₁)`** via the row-correspondence eq. (6.62) ("the rows associated with `v₀v₂` in `R(G₁,q₁)`
  correspond to those associated with `v₀v₁` in `R(G,pᵢ)`", + the `vⱼvⱼ₊₁ ↔ vⱼ₋₁vⱼ` shifts); KT then
  applies the **same `λ` redundancy weights of eq. (6.52)** (`∑_{e,j} λₑⱼ R(G₁,q₁;eⱼ) = 0`) and, **by
  (6.52), "all the entries of the part of the new row vector (6.63) associated with `V∖{vᵢ}` become
  zero"** (p. 696). The surviving `R(G₁,q₁)` rows are genuine rigidity rows; the redundancy `r =
  ∑_j λ(v₀v₂)j r_j(q₁(v₀v₂))` is a fixed combination living in the `(v₀v₂)`-block. **Eq. (6.66)** —
  "*due to the fact that `vᵢ` is a vertex of degree two in `G₁` … in a manner similar to the previous
  lemma (cf. (6.44))*: `∑_j λ(vᵢvᵢ₊₁)j r_j(q(vᵢvᵢ₊₁)) = ± r`" — establishes `r` lies in the
  `(vᵢvᵢ₊₁)`-block too, hence (eq. 6.66 sentence following) "`Mᵢ` does not have full rank iff `r` is in
  the orthogonal complement of `C(Lᵢ)`". So KT's perp is a **consequence of the degree-2 two-edge
  cancellation** (eq. (6.43)→(6.44): the `vᵢ`-column of (6.52) has only the two incident blocks
  `(vᵢ₋₁vᵢ)`/`(vᵢvᵢ₊₁)`, forcing `∑λ(vᵢ₋₁vᵢ)·r + ∑λ(vᵢvᵢ₊₁)·r = 0`), **iterated along the chain**:
  `r ∈ (v₀v₂)-block ⟹ r ∈ (v₂v₃)-block ⟹ … ⟹ r ∈ (vₛvₛ₊₁)-block` for every chain edge, so `r ⊥
  C(q₁(vₛvₛ₊₁))` at every chain edge. **The perp IS true and KT-grounded** — it is exactly the iterated
  eq.-(6.44) carry. KT never names it separately because the *whole* (6.63) row-operation discharges it
  in one matrix manipulation; the Lean telescope (`wstep_foldl_hingeRow_telescope`) splits the same
  operation into named summands `hingeRow (w s)(w (s+1)) ρ₀`, which re-surfaces the per-summand perp as
  an explicit obligation. [KT p. 695–697 quoted; the 6.44 mechanism cross-checked vs the d=3 Lemma 6.10,
  p. 689–690, where eq. (6.44) `r = −∑_j λ(ac)j r_j(q(ac))` is the *single-step* version.]

  *(Q2 — does route (a) hold in the LANDED Lean? — YES, but composition is a NEW sub-lemma.)* The Lean
  carrier of eq. (6.44) is **G4d-i `acolumn_mem_hingeRowBlock_of_span_rigidityRows`** (`Relabel.lean:2242`,
  hover-verified): from `wGv ∈ span Fv.rigidityRows` + **`a` degree-2 in `Fv` with its SOLE edge
  `e_c = ac`** (`hdeg2`/`hdeg2r`: `∀ f x, Fv.IsLink f a x → f = e_c`), it gives `wGv ∘ single a ∈
  Fab.hingeRowBlock e_c`. This is the **one-edge** specialization (the `vᵢ` endpoint, whose only
  *surviving* `G−vᵢ` edge after the fresh-pair surgery is `e_c`) — it is exactly how the d=3 `M₃` `hρ_ac`
  reads the candidate perp (`Relabel.lean:2419–2430`, ONE application at `vᵢ`; `candidateRow_ac_eq_neg`
  `Claim612.lean:1194` is the column-equation eq.-(6.44) form). **It does NOT directly apply to an
  *interior* chain vertex `vₛ₊₁`**, which has **TWO** surviving `G−vᵢ` edges (`edge s = vₛvₛ₊₁` and
  `edge (s+1) = vₛ₊₁vₛ₊₂`), so the `hdeg2`/`hdeg2r` single-edge hypotheses are FALSE there. KT's eq. (6.66)
  cancellation is the genuine **two-edge** degree-2 relation: it relates the two incident blocks, giving a
  block-to-block transport, not a single-block membership. So route (a) is **mathematically true and
  KT-faithful but requires a NEW Lean sub-lemma** — the two-edge / iterated form (the analogue of G4d-i for
  an interior, degree-2-with-two-edges vertex): from `r ∈ hingeRowBlock (edge s)` (a known block membership)
  and `vₛ₊₁` degree-2 in `G−vᵢ` with edges `{edge s, edge (s+1)}`, derive `r ∈ hingeRowBlock (edge (s+1))`
  (up to ±), then induct `s = 0 … i−2` from the base `r ∈ hingeRowBlock (e₀-spliced v₀v₂)` (the W6b
  `hρe₀`-gate). **Lean-confirmed this session (`lean_run_code`): G4d-i's single-edge premise is provably
  FALSE at an interior vertex** — `¬ (∀ f x, G.IsLink f (cd.vtx ⟨s+1⟩) x → f = cd.edge ⟨s⟩)` closes from
  `cd.link ⟨s+1⟩ : IsLink (edge (s+1)) vₛ₊₁ vₛ₊₂` + `cd.edge_inj` (the second incident chain edge witnesses
  the refutation), so `acolumn_mem_hingeRowBlock_of_span_rigidityRows`'s `hdeg2`/`hdeg2r` cannot be supplied
  at `vₛ₊₁`; the new two-edge lemma is required, not a re-instantiation. **Closed form of
  the new sub-lemma** (the smallest honest P2 unit): a `hingeRowBlock`-to-`hingeRowBlock` carry
  ```
  theorem ρ₀_perp_interior_chain_edge (cd : G.ChainData n) (i : Fin cd.d) (s : ℕ) (hs : s + 1 < (i:ℕ)−1)
      (ρ₀ …) (hbase : ρ₀ ∈ (…G−vᵢ… qρ).hingeRowBlock (cd.edge ⟨s,_⟩)) :
      ρ₀ ∈ (…G−vᵢ… qρ).hingeRowBlock (cd.edge ⟨s+1,_⟩)
  ```
  via the two-edge degree-2 cancellation at `vₛ₊₁` (KT eq. (6.44) two-block form, `deg_two` field at
  `i = s+1`), iterated to give `ρ₀ ∈ hingeRowBlock (edge s)` for all `s < i−1` from the base. Then P2's
  `hperp_s` = `(mem_hingeRowBlock_iff).1` of that. ~1–2 commits, the real-math content (I.8.3 P2 estimate
  stands). [The two-edge degree-2 cancellation is NOT yet a landed lemma; G4d-i is its one-edge cousin.]

  *(Q3 — is route (b) circular? — YES, refuted as a P2 discharge.)* `chainData_bottom_relabel`
  (`Relabel.lean:1939`, the landed genuine-row `hwmem` leaf) takes `hφ : φ ∈ rigidityRows(G−v₁) ∨
  ∃ρ', (ρ' ⊥ panel(v₂v₀)) ∧ φ = hingeRow v₂ v₀ ρ'` and transports the disjunction across `(shiftPerm i)⁻¹`
  (verified the input/output types, `:1949–1972`). To use it for the P2 summand `hingeRow (vtx s)(vtx s+1)
  ρ₀`, that summand must FIRST inhabit the LEFT disjunct `∈ rigidityRows(G−v₁)` — i.e. `ρ₀ ⊥
  panel(q(vₛvₛ₊₁))` at the **base** framework — which is the SAME perp obligation moved to the base, or
  the RIGHT disjunct (a `(v₂v₀)`-block row, which the interior edge is not). So route (b) **transports a
  perp it cannot establish**: circular for P2, confirmed. (It IS the right tool for the genuine-row
  `hwmem` transport it was built for — where the base membership is supplied by the W6b gate — just not
  for manufacturing the interior-edge perp.)

  *(Q4 — VERDICT.)* **Route (a) discharges P2** (KT-faithful, the iterated eq.-(6.44) carry), **gated on
  ONE genuinely-new sub-lemma** — the **two-edge degree-2 `hingeRowBlock`-to-`hingeRowBlock` cancellation
  at an interior chain vertex** (`ρ₀_perp_interior_chain_edge` above), the honest analogue of G4d-i for a
  two-edge vertex, iterated from the W6b `hρe₀` base. **Route (b) is circular** and is NOT a P2 discharge
  (it is the landed `hwmem` transport, a different slot). This is **NOT a motive/IH/signature change and
  NOT an obstruction** — it is a buildable missing leaf *inside* option (b); the d=3 `M₃` arm never needed
  it because at `i = 2` (`m = i−1 = 1`) the single surviving row is the *reproduced* `e_b`-row whose perp
  IS `hρe₀` (so zero interior chain edges; `case_III_arm_realization_M3` `case hρGv`,
  `Relabel.lean:2527–2537`, uses `hρe₀` directly). The first honest interior-perp case is `i = 3`
  (`m = 2`): summand `hingeRow v₀v₁ ρ₀` (`edge 0`, interior vertex `v₁` deg-2) needs the new carry; summand
  `hingeRow v₁v₂ ρ₀` (`edge 1`, interior vertex `v₂` deg-2) likewise — the `i3_freshEdge_surviving_rows_mem_deRisk`
  gate (`Relabel.lean:2700`) took these as `hperp0`/`hperp1` hyps precisely because the carry was unbuilt.
  **What would resolve it:** land `ρ₀_perp_interior_chain_edge` (the two-edge cancellation), de-risked at
  `i = 3` by discharging `hperp0`/`hperp1` of `i3_freshEdge_surviving_rows_mem_deRisk` for real from the
  W6b `hρe₀`-gate + the `deg_two` field at `i = 1`/`i = 2`. **The two-edge column brick is now LANDED
  2026-06-20** (`acolumn_mem_hingeRowBlock_sup_of_span_rigidityRows`, `Relabel.lean`, axiom-clean): the
  honest two-block analogue of G4d-i — for `wGv ∈ span Fv.rigidityRows` with `a` degree-2 over its two
  surviving links `e_c = ac`/`e_d = ad`, the `a`-column lands in `hingeRowBlock e_c ⊔ hingeRowBlock e_d`
  (`span_induction` + `IsLink.right_unique`, the generator's `u=a`/`w=a` cases case-split on which edge).
  This is the route-(a) crux KT eq.(6.44) two-block step; what remains is the **iteration**
  `ρ₀_perp_interior_chain_edge` (chain it from `hρe₀` along interior vertices) + the de-risk discharge.
  **Clause (ii) honesty flag:** the prior
  (I.8.3) "two candidate routes, choose at build" framing **understated** route (a): it is not "likely,
  KT-grounded but UNVERIFIED" plug-in of `candidateRow_ac_eq_neg` — `candidateRow_ac_eq_neg`/G4d-i are the
  **one-edge** form and do **not** instantiate at an interior vertex; route (a) needs the *new* two-edge
  lemma. Naming that missing leaf (not asserting "route (a) plugs in") is the safe pin.

  **(I.8.3.v-REFUTED — 2026-06-20, row-321 adversarial build, coordinator-verified vs the landed defs.)**
  The (I.8.3.v) verdict's *closed-form signature* for `ρ₀_perp_interior_chain_edge` — the **isolated
  implication** `(hbase : ρ₀ ∈ hingeRowBlock (edge s)) → ρ₀ ∈ hingeRowBlock (edge (s+1))` over an
  arbitrary `ρ₀` — is **WRONG / unprovable as stated**. A build dispatched to land it returned BLOCKED with
  the finding (coordinator-confirmed against `hingeRowBlock e = (span {supportExtensor e})^⊥`,
  `Basic.lean:433`; the landed `acolumn_mem_hingeRowBlock_sup_of_span_rigidityRows` conclusion; `hρe₀`,
  `Realization.lean:799`): the lemma as written is **false**. Three problems:
  (1) the landed two-edge crux gives only **sup** membership `wGv ∘ single a ∈ block e_c ⊔ block e_d`, which
  decomposes as `x+y` (x⊥C_c, y⊥C_d) and does NOT yield whole-`ρ₀ ⊥ C_d`;
  (2) consecutive chain-edge panels `qρ(vₛvₛ₊₁)` vs `qρ(vₛ₊₁vₛ₊₂)` are panels of *different* vertex pairs —
  independent subspaces, so the generic per-edge perp-transport is false;
  (3) KT eq.(6.44)/(6.66) is a property of the **specific vanishing combination** `r = ∑ⱼ λ(v₀v₂)ⱼ rⱼ(q(v₀v₂))`
  (its `a`-column at the degree-2 vertex vanishes, giving `r ∈ block e_c ⟺ r ∈ block e_d` for **this** `r`),
  NOT an isolated implication valid for arbitrary `ρ₀`. The landed telescope `wstep_foldl_hingeRow_telescope`
  gives `W φ = (∑ surviving) + slot` as *linear maps* and the W9a fold gives the telescope *sum* ∈ span —
  neither exposes the individual surviving summands as span members to peel out.
  So Q1's "iterated `r ∈ block(s) ⟹ r ∈ block(s+1)`" is correct **for the specific `r`**, but the *Lean
  signature* encoding it as a generic `ρ₀`-implication with only `hbase` is unprovable. **This is the 5th
  mis-pin of this exact crux** (4× rows 263–272 + this), all the same global-accumulation-vs-isolated-per-step
  error. **The route is RE-OPENED; two candidate re-derivations** (the BLOCK's, to settle at a fresh
  global-structure-first design-pass): **(a)** a forward construction exposing each intermediate fold value
  `(foldl over the first s bodies)(hingeRow v₀v₂ ρ₀)` as a `span (F s)`-member, peeling surviving rows by
  induction **with the next frontier carried as the recursion variable** (via the landed
  `wstep_hingeRow_frontier`: `frontier = surviving + next-frontier`); **(b)** routing through the genuine
  vanishing-combination `a`-column argument (`candidateRow_ac_eq_neg`-style), which needs the explicit
  `λ`-combination data the telescope **abstracted away** (MAY force a landed-telescope signature change).
  Pick (a)/(b)/a third at the design-pass; flag-don't-force if it touches the motive/IH or the landed
  telescope. The infra bricks (`acolumn_..._sup_...`, `freshEdge_surviving_row_mem`) STAND as necessary
  scaffolding; only the isolated-implication *signature* `ρ₀_perp_interior_chain_edge` is withdrawn.

  **(I.8.3.v-PAIR — 2026-06-20, adversarial design-pass PAIR (rows 322/323, opus-vs-opus per OPUS-ONLY,
  user-authorized for this 5×-mis-pinned crux); CONVERGED on the refutation, DIVERGED on the fix; both
  flag-don't-force, both stop short of a frozen signature → USER-ADJUDICATED.)** The pair settles two things
  with HIGH confidence and surfaces one open structural question:
  - **Route (a) is DEAD — Lean-witnessed by BOTH.** The forward fold-value-as-span-member induction cannot
    supply the perp: every telescope term is a `hingeRow` sharing the single `ρ₀`, and the intermediate fold
    value `Pₛ` has a **zero column at the next frontier vertex `vₛ₊₁`** (`(hingeRow vₛvₛ₊₂ ρ₀).comp (single
    vₛ₊₁) = 0`, `hingeRow_comp_single_off`, witnessed). Feeding `Pₛ` to the two-edge crux at the degree-2
    interior `vₛ₊₁` yields `0 ∈ block e_c ⊔ block e_d` — vacuous, no constraint on `ρ₀`. The forward
    construction relocates the gap; it does not close it (route (a) = the 6th form of the mis-pin).
  - **The per-edge perp is NOT a fact KT establishes (recon B's deepest finding, KT pp.695–698 end-to-end).**
    KT eq. (6.66) is the vector **equality** `∑ⱼ λ(vᵢvᵢ₊₁)ⱼ rⱼ(q(vᵢvᵢ₊₁)) = ±r`, used ONLY to convert
    "`Mᵢ` not full rank ⟺ `r ⊥ C(Lᵢ)`" and then run the eq.-(6.67) **counting** argument (the `d+1` joins
    span dimension `D`, Lemma 2.1) to conclude **at least one `Mᵢ` IS full rank** — i.e. the per-edge perp
    is a *hypothetical in a contradiction*, NOT simultaneously true for all edges, and false in general.
    So the `hperp`/`hperp0`/`hperp1`/`hsurv` hyps **encode a claim KT never makes**; "filling" them is the
    6th pin. The d=3 `M₃` arm `case hρGv` (`Relabel.lean:2539–2608`) has **ZERO interior perp obligations**:
    at `i=2` (`m=1`) the sole surviving row is the *reproduced `e_b`-row* `hingeRow v b ρ` whose membership
    is `hρe₀` **directly** (`:2606`), and the slot is `Submodule.sub_mem`-peeled against it. The landed
    closed-form telescope `wstep_foldl_hingeRow_telescope` STANDS (true linear-map identity); only the
    membership *corollary* `wstep_foldl_freshEdge_slot_mem`'s per-edge `hsurv` decomposition is wrong.
  - **Two candidate fixes — BOTH touch a LANDED signature / IH, BOTH flagged (not frozen):**
    - **Route A (recon A): carry the eq.-(6.52) vanishing-combination witness `g` out of the W6b producer.**
      Strengthen `exists_candidateRow_bottomRows_of_rigidOn` (`Candidate.lean:404`, drops the λ-data at the
      `obtain ⟨ρ,…⟩`) / `chainData_split_w6b_gates` (`Realization.lean:771`) so `ρ₀` arrives with its `g`
      (the redundancy `r`, whose **interior columns are non-trivial**, unlike the bare `hingeRow`s); then the
      perp via the two-edge crux on `g`. **Touches live d=3 callers** (re-plumb `M₃`, re-verify
      zero-regression). Leaf-A signature MEDIUM-confidence (not pinned — recon A explicitly refused to freeze).
    - **Route B/C (recon B): abandon the per-edge `hsurv` decomposition; replicate the d=3
      `sub_mem`-of-whole-fold structure via the `htrans` block-inclusion chain induction** (IH-level redesign
      of `wstep_foldl_freshEdge_slot_mem`; drop `hperp`/`hsurv`). The surviving rows are reproduced as genuine
      candidate rows via `Fv.hingeRowBlock f ≤ Fva.hingeRowBlock f` transport, NOT a per-edge `ρ₀` perp.
  - **THE OPEN STRUCTURAL QUESTION (the linchpin between A and B/C):** at general `i ≥ 3` (`m ≥ 2`), are the
    interior surviving rows `hingeRow vₛvₛ₊₁ ρ₀` (`s = 1 … m−1`) genuinely **independent** memberships
    (→ they need the λ-witness `g`, route A) or do they **collapse** into the base-redundancy `htrans`
    transport as the d=3 `M₃` arm does (→ route B/C)? d=3 (`m=1`, only `s=0` = the base edge, perp = `hρe₀`)
    does NOT discriminate. **Coordinator note:** the interior rows `s ≥ 1` are NOT backed by `hρe₀` (which is
    perp ONLY the base spliced panel), which *leans toward genuine independence → route A* — but neither recon
    froze it, and recon B recommends a focused tie-breaker recon on collapse-vs-independent (grounded in the
    d=3 `case hρGv` structure) BEFORE any signature is frozen. **Surfaced to the user.**

  **(I.8.3.v-SETTLED — 2026-06-20, user-authorized tie-breaker recon (row 324), coordinator-scrutinized.)
  VERDICT: Route A (carry the redundancy witness out of W6b); route B/C REFUTED as circular.** The recon
  settled the linchpin: the interior surviving rows are **GENUINELY INDEPENDENT** (not a d=3-style collapse).
  Decisive grounding (Lean-/source-verified): (1) the d=3 `case hρGv` (`Relabel.lean:2596–2606`) discharges
  its single surviving row by `hρe₀` **directly** (a genuine `e_b`-row via `subset_span`, `exact hρe₀` for the
  block membership) — NOT via `htrans`; its row is the off-chain *reproduced* `(a,b)`-pair which `hρe₀`
  annihilates, structurally different from an interior chain edge. (2) d=3 (`m=1`) has only `s=0` (the
  reproduced edge) → silent on `s≥1`; the first honest interior case is `i=3` (`m=2`), where surviving rows
  `hingeRow v₀v₁ ρ₀`/`hingeRow v₁v₂ ρ₀` are NEITHER the `v₀v₂` panel `hρe₀` annihilates. (3) **Route B/C is the
  route-(b) circularity in disguise:** `htrans`'s block conjunct is forward-only `≤`, and for interior edges
  the base/candidate panels coincide (`shiftBodyFramework_htrans`'s block is `le_refl`, `Relabel.lean:1564–1570`),
  so "transport via `htrans`" reduces to the identical per-edge perp at the base — circular. So the membership
  must come from the SPECIFIC redundancy `r`/`g`, whose interior `a`-columns are non-trivial (the two-edge crux
  has content there, unlike the bare hingeRows).
  **Route A build sequence (de-risk-first, coordinator-refined ordering vs the recon's producer-first):**
  - **(A-2 de-risk — DONE 2026-06-20, zero blast radius):** the self-contained perp carrier
    `candidate_perp_two_incident_panels` + the `supportExtensor`-perp form
    `candidate_perp_two_incident_supportExtensors` (`Relabel.lean`, both axiom-clean). Takes the eq-(6.52)
    witness in the **`λ`-grouped per-edge form** (the `candidateRow_ac_eq_neg` interface: `lamAB`/`rab`,
    `lamAC`/`rac`, `grest`, + the column-vanishing `hcol`/`hrest`) as EXPLICIT hyps, and discharges the
    de-risk gate's `hperp0`/`hperp1` (and the general `freshEdge_surviving_row_mem`'s `hperp`) FOR REAL:
    the common candidate `r̂ := ∑λab•rab` is ⊥ both incident panels — ⊥ `C_c` direct (block closed under the
    combination), ⊥ `C_d` via eq.~(6.44) `candidateRow_ac_eq_neg` (`rAC = −r̂`). **Finding (resolves the
    opaque-combination sub-risk):** the `λ`-grouped form IS needed — the bare `_acolumn_zero` zero-functional
    (`Candidate.lean:557`) is too opaque, but the landed `d=3` `candidateRow_ac_eq_neg` (`Claim612.lean:1194`)
    already takes exactly the `λ`-grouped form and **applies verbatim at an interior chain vertex** (`a :=
    vₛ₊₁`, `b := vₛ`, `c := vₛ₊₂`, degree-2), so A-2 is a thin wrap of it, NOT a new column-cancellation
    proof. The pinned witness shape is therefore `candidateRow_ac_eq_neg`'s; A-1 supplies it.
  - **(A-1 — DONE 2026-06-20, axiom-clean):** strengthened the W6b producer
    `exists_candidateRow_bottomRows_of_rigidOn` (`Candidate.lean`) + `chainData_split_w6b_gates`
    (`Realization.lean`) to supply the **`candidateRow_ac_eq_neg`-shaped per-edge witness** `lamAB`/`rab`
    (`∀ j, rab j ∈ hingeRowBlock e₀`, `ρ = ∑ⱼ lamAB j • rab j`): the in-scope `r`/`lam` re-threaded via the
    per-row `Eb = map (hingeRow …).dualMap block` decomposition + `hingeRow` injectivity at distinct endpoints.
    The wrapper threads it to its output in chain order (`(b,a)` branch negates `rab → −rab`, W8 sign-swap).
    3 live callers re-plumbed (`case_III_candidate_dispatch` + `chainData_split_realization` `_`-ignore until
    the arm); full project green + lint clean, d=3 zero-regression. **The blast-radius step (B=2), landed as
    scoped.**
  - **(A-3 single-vertex composition — DONE 2026-06-20, axiom-clean, zero blast radius):**
    `freshEdge_surviving_row_mem_of_witness` (`Relabel.lean`) — at a surviving edge's interior degree-2
    vertex `vtx (s+1)` (`hsd : s+1 < cd.d`), feed the A-1 eq-(6.52) `λ`-grouped two-edge witness through A-2
    (`candidate_perp_two_incident_supportExtensors`) to discharge `freshEdge_surviving_row_mem`'s abstract
    `hperp` FOR REAL (`ρ₀ ⊥ Fva.supportExtensor (edge s)` = A-2's first conjunct), then thread to the
    `link`-half builder. **REMAINING (A-3):** the all-`i` lift (propagate the witness across the chain off
    the W6b `hρe₀` base — the iterated KT eq-(6.66) carry; each interior vertex needs its own col-vanishing
    witness, which W6b gives only at the base, the genuinely-hard piece), then the arm `chainData_relabel_arm`.
  The refuted-signature leaves `freshEdge_surviving_row_mem` (`:2833`, now superseded by `_of_witness`) + the `hsurv` form of
  `wstep_foldl_freshEdge_slot_mem` (`:3006`) are WITHDRAWN at the arm build (zero live callers); the
  closed-form telescope `wstep_foldl_hingeRow_telescope` (`:2938`) + the infra bricks + **A-2's two new
  perp-carrier lemmas STAND**. **NO motive/IH change.** Confidence HIGH on Route A + the B/C refutation.
  **A-2 de-risk DONE 2026-06-20** — the pinned witness shape is `candidateRow_ac_eq_neg`'s `λ`-grouped form
  (the `d=3` lemma applies verbatim at an interior vertex; A-2 is a thin wrap, not a new cancellation proof).

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
2. **[⚠ SUPERSEDED by (I.8.7) — the `ρ₀_perp_interior_chain_edge` route named here is the row-321-REFUTED
   isolated implication; the live all-`i` route fork (Route W vs the recommended G4d-i-PROJECTED) + the i=3
   de-risk are (I.8.7). The single-vertex A-3 composition landed via Route A; only the all-`i` lift remains.]**
   `chainData_freshEdge_surviving_row_mem` (P2, ~1–2 commits, the real math). For `s < (i:ℕ)−1`:
   ```
   theorem … (cd : G.ChainData n) (i : Fin cd.d) (s : ℕ) (hs : s + 1 < (i:ℕ)) (ends₀ q …) :
       BodyHingeFramework.hingeRow (cd.vtx ⟨s,_⟩) (cd.vtx ⟨s+1,_⟩) ρ₀
         ∈ Submodule.span ℝ (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx i.castSucc))
             (relabelled ends) qρ).toBodyHinge.rigidityRows
   ```
   crux: `ρ₀ ⊥ panel(qρ(vtx s, vtx (s+1)))` — **PERP-ROUTE SETTLED (I.8.3.v): route (a)** (the iterated
   eq.-(6.44) degree-2 carry), **NOT a `candidateRow_ac_eq_neg`/G4d-i re-instantiation** (those are the
   one-edge form, provably non-instantiable at an interior vertex; Lean-confirmed I.8.3.v), but a NEW
   two-edge sub-lemma `ρ₀_perp_interior_chain_edge` (`hingeRowBlock (edge s) → hingeRowBlock (edge (s+1))`
   via the two-edge degree-2 relation at `vₛ₊₁`, iterated from the W6b `hρe₀` base). **Route (b)
   `chainData_bottom_relabel` is CIRCULAR for P2** (it transports a base perp, cannot establish it).
   Link via `cd.link` + survival `s, s+1 < i`. **i=3 de-risk LANDED 2026-06-20**
   (`i3_freshEdge_surviving_rows_mem_deRisk`): the link/membership half is concrete-clean, so the general
   lemma's only un-landed half is the per-edge **perp** (`ρ₀ ⊥ Fva.supportExtensor (edge s)`), now routed
   through the new two-edge carry; the rest of the body = the de-risk gate's `hrow` builder, generalized
   from `i=3` to `s < i−1`. The smallest P2 step = **land `ρ₀_perp_interior_chain_edge` (the two-edge
   cancellation) + discharge `i3_freshEdge_surviving_rows_mem_deRisk`'s `hperp0`/`hperp1` from it for
   real** (the de-risk's `hp` slots, currently hyps).
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

**(I.8.6.v) [⚠ SUPERSEDED by (I.8.7) — pins the row-321-REFUTED `ρ₀_perp_interior_chain_edge`; live route fork in (I.8.7).] PERP-ROUTE settled into the P2 estimate (2026-06-20, opus).** I.8.3.v settles which of the two
flagged routes discharges the P2 perp: **route (a)** (the iterated KT eq.-(6.44) degree-2 carry — true,
KT-faithful), **gated on ONE genuinely-new sub-lemma** `ρ₀_perp_interior_chain_edge` (the two-edge degree-2
`hingeRowBlock`-to-`hingeRowBlock` cancellation at an interior chain vertex — the honest analogue of G4d-i,
which is the one-edge form and is **provably non-instantiable** at an interior vertex, Lean-confirmed). **Route
(b) `chainData_bottom_relabel` is CIRCULAR** for P2 (it transports a base perp, cannot establish it; it is the
landed `hwmem` slot, a different obligation). So P2 = land the two-edge carry + iterate from the W6b `hρe₀`
base + de-risk by discharging `i3_freshEdge_surviving_rows_mem_deRisk`'s `hperp0`/`hperp1` from it. This
**confirms** the (I.8.6) P2 estimate (~1–2 commits, real math) and the "no motive/IH/signature change, option
(b) + d=3 zero-regression stand" verdict; it **refines** the route choice (the prior "two routes, choose at
build" understated route (a)'s need for the new two-edge lemma — neither route is a plug-in of an existing
brick). Honesty flag (clause ii): naming the missing leaf `ρ₀_perp_interior_chain_edge` is the safe pin; a
"route (a) plugs in `candidateRow_ac_eq_neg`" pin would have been confident-wrong (the one-edge brick does not
fit the two-edge interior vertex).

**(I.8.7) ALL-`i` LIFT ROUTE FORK — RECON VERDICT (2026-06-20, opus read-only Plan, coordinator-scrutinized;
row 328). SUPERSEDES (I.8.4) step 2 + (I.8.6.v).** A-3's single-vertex composition
`freshEdge_surviving_row_mem_of_witness` (LANDED, row 327) discharges the interior perp at ONE vertex but takes
the eq.-(6.52)/(6.43) witness (`lamAB`/`rab`/`lamAC`/`rac`/`grest` + `hperp_ab`/`hperp_ac` + `hcol`/`hrest`) AS
HYPS; the all-`i` lift must SUPPLY that witness at each interior `s < i−1` (the `hsurv` summands of
`wstep_foldl_freshEdge_slot_mem`, `m=i−1`), and A-1's W6b producer supplies it only at the base `e₀`. The recon
(verifying the landed bodies, axiom-clean line refs below) found a FORK:
- **Route W (witness propagation — NOT recommended).** Build a producer re-deriving KT eq.-(6.24)'s redundancy
  decomposition of the SHARED `ρ₀` at each interior vertex in the candidate framework `G−vᵢ` — i.e. KT eq.-(6.66)
  as an explicit per-vertex `λ`-witness. No landed supply (grep-confirmed); a genuinely-new ~3–5-commit producer
  `exists_interior_redundancy_witness` generalizing `exists_redundant_panelRow_ab_decomposition_acolumn_zero`
  (`Candidate.lean:571`). Consumes A-3's `_of_witness` + A-2.
- **Route G4d-i-PROJECTED (RECOMMENDED — the d=3 mechanism).** The d=3 M₃ engine
  (`case_III_arm_realization_M3`, `Relabel.lean:2515`; `hρ_ac`:2582) discharges its interior perp from `hρGv`
  (the candidate's own column membership) via the ONE-edge G4d-i `acolumn_mem_hingeRowBlock_of_span_rigidityRows`
  (`:2242`) — NOT via `hcol`/`hrest`. At an interior vertex (genuinely degree-2, `ChainData.deg_two`
  `Operations.lean:1306`; both `edge s`/`edge (s+1)` survive) the one-edge form fails; the LANDED two-edge sup
  form `acolumn_mem_hingeRowBlock_sup_of_span_rigidityRows` (`:2342`) gives only `block e_c ⊔ block e_d` (the
  vacuous `=⊤` that refuted the row-318 isolated implication). The route = a per-`s` chain INDUCTION carrying
  `ρ₀ ∘ single (vtx (s+1)) ∈ block (edge s)`, SEEDED at the base by `hρe₀` and propagated by the eq.-(6.44)
  two-edge identity (a SUP-PROJECTION picking the correct summand) — using the genuinely-available `hρe₀` + `hW`
  fold output (`W φ ∈ span`) + the telescope, NOT a circular `hρGv`. **Hinges on ONE genuinely-new sup-projection
  lemma the recon could NOT find landed — FLAGGED, not pinned.**

**SMALLEST NEXT COMMIT = the i=3 DE-RISK (mandatory; decides the fork before ANY leaf signature is pinned —
the row-321 failure mode is a confident pin ahead of the de-risk).** At `i=3` (`m=2`, the first honest
two-residue case; vertices v₀…v₄, interior vertex v₁, edges `edge 0=v₀v₁`/`edge 1=v₁v₂`), confirm the interior
perp `ρ₀ ⊥ Fva.supportExtensor (edge 0)` is derivable from `hρe₀` + `hW`/the fold output + the two-edge degree-2
geometry WITHOUT the per-vertex `hcol`/`hrest`. **SUCCESS → Route G4d-i-PROJECTED** (then the `interior_perp_carry`
leaf + the `s↦s+1` induction `chainData_freshEdge_surviving_row_mem` + the arm; `_of_witness`/A-2 orphaned,
confirm-and-delete at the arm). **FAILURE** (the sup is not projectable without the full `λ`-witness) **→ Route W
forced** (`_of_witness`/A-2 STAND) — **FLAG-AND-STOP for user adjudication** (the genuinely-new-math fork).

**Orphan status is FORK-DEPENDENT** — do NOT confirm-and-delete `freshEdge_surviving_row_mem_of_witness` /
`candidate_perp_two_incident_*` until the de-risk decides (they STAND under Route W). `freshEdge_surviving_row_mem`
(the perp-half consumer — its BUILDER is LIVE under BOTH routes; only the per-edge-perp slot-peel *framing* was
withdrawn, not the lemma) + the telescope `wstep_foldl_hingeRow_telescope` + `wstep_foldl_freshEdge_slot_mem` +
`acolumn_..._sup_...` STAND under both. **NO motive/IH/contract change under either route** (`ChainData` frozen,
the `hρGv` slot KT-faithful, both routes operate BELOW the dispatch; d=3 zero-regression preserved — M₃ is the
`m=1` single-summand case, exercising neither interior leaf). P3 (`shiftSeedAdv q (i−1) = qρ` seed bridge, I.8.5)
remains orthogonal. **§(o‴)(B)'s G4d-i seed STANDS** as the recommended route's basis. The route-β "±r chain
absorbed, no lemma" framing (lines ~2008/1976) is CORRECTED: the ±r chain is absorbed at the DISPATCH/discriminator
level, but the per-candidate `hρGv` span-membership needs the iterated per-vertex degree-2 column carry (the
recommended `interior_perp_carry`), NOT a free absorption.

**(I.8.7-RESULT) i=3 DE-RISK RAN — VERDICT: FAILURE → Route W FORCED → FLAG-AND-STOP (2026-06-20,
Lean-verified, axiom-clean).** The de-risk landed as `Graph.ChainData.i3_freshEdge_interior_acolumn_sup_deRisk`
(`Relabel.lean`): from `hW : φ ∈ span Fva.rigidityRows` (the W9a fold output at candidate `i=3`,
`Fva = ofNormals (G−vtx 3) ends qρ`), the interior `vtx 1`-column `φ ∘ single (vtx 1)` lands in the **sup**
`block(edge 0) ⊔ block(edge 1)` — NOT a single block — via the landed two-edge `acolumn_..._sup_...`. This is
the strongest column projection available from `hW` alone, because at honest `i=3` the interior vertex `vtx 1`
is **genuinely degree-2** in `Fva` (both incident chain edges `edge 0=v₀v₁`/`edge 1=v₁v₂` survive `removeVertex
(vtx 3)`, endpoints `< 3`). Route G4d-i-PROJECTED's hoped single-block projection (the d=3 M₃ `hρ_ac`
one-edge mechanism) **does not exist here** — at d=3 the interior vertex is degree-**one** in the candidate
split (its 2nd incident edge links the *removed* vertex `v`, dying in `removeVertex v`, the `hdeg2` single-edge
premise of the one-edge form), which is exactly what produced the single-block landing there. So `ρ₀ ⊥ C(edge
0)` (a single-block perp) is **not separable** from the sup without the per-vertex eq.-(6.52) `λ`-witness — the
"vacuous `=⊤`" obstruction (I.8.3.v-REFUTED) now Lean-confirmed. **Route W is FORCED**: the all-`i` lift needs
the per-vertex redundancy witness (KT eq.~(6.66)) SUPPLIED at each interior vertex, via a genuinely-new producer
`exists_interior_redundancy_witness` (no landed supply, grep-confirmed) feeding
`freshEdge_surviving_row_mem_of_witness` + A-2. **This is genuinely-new math the design pinned for user
adjudication** — the coordinator/dispatch cannot authorize it as a smallest-next-commit; the next session is a
FLAG-AND-STOP awaiting the user's go-ahead on Route W's producer. Orphan status RESOLVED: `_of_witness` / A-2
`candidate_perp_two_incident_*` STAND (Route W's building blocks).

**(I.8.8) ROUTE W PRODUCER — RECON VERDICT (2026-06-20, opus read-only Plan, coordinator-scrutinized; row
330). User-adjudicated: recon Route W first. Verdict = option (a′), gated on an i=3 panel-correspondence
de-risk.** Scoping `exists_interior_redundancy_witness` (the per-vertex eq.-(6.52) witness
`freshEdge_surviving_row_mem_of_witness` consumes). The recon (source-verified the decomposition's hypotheses)
refuted the two cheap hopes and identified the one viable route:
- **Option (b) — transport the witness from A-1's base witness via the relabel — REFUTED** (consistent with the
  i=3 fork de-risk): the base supplies only the `e₀` perp; the interior perp is not extractable from `hW` + a
  base perp (the sup is vacuous `=⊤`). A relabel transports genuine *rows* (the `hwmem` slot), NOT the witness's
  `hcol`/perps.
- **Option (a-literal) — re-run the landed decomposition `exists_redundant_panelRow_ab_decomposition_acolumn_zero`
  (`Candidate.lean:571`) at the interior framework `G−vtx i` — INFEASIBLE:** that decomposition requires `h618`
  (`Gab` rigid at full rank `D(m−1)`) + `h622` (the nested-IH lower bound), BOTH keyed to the **`v₁`-split** `G₁`;
  the candidate framework `G−vtx i` is the *deleted* graph, not a rigid split, and carries neither premise. There
  is no per-interior-vertex rigid split (route β does NOT split `d` times — the candidates are role-relabels).
- **Option (a′) — RECOMMENDED (KT's actual mechanism, eqs. 6.59–6.64):** re-derive the witness at the **BASE
  split `G₁`** (where `h618`/`h622lb` ARE available — reuse A-1's exact instantiation), obtaining the
  interior-vertex witness *as it sits in `G₁`*, then transport the *conclusion* (the perp) to `Fva = G−vtx i` via
  the relabel `(shiftPerm i)⁻¹` / the `qᵢ = q∘ρᵢ` seed identity (KT 6.56). The A-2 carrier
  `candidate_perp_two_incident_supportExtensors` + `candidateRow_ac_eq_neg` are graph-free and apply verbatim, so
  the math content is entirely the witness's `hcol` + the transport. **Forces a NEW transport identity** (the
  eq.-(6.59)/(6.62) panel-correspondence at the `supportExtensor` level) + the already-flagged P3 seed bridge
  `shiftSeedAdv_eq_funLeft_shiftPerm` (I.8.5); ~3–4 commits; **NO motive/IH/contract change.**
- **Option (a″) — per-interior-vertex rigidity premise on the chain — NOT recommended:** forces a `ChainData`
  contract change + diverges from locked route β.

**SMALLEST NEXT COMMIT = the i=3 PANEL-CORRESPONDENCE DE-RISK** (before pinning any producer signature — the
row-321 discipline): prove `Fva.supportExtensor (edge s)` = the `(shiftPerm)⁻¹`-relabel-image of `G₁`'s panel at
the KT-corresponding edge (eqs. 6.59/6.62 at the `supportExtensor` level), for the single interior vertex `vtx 1`
at `i=3`. **SUCCESS** → option (a′) is buildable (the witness comes from A-1's base producer composed with the
transport); the producer + the all-`i` lift + the arm follow. **FAILURE / needs P3 first** → localizes the true
blocker before any producer signature is pinned. Orphans: none new (Route-G4d-i-PROJECTED's `interior_perp_carry`
is dead — that route is refuted by the fork de-risk). Stands: `_of_witness`/A-2/`candidateRow_ac_eq_neg`/the
telescope/the de-risk gates. Consumes (a′): the eq.-6.24 decomposition at base + the transport machinery
(`chainData_bottom_relabel`/`shiftPerm`/`shiftSeedAdv`).

**(I.8.8-RESULT) i=3 PANEL-CORRESPONDENCE DE-RISK RAN — VERDICT: SUCCESS → option (a′) BUILDABLE
(2026-06-20, Lean-verified, axiom-clean).** Landed as
`Graph.ChainData.i3_panelCorrespondence_supportExtensor_deRisk` (`Relabel.lean`): for the interior vertex
`vtx 1` at `i = 3`, the candidate framework's supporting extensor at each of the two surviving incident chain
edges equals the `v₁`-base framework's at the KT-corresponding edge —
`Fva.supportExtensor (edge 0) = G₁-base.supportExtensor e₀` and
`Fva.supportExtensor (edge 1) = G₁-base.supportExtensor (edge 2)`, where the KT correspondence is the
`shiftEdgePerm 3`-image (`edge 0 ↦ e₀` via `shiftEdgePerm_apply_edge_zero`, `edge 1 ↦ edge 2` via
`shiftEdgePerm_apply_edge_interior`). The candidate framework `Fva = ofNormals (G − vtx 3) endsσρ qρ` IS the
relabel-perm `endsσρ`/`qρ` shape (`ρ = shiftPerm 3.castSucc`, `σ = shiftEdgePerm 3`) that the landed `hwmem`
slot `chainData_bottom_relabel` produces, so the correspondence is a **direct application of the already-landed
`ofNormals_supportExtensor_relabel_perm`** (`Q'.supportExtensor f = Q.supportExtensor (σ f)`). The one residual
— the relabel lemma's base graph is `G − vtx 3`, the de-risk's base is `G − vtx 1` — is discharged by the
closing `simp only [toBodyHinge_supportExtensor, ofNormals_ends, ofNormals_normal]`: `supportExtensor` reads
only `ends₀`/`normal`, never the graph, so the two base frameworks have equal support extensors. **No
metric / Plücker step, no new transport identity needed at the `supportExtensor` level** — the eqs.~(6.59)/(6.62)
panel correspondence is `ofNormals_supportExtensor_relabel_perm` itself. So **option (a′) is buildable**: Route
W's per-interior-vertex perp transports across this `supportExtensor` coincidence (a `rw` of the de-risk identity
turns the candidate-side perp `ρ₀ ⊥ Fva.supportExtensor (edge s)` into the base-side perp at the corresponding
edge, which A-1's base witness supplies). **NEXT (after this commit): Route W's producer
`exists_interior_redundancy_witness`** — re-derive A-1's eq-(6.52) two-edge witness at the base `G₁` (where
`h618`/`h622lb` are available), then thread its perp through the panel correspondence + the flagged P3 seed
bridge to `Fva = G − vtx i`, feeding `freshEdge_surviving_row_mem_of_witness` + A-2 per interior vertex.
Generalizing the de-risk from `i = 3`/`vtx 1` to general candidate `i`/edge `s + 1 < (i : ℕ)` re-indexes the
two `shiftEdgePerm_apply_*` rewrites (the head `edge 0 ↦ e₀` only at `s = 0`; interior `edge s ↦ edge (s+1)`).
No motive/IH/contract change; d=3 (`i = 2`) zero-regression.

**(I.8.8-GENERAL) PANEL-CORRESPONDENCE GENERALIZED TO ALL-`i` — LANDED 2026-06-20, axiom-clean.** Landed as
`Graph.ChainData.panelCorrespondence_supportExtensor` (`Relabel.lean`), the general-candidate-`i` form the
producer consumes: for ANY `i : Fin cd.d` and ANY surviving interior chain edge `edge s` with
`s + 1 < (i : ℕ)`, `candidate-i.supportExtensor (edge s) = v₁-base.supportExtensor (shiftEdgePerm i (edge s))`.
The proof is the i=3 de-risk's verbatim — one `rw [ofNormals_supportExtensor_relabel_perm (shiftPerm i.castSucc)
(shiftEdgePerm i)]` + the closing `simp only [toBodyHinge_supportExtensor, ofNormals_ends, ofNormals_normal]`
(the candidate base graph `G − vtx i` vs the `v₁`-base `G − vtx 1` is irrelevant — `supportExtensor` reads only
`ends₀`/`normal`). The base-edge image resolves via `shiftEdgePerm_apply_edge_{zero,interior}`. **The i=3 gate
`i3_panelCorrespondence_supportExtensor_deRisk` is now a thin two-conjunct corollary** (`s := 0`/`s := 1` at
`i := ⟨3,_⟩`; same statement, d=3 zero-regression). The flagged `hi : 2 ≤ i` was dropped (`hsi : s+1 < i`
subsumes it). This SUPPLIES the transport identity option (a′)'s producer threads its perp across — so the
`exists_interior_redundancy_witness` build now consumes a landed `panelCorrespondence_supportExtensor` rather
than re-deriving the transport. No motive/IH/contract change.

**(I.8.8-BRIDGE) THE PER-EDGE PERP-TRANSPORT BRIDGE — LANDED 2026-06-20, axiom-clean.** Landed as
`Graph.ChainData.candidate_supportExtensor_perp_of_base` (`Relabel.lean`), the producer-facing wrapper of
`panelCorrespondence_supportExtensor`: for any `i : Fin cd.d` and any surviving interior chain edge `edge s`
(`s + 1 < (i : ℕ)`), a screw-level functional `ρ'` perp to the `v₁`-base framework's
`supportExtensor (shiftEdgePerm i (edge s))` is perp to the candidate-`i` framework's `supportExtensor
(edge s)`. The proof is two lines — `rw [panelCorrespondence_supportExtensor i s hsi]; exact hperp` (the
transport identity is an *equality* of support extensors, so the perp `rw`s straight across). This is the
shape the producer `exists_interior_redundancy_witness` threads its witness's per-row perps across: A-1's base
witness at `G₁` supplies `rab j ⊥ v₁-base.supportExtensor (shiftEdgePerm i (edge s))`, and this bridge yields
the candidate-side `hperp_ab : rab j ⊥ candidate-i.supportExtensor (edge s)` that
`freshEdge_surviving_row_mem_of_witness` (A-3) consumes. Self-contained over the landed transport identity,
zero blast radius. **NEXT (after this commit): the producer body `exists_interior_redundancy_witness`** —
re-derive A-1's eq-(6.52) two-edge witness at the base split `G₁` (where `h618`/`h622lb` are available),
thread its per-row perps through this bridge at the interior vertex `vtx (s+1)`'s two surviving incident edges
`edge s`/`edge (s+1)`, and feed `freshEdge_surviving_row_mem_of_witness` + A-2 per interior vertex (+ the
flagged P3 seed bridge `shiftSeedAdv_eq_funLeft_shiftPerm`). No motive/IH/contract change; d=3 (`i = 2`)
zero-regression.

**(I.8.9) PRODUCER-CORE RECON — the witness-DATA regrouping is the unsolved crux; (a′) was under-specified
(2026-06-20, opus read-only Plan, coordinator-scrutinized; row 334). QUALIFIES (I.8.8)/(I.8.8-RESULT): "a′
buildable" validated only the TRANSPORT/perp half.** The producer-core recon (source-verified the decomposition
body + the `hingeRow` def) localized the genuinely-hard remaining piece:
- **The consumer's witness has 3 parts; only the perp transports.** (a) the perps `hperp_ab`/`hperp_ac` —
  transport FREE via the landed `candidate_supportExtensor_perp_of_base`. (b) `hcol`/`hrest` — **FRAMEWORK-FREE**
  (`hingeRow u v r = r ∘ screwDiff u v`, `Basic.lean:490` — depends only on endpoints + screw functional, NOT
  the framework/graph), so once produced they hold at the candidate VERBATIM; NOT a transport problem, and no
  `hingeRow`/`hcol` transport analogue is needed or exists. (c) the DATA `lamAB`/`rab`/`lamAC`/`rac`/`grest` +
  the PROOF that `hcol`/`hrest` hold — **the genuinely-open piece.**
- **A-1 does NOT supply it; the eq-6.24 decomposition does NOT run at interior vertices.** A-1 gives SINGLE-edge
  data at `e₀` only; the eq-6.24 decomposition (`exists_redundant_panelRow_ab_decomposition_acolumn_zero`,
  Candidate.lean:571) is keyed to the single split edge `e₀` (`hsplit : Gab = Gv + {e₀}`) and its `acolumn`
  conclusion is `g = 0` GLOBALLY (`sub_self`, `:606`), NOT the regrouped two-edge `hcol` form. The regrouping
  (collect `g`'s terms incident to the interior degree-2 vertex `vtx(s+1)`, leaving `grest`) needs `wGv` exposed
  as an explicit EDGE-INDEXED `hingeRow` combination — it currently arrives as an opaque `span` member (`:213`).
  **This regrouping of the global redundancy `g` at each interior vertex IS the recurring 5×-mis-pinned crux**
  (the global-vs-per-vertex error, I.8.3.v-REFUTED); KT eq-6.66 (iterated eq-6.44) proves it true, but no landed
  lemma produces it.
- **THE FORK (flagged for adjudication):** **(a′-i)** expose `g` edge-grouped — an **A-1 SIGNATURE CHANGE with
  live d=3 callers** (`chainData_split_w6b_gates`/`case_III_candidate_dispatch`/`chainData_split_realization`)
  to re-plumb — + a NEW base-side "regroup-at-interior-degree-2-vertex" lemma (the eq-6.43 two-edge analogue);
  ~3–5 commits; below-dispatch (no motive/IH change) but NOT the clean instantiation (I.8.8) implied — it is
  exactly the "carry the redundancy witness `g` out of W6b" the I.8.3.v-SETTLED verdict named but never executed.
  **(a′-ii)** bypass `_of_witness`/A-2, supply `freshEdge_surviving_row_mem`'s bare `hperp` directly — but the
  base interior perp is itself the iterated eq-6.66 carry (row-321 showed it's unprovable as an isolated
  `ρ₀`-implication; needs the specific `g`-derived `ρ₀`), so it needs the SAME base regrouping content; ~3–4
  commits, orphans A-2/`_of_witness`.
- **SMALLEST NEXT COMMIT = the BASE-`G₁` interior-regrouping de-risk** at `i=3`/`vtx⟨1⟩` (before pinning the
  producer): can the base redundancy `g` (eq-6.24, at the `v₁`-split where h618/h622lb hold) be regrouped at the
  base-interior degree-2 vertex `vtx⟨1⟩` into `(ab) + (ac) + grest` with `grest` vanishing on `vtx⟨1⟩`'s column —
  i.e. is `wGv` accessible edge-grouped, and is `vtx⟨1⟩` degree-2 in `G−v₁`? SUCCESS → (a′-i) buildable;
  FAILURE → the A-1 signature change is forced regardless. **NO motive/IH/contract change either way; but (a′-i)
  forces an A-1 LANDED-SIGNATURE change (live d=3 callers) — surfaced for user adjudication.**

**(I.8.9-RESULT) BASE-`G₁` DEGREE de-risk RAN — VERDICT: the base immediate-successor interior vertex is
degree-ONE (single-block, tractable); the "degree-2 at `G−v₁`" half of the §(I.8.9) sub-question is a
mis-statement of WHICH vertex (2026-06-20, Lean-verified, axiom-clean).** Landed as
`Graph.ChainData.i3_base_interior_acolumn_single_deRisk` (`Relabel.lean` tail, the base-side mirror of the
candidate-side `i3_freshEdge_interior_acolumn_sup_deRisk`). The §(I.8.9) sub-question "is `vtx⟨1⟩` degree-2 in
`G−v₁`?" is structurally void as literally written — `vtx 1` is the *removed split apex* of `G − vtx 1`, not a
vertex of it. The de-risk-able fact is the degree of the **first surviving interior chain neighbour `vtx 2`**:
the `v₁`-removal kills `vtx 2`'s *predecessor* chain edge `edge 1 = v₁v₂` (it has the removed apex as an
endpoint), so `vtx 2` retains only its *successor* `edge 2 = v₂v₃` and is **degree-ONE** in `G − vtx 1`. The
Lean lemma proves: a span member `wGv ∈ span (G − vtx 1) rigidityRows` has its `vtx 2`-column landing in the
**single** block `block (edge 2)` (via the landed one-edge `acolumn_mem_hingeRowBlock_of_span_rigidityRows`),
NOT the obstructed two-edge sup that blocked the *candidate*-side lift (where `vtx 2` keeps both edges and is
genuinely degree-two). **VERDICT = SUCCESS for the column-projection brick at the FIRST interior vertex** — the
base behaves like the d=3 `M₃` degree-one interior, so the base regrouping at `vtx 2` threads the one-edge form
with landed infrastructure, no new two-block carry. **CAVEAT (the residual the de-risk DOES NOT clear):** this
covers only the first interior neighbour `vtx 2`; *deeper* interior vertices (`vtx 3, …`) survive `removeVertex
(vtx 1)` with BOTH chain edges, so they remain genuinely degree-two at the base, and the §(I.8.9) two-edge
regrouping crux (exposing `wGv` edge-grouped + the eq-6.43 two-edge `hcol`/`hrest` proof) still stands for them
— the FORK (a′-i vs a′-ii, the A-1 signature change) is NOT resolved by this de-risk, only narrowed (the head of
the chain is the tractable single-block case). **NO motive/IH/contract change; the A-1 signature question
remains user-adjudication-flagged** for the deeper-vertex regrouping.

**(I.8.9-A1) THE (a′-i) A-1 SIGNATURE CHANGE — LANDED 2026-06-20 (axiom-clean, full project green+lint,
salvaged WIP). User-adjudicated (a′-i).** The W6b producer `exists_candidateRow_bottomRows_of_rigidOn`
(`Candidate.lean`) now also outputs the candidate row `hρGv` in **EDGE-GROUPED** form: `∃ nGv cGv evGv uvGv
vvGv rvGv, (∀ j, Gv.IsLink (evGv j)(uvGv j)(vvGv j)) ∧ (∀ j, rvGv j ∈ hingeRowBlock (evGv j)) ∧ hingeRow (ab) ρ
= ∑ⱼ cGv j • hingeRow (uvGv j)(vvGv j)(rvGv j)`. Powered by the new general
`BodyHingeFramework.exists_edgeIndexed_combination_of_mem_span_rigidityRows` (`RigidityMatrix/Basic.lean`) —
the `Submodule.mem_span_set'` + `choose` unpacking of a `span rigidityRows` member into its carrying links +
block rows. The 2 live d=3 callers (`case_III_candidate_dispatch`/`chainData_split_w6b_gates`) `_`-ignore the
new `_hedgeGv` output; d=3 zero-regression. This is the "carry `g` out of W6b" the I.8.3.v-SETTLED verdict
named: it exposes the opaque `g`/`hρGv` so the regroup is consumable. (Coordinator-salvaged: the dispatch
produced this complete Lean WIP but returned neither LANDED nor BLOCKED — it ended its turn awaiting its own
background build; the coordinator verified all gates green + faithful and committed it, adding the notes. Row
336.) **NEXT = the base regroup-at-interior-degree-2-vertex lemma** consuming the edge-grouped `hρGv` to
produce the eq-6.43 `(ab)+(ac)+grest` witness (`hcol`/`hrest`; `g=0` makes `hcol` trivial). NO motive/IH/contract
change.

**(I.8.9-COL) THE REGROUP COLUMN FOUNDATION — LANDED 2026-06-20 (axiom-clean, full project green+lint).** The
mechanical `hrest`/`grest`-vanishing core of the base regroup lemma: `BodyHingeFramework.edgeIndexedCombination_comp_single_off`
(`Relabel.lean` tail). For an edge-indexed `hingeRow` combination `∑ⱼ cⱼ • hingeRow (uvⱼ)(vvⱼ)(rvⱼ)` whose summands
all avoid body `a` (`a ≠ uvⱼ ∧ a ≠ vvⱼ`), the `a`-column `(…).comp (single a) = 0` (proof =
`LinearMap.ext` → per-summand `hingeRow_comp_single_off` + additivity, via `LinearMap.coe_sum`/`Finset.sum_eq_zero`).
This is KT eq.~(6.43)/(6.66)'s "every edge off `a` contributes 0 to `a`'s column", framework-free, zero blast
radius — the `grest`-remainder/`hrest` obligation the A-2 carrier `candidate_perp_two_incident_supportExtensors`
/ A-3 `freshEdge_surviving_row_mem_of_witness` consume.

**(I.8.9-COL2) THE REGROUP COLUMN-ISOLATION CORE — LANDED 2026-06-20 (axiom-clean, full project green+lint).**
The complement of (I.8.9-COL): `BodyHingeFramework.edgeIndexedCombination_comp_single_eq_incident`
(`Relabel.lean` tail). For an edge-indexed `hingeRow` combination `∑ⱼ cⱼ • hingeRow (uvⱼ)(vvⱼ)(rvⱼ)`, its
`a`-column `(…).comp (single a)` EQUALS the `a`-column of the restriction to the `a`-**incident** summands
`Finset.univ.filter (fun j => a = uvⱼ ∨ a = vvⱼ)`. Proof = split the index set by incidence at `a`
(`Finset.sum_filter_add_sum_filter_not` + `LinearMap.add_comp`); the off-`a` part's `a`-column is `0` by the
off-foundation (`hingeRow_comp_single_off` per summand, the negated disjunction destructured by `not_or.mp`),
so `add_zero`. KT eq.~(6.43)'s "only the edges meeting `a` contribute to `a`'s column"; framework-free, zero
blast radius. Together (I.8.9-COL)/(I.8.9-COL2) are the column-algebra core of the regroup: `_eq_incident`
isolates the `a`-column to the incident summands, then the regroup proper splits those by the degree-2 graph
fact. **STILL NEXT = the regroup lemma proper:** with the `a`-column now isolated to the incident summands,
the remaining open piece is the **index partition** tying each incident `hρGv` summand to one of the two
incident chain edges (a degree-2 GRAPH fact) + reshaping its endpoints to the canonical `hingeRow a b` /
`hingeRow a c` form, then `hcol` from the global `g = 0` (NOT `hρGv` — `hcol`'s provenance is
`exists_redundant_panelRow_ab_decomposition_acolumn_zero`'s `sub_self`). NO motive/IH/contract change.

**(I.8.9-RECON) REGROUP-PROPER CONSUMER-INTERFACE RECON — VERDICT: NEEDS-ADJUDICATION; the regroup proper does
NOT close the consumer, the genuine open piece is the KT eq-(6.66) ±r screw-level identity (2026-06-20, opus
read-only Plan, coordinator source-verified; row 339). Caught the would-be 6th mis-pin.** After three leaves
(I.8.9-A1/-COL/-COL2) the "regroup is ~mechanical" pin was tested against the actual consumer signatures and
FAILS on the screw-level identity — the same global-vs-per-vertex face that broke the 5 prior pins.
- **The consumer needs a SHARED `ρ₀`; the regroup supplies a PER-VERTEX group.** A-3
  `freshEdge_surviving_row_mem_of_witness` (`Relabel.lean:3074-3098`) concludes
  `hingeRow (vtx⟨s⟩)(vtx⟨s+1⟩) (∑ⱼ lamAB j • rab j) ∈ span Fva.rigidityRows` — built on the **per-vertex**
  `(ab)`-group `∑ⱼ lamAB j • rab j` (`:3095-3096`). The all-`i` lift `wstep_foldl_freshEdge_slot_mem`
  (`Relabel.lean:3255-3263`) requires `hsurv : ∀ s ∈ range m, hingeRow (w s)(w s+1) ρ₀ ∈ S` and the slot row
  over the **single shared** `ρ₀` (forced by settled Fix A §(o‴)(H): per-`i` re-seed = Fix B INFEASIBLE,
  breaks KT's single-`r` existence). So the regroup must additionally prove `∑ⱼ lamAB_s j • rab_s j = ±r̂`
  (= the shared `ρ₀`) at every interior vertex — KT eq-(6.66)'s ±r carry. **No landed lemma produces this**
  (grep-confirmed; the LANDED telescope `wstep_foldl_hingeRow_telescope` is over the shared `ρ₀` and only
  expresses the slot in terms of surviving rows — it does NOT establish their membership, which still needs
  `shared ρ₀ ⊥ supportExtensor(edge s)`, the row-321-refuted isolated perp, recoverable only from the `g`
  structure via this identity).
- **What DOES match (mechanical, framework-free):** the perp half (A-2
  `candidate_perp_two_incident_supportExtensors :2472-2489` + `candidate_supportExtensor_perp_of_base :3394`)
  and the `hcol`/`hrest` half (the two landed column cores + `deg_two Operations.lean:1306` + `hingeRow_swap
  Basic.lean:535`). The interface-match check passes on these, fails ONLY on the screw-level identity —
  consistent with (I.8.8-RESULT) "only the transport/perp half validated".
- **Buildable-leaf decomposition (dependency order):** **leaf 1** `regroup_acolumn_incident_split` (the base
  regroup at a genuinely-degree-2 vertex producing `lamAB/rab`@`edge s` + `lamAC/rac`@`edge s+1` + `grest` +
  `hcol`/`hrest`) — MECHANICAL, buildable as-is from the two column cores + `deg_two` + `hingeRow_swap`; *this
  is the lemma the prompt scoped, and it IS buildable — but alone it does NOT satisfy the consumer*. **leaf 2**
  `∑ lamAB_s • rab_s = ±r̂` — GENUINELY-NEW, no producer, the crux (KT eq-6.66). **leaf 3** sign reconciliation
  on `_of_witness`/`_slot_mem` — likely `Submodule.neg_mem`-absorbable at the membership level (hingeRow linear
  in `r`, span closed under negation), to confirm; possibly a no-op, NOT necessarily an interface change.
- **DECISION PENDING (user-adjudicated): how to attack leaf 2 (the genuine crux).** (A) a KT eq-(6.66)
  source-verification recon first — read the PDF pp.696-698, adversarially pin EXACTLY how KT establishes the
  per-vertex-group = ±r̂ identity in the rigidity-matrix terms the formalization uses, before building (the
  rows-322/323 precedent for a repeatedly-mis-pinned crux); (B) build leaf 1 then attempt leaf 2 directly,
  accepting leaf 2 is the hard crux; (C) bank leaf 1 standalone now (additive, on-path) then decide leaf 2.
  NO motive/IH/contract change in any branch. Coordinator source-verified A-3's conclusion shape
  (`:3095-3098`) against this verdict.

**(I.8.9-PAIR) ADVERSARIAL RECON PAIR (opus×opus, rows 340/341) — CONVERGED: leaf 2 as pinned is the 6th
global-vs-per-vertex mis-pin; the genuine KT-6.66 mechanism is an eq-(6.44) CHAIN INDUCTION off the single base
redundancy (2026-06-20, both reads source-verified vs KT 2011 §6.4.1/§6.4.2 + the 2009 arXiv (7.44/7.66),
coordinator-scrutinized; user-adjudicated "recon first", the rows-322/323 precedent for this 5×-mis-pinned
crux).** Both independent reads returned NOT-PROVABLE-AS-PINNED / NEEDS-NEW-PREREQUISITE:
- **The pinned identity `∑ lamAB_s • rab_s = ±ρ₀` (per-vertex group = the shared head redundancy DIRECTLY) is
  the wrong target.** KT eq-(6.66)'s `±r` is NOT a per-vertex fact: it is carried by a CHAIN of `d−2` degree-2
  column cancellations (eq-(6.44) = `candidateRow_ac_eq_neg Claim612.lean:1194-1219`) off the SINGLE global
  dependency (KT eq-(6.52), = the base redundancy `r̂`), anchored at the head edge `v₀v₂` and propagated along
  the interior chain via the (6.62) row correspondence. `candidateRow_ac_eq_neg` gives only the per-vertex
  ADJACENCY relation `(ac)-group = −(ab)-group` at one vertex — NOT `= ±ρ₀`. KT p.698 ("vᵢ degree-2 in G₁ … in
  a manner similar to (6.44)") compresses exactly this telescope.
- **The genuinely-new piece = the CHAIN INDUCTION** (recon A's PREREQ-B): an induction over the interior chain,
  anchored at the base redundancy, propagating `ρ₀` (with the `±` sign) to each interior edge-group via
  eq-(6.44) at each degree-2 vertex. No landed lemma does it (the LANDED `wstep_foldl_hingeRow_telescope` is a
  DIFFERENT mechanism — telescopes a fixed-`ρ₀` row through `wstep`, never establishing group-equals-`ρ₀`).
- **Both AGREE the regroup runs at the BASE `G₁`** (where `r̂`/`hρGv` + the rigidity premises `h618`/`h622`
  live; the candidate `G − vtx i` is the *deleted* graph, no eq-(6.24) dependency there — Phase23b:444-445),
  with the resulting per-edge perp transported to the candidate via the LANDED
  `candidate_supportExtensor_perp_of_base`/`panelCorrespondence_supportExtensor` — i.e. WITHIN Route W (a′),
  NO motive/IH/contract change.
- **DIVERGENCE (residual buildable-detail to settle at the pin/build):** (1) the `hcol` at an interior vertex —
  recon A: MECHANICAL (`r̂ = hingeRow(e₀=v₀v₂)ρ₀` has `a`-column `0` for a deeper interior `a ∉ {v₀,v₂}` by
  `hingeRow_comp_single_off`, so `hcol` is free); recon B: pessimistic (the global `g` is `sub_self`-zero,
  carries no per-vertex content). Coordinator reading sides with recon A for DEEPER vertices (r̂ is a single
  e₀-row missing them); (2) the ANCHOR — how the first edge-group ties to `ρ₀` given `e₀=v₀v₂` is the removed
  split edge — is UNPINNED and is the chain induction's base case.
- **Leaf 3 (sign) confirmed MINOR** (both: `Submodule.neg_mem`, span closed under negation; not an interface
  change). The Fix-A single-shared-`ρ₀` requirement re-confirmed load-bearing (KT eq-(6.67), §(o‴)(H.1-3)).
- **SUPERSEDES the §(I.8.9-RECON) leaf-1/leaf-2/leaf-3 decomposition** (leaf 2 was the wrong object). **NEXT
  (user-adjudication surfaced):** pin the eq-(6.44) chain-induction lemma's exact signature (anchor base case +
  the `hcol` sub-question) then build, vs build the chain directly. Coordinator-scrutinized: convergence =
  high-confidence refutation; the divergence is buildable-detail, not a route fork.

**(I.8.9-SETTLE) CHAIN-INDUCTION DESIGN-SETTLE — PINNED + BUILDABLE (2026-06-20, opus read-only Plan, row 342;
user-adjudicated option α; coordinator-verified the linchpin).** Route sound; signature + anchor + `hcol` pinned;
5-leaf decomposition (~7-9 commits); NO motive/IH/contract change. Resolves the §(I.8.9-PAIR) open details:
- **ANCHOR = `v₂` (the first surviving interior vertex).** Its two `G₁`-incident edges are the spliced
  `e₀ = v₀v₂` (whose group IS `ρ₀`, coeff 1 — the redundant row) and the surviving `edge 2 = v₂v₃`. The
  `v₂`-column of the base dependency gives `group(edge 2) = −ρ₀` DIRECTLY — one application of
  `candidateRow_ac_eq_neg` (eq-6.44) at `(a,b,c)=(v₂,v₀,v₃)`. KT p.690-691/698.
- **`hcol` VERDICT (corrected 2026-06-20 — the design-settle's `∀ a` claim was the coordinator-diagnosed
  defect; do NOT re-introduce it).** The original settle claimed `hcol` "suppliable at EVERY interior vertex"
  via the global `acolumn_zero` (`∀ a`). **That is jointly contradictory with `hcomb`:** a screw functional
  on `α → ScrewSpace k` vanishing on every `single a` is `0` (`LinearMap.pi_ext`, `[Finite α]`), so
  `hcomb ∧ (∀ a, g.comp (single a) = 0) ⟹ hingeRow ab₁ ab₂ ρ₀ = 0` — the lemma would be vacuous (usable only
  at `r̂ = 0`), and the real `hρGv` caller (whose `r̂ = hingeRow(v₀v₂)ρ₀` has `v₂`-column `ρ₀ ≠ 0`) cannot
  supply `∀ a`. The conflation: KT eq-6.43 is the column-vanishing of the *global* base dependency `g`, but
  the lemma binds `g` *exposed edge-grouped as the candidate row* `hingeRow ab₁ ab₂ ρ₀` (NOT column-vanishing
  `∀ a`). **Corrected:** the lemma takes the endpoint identification `hab₁ : ab₁ = v₀` / `hab₂ : ab₂ = v₂`
  (the eq-6.52 `(v₀v₂)`-redundant-edge endpoints) and DERIVES the column-vanishing it needs only at the deeper
  step vertices `vtx (i+1)` (`i+1 ≥ 3`, off both `v₀`/`v₂` so `r̂`'s column is `0`, via
  `hingeRow_comp_single_off`); the anchor `v₂` (column `= ρ₀ ≠ 0`) is LEAF 2, which uses NO `hcol`.
- **SIGNATURE:** `interior_group_eq_baseRedundancy` — motive `P(i)`: "the `(vᵢvᵢ₊₁)`-edge group `= ±ρ₀`"
  (`2≤i≤d−1`); base `P(2)` = anchor; step `P(i)→P(i+1)` = `group(edge i+1) = −group(edge i)` from the
  `vᵢ₊₁`-column (degree-2-in-`G₁`, `deg_two_split`) + IH. CONSUMER-MATCH CONFIRMED: feeds
  `wstep_foldl_freshEdge_slot_mem`'s shared-`ρ₀` `hsurv` (via A-3 once `group = ±ρ₀`; the `±` by `neg_mem`),
  verified vs the d=3 M₃ arm (`hρGv` case over the shared `ρ`).
- **5-LEAF DECOMPOSITION (dependency order):** (1) `interiorGroup_acolumn_adjacency` — step kernel
  `group(edge i) = −group(edge i−1)` at a deeper degree-2 vertex (MECHANICAL: the 2 column cores +
  `candidateRow_ac_eq_neg` + `deg_two_split` + an `incidentGroup` index-partition; ~1-2c). (2)
  `anchor_group_eq_neg_baseRedundancy` — `group(edge 2) = −ρ₀` (genuinely-new-but-small: `v₂`'s 2nd edge is the
  spliced `e₀`, so the `(ab)`-group is `hρGv`'s LHS `ρ₀`; ~1-2c). (3) `interior_group_eq_baseRedundancy` —
  `Nat.le_induction` base=leaf2 step=leaf1 (MECHANICAL ~1c). (4) `interior_group_acolumn_eq_neg_baseRedundancy`
  — read the LEAF-3 constant value as `−ρ₀` (`hingeRow_swap` + `hingeRow_comp_single_tail` on the redundant
  base row's head body `vtx 2`); the consumer threads it through `neg_mem` + the A-2 carrier +
  `freshEdge_surviving_row_mem` at LEAF 5 (MECHANICAL ~1c). (5) arm wiring `chainData_relabel_arm` `hsurv`
  slot + the P3 seed bridge `shiftSeedAdv_eq_funLeft_shiftPerm` (~2-3c). **Genuinely-new content = leaves
  1+2; the rest is assembly over landed infra.**
  **LEAF 1 `Graph.ChainData.interiorGroup_acolumn_adjacency` LANDED 2026-06-20** (`CaseIII/Relabel.lean` tail,
  axiom-clean; full project green + lint, d=3 zero-regression, zero callers). Built cleaner than pinned: the
  "group" = the orientation-agnostic `a`-column restriction `(·).comp (single a)` (a screw functional), so the
  conclusion is `(edge i-group).comp (single a) = −(edge (i−1)-group).comp (single a)` and
  `candidateRow_ac_eq_neg`'s re-orientation is subsumed by the column restriction; the partition is via
  `edgeIndexedCombination_comp_single_eq_incident` (only `a`-incident summands) + `deg_two_split` +
  `IsLink.eq_and_eq_or_eq_and_eq`/`edge_inj` (disjoint incident split).
  **LEAF 2 `Graph.ChainData.anchor_group_acolumn_eq_baseRedundancy` LANDED 2026-06-20** (`CaseIII/Relabel.lean`
  tail, axiom-clean; full project green + lint, d=3 zero-regression, zero callers). The base case `P(2)`, in
  the same `v₂`-column form as LEAF 1 per the shape-check note (i) — built in the orientation-agnostic
  column-isolation form `(edge 2-group).comp(single v₂) = (hingeRow ab₁ ab₂ ρ₀).comp(single v₂)`, the `= ±ρ₀`
  reading deferred to LEAF 4 (cleaner than the pinned `= −ρ₀`; sidesteps committing to `e₀`'s orientation). At
  the first surviving interior vertex `vtx 2` — degree-ONE in `G_v = G − vtx 1` (the de-risked `hdeg1`, arm-
  supplied; `i3_base_interior_acolumn_single_deRisk`) — the edge-grouped candidate identity `hcomb`
  (`∑ⱼ cⱼ • hingeRow … = hingeRow ab₁ ab₂ ρ₀`, A-1's output) forces it: `_eq_incident` reduces the `v₂`-column
  to the `v₂`-incident summands, `hdeg1` (incident ⟹ edge 2) + `hinc_e2` (edge 2 ⟹ incident, `IsLink` uniq at
  `edge 2 = v₂v₃`) collapse it to the `edge 2`-group, `hcomb` reads the candidate identity on the column. The
  `e₀ = v₀v₂`-group contributing `ρ₀` (shape-check note (i)) is then the trivial `hingeRow_comp_single_tail`
  reading of the RHS at LEAF 4.
  **LEAF 3 `Graph.ChainData.interior_group_eq_baseRedundancy` LANDED 2026-06-20** (`CaseIII/Relabel.lean`
  tail, axiom-clean; full project green + lint, d=3 zero-regression, zero callers). The `Nat.le_induction`
  (base=leaf2 step=leaf1) + the note-(ii) endpoint-column bookkeeping, done as two new framework-free
  primitives: `BodyHingeFramework.hingeRow_comp_single_endpoint_flip` (a single hinge's two
  endpoint-columns negate: `col@y = −col@x`, via `hingeRow_comp_single_tail` + `hingeRow_swap`) and its
  edge-group form `edgeGroup_comp_single_endpoint_flip` (per-summand flip via `IsLink` uniqueness at the
  chain edge, summed over the group). **Built cleaner than the pinned `= ±ρ₀`:** the motive is "every
  interior edge-group's TAIL column is the SAME constant `(hingeRow ab₁ ab₂ ρ₀).comp(single v₂)`"
  (`2≤i≤d−1`) — the step's LEAF-1 sign and the head→tail flip's sign cancel (`rw [hadj, hflip, neg_neg]`),
  so the column value is constant along the chain; the `±ρ₀` reading is deferred to LEAF 4.
  **CORRECTED 2026-06-20 (coordinator-diagnosed defect):** the as-landed signature took the global
  `hcol : ∀ a, g.comp(single a) = 0` ALONGSIDE `hcomb` — jointly contradictory (forces `r̂ = 0`; see the
  `hcol` VERDICT bullet above), so the lemma was vacuous + un-instantiable by the real caller. `hcol ∀a`
  REPLACED by `hab₁ : ab₁ = v₀` / `hab₂ : ab₂ = v₂`; the step now DERIVES the column-vanishing at the deeper
  step vertex `vtx (i+1)` INTERNALLY from `hcomb` + `hingeRow_comp_single_off` (off both `v₀`/`v₂`, `r̂`'s
  column is `0`). Same name, same conclusion; LEAF 1/2 + the two flip primitives unchanged. Instantiability
  re-confirmed in tree (caller supplies `hab₁`/`hab₂` by `rfl rfl` after re-orienting `e₀`). `Nat.le_induction`
  auto-generalized the `i < cd.d` bound into the IH.
  **LEAF 4 `Graph.ChainData.interior_group_acolumn_eq_neg_baseRedundancy` LANDED 2026-06-20**
  (`CaseIII/Relabel.lean` tail, axiom-clean; full project green + lint, d=3 zero-regression, zero callers).
  The consumer reading: every interior chain edge-group's tail column `= −ρ₀` (`2 ≤ i ≤ d−1`). Proof =
  `rw [interior_group_eq_baseRedundancy]` (LEAF 3's constant value) then read the redundant base row
  `hingeRow ab₁ ab₂ ρ₀` on its head body `ab₂ = vtx 2` — `hingeRow_swap` rewrites to `hingeRow ab₂ ab₁ (−ρ₀)`,
  tail column at `ab₂` is `−ρ₀` (`hingeRow_comp_single_tail`, `ab₂ ≠ ab₁` by `vtx_inj`). Two-line, no
  friction.
  **LEAF 5 `hρGv`-SLOT CORE `Graph.ChainData.chainData_freshEdge_slot_mem` LANDED 2026-06-20**
  (`CaseIII/Relabel.lean` tail, axiom-clean; full project green + lint, d=3 zero-regression, zero callers).
  The general-`i` lift of the abstract `i=3` gate `i3_freshEdge_slot_mem_deRisk` to the *concrete* fold
  framework — LEAF 5's hard, isolatable core, decoupled from the `refine case_III_arm_realization` slot
  bookkeeping. For interior `i : Fin (cd.d+1)` (`1 ≤ i`, `i < cd.d`), from the W6b base redundancy `hφ`
  (`hingeRow (vtx 0)(vtx 2) ρ₀ ∈ span (G − v₁) rows`) + the per-edge perps `hperp` (`ρ₀ ⊥
  Fva.supportExtensor (edge s)`, `s+1 < i` — the P2 LEAF 4 + A-2 supply), the slot row `hingeRow vᵢ₋₁
  vᵢ₊₁ ρ₀` reaches `span (ofNormals (G − vᵢ) ends (shiftSeedAdv q (i−1))).rigidityRows`. Assembly: the
  seed-advancing fold `shiftBodyListAsc_foldl_mem_span_rigidityRows` gives `W φ ∈ span`; the closed-form
  telescope `wstep_foldl_freshEdge_slot_mem` peels the slot off `W φ` minus the `m = i−1` surviving rows,
  each from `freshEdge_surviving_row_mem`. Glue: telescope vertex fn `w s = vtx (min s d)` (= `vtx` on the
  touched range `s ≤ i+1 ≤ d`), `hinj` from `vtx_inj`, `hbodies` matching `shiftBodyListAsc` to the
  telescope `List.ofFn` shape, `hFvaEq`/`hFvaStart` framework identifications. KT eq.~(6.66) concrete; `i=2`
  is the `M₃` `case hρGv`.
  **PER-EDGE PERP DISCHARGE `Graph.ChainData.chainData_freshEdge_perp_of_witness` LANDED 2026-06-20**
  (`CaseIII/Relabel.lean` tail, axiom-clean; full project green + lint, d=3 zero-regression, zero callers).
  The rung between the A-2 carrier and the LEAF 5 core's abstract `hperp`: for a single surviving chain edge
  `s` (`s+1 < cd.d`), from the eq.~(6.52) `λ`-grouped two-edge witness at the interior degree-2 vertex
  `vtx (s+1)` (the same `lamAB`/`rab`/`lamAC`/`rac`/`grest` + `hperp_ab`/`hperp_ac` + `hcol`/`hrest` interface
  as `freshEdge_surviving_row_mem_of_witness`, A-3) PLUS the regroup identity `hρ₀` (`∑ⱼ lamAB j • rab j = ρ₀`,
  the LEAF 4 `group = ±ρ₀` reading), it discharges `ρ₀ ⊥ Fva.supportExtensor (edge s)` — the EXACT `hperp s`
  shape `chainData_freshEdge_slot_mem` consumes. Proof = A-2 `candidate_perp_two_incident_supportExtensors`'s
  `.1` rewritten by `hρ₀`. So the arm `chainData_relabel_arm` supplies the slot core's `hperp` per surviving
  edge from the witnesses (no abstract perp left). **NEXT = leaf-5 ASSEMBLY** (arm `chainData_relabel_arm`:
  `refine case_III_arm_realization` per-`i`; `hwmem ← chainData_bottom_relabel`; `hρGv ←
  chainData_freshEdge_slot_mem` with its `hperp` from `chainData_freshEdge_perp_of_witness` (the witness from
  A-1 + the LEAF 4 regroup `interior_group_acolumn_eq_neg_baseRedundancy`), seed via P3
  `shiftSeedAdv_eq_funLeft_shiftPerm`, orientation via `hingeRow_swap`).
  **Coordinator shape-check note (leaf-2/3 consistency, 2026-06-20).** Leaf 1 landed in `a`-column form
  `(group i).comp(single vᵢ) = −(group i−1).comp(single vᵢ)` — both groups' columns at the SHARED vertex
  `vᵢ = vtx i.castSucc` — which is (±) the screw functional, so it is equivalent to the pinned screw-functional
  kernel (benign reformulation, gate+axiom-clean, NOT a deviation). Consequence for the downstream leaves:
  (i) **leaf 2 (anchor) lands naturally in the SAME `a`-column form** `(group(edge 2)).comp(single v₂) = −ρ₀`
  (the `v₂`-column of `g=0`: `ρ₀ + (edge2-group).comp(single v₂) = 0`, the `e₀`-group contributing `ρ₀`); keep
  it `a`-column for chainability. (ii) **leaf 3 (induction) must additionally relate each edge-group's TWO
  endpoint-columns** (`(group i).comp(single vᵢ)` ↔ `(group i).comp(single vᵢ₊₁)`, a per-edge sign from
  `hingeRow`'s head-vs-tail column) to chain leaf-1@`i` with leaf-1@`i+1` — the orientation bookkeeping leaf 1
  deferred (mechanical, but real; the "leaf 3 MECHANICAL ~1c" estimate now includes it). (iii) the
  screw-functional `group(edge s) = ±ρ₀` the consumer wants is recovered at **leaf 4** (the `±`/`neg_mem`
  there absorbs the column-sign). Net: same plan, the orientation sign relocated leaf-1→leaf-3/4.

**(I.8.10) i=3 EDGE-ALIGNMENT DE-RISK — RAN, VERDICT: Q2-with-a-twist; the per-summand transport is a
clean BIJECTIVE re-index (NOT a re-grouping); the candidate-level edge-grouped transport leaf decomposes
into three buildable sub-leaves.** **⚠ T-1/T-2/T-3 DECOMPOSITION SUPERSEDED by §(I.8.11):** the de-risk
anchor `i3_candidateBlock_transport_deRisk` is correct, but the T-1/T-2/T-3 *family transport* it spawned
is MIS-TARGETED against the landed consumer (the `hcomb` RHS / `hrv` framework pin incompatible levels).
The correct route does NOT transport the family — see §(I.8.11) for the verdict + corrected route + T-1/T-2's
orphaned-for-the-arm fate. (Retained below for the anchor's still-valid block-correspondence verdict.)
(2026-06-21, opus; anchor lemma `i3_candidateBlock_transport_deRisk`
LANDED axiom-clean + warning-clean + lint-clean; full project green).** Settles the row-352 GAP-FOUND gap
and the flagged subtlety (A-1's base summand edges `ev j` are arbitrary `G−v₁`-links, not
`shiftEdgePerm`-images). Verified against the **landed bodies** (file:line below), NOT the prior prose.

  *(The gap, re-confirmed against the landed source.)* `chainData_freshEdge_perp_of_baseRedundancy`
  (`Relabel.lean:4311–4343`, LANDED) consumes its edge-grouped data through exactly THREE hypotheses:
  **(h1)** `hlink : ∀ j, G.IsLink (ev j)(uv j)(vv j)` — `G`-links, framework-free; **(h2)** `hcomb :
  (∑ⱼ c j • hingeRow (uv j)(vv j)(rv j)) = hingeRow (vtx 0)(vtx 2) ρ₀` — an equation of
  `Module.Dual ℝ (α → ScrewSpace k)` functionals, **framework-free**; **(h3)** `hrv : ∀ j, rv j ∈
  Fva.hingeRowBlock (ev j)` at the **CANDIDATE** `Fva = ofNormals (G−vᵢ) ends qρ` — **the ONLY
  framework-bound hypothesis**. A-1 `exists_candidateRow_bottomRows_of_rigidOn` (`Candidate.lean:400–445`)
  supplies the edge-grouped form (its lines 439–445) at the **BASE** `ofNormals Gv ends q` (Gv = G−v₁): a
  family `(nGv, cGv, evGv, uvGv, vvGv, rvGv)` with `∀ j, Gv.IsLink (evGv j)(uvGv j)(vvGv j)`, `∀ j, rvGv j ∈
  (ofNormals Gv ends q).hingeRowBlock (evGv j)`, and `hingeRow (ab) ρ = ∑ⱼ cGv j • hingeRow …`. So h2/h1
  are base-level; h3 is the level mismatch. The `evGv j` come from `mem_span_set' + choose`
  (`Basic.lean:622–637`) — they are **arbitrary `Gv`-links**, NOT `shiftEdgePerm`-images. [Source-verified
  A-1's `∃`-tail + `exists_edgeIndexed_combination_of_mem_span_rigidityRows`'s `choose` provenance.]

  *(Q1/Q2/Q3 VERDICT = Q2-with-a-twist — the non-alignment is a NON-ISSUE.)* The block correspondence holds
  for **EVERY** edge: `ofNormals_supportExtensor_relabel_perm` (`Relabel.lean:63–71`) gives
  `Fva.supportExtensor f = (base).supportExtensor (shiftEdgePerm i f)` for arbitrary `f` (the base graph is
  irrelevant — `supportExtensor` reads only `ends`/`normal`, never the graph), and `hingeRowBlock F e =
  (span {F.supportExtensor e})ᗮ` (`Basic.lean:431–433`). Hence (LANDED de-risk
  `i3_candidateBlock_transport_deRisk`, `Relabel.lean` tail): `r ∈ (base).hingeRowBlock f ⟹ r ∈
  Fva.hingeRowBlock ((shiftEdgePerm i).symm f)` — a 3-line `rw` + `simpa`. So A-1's h3 at the base edge
  `evGv j` is **exactly** the candidate h3 at `(shiftEdgePerm i).symm (evGv j)`: a **BIJECTIVE re-labelling
  of the SAME summands** (none dropped/split/merged), NOT the re-grouping the row-321 family feared.
  **Why the arbitrary `evGv j` are harmless downstream:** the chain induction LEAVES 1–4
  (`interiorGroup_acolumn_adjacency:3680`, `anchor_group_acolumn_eq_baseRedundancy:3781`,
  `interior_group_eq_baseRedundancy:3936`, `interior_group_acolumn_eq_neg_baseRedundancy:4017`) are
  **framework-free** and group summands by **FILTERING** `ev j = cd.edge ⟨i⟩` — non-chain-edge summands
  contribute `0` to the relevant `a`-column via the degree-2 closure `deg_two_split` + `_eq_incident`. The
  ONLY framework-bound consumer, `edgeGroup_acolumn_mem_block` (`:3592`), needs h3 at the candidate, which
  the bijective re-index supplies. So the "do the base summand edges align with chain-edge `shiftEdgePerm`
  images?" question is answered: **they need NOT align — the transport is clean per-summand regardless.**
  [Lean-verified: `i3_candidateBlock_transport_deRisk` axiom-clean (`propext`/`Classical.choice`/`Quot.sound`
  only), warning-clean, lint-clean, full project green.]

  *(THE NEXT BUILDABLE COMMIT + the transport-leaf decomposition.)* The genuinely-new leaf
  `chainData_candidateRow_edgeGrouped_transport` is **buildable as 3 sub-leaves** (none a motive/IH/contract
  change; the chain `G`-links + the relabel are landed-brick instantiations, the block transport is the
  de-risked anchor). It must produce the candidate-level `(c, ev, uv, vv, rv, hlink, hrv, hcomb)` that
  `chainData_freshEdge_perp_of_baseRedundancy` (h1/h2/h3) consumes, from A-1's base output:
  - **T-1 `…_edgeGrouped_transport_blocks`** (the de-risked half, ~1c). Re-index A-1's edge family by
    `evGv' j := (cd.shiftPerm i.castSucc) ... ` — actually the CANDIDATE-side `ev` stays the summand-carrying
    `G−vᵢ`-links and the BLOCK transports per-summand: `hrv_cand j : rvGv j ∈ Fva.hingeRowBlock (evGv' j)`
    via `i3_candidateBlock_transport_deRisk` (general-`i` form), where `evGv' j = (shiftEdgePerm i).symm
    (evGv j)`. SIGNATURE: `(cd) (i) (the A-1 base family + `hrv_base`) → ∀ j, rvGv j ∈ Fva.hingeRowBlock
    ((shiftEdgePerm i).symm (evGv j))`. **De-risked: it is the all-`i` lift of `i3_candidateBlock_transport_deRisk`**
    (drop the `i := 3`/single-`f` specialization to general `i`/`∀ j`). TRANSPORT, no new math.
  - **T-2 `…_edgeGrouped_transport_comb`** (relabel of `hcomb`, ~1c). Carry A-1's base combination identity
    `hingeRow (ab) ρ = ∑ⱼ cGv j • hingeRow (uvGv j)(vvGv j)(rvGv j)` across the
    `(funLeft (shiftPerm i.castSucc).symm).dualMap` relabel to the candidate orientation `hingeRow (vᵢ₋₁)(vᵢ₊₁)
    ρ₀ = ∑ⱼ cGv j • hingeRow (relabelled endpoints) (rvGv j)`, EXACTLY as `chainData_bottom_relabel`
    (`:1939–1972`) carries genuine rows (the `dualMap` is linear, distributes over `∑` + `•`). The endpoint
    relabel `uvGv' j := (shiftPerm i.castSucc).symm (uvGv j)` makes the candidate `hcomb`'s RHS match the
    re-indexed `hlink_cand`. The `G`-links T-3 supplies. SIGNATURE: the `dualMap`-image of A-1's `hcomb`
    equals the candidate edge-grouped form. TRANSPORT (landed-brick instantiation of the `dualMap`-over-sum
    distribution).
  - **T-3 `…_edgeGrouped_transport_links`** (the `G`-links, ~½c). The candidate-side summand links are
    `G`-links of the re-indexed/relabelled endpoints; `Gv.IsLink (evGv j)(uvGv j)(vvGv j)` (A-1) ⟹ via
    `removeVertex_isLink` + the `shiftBodyGraph`/`splitOff_isLink_shiftRelabel_iff` graph-iso (LANDED) the
    `G.IsLink (evGv' j)(uvGv' j)(vvGv' j)` that h1 wants. (Or, since h1 is just `G.IsLink`, lift each base
    `Gv`-link to a `G`-link by `removeVertex_isLink.mp .1` — the simplest form if the re-indexed endpoints
    coincide on `G`-links.) TRANSPORT/bookkeeping.
  Then the arm `chainData_relabel_arm` feeds T-1/T-2/T-3's outputs to
  `chainData_freshEdge_perp_of_baseRedundancy` per surviving edge, supplying its `hperp` to
  `chainData_freshEdge_slot_mem`'s `hperp` slot, with `hwmem ← chainData_bottom_relabel`, seed via P3
  `shiftSeedAdv_eq_funLeft_shiftPerm`, orientation via `hingeRow_swap` (the d=3 M₃ `case hρGv` shape,
  re-indexed). **NET: the transport leaf is 3 buildable TRANSPORT sub-leaves (~2–3c) + the arm assembly
  (~1–2c); ~3–5c total to the arm, then CHAIN-2c-iii `chainData_dispatch`.** NO motive/IH/contract change
  anywhere. **CLAUSE (ii) HONESTY:** the de-risk found NO genuinely-new-math fork — Q3's feared re-grouping
  does NOT arise (the block correspondence holds for arbitrary edges, so the bijective re-index suffices).
  The only residual flag is **P3** (`shiftSeedAdv_eq_funLeft_shiftPerm`, the fold-seed = engine-seed bridge,
  §(I.8.5)) — LANDED 2026-06-20 (`Phase23b` landed-inventory), so it is NOT an open obstruction. The arm is
  now mechanical-given-T-1/T-2/T-3.

**(I.8.11) ROUTE-SETTLING RECON — VERDICT: the (I.8.10) T-1/T-2/T-3 decomposition is MIS-TARGETED against
the LANDED consumer; the CORRECT route is base-level edge-grouping + a single scalar perp transport; T-1/T-2
ARE ORPHANED-FOR-THE-ARM (2026-06-21, opus; CONFIRMS the coordinator's row-357-triage finding; all claims
Lean-verified against the landed bodies via 4 throwaway probes that each compiled axiom-clean + warning-clean,
then reverted — docs-only, no Lean landed).** This is the 2nd level/shape mismatch on this arm (row-352 was
the 1st). Verified against the **landed `def`/`theorem` bodies** (`Relabel.lean` consumer `:4311`; A-1
`Candidate.lean:400`; `shiftPerm`/`shiftEdgePerm` `Induction/Operations.lean:1468`/`:2018`; d=3 dispatch
`Realization.lean:268`; M₃ arm `Relabel.lean:2515`; slot `:4136`; `freshEdge_surviving_row_mem` `:3019`) and
**KT 2011 §6.4.2 eqs. (6.60)–(6.67) read end-to-end** (p. 696–698, pdf p. 50–52), NOT the prior prose.

  *(Q-A — CONFIRMED, the mismatch is real.)* The consumer `chainData_freshEdge_perp_of_baseRedundancy`
  (`Relabel.lean:4311`) consumes its family through THREE hyps simultaneously pinned at INCOMPATIBLE levels:
  `hcomb` is **framework-free** with RHS HARDCODED `hingeRow (vtx 0)(vtx 2) ρ₀` (the BASE-vertex spliced row;
  `:4322`, fed verbatim to LEAF-4 `interior_group_acolumn_eq_neg_baseRedundancy` `:4334` whose `ab₁/ab₂ = vtx
  0/vtx 2` is rigid), while `hrv : ∀ j, rv j ∈ Fva.hingeRowBlock (ev j)` is at the **CANDIDATE** `Fva = ofNormals
  (G−vᵢ) ends qρ`. Feeding the **re-indexed family** (T-1/T-2): T-1 gives `hrv` at candidate-block of the
  re-indexed edge `(shiftEdgePerm i).symm (evGv j)` ✓, but T-2's `hcomb` LHS becomes `hingeRow (σ.symm v₀)(σ.symm
  v₂) ρ₀` with `σ = shiftPerm i.castSucc` — and **Lean-verified** `σ.symm v₀ = v₀` (`shiftPerm_inv_apply_vtx_off`
  m=0) but `σ.symm v₂ = v₁` (`shiftPerm_inv_apply_interior` j=1, holds ∀ `i ≥ 2`) → T-2 LHS = `hingeRow v₀ v₁ ρ₀`
  ≠ consumer's `hingeRow v₀ v₂ ρ₀`. Feeding A-1 **un-relabelled**: `hcomb`/`hlink` match directly, but `hrv` then
  demands candidate-block at the SAME un-re-indexed edge `evGv j` — and the only landed correspondence
  (`ofNormals_supportExtensor_relabel_perm` `:63`) is `candidate.supp f = base.supp (σ_e f)` (a DIFFERENT edge),
  so candidate-block(`evGv j`) = base-block(`σ_e(evGv j)`) ≠ A-1's base-block(`evGv j`). So neither feeds the
  consumer; T-1/T-2 (the row-354 decomposition) ARE mis-targeted. **Refutations actively checked + dissolved:**
  (b) the consumer is genuinely applied at deep candidate `i` (`2 ≤ i ≤ d−1`) where σ moves v₂ — NOT only where
  σ fixes v₂; (c) the splice `e₀` is NOT relabel-invariant — `shiftEdgePerm`'s edge cycle is `[edge 0, e₀, edge
  i, edge 1, …]`, so `e₀` MOVES (`shiftEdgePerm i e₀ = edge i`); (d) the W9a-fold route does NOT bypass the perp
  leaf — at general `d` the fold's `hsurv` needs the per-edge perp at EACH surviving edge (the genuinely-new P2,
  §(I.8.3)), unlike d=3 M₃'s single `e_b` row off `hρe₀` — so the perp leaf is load-bearing.

  *(Q-B — the CORRECT route, ALL FOUR STEPS Lean-verified buildable.)* **KT works entirely at the BASE `(G₁,q₁)
  = ofNormals (G−v₁) ends q`** (the recon's key source finding): eqs. (6.62)/(6.66)/(6.67) express the redundancy
  `r`, the carry `∑ λ rⱼ(q(vᵢvᵢ₊₁)) = ±r` (6.66), and ALL panels `Πᵢ = Π_{G₁,q₁}(vᵢ₊₁)` (6.67) in the SINGLE base
  framework; the candidate `pᵢ` enters ONLY through the row-correspondence iso `ρᵢ` (6.62), never as a separate
  `ofNormals (G−vᵢ)` framework. So the Lean architecture's choice to state the per-edge perp at a separately-
  relabelled candidate `Fva` is what creates the level-mix. The correct route:
  - **STEP 1 — base perp (NO new lemma): the EXISTING consumer instantiated at base index `i := ⟨1⟩`.** With `i =
    ⟨1⟩`, `Fva = ofNormals (G−v₁) ends q` = the base, so `hrv` is A-1's `hrvGv` DIRECTLY, `hcomb`/`hlink`/`hdeg1`
    are A-1's outputs DIRECTLY — NO transport. Produces `ρ₀ ⊥ (base).supportExtensor (edge t)` for any `2 ≤ t <
    d`. **[Probe-verified: `chainData_freshEdge_perp_of_baseRedundancy h3 ⟨1,_⟩ t … hlinkGv hrvGv hcombGv hdeg1`
    type-checks axiom-clean.]** The consumer's "candidate-vs-base" framing was a RED HERRING — its free
    `ends`/`qρ` make it a base-level leaf; the candidate instantiation was the wrong call site.
  - **STEP 2 — scalar perp transport (ONE new ~10-line lemma): base perp@`edge(s+1)` → candidate perp@`edge s`.**
    `candidate.supp(edge s) = base.supp(shiftEdgePerm i (edge s))` (`ofNormals_supportExtensor_relabel_perm`),
    `shiftEdgePerm i (edge s) = edge(s+1)` (interior step `shiftEdgePerm_apply_edge_interior`, `1 ≤ s, s+1 < i`),
    + supportExtensor graph-independence (G−vᵢ ≡ G−v₁ on `ends`/`q`). **[Probe-verified axiom-clean.]**
  - **STEP 2′ — the `s = 0` branch: candidate perp@`edge 0` ⟸ base perp@`e₀` = A-1's `hρe₀`.** `shiftEdgePerm i
    (edge 0) = e₀` (`shiftEdgePerm_apply_edge_zero`), so the splice-panel annihilation A-1 already supplies (`hρe₀`,
    `Candidate.lean:419`) IS the `s=0` base perp. **[Probe-verified axiom-clean.]** (`s=1` routes through STEP 2 at
    `t=2`.)
  - **STEP 3 — compose per surviving edge `s` (`s+1 < i`): STEP 1 at `t := s+1` (or STEP 2′ at `s=0`) → STEP 2 →
    candidate perp@`edge s` → feeds `chainData_freshEdge_slot_mem`'s `hperp s` (`:4148`).** The index range matches:
    the slot consumes `hperp s` for `s+1 < i` (`hsurv`, `:4211`), and `s+1 < i ≤ d−1` gives `2 ≤ s+1 < d` ✓ for the
    base leaf; `s ∈ {0,1,…}` all covered (s=0 via STEP 2′, s≥1 via STEP 2).

  **STEP 2 LANDED 2026-06-21** as `chainData_freshEdge_perp_transport_base_to_candidate` (`Relabel.lean`,
  axiom-clean). The shipped form takes the base perp at an arbitrary graph `Gb` (supportExtensor is
  graph-independent, so STEP 1's `G−v₁` perp feeds directly), and merges the `s=0`/`s≥1` branches by an
  `if s = 0 then e₀ else edge (s+1)` on the hypothesis edge (`rcases Nat.eq_zero_or_pos s` in the proof).

  **SIGNATURE (as landed; the original recon sketch below merged the branches by `match s` — the `if` form
  shipped instead):**
  ```
  theorem ChainData.chainData_freshEdge_perp_transport_base_to_candidate
      [DecidableEq α] [DecidableEq β] (cd : G.ChainData n) (i : Fin cd.d) (hi : 1 ≤ (i:ℕ))
      (s : ℕ) (hs1i : s + 1 < (i:ℕ)) {ends₀ : β → α × α} {q : α × Fin (k+2) → ℝ}
      {ρ₀ : Module.Dual ℝ (ScrewSpace k)}
      (hbase : ρ₀ ((ofNormals (G−vtx i.castSucc) ends₀ q).toBodyHinge.supportExtensor
                 (if s = 0 then cd.e₀ else cd.edge ⟨s+1,_⟩)) = 0) :
      ρ₀ ((ofNormals (G−vtx i.castSucc) [σρ-relabelled ends₀] [σ-relabelled q]).toBodyHinge.supportExtensor
            (cd.edge ⟨s,_⟩)) = 0
  ```
  (in the arm, the `if`-branch's base perp comes from STEP 1 / `hρe₀`; the candidate-framework `ends`/`qρ` are the
  arm's `endsσρ`/`qρ` — coincide via P3 `shiftSeedAdv_eq_funLeft_shiftPerm` with the slot's `shiftSeedAdv q (i−1)`).

  *(Q-C — T-1/T-2's fate: ORPHANED-FOR-THE-ARM, confirm-and-delete.)* `chainData_candidateRow_edgeGrouped_transport_blocks`
  (T-1, `Relabel.lean:4427`) and `chainData_candidateRow_edgeGrouped_transport_comb` (T-2, `:4464`) implement a
  PER-SUMMAND family transport (whole `(c, ev, uv, vv, rv)` re-indexed/relabelled). The correct route never
  transports the family — the edge-grouping runs at the base (STEP 1), and only the SINGLE scalar perp transports
  (STEP 2). So T-1/T-2 feed nothing in the correct route. Their underlying ANCHOR
  `i3_candidateBlock_transport_deRisk` (`:4383`) and `ofNormals_supportExtensor_relabel_perm` (`:63`) STAND
  (STEP 2 reuses the SAME relabel identity, applied once to a scalar). **Disposition: confirm-and-delete T-1/T-2
  at the arm-build commit** (`git grep` zero non-test callers expected once the arm lands STEP 2); the anchor +
  relabel identity are NOT deleted. T-3 (`…_transport_links`, never built) is **mooted** — the correct route's
  `G`-links are the base leaf's (A-1's `hlinkGv`), no re-indexed candidate links needed.

  **CLAUSE (ii) HONESTY.** NO motive/IH/contract change: STEP 1 reuses the LANDED consumer unchanged (different
  call site only); STEP 2 is one new transport lemma (~10 lines, two probe-verified branches); the slot/arm
  signatures are untouched. The consumer `chainData_freshEdge_perp_of_baseRedundancy` is **NOT modified** — its
  hardcoded `(vtx 0, vtx 2)` RHS is CORRECT (it is exactly KT's base redundancy `r = ∑ λ rⱼ(q(v₀v₂))`); the bug
  was the WIRING decision to call it at the candidate index. NO genuinely-new-math fork (STEP 2 is bookkeeping over
  the landed relabel identity). **NET to the arm: ~1c (STEP 2 lemma) + the arm assembly (~1–2c) = ~2–3c**, down
  from (I.8.10)'s "3 sub-leaves + assembly", because the family transport (T-1/T-2/T-3) is eliminated, not built.

**(I.8.12) HOLISTIC ARM-ARCHITECTURE RECON — VERDICT: the `hφ` seam is REAL (3rd touch of the v₂-relabel /
member-mapping wall); the engine slots ALL cohere on selector; the reconciliation needs a SLOT-CORE
DECISION — FLAG-DON'T-FORCE (2026-06-21, opus; every load-bearing claim Lean-verified against the landed
bodies via 6 throwaway probes, each compiled, reverted — docs-only, no Lean landed).** Triggered by the
`hφ` seam `chainData_relabel_arm_hρGv` exposed (the 3rd selector/relabel mismatch after rows 352/358). The
coordinator's Lean-grounded triage is **CONFIRMED, not refuted**. Verified against `chainData_relabel_arm_hρGv`
(`Relabel.lean:4625`), the slot core `chainData_freshEdge_slot_mem` (`:4136`) + its fold
`shiftBodyListAsc_foldl_mem_span_rigidityRows` (`:1785`) + single-step gate
`funLeft_dualMap_sub_acolumn_seedAdvance_mem_span_rigidityRows` (`:1201`), A-1 (`Candidate.lean:400`), the
engine `case_III_arm_realization` (`Arms.lean:72`), `chainData_bottom_relabel` (`:1939`),
`ofNormals_supportExtensor_relabel_perm` (`:63`), `rigidityRows_ofNormals_relabel` (`:647`), the shift-action
lemmas (`Operations.lean:1468`/`:2018`).

  *(R-1 — the slot core's selector-fixing is INTRINSIC to KT 6.62 as implemented, NOT a session-#19 artifact.)*
  The fold `shiftBodyListAsc_foldl_mem_span_rigidityRows` uses ONE selector throughout: `hφ`'s start framework
  `shiftBodyFrameworkAsc 0 ends q = ofNormals (G−v₁) ends q` and the conclusion
  `shiftBodyFrameworkAsc (i−1) ends q = ofNormals (G−vᵢ) ends qρ` share `ends`; the SEED advances `q → qρ`
  (KT 6.62 = seed-advance + the leading `funLeft (shiftPerm i)` of the `wstep` product, NOT a per-step selector
  relabel). [Lean-verified: the fold's docstring "selector `ends` is fixed (so the gate's `hends'_off` is
  `rfl`)" matches the body.] The single-step gate ALLOWS `ends ≠ ends'` (off the two moved edges) but the fold
  fixes it. Could the fold start at `ends₀` and arrive at `endsσρ`? NO — the member would transform through
  `(funLeft (shiftPerm i))^{i−1}` (the inverse cycle), landing the start member at `hingeRow (σ⁻¹ v₀)(σ⁻¹ v₂)
  ρ₀`, AND the foldl's `htrans`/`hrec` over the intermediate graphs `G−vₛ₊₁` need the FIXED selector to record
  them. So `hφ@endsσρ` is genuinely forced by the architecture.

  *(R-2 — `hingeRow v₀ v₂ ρ₀ ∈ span (ofNormals (G−v₁) endsσρ q)` is the WALL; none of (i)–(iv) is a clean
  build.)* The seam framework is the BOTTOM graph `G−v₁`, RELABELLED selector `endsσρ`, BASE seed `q` — a
  HYBRID that appears NOWHERE else (it is purely the fold's start slot; `git grep` confirms no landed lemma
  *concludes* a membership in it). A-1 supplies the same literal member `hingeRow v₀ v₂ ρ₀` at `ends₀` (same
  graph, same seed, DIFFERENT selector). Why each route fails:
  - **(i) call A-1 at `endsσρ`:** A-1's row is `hingeRow (endsσρ e₀).1 (endsσρ e₀).2 ρ`, and `endsσρ e₀ =
    (vtx(i−1), vtx(i+1))` [Lean-verified: `shiftEdgePerm i e₀ = edge i`, `ends₀(edge i) = (vtx i, vtx(i+1))`,
    `σ⁻¹ vtx i = vtx(i−1)`, `σ⁻¹ vtx(i+1) = vtx(i+1)`] — NOT `hingeRow v₀ v₂ ρ₀`. Wrong member.
  - **(ii) the candidate's own redundancy:** same as (i) — the splice in the relabelled framework is at
    `(vtx(i−1), vtx(i+1))`, not `(v₀, v₂)`.
  - **(iii) a span-membership transport of the FIXED member `v₀v₂`:** `ofNormals_supportExtensor_relabel_perm`
    gives `(hybrid).supp f = (base).supp (σ_e f)` [Lean-verified] — so the hybrid's blocks are a `σ_e`-permutation
    of A-1's. But transporting the edge-grouped `hcomb` (A-1's `hingeRow v₀ v₂ ρ₀ = ∑ⱼ cⱼ hingeRow uⱼ vⱼ rⱼ`,
    `rⱼ ∈ (base).block(eⱼ)`) needs each `rⱼ ∈ (hybrid).block(eⱼ) = (base).block(σ_e eⱼ)` — the WRONG edge
    (A-1 gives `block(eⱼ)`, not `block(σ_e eⱼ)`). This is the SAME member/edge wall the refuted T-1/T-2
    family transport (I.8.10) hit, and the same `funLeft σ⁻¹`-maps-the-member wall the d=3 `mem_span_…_relabel`
    (`:822`) was *superseded* for (W9a strips the relabel-image post hoc, but only for the single candidate row,
    not a fixed base member). [Lean-verified `σ⁻¹ v₀ = v₀`, `σ⁻¹ v₂ = v₁` for `i ≥ 2` → any apparatus transport
    lands on `hingeRow v₀ v₁ ρ₀`, the WRONG member.] Unlike the PERP (a single support-extensor scalar `= 0`,
    graph-independent → STEP-2 transports cleanly), `hφ` is a row-SPAN membership and does NOT transport member-free.
  - **(iv) change the slot core to start at `ends₀`, transport selector internally:** = R-1's NO (the fold's
    member would mis-map at the start, and the intermediate-graph recording needs the fixed selector). The
    candidate-TOP variant (fold at `ends₀` → `ofNormals (G−vᵢ) ends₀ qρ`, then bridge `ends₀ → endsσρ`) ALSO
    fails: `ends₀` does NOT record `G−vᵢ`'s interior links (it records `G−v₁`'s), so the `G−vᵢ` fold is ill-formed.

  *(R-3 — the engine slots ALL cohere on `(endsσρ, qρ)`; the mismatch is NOT among slots, it is engine-vs-A-1.)*
  `case_III_arm_realization` (`Arms.lean:74,91,96`) binds `hρGv` AND `hwmem` at the SAME `ofNormals Gv ends q`,
  with `hends_ea`/`hends_eb` (`:78`) + `hLn`/`hgab`/`hρgate`/`hρe₀` (`:86–90`) all reading the same `ends`/`q`.
  The arm's `(ends, q) = (endsσρ, qρ)` is FORCED by the `hwmem` leaf `chainData_bottom_relabel`, whose conclusion
  (`:1960–1972`) is at `ofNormals (G−vᵢ) endsσρ qρ` (the genuine-row transport lands there). So every engine slot
  reading `ofNormals Gv ends q` coheres on `(endsσρ, qρ)` by construction — NO incoherence among slots. The
  `hrec`-over-`G` for `endsσρ` IS satisfiable (the conjugate selector `endsσρ = σ⁻¹∘ends₀∘σ_e` records `G`'s
  chain links via the coupled edge/vertex cycle — [Lean-verified: `endsσρ(edge 1) = (v₁, v₂)` records
  `edge 1 = v₁v₂` correctly]; an early "second seam" worry on this DISSOLVED). The 3rd recurrence is NOT a
  systematic slot incoherence — it is the ONE structural fact that the SLOT-CORE FOLD wants the base redundancy
  at the relabelled-selector framework `endsσρ` (its conclusion's selector), while A-1 (KT's argument) produces
  it at the un-relabelled `ends₀` (KT works ENTIRELY at the base `(G₁,q₁)`, candidate enters only via the
  row-iso `ρᵢ` — §(I.8.11) Q-B). The slot core's selector-fixed fold is what re-introduces the candidate selector
  into the BASE redundancy — exactly the level-mix the perp's STEP-1-at-base eliminated, here un-eliminable
  because `hφ` is a span membership, not a scalar perp.

  **VERDICT — FLAG-DON'T-FORCE (the decision for user adjudication).** `hφ@endsσρ` is genuinely required by the
  current slot core and is NOT obtainable from A-1's `hφ@ends₀` by any landed-apparatus transport (the
  member-mapping wall; 3rd touch). There is NO clean buildable transport leaf — a confident "STEP-2-analogue for
  `hφ`" pin would be the 4th mismatch. **Two honest routes, neither a clean instantiation; the user picks:**
  - **ROUTE α (slot-core re-architecture, the KT-faithful fix; est. ~2–4c, recon-first).** Restate the slot core
    `chainData_freshEdge_slot_mem` to consume A-1's `hφ@ends₀` (the base redundancy at the un-relabelled base
    selector) and run the fold so the BASE redundancy stays at `ends₀` while only the *transported* rows pick up
    the relabel — i.e. fold the selector relabel INTO the per-step transport (the single-step gate already permits
    `ends ≠ ends'`), threading `ends₀ → endsσρ` across the `i−1` steps in lockstep with the seed advance. This
    matches KT 6.62 honestly (the relabel `ρᵢ` is applied step-by-step, NOT pre-applied to the base redundancy)
    and eliminates the hybrid framework. RISK: the per-step member-mapping must be re-tracked (the telescope
    LEAF-1–4 closed form assumes the fixed-selector fold); needs a recon-before-build on whether the closed-form
    telescope survives a relabelling fold. This is the genuinely-new piece, NOT bookkeeping.
  - **ROUTE β (accept the hybrid as a hypothesis; est. ~1c to defer, pushes the decision to ENTRY/dispatch).**
    Keep `chainData_relabel_arm_hρGv`'s `hφ@endsσρ` as a carried hypothesis (as landed), and discharge it at the
    dispatch/ENTRY where the chain's base realization is in scope — IF the hybrid `ofNormals (G−v₁) endsσρ q` can
    be shown rigid there (then A-1 re-derives, but at the wrong member per R-2(i), so this ALSO needs a
    member-bridge — likely circular). LIKELY DEAD; recorded for completeness.
  **RECOMMENDATION: ROUTE α**, opened with a recon-before-build pass on the telescope-under-relabelling-fold
  (whether LEAF-1–4's closed form `wstep_foldl_hingeRow_telescope` survives a non-fixed selector). The d=3 M₃
  arm does NOT exercise this (`i=2`, single surviving edge, no general fold, no `hφ` slot — the M₃ `hρGv` goes
  through W9a on the single candidate row directly), so it is a strict general-`d` obligation; zero-regression
  holds.

  **CLAUSE (ii) HONESTY.** This NAMES an open slot-core decision; it does NOT pin a transport leaf. `chainData_relabel_arm_hρGv`
  AS LANDED is a CORRECT lemma (it takes `hφ@endsσρ` + `hrec@endsσρ` as honest hypotheses, both satisfiable in
  principle) — it is NOT vacuous and NOT wrong; the open question is purely how the SHELL discharges its `hφ`
  slot. No motive/IH/contract change either way. The slot core's `hφ@endsσρ` hardcodes the BASE-vertex member
  `hingeRow (vtx 0)(vtx 2) ρ₀` at the candidate-selector framework — base-member-at-candidate-selector is the
  precise cross-grain. **NET: the arm shell is NOT a mechanical assembly; it is gated on the ROUTE-α slot-core
  decision (a recon-first ~2–4c), not the ~1–2c "M₃-template bookkeeping" the prior *Hand-off* assumed.**

**(I.8.13) ROUTE-α DESIGN-SETTLE — the central telescope-survival question is ANSWERED (it survives:
the telescope is selector-free); ROUTE α decomposes into buildable leaves with exact signatures; the
make-or-break is one genuinely-new `shiftEndsAdv` selector-advancing fold, NOT the telescope (2026-06-21,
opus; ROUTE α USER-CONFIRMED over β this session; every load-bearing claim Lean-verified against the
landed bodies via 4 `lean_run_code` probes — PROBE 1/2/3 each compiled `success:true` warning-clean apart
from a cosmetic long-line, PROBE 4 the target signature type-checked under `sorry`; docs-only, no Lean
landed).** Verified against the landed `def`/`theorem` bodies: telescope `wstep_foldl_hingeRow_telescope`
(`Relabel.lean:3187`), slot-mem corollary `wstep_foldl_freshEdge_slot_mem` (`:3255`), foldl core
`wstep_foldl_mem_span_rigidityRows` (`:1338`), the seed-fixed fold `shiftBodyListAsc_foldl_mem_span_rigidityRows`
(`:1785`), the single-step gate `funLeft_dualMap_sub_acolumn_seedAdvance_mem_span_rigidityRows` (`:1201`),
the slot core `chainData_freshEdge_slot_mem` (`:4136`), surviving-row builder `freshEdge_surviving_row_mem`
(`:3019`), the seed accumulator `shiftSeedAdv` (`:1711`) + its bulk identity `shiftSeedAdv_eq_funLeft_shiftPerm`
(`:4097`), the arm slot `chainData_relabel_arm_hρGv` (`:4625`).

  *(a) THE CENTRAL QUESTION — does the LEAF-1–4 closed-form telescope survive a non-fixed-selector fold?
  ANSWER: YES, TRIVIALLY — the telescope is selector-free / framework-free / graph-free.* The genuinely-new
  worry (I.8.12 left open) DISSOLVES on reading the landed statement. `wstep_foldl_hingeRow_telescope`
  (`:3187–3194`) is a **pure linear-map identity over `(w : ℕ → α)`**: `(foldl wstep) (hingeRow (w 0)(w 2) ρ₀)
  = (∑_{s<m} hingeRow (w s)(w (s+1)) ρ₀) + hingeRow (w m)(w (m+2)) ρ₀`. It mentions **no `ends`, no framework,
  no `ofNormals`, no graph** — only `BodyHingeFramework.wstep`/`hingeRow` linear maps and the finite-range
  injectivity `Set.InjOn w (Set.Iic (m+2))` (the P1 fix is ALREADY landed — the dead `Function.Injective (ℕ→α)`
  is gone; I.8.2's blocker is resolved in tree). **[PROBE 1: the telescope applies verbatim to the bare
  `w`-fold — `success:true`.]** A selector is NOT part of the telescope; therefore changing the fold's selector
  per-step cannot disturb it. The selector enters EXCLUSIVELY at the *membership* layer — `hφ@(F 0)`,
  `hsurv@(F s)`, conclusion`@(F m)` in `wstep_foldl_freshEdge_slot_mem` (`:3255`, abstract over `S`) — never
  in the telescope algebra. So I.8.12's RISK ("the per-step member-mapping must be re-tracked; the telescope
  assumes the fixed-selector fold") is FALSE as stated: the telescope makes NO selector assumption. **The
  real make-or-break is one level up: the *membership* fold `shiftBodyListAsc_foldl_mem_span_rigidityRows`,
  which currently FIXES the selector — restating it to advance the selector is ROUTE α's genuinely-new leaf.**

  *(b) WHY the membership fold currently fixes the selector, and why the foldl core does NOT force it.* The
  seed-fixed fold `shiftBodyListAsc_foldl_mem_span_rigidityRows` (`:1785`) takes a **single `ends`** (`:1787`)
  used at BOTH the `hφ` start framework `shiftBodyFrameworkAsc (s:=0) ends q` (`:1790`) and the conclusion
  `shiftBodyFrameworkAsc (s:=(i−1)) ends q` (`:1794`); its docstring says outright "the selector `ends` is
  **fixed** (so the gate's `hends'_off` is `rfl`)" (`:1779–1780`). This is a CHOICE of that lemma, NOT a
  constraint of the machinery: the foldl core `wstep_foldl_mem_span_rigidityRows` (`:1338`) takes an
  **arbitrary per-step framework family `F : ℕ → BodyHingeFramework k α β`** — `hφ@(F 0)`, conclusion`@(F
  bodies.length)`, and the per-step `hstep` constrains only graph-links / degree-2 closures / `hingeRowBlock`
  monotonicity, NEVER that `F s` and `F (s+1)` share a selector. **[PROBE 2: `#check` confirms `F : ℕ →
  BodyHingeFramework` is the only framework input — no fixed-selector hypothesis.]** And the single-step gate
  `funLeft_dualMap_sub_acolumn_seedAdvance_mem_span_rigidityRows` (`:1201`) takes **two distinct selectors
  `ends ends'`** (`:1203`), input membership at `ends` (`:1209`), output at `ends'` (`:1219`), agreeing only
  off the two moved edges `edge(s+1)`/`edge(s+2)` (`hends'_off`, `:1204`). **[PROBE 3: the gate type-checks fed
  two genuinely-different selectors — confirms `ends ≠ ends'` permitted, clause-(i) mandate satisfied.]** So
  the per-step apparatus is ALREADY selector-advancing-ready; only the two convenience wrappers
  (`shiftBodyListAsc_foldl_mem…` and `shiftBodyFrameworkAscTotal`) collapse it to one selector.

  *(c) THE ROUTE-α FIX — fold the selector relabel INTO the per-step advance, mirroring `shiftSeedAdv`.* The
  seed already advances per-step: `shiftSeedAdv q : ℕ → (seed)` (`:1711`, `Q 0 = q`, `Q(s+1) = Q s ∘ swap`)
  with the bulk identity `shiftSeedAdv q (i−1) = q ∘ shiftPerm i` (`shiftSeedAdv_eq_funLeft_shiftPerm`, `:4097`,
  = P3). ROUTE α adds the **exact selector analogue**: a selector accumulator `shiftEndsAdv` advancing
  `ends₀ → endsσρ` one swap per step, with `shiftEndsAdv ends₀ 0 = ends₀` (so A-1's `hφ@ends₀` matches the
  start) and `shiftEndsAdv ends₀ (i−1) = endsσρ` (so the conclusion is the engine's relabelled selector,
  UNCHANGED from the landed arm). The per-step selector swap is the gate's `ends'`-vs-`ends` move; the bulk
  identity is the selector cousin of P3. The base redundancy `hφ` then stays at the **un-relabelled `ends₀`**
  (= A-1's genuine output, eliminating the hybrid wall R-2 identified), while only the *transported* fold output
  picks up the relabel — KT-6.62-faithful (the iso `ρᵢ` applied step-by-step, never pre-applied to the base
  redundancy). **[PROBE 4: the proposed selector-advancing fold signature — `selAdv : ℕ → β → α × α`, input
  `@selAdv 0`, output `@selAdv (i−1)` — type-checks under `sorry`.]** Crucially, the slot core's CONCLUSION
  framework (`G−vᵢ, endsσρ, qρ`) and the surviving-row perp framework are **UNCHANGED**: the perp half
  (STEP 1∘STEP 2 = `chainData_freshEdge_slot_perp`, LANDED) is at the final selector `endsσρ` already, so it is
  untouched. ONLY the `hφ` input selector moves `endsσρ → ends₀`.

  *(d) EXACT RESTATED SIGNATURES.*

  **Leaf A (genuinely-new) — the selector accumulator** (`Operations.lean`, beside `shiftSeedAdv`):
  ```
  noncomputable def Graph.ChainData.shiftEndsAdv [DecidableEq α] [DecidableEq β]
      (cd : G.ChainData n) (ends₀ : β → α × α) : ℕ → β → α × α
    | 0       => ends₀
    | (s + 1) => fun e => let p := cd.shiftEndsAdv ends₀ s e
                          ((cd.shiftSeedSwap s) p.1, (cd.shiftSeedSwap s) p.2)   -- relabel endpoints by the per-step swap
  ```
  (the per-step swap is `shiftSeedSwap s = swap (vtx(s+2)) (vtx(s+1))`, `:1695`, the SAME swap the seed uses —
  so selector and seed advance in lockstep). **Leaf A-bulk — the P3 selector cousin** (`Relabel.lean`):
  ```
  theorem Graph.ChainData.shiftEndsAdv_eq_relabel [DecidableEq α] [DecidableEq β]
      (cd : G.ChainData n) (ends₀ : β → α × α) (i : Fin cd.d) (hi : 1 ≤ (i:ℕ)) :
      cd.shiftEndsAdv ends₀ ((i:ℕ) - 1)
        = fun e => ((cd.shiftPerm i.castSucc).symm (ends₀ (cd.shiftEdgePerm i e)).1,
                    (cd.shiftPerm i.castSucc).symm (ends₀ (cd.shiftEdgePerm i e)).2)
  ```
  (RHS = the arm's `endsσρ` verbatim, `Relabel.lean:4666–4668`; proof = the `shiftSeedAdv_eq_funLeft_shiftPerm`
  template at `:4102–4113`, the `(i−1)`-fold swap product = `shiftPerm i.castSucc` via
  `shiftPerm_eq_prod_map_swap_shiftBodyListAsc`, but acting on the selector's endpoint pair through
  `shiftEdgePerm` on the edge argument — RISK noted in (e)). **N.B.** the selector relabel composes the per-step
  vertex swaps on the *output endpoints* AND advances the *edge argument* via `shiftEdgePerm`; (e) flags this
  edge-vs-vertex coupling as the one unverified algebraic step.

  **Leaf B (restate, genuinely-new proof) — the selector-advancing membership fold** (`Relabel.lean`, replaces
  the seed-fixed `shiftBodyListAsc_foldl_mem_span_rigidityRows` OR a sibling beside it):
  ```
  theorem Graph.ChainData.shiftBodyListAsc_foldl_mem_span_rigidityRows_selAdv [DecidableEq α]
      (cd : G.ChainData n) (i : Fin cd.d) (ends₀ : β → α × α) (q : α × Fin (k+2) → ℝ)
      (hrec : ∀ s f x y, G.IsLink f x y →                          -- recording at EACH advanced selector
        cd.shiftEndsAdv ends₀ s f = (x, y) ∨ cd.shiftEndsAdv ends₀ s f = (y, x))
      {φ : Module.Dual ℝ (α → ScrewSpace k)}
      (hφ : φ ∈ Submodule.span ℝ
        (cd.shiftBodyFrameworkAsc (s := 0) _ (cd.shiftEndsAdv ends₀ 0) q).rigidityRows) :  -- = ends₀ at s=0
      ((cd.shiftBodyListAsc i).foldl (fun T b => (BodyHingeFramework.wstep b.1 b.2.1 b.2.2).comp T)
          LinearMap.id) φ
        ∈ Submodule.span ℝ
            (cd.shiftBodyFrameworkAsc (s := (i:ℕ)-1) _ (cd.shiftEndsAdv ends₀ ((i:ℕ)-1)) q).rigidityRows
  ```
  Proof = the landed `:1797–1811` template, but feeding the foldl core a framework family
  `F s = ofNormals (G−vₛ₊₁) (shiftEndsAdv ends₀ s) (shiftSeedAdv q s)` (selector AND seed both advancing), and
  discharging each step's gate with `ends := shiftEndsAdv ends₀ s`, `ends' := shiftEndsAdv ends₀ (s+1)` — the
  per-step `hends'_off` is `shiftEndsAdv_succ` restricted off the two moved edges (NOT `rfl` anymore; the
  genuinely-new proof obligation). **[PROBE 4 confirms the signature is well-formed.]**

  **Leaf C (restate) — the slot core** (`chainData_freshEdge_slot_mem`, `:4136`): change the `hφ`/`hrec`/`hperp`
  signature so `hφ` is consumed at `shiftEndsAdv ends₀ 0 = ends₀` (NOT a single `ends`), and the conclusion +
  the per-edge `hperp` are at `shiftEndsAdv ends₀ ((i:ℕ)-1) = endsσρ`:
  ```
  theorem Graph.ChainData.chainData_freshEdge_slot_mem_selAdv [DecidableEq α]
      (cd : G.ChainData n) (i : Fin (cd.d+1)) (hi : 1 ≤ (i:ℕ)) (hid : (i:ℕ) < cd.d)
      (ends₀ : β → α × α) (q : α × Fin (k+2) → ℝ)
      (hrec : ∀ s f x y, G.IsLink f x y →                          -- per-step recording (Leaf B's hrec)
        cd.shiftEndsAdv ends₀ s f = (x, y) ∨ cd.shiftEndsAdv ends₀ s f = (y, x))
      {ρ₀ : Module.Dual ℝ (ScrewSpace k)}
      (hφ : BodyHingeFramework.hingeRow (cd.vtx ⟨0,_⟩) (cd.vtx ⟨2,_⟩) ρ₀ ∈
        Submodule.span ℝ (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx ⟨1,_⟩))
          ends₀ q).toBodyHinge.rigidityRows)                       -- ← AT ends₀ NOW (A-1's genuine output)
      (hperp : ∀ s, (hs : s + 1 < (i:ℕ)) → ρ₀ ((PanelHingeFramework.ofNormals
          (G.removeVertex (cd.vtx ⟨(i:ℕ),_⟩)) (cd.shiftEndsAdv ends₀ ((i:ℕ)-1))   -- ← endsσρ, unchanged
            (cd.shiftSeedAdv q ((i:ℕ)-1))).toBodyHinge.supportExtensor (cd.edge ⟨s,_⟩)) = 0) :
      BodyHingeFramework.hingeRow (cd.vtx ⟨(i:ℕ)-1,_⟩) (cd.vtx ⟨(i:ℕ)+1,_⟩) ρ₀
        ∈ Submodule.span ℝ (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx ⟨(i:ℕ),_⟩))
            (cd.shiftEndsAdv ends₀ ((i:ℕ)-1)) (cd.shiftSeedAdv q ((i:ℕ)-1))).toBodyHinge.rigidityRows
  ```
  Proof = the landed `:4156–4227` body, with `hfold := …shiftBodyListAsc_foldl_mem_span_rigidityRows_selAdv`
  (Leaf B) instead of the seed-fixed fold, and the `hFvaStart` reduction `shiftEndsAdv ends₀ 0 = ends₀` via
  `shiftEndsAdv` `rfl`. The telescope (`wstep_foldl_freshEdge_slot_mem`) and the surviving-row builder
  (`freshEdge_surviving_row_mem`, at the final `endsσρ`) are CALLED UNCHANGED.

  *(e) HOW `chainData_relabel_arm_hρGv` RE-THREADS (`:4625`).* The arm's `hφ` hypothesis (`:4649–4653`) drops
  its relabelled-selector wrapper and becomes `hφ@ends₀` — i.e. the arm takes A-1's genuine output
  `hingeRow (vtx 0)(vtx 2) ρ₀ ∈ span (ofNormals (G−v₁) ends₀ q)` DIRECTLY (no transport, no member-mapping
  wall). The `refine cd.chainData_freshEdge_slot_mem_selAdv …` call (replacing `:4687`) passes `ends₀` (NOT
  `endsσρ`); the `case hφ` becomes `exact hφ` after `shiftEndsAdv ends₀ 0` `rfl`-reduces to `ends₀` (the
  landed `:4690–4693` `shiftSeedAdv_zero`-style reduction); the `case hperp` is UNCHANGED (the perp is already
  at `endsσρ = shiftEndsAdv ends₀ (i−1)` via Leaf A-bulk `shiftEndsAdv_eq_relabel`, so
  `chainData_freshEdge_slot_perp` feeds it verbatim, `:4694–4699`). The conclusion framework is identical
  (the engine's `endsσρ`/`qρ`), so the arm shell + the engine `case_III_arm_realization` call are unchanged.
  Net arm-signature change: ONE hypothesis selector (`endsσρ → ends₀` on `hφ`); the `hrec` slot upgrades to
  the per-step form (Leaf B's `hrec`, satisfiable because `shiftEndsAdv ends₀ s` records `G`'s links at every
  step — the conjugate-selector recording R-3 confirmed `endsσρ` satisfies, now needed at each intermediate `s`).

  *(f) BUILDABLE LEAVES IN DEPENDENCY ORDER (each one line; the next build dispatch is mechanical).*
  1. **`shiftEndsAdv`** (`Operations.lean`, def + `_zero`/`_succ` `rfl` lemmas) — the selector accumulator
     (Leaf A); ~1 commit, mirrors `shiftSeedAdv` (`:1711–1722`).
  2. **`shiftEndsAdv_eq_relabel`** (`Relabel.lean`) — the bulk identity `shiftEndsAdv ends₀ (i−1) = endsσρ`
     (Leaf A-bulk); ~1 commit, mirrors `shiftSeedAdv_eq_funLeft_shiftPerm` (`:4097`). **THE RISK LEAF** (see (g)).
  3. **`shiftBodyListAsc_foldl_mem_span_rigidityRows_selAdv`** (`Relabel.lean`) — the selector-advancing
     membership fold (Leaf B); ~1–2 commits, the per-step `hends'_off` is the new obligation.
  4. **`chainData_freshEdge_slot_mem_selAdv`** (`Relabel.lean`) — the restated slot core (Leaf C); ~1 commit,
     a near-mechanical re-thread of `:4156–4227` onto Leaf B.
  5. **`chainData_relabel_arm_hρGv` re-thread** (`Relabel.lean:4625`) — `hφ@ends₀` + `hrec` per-step + call
     Leaf C (per (e)); ~1 commit. THEN the arm shell (`refine case_III_arm_realization`) + **2c-iii**
     `chainData_dispatch`.

  *(g) THE ONE HONEST RISK — FLAGGED, NOT FORCED.* Leaf A-bulk (`shiftEndsAdv_eq_relabel`, leaf 2) is the
  single un-verified algebraic step: `shiftEndsAdv` advances by composing per-step *vertex* swaps on the
  selector's *output endpoints*, whereas the target `endsσρ` is `σ⁻¹ ∘ ends₀ ∘ shiftEdgePerm` — a vertex
  relabel on the output AND an *edge* relabel on the input. These must coincide. The seed analogue
  (`shiftSeedAdv_eq_funLeft_shiftPerm`) only needed the vertex side (the seed has no edge argument), so this
  is genuinely MORE than the P3 template — the edge-side `shiftEdgePerm`-vs-vertex-`shiftPerm` coupling (the
  KT-6.54 `vⱼ ↦ vⱼ₊₁` / edge `eⱼ ↦ eⱼ₊₁` lockstep, `shiftEdgePerm_apply_edge_interior`,
  `Operations.lean:2064`) must be shown to make the per-step output-endpoint swap equal the bulk
  input-edge-relabel-plus-output-vertex-relabel. This is plausible (the cycle couples edge and vertex
  indices by construction) and NOT a motive/IH/contract change, but it is the recon's residual unknown:
  **if leaf 2 does NOT close (the edge/vertex coupling does not telescope), the `shiftEndsAdv` accumulator
  must instead be DEFINED to relabel the edge argument too** (`shiftEndsAdv ends₀ (s+1) e := (swap…)·(shiftEndsAdv
  ends₀ s ((shiftEdgePerm-step) e))`), shifting the work into leaf 1's `def` and re-checking leaf 2 against it.
  Either way the leaf count + signatures (d)/(f) hold; only leaf 2's proof shape is at risk, and it is a
  selector-algebra identity (no new geometry, no new span/rank fact). **The build should open at leaf 1
  (mechanical) and resolve leaf 2's edge/vertex coupling with a recon-or-spike before committing to the
  `shiftEndsAdv` def shape.** No telescope re-proof, no new invariant, no motive change — the genuinely-new
  math (the perp, P2, the chain induction) is all LANDED; ROUTE α is a selector-bookkeeping re-architecture
  with one algebraic identity (leaf 2) as its only honest unknown.

  **CLAUSE (ii) HONESTY.** This pins a buildable decomposition with exact signatures grounded in the landed
  bodies (4 probes), and NAMES the one residual algebraic risk (leaf 2) rather than asserting it closes. It is
  NOT a confident transport-leaf pin (the I.8.12 trap): the telescope-survival question is answered with
  Lean evidence (it is selector-free), the foldl core + gate are confirmed selector-advancing-ready, and the
  one unknown is honestly flagged with a fallback. No motive/IH/contract change; `d=3` M₃ unaffected (`i=2`,
  no `hφ` slot, no general fold). The landed `chainData_relabel_arm_hρGv` stays a correct lemma until leaf 5
  re-threads it; nothing reverts. **N.B. — leaf 2 (g)'s risk is RESOLVED NEGATIVE; see (I.8.14): leaf 2 as
  stated in (d)/(f) is FALSE against the landed leaf-1 def, and (g)'s fallback (fold `shiftEdgePerm` into
  leaf 1's `def`) is REQUIRED. Read (I.8.14) before building.**

**(I.8.14) LEAF-2 RISK RESOLVED — NEGATIVE: the recon-or-spike (g) mandated ran; leaf 2 as stated is FALSE
against the landed leaf-1 `def`; (g)'s fallback (fold `shiftEdgePerm` into leaf 1) is REQUIRED, and it
collides with leaf 3's per-step gate — the genuine multi-leaf difficulty, now pinned (2026-06-21, opus;
docs-only, no Lean landed; the finding was Lean-verified by a throwaway probe `theorem … = fun e => …`
that compiled `success:true` warning-clean apart from a cosmetic `[DecidableEq β]` unused-arg, then deleted —
tree byte-clean).** Per (g)'s explicit instruction ("resolve leaf 2's edge/vertex coupling with a
recon-or-spike before committing to the `shiftEndsAdv` def shape"), the spike computed the landed leaf-1
`shiftEndsAdv`'s closed form and compared it to the arm's `endsσρ` (`Relabel.lean:4688–4690`).

  *(a) THE LANDED `shiftEndsAdv (i−1)` CLOSED FORM (Lean-verified):*
  `cd.shiftEndsAdv ends₀ ((i:ℕ)−1) = fun e => ((cd.shiftPerm i.castSucc).symm (ends₀ e).1,
  (cd.shiftPerm i.castSucc).symm (ends₀ e).2)`. The proof chain (all from landed lemmas):
  (i) `shiftEndsAdv ends₀ s e = (P_s.reverse.prod (ends₀ e).1, P_s.reverse.prod (ends₀ e).2)` with
  `P_s = List.ofFn (fun t : Fin s => shiftSeedSwap t)` — by induction, the `_succ` recursion wraps the NEW
  swap OUTERMOST, so the accumulated swaps read off the **reverse** product (vs `shiftSeedAdv`'s `.prod`,
  whose `_succ` applies the new swap to the argument, innermost); (ii) `P_{i−1}.reverse.prod =
  (P_{i−1}.prod)⁻¹` because every `shiftSeedSwap t` is an involution (`Equiv.swap_inv`/`inv_one`, via
  `List.prod_inv_reverse`); (iii) `P_{i−1}.prod = shiftPerm i.castSucc` (the internal step of
  `shiftSeedAdv_eq_funLeft_shiftPerm`, `hlist` + `shiftPerm_eq_prod_map_swap_shiftBodyListAsc`); so
  `P_{i−1}.reverse.prod = (shiftPerm i.castSucc)⁻¹ = (shiftPerm i.castSucc).symm`.

  *(b) THE VERDICT — the endpoint half is ALREADY CORRECT; the EDGE argument is the sole discrepancy.* The
  landed `shiftEndsAdv (i−1)` already applies `(shiftPerm i.castSucc).symm` to the endpoints (the `.symm`/
  inverse direction `endsσρ` wants — so (g)'s "per-step *vertex* swaps vs `σ⁻¹`" worry is a NON-issue: the
  order-reversal in the recursion silently produces the inverse, matching `endsσρ`). The ONE genuine
  discrepancy is the EDGE argument: landed reads `ends₀ e`; `endsσρ` reads `ends₀ (shiftEdgePerm i e)`. So
  **leaf 2 `shiftEndsAdv ends₀ (i−1) = endsσρ` is FALSE for arbitrary `ends₀`** (the two sides read `ends₀`
  at distinct edges `e` vs `shiftEdgePerm i e`). (g)'s fallback is therefore REQUIRED, and is also MINIMAL:
  leaf 1's `def` must fold the `shiftEdgePerm i` edge relabel into the edge argument; nothing else changes.

  *(c) THE GENUINE MULTI-LEAF DIFFICULTY NOW PINNED — leaf 1's def is DOUBLY CONSTRAINED, and the two
  constraints collide.* (i) Leaf 2 needs leaf 1 to advance the edge by the WHOLE `shiftEdgePerm i` cycle at
  the top step. (ii) Leaf 3's per-step gate `funLeft_dualMap_sub_acolumn_seedAdvance_mem_span_rigidityRows`
  (`Relabel.lean:1201`) takes `hends'_off : ∀ f, f ≠ edge(s+1) → f ≠ edge(s+2) → ends' f = ends f` — the
  per-step selector advance may move ONLY edges `edge(s+1)`/`edge(s+2)`. So leaf 1 must advance the edge
  ONE gate-compatible swap per step AND telescope to the full `shiftEdgePerm i`. But `shiftEdgePerm i =
  formPerm [edge 0, e₀, edge i, edge 1, …, edge(i−1)]` is the edge cycle through the fresh `e₀`/top `edge i`
  reorderings — it does NOT decompose into the same ascending adjacent swaps as `shiftPerm` (there is NO
  `shiftEdgePerm_eq_swap_mul` analogue of `shiftPerm_eq_swap_mul`, `Operations.lean:1522`). Reconciling the
  gate's `{edge(s+1), edge(s+2)}`-only per-step move with the `e₀`-threaded edge cycle is the real
  make-or-break — NOT a mechanical mirror of the seed. This is genuine new structure (likely a per-step edge
  swap accumulator + a `shiftEdgePerm` factorization theory), not a one-commit leaf; the recon-or-spike (g)
  asked for was right to gate it.

  *(d) NEXT STEP (corrected; supersedes (f)'s "open at leaf 1, mechanical").* Leaf 1's landed
  `shiftEndsAdv` (`Relabel.lean:1731`) is the WRONG def shape and must be RE-DESIGNED (not merely consumed):
  fold a gate-compatible per-step EDGE advance into it, reconciling constraints (c)(i)/(c)(ii). The
  smallest concrete next commit is the **leaf-1-def re-design recon** — pin the per-step edge swap (what
  edge move at step `s` is BOTH gate-compatible — touches only `edge(s+1)`/`edge(s+2)` — AND accumulates to
  `shiftEdgePerm i`), likely needing a `shiftEdgePerm` step-factorization first. Until that def is settled,
  leaves 2–5's signatures (which name `shiftEndsAdv`) are provisional. The endpoint-half closed form (a) is
  verified and reusable. NO motive/IH/contract change; `d=3` M₃ still unaffected (`i=2`, no `hφ` slot, no
  general fold); `chainData_relabel_arm_hρGv` stays a correct lemma (its `hφ@endsσρ` slot is the wall ROUTE α
  dissolves) until leaf 5 re-threads it — nothing reverts.

  **CLAUSE (ii) HONESTY.** This is a NEGATIVE finding pinned with Lean evidence (the probe compiled the
  closed form), not a confident pin: it overturns (f)'s "leaf 1 mechanical, open there" by showing leaf 1's
  landed def is wrong-shaped, and it names the leaf-1/leaf-3 constraint collision as the genuine difficulty
  rather than asserting a fix. No Lean landed (the probe was deleted; tree byte-clean).

**(I.8.15) LEAF-1-DEF RE-DESIGN — VERDICT: OPTION B. The gate-compatible per-step edge accumulator does NOT
exist; no product of `{edge(s+1),edge(s+2)}`-supported per-step edge swaps can accumulate to `shiftEdgePerm
i`. ROUTE α (the per-step selector fold reaching `endsσρ`) is INFEASIBLE; the obstruction is structural, not
a proof-shape gap. The correct alternative is a TRANSPORT-based `hρGv` slot mirroring the landed `hwmem` brick
`chainData_bottom_relabel`, NOT a per-step fold (2026-06-21, opus; docs-only, no Lean landed; every
load-bearing claim Lean-verified against the landed bodies via 5 `lean_multi_attempt` probes — each `have`
type-checked in the live `chainData_relabel_arm_hρGv` context; tree byte-clean throughout, no file written).**
Per (I.8.14)(d)'s mandated leaf-1-def re-design recon, the question (I.8.14)(c) posed — "is there a per-step
edge move (touching only `edge(s+1)`/`edge(s+2)`) whose accumulated product = `shiftEdgePerm i`?" — is now
answered DEFINITIVELY NO.

  *(a) THE PROOF OF INFEASIBILITY (Lean-grounded).* The membership fold runs `i−1` steps `s = 0,…,i−2`. At
  step `s` the gate `funLeft_dualMap_sub_acolumn_seedAdvance_mem_span_rigidityRows` (`Relabel.lean:1201`)
  permits the per-step selector advance `ends → ends'` ONLY via `hends'_off : ∀ f, f ≠ edge(s+1) → f ≠
  edge(s+2) → ends' f = ends f` (`:1204`) — i.e. the per-step move may touch ONLY `edge(s+1)` and `edge(s+2)`.
  So across the whole fold, the accumulated per-step moves can differ from `ends₀` ONLY on the union
  `⋃_{s=0}^{i−2} {edge(s+1), edge(s+2)} = {edge 1, …, edge i}`. But the target `endsσρ = σ⁻¹ ∘ ends₀ ∘
  shiftEdgePerm i` (the landed arm's candidate selector, `:4688–4690`) differs from `ends₀` on the support of
  `shiftEdgePerm i`, which **includes `edge 0` and `e₀`** — both OUTSIDE `{edge 1,…,edge i}`. Lean-verified:
  **PROBE A** `shiftEdgePerm i e₀ = edge i` (`shiftEdgePerm_apply_e₀`) with `e₀ ≠ edge i` (`e₀_ne_edge`) — so
  `shiftEdgePerm i` moves `e₀`; **PROBE B** `shiftEdgePerm i (edge 0) = e₀` (`shiftEdgePerm_apply_edge_zero`) —
  so it moves `edge 0`; **PROBE E** `edge 0 ∉ {edge 1,…,edge i}` and `e₀ ∉ {edge 0,…,edge(d−1)}` (`edge_inj` /
  `e₀_ne_edge`), so EVERY gate-compatible per-step swap fixes both `edge 0` and `e₀`. Hence the accumulated
  selector at `edge 0` is ALWAYS `ends₀ (edge 0)`, whereas `endsσρ (edge 0)` reads `ends₀` at `shiftEdgePerm i
  (edge 0) = e₀` — a DIFFERENT edge. For arbitrary `ends₀ : β → α × α` (the leaf is universally quantified)
  these disagree. ∴ no gate-compatible per-step accumulator equals `endsσρ`.

  *(b) WHY THE DISCREPANCY IS LOAD-BEARING (it is NOT a free-on-non-links coincidence).* One might hope the
  selector mismatch at `edge 0`/`e₀` is invisible because `rigidityRows` (`Basic.lean:603`) ranges only over
  graph-LINKS and `toBodyHinge.supportExtensor e` (`PanelHinge.lean:89`) reads `ends` only AT `e`. That rescues
  `e₀` (Lean-verified `e₀ ∉ E(G)`, never a link → span insensitive there) — but NOT `edge 0`: **PROBE C/D**
  confirm `edge 0 = v₀v₁` IS a surviving link of `G − vᵢ` for `i ≥ 2` (`G.IsLink (edge 0)(vtx 0)(vtx 1)` from
  `cd.link`, and `vtx 0`, `vtx 1` both `≠ vtx i` by `vtx_inj`). So the conclusion framework `ofNormals (G−vᵢ)
  endsσρ qρ`'s rigidity-row span genuinely DEPENDS on the selector at `edge 0`, and the accumulated-selector
  framework would have a DIFFERENT `edge 0` panel — a different span. Even a relaxed Leaf C (conclude at the
  accumulated selector + a span-equality bridge) cannot close: the bridge needs agreement on EVERY link of
  `G − vᵢ`, which fails at `edge 0`.

  *(c) THE ROOT CAUSE — a per-step fold is the WRONG mechanism for a CYCLE edge relabel.* `endsσρ`'s edge
  relabel is the full cycle `shiftEdgePerm i = formPerm [edge 0, e₀, edge i, edge 1, …, edge(i−1)]` (an
  `(i+2)`-cycle threading the fresh `e₀` and the top `edge i`), which — as (I.8.14)(c) flagged and this
  confirms — does NOT decompose into ascending adjacent edge swaps `(edge(s+1) edge(s+2))` (no
  `shiftEdgePerm_eq_swap_mul` analogue of the vertex `shiftPerm_eq_swap_mul`, `Operations.lean:1522`). The
  vertex side telescopes (P3 `shiftSeedAdv_eq_funLeft_shiftPerm`) precisely because `shiftPerm i.castSucc` is
  the consecutive-vertex cycle `vtx 1 → … → vtx i`, a product of adjacent swaps; the edge cycle is NOT. ROUTE α
  was a category error: it tried to reach a non-adjacent-transposition cycle as a product of adjacent
  transpositions.

  *(d) WHY THE LANDED `hwmem` BRICK ESCAPES — and what the corrected `hρGv` route IS.* The landed `chainData_
  bottom_relabel` (`:1961`, the `hwmem` slot) ALSO lands its rows at the edge-relabelled `endsσρ` (`:1984`,
  `shiftEdgePerm i e` in its output selector) — and succeeds — because it reaches `endsσρ` by **inverse-cycle
  TRANSPORT** (`ofNormals_supportExtensor_relabel_perm` + the `shiftPerm_inv_*`/`shiftEdgePerm_inv_*` action
  lemmas), applying the WHOLE relabel at once, NOT by a per-step fold. The corrected `hρGv` slot must do the
  same: reach `span (ofNormals (G−vᵢ) endsσρ qρ)` by transporting A-1's base redundancy across the whole
  `(shiftPerm i.castSucc)`/`shiftEdgePerm i` relabel — NOT by a selector-advancing fold. **The
  per-step-selector-advance idea (ROUTE α leaves 1–5) is abandoned in full** (no leaf-1 def is gate-compatible;
  the foldl-core / single-step-gate machinery is the wrong tool for `hφ`).

  *(e) WHAT THE OPTIONS NOW ARE (for coordinator/user adjudication).* The (I.8.12) VERDICT stands re-confirmed
  with the ROUTE-α arm removed: `hφ@endsσρ` is genuinely required by the slot core and is NOT reachable by any
  per-step fold. Three honest routes remain; none is a one-commit instantiation:
  - **B1 — whole-relabel `hφ` transport (the analogue of `chainData_bottom_relabel`, recon-first).** Build a
    transport lemma `hingeRow v₀ v₂ ρ₀ ∈ span (ofNormals (G−v₁) ends₀ q) → hingeRow v₀ v₂ ρ₀ ∈ span
    (ofNormals (G−v₁) endsσρ q)` (the seam framework, fixed graph/seed, ONLY the selector moves `ends₀ →
    endsσρ`). This is the `hφ`-specific instance of the R-2(iii) wall (I.8.12): the edge-grouped `hcomb`
    transports across `ofNormals_supportExtensor_relabel_perm` only with each `rⱼ ∈ block(σ_e eⱼ)` (the WRONG
    edge), and `σ⁻¹ v₀ = v₀`, `σ⁻¹ v₂ = v₁` for `i ≥ 2` make any apparatus transport land on the WRONG member
    `hingeRow v₀ v₁ ρ₀`. R-2(iii) flagged this as un-clean; B1 would need a genuinely-new argument (e.g. a
    DIRECT span re-derivation at `endsσρ`, not an A-1 transport), risk-HIGH, recon-mandatory. **NOT obviously
    feasible — the member-mapping wall (4th touch) is the same one that killed T-1/T-2 and now ROUTE α.**
  - **B2 — restate the slot core to NOT fix the start selector at the relabelled framework (the eliminate-the-
    hybrid fix, done RIGHT this time).** ROUTE α's INTENT was sound (keep `hφ` at `ends₀`), only its MECHANISM
    (per-step fold) was wrong. The slot core `chainData_freshEdge_slot_mem` currently runs the seed-advancing
    fold which forces ONE selector. A correct restate would: (i) prove the slot row at the `ends₀`-selector
    candidate framework `ofNormals (G−vᵢ) ends₀ (shiftSeedAdv q (i−1))` via the fold (selector genuinely fixed
    at `ends₀`, gate's `hends'_off` is `rfl` — but then the fold's intermediate-graph `hrec`/`htrans` need
    `ends₀` to record `G−vᵢ`'s interior links, which it does NOT — it records `G−v₁`'s — so this is R-2(iv)'s
    candidate-TOP failure, ALSO dead); OR (ii) re-architect the fold to record links at the per-step graph's
    OWN selector while keeping the conclusion at `endsσρ` by transport. (ii) collapses to B1. **B2 is either
    dead (the `ends₀`-records-`G−vᵢ` ill-formedness) or = B1.**
  - **B3 — carry `hφ@endsσρ` as a hypothesis to the dispatch/ENTRY (ROUTE β of I.8.12, the defer).** Keep
    `chainData_relabel_arm_hρGv` AS LANDED (it is a CORRECT lemma taking `hφ@endsσρ` honestly) and discharge
    the hybrid at the dispatch where the chain's base realization is in scope. R-2/I.8.12 flagged this LIKELY
    DEAD (the rigidity of the hybrid `ofNormals (G−v₁) endsσρ q` re-derives via A-1 but at the WRONG member,
    needing a member-bridge = B1, likely circular). **Defers the wall, does not dissolve it.**
  **RECOMMENDATION: a focused recon on B1** (the whole-relabel `hφ` transport) is the only route that attacks
  the wall head-on; if B1's member-mapping cannot be beaten by a direct re-derivation at `endsσρ`, the honest
  conclusion is that the `hρGv` slot needs `hφ` produced at `endsσρ` DIRECTLY (re-thread A-1 / the W6b producer
  `exists_candidateRow_bottomRows_of_rigidOn` to output its base redundancy at the relabelled selector) —
  which IS a contract-touching change (A-1's output type), the first the CHAIN arm would force, and must go to
  user adjudication before any build. **This is NOT a leaf-1 re-design; it is an `hφ`-production re-architecture
  one level up, and the make-or-break is the member-mapping wall, not a `shiftEndsAdv` def shape.**

  **CLAUSE (ii) HONESTY.** This is OPTION B: an honest infeasibility verdict on ROUTE α's per-step edge
  accumulator (Lean-grounded by 5 probes against the landed bodies), naming precisely what fails (no
  gate-compatible per-step swap product reaches `shiftEdgePerm i`; `edge 0` is the load-bearing surviving-link
  discrepancy) and what the options then are (B1/B2/B3, with B1 the only head-on attack and an `hφ`-production
  re-architecture as the fallback — contract-touching, user-adjudication-gated). It does NOT pin a confident
  corrected def. No motive/IH/contract change is made HERE (B1/B2 would not change the contract; the fallback
  would touch A-1's output type and is explicitly flagged for user adjudication). `d=3` M₃ remains unaffected
  (`i=2`, no `hφ` slot, no general fold); `chainData_relabel_arm_hρGv` stays a CORRECT lemma (its `hφ@endsσρ`
  slot is the wall) until the `hρGv` route is settled — nothing reverts. The landed ROUTE-α leaf 1
  `shiftEndsAdv` (`Relabel.lean:1731`) + `shiftEndsAdv_zero`/`_succ` are now ORPHANED (no consumer; the
  per-step-selector-fold route is abandoned) — confirm-and-delete at the `hρGv`-route-settle commit, alongside
  T-1/T-2.

**(I.8.16) `hφ`-AT-SOURCE SCOPING RECON — VERDICT: the source-production replacement for the infeasible ROUTE
α is FEASIBLE but CONTRACT-TOUCHING. A-1 is fully parametric over `ends`, but instantiating it at `endsσρ`
produces the WRONG member (Lean-verified): A-1's output member is `hingeRow (ends e₀).1 (ends e₀).2 ρ`, and
`endsσρ e₀` reads `ends₀` at `edge i` (NOT `e₀`), so A-1@`endsσρ` gives `hingeRow (σ⁻¹(ends₀(edge i))…) ρ`,
not `hingeRow v₀ v₂ ρ₀`. The ONLY way to land `hingeRow v₀ v₂ ρ₀ ∈ span (ofNormals (G−v₁) endsσρ q)` at the
source is to re-thread A-1 / the W6b producer so the candidate-row output is stated at the relabelled selector
— which CHANGES the third lockstep CHAIN↔ENTRY decl's premise bundle (the `hφ` shape the producer feeds the
arm) and A-1's output type. So: feasible mechanism exists, but it is the FIRST contract-touching change the
CHAIN arm forces — READY FOR USER SIGN-OFF (2026-06-21, opus; docs-only, no Lean landed; the 3 load-bearing
claims Lean-verified by `lean_multi_attempt` `have`-blocks in the live `chainData_relabel_arm_hρGv` context
— each typechecked, tree byte-clean throughout).** Verified against A-1
`exists_candidateRow_bottomRows_of_rigidOn` (`Candidate.lean:400`, its FULL input bundle + output, `:414–445`),
the W6b producer `chainData_split_w6b_gates` (`Realization.lean:771`, its A-1 call `:888–891`), the arm slot
`chainData_relabel_arm_hρGv` (`Relabel.lean:4647`, the `hφ` slot `:4671–4675`), the slot core
`chainData_freshEdge_slot_mem` (`:4158`, its `hφ` at one `ends`, `:4165–4168`), `rigidityRows_ofNormals_congr_ends`
(`Realization.lean:49`), `removeVertex_isLink` (`Operations.lean:546`), the shift-action lemmas
(`shiftEdgePerm_apply_e₀`/`_edge_zero`/`_edge_interior`, `Operations.lean:2044/2054/2064`).

  *(1) FEASIBILITY — A-1 IS parametric over `ends`, but A-1@`endsσρ` is the WRONG member (the coordinator's
  optimistic hypothesis is FALSE; Lean-grounded).* A-1 (`Candidate.lean:401`) takes `{ends : β → α × α}` freely,
  and its `hρGv` conclusion (`:420`) is `hingeRow (ends e₀).1 (ends e₀).2 ρ ∈ span (ofNormals Gv ends q).rows`.
  So A-1@`endsσρ` would land `hingeRow (endsσρ e₀).1 (endsσρ e₀).2 ρ`. **PROBE A (typechecked):** `endsσρ e₀ =
  ((shiftPerm i.castSucc).symm (ends₀ (edge i)).1, …)` (since `shiftEdgePerm i e₀ = edge i`, `shiftEdgePerm_apply_e₀`)
  — i.e. A-1@`endsσρ`'s member reads `ends₀` at `edge i`, NOT at `e₀`, giving `hingeRow (σ⁻¹ v_i)(σ⁻¹ v_{i+1}) ρ`,
  the candidate's OWN splice member (= R-2(i)/(ii) of I.8.12), NOT the base `hingeRow v₀ v₂ ρ₀` the slot core
  wants. **The member endpoints are TIED to A-1's `(ends e₀)` slot and MOVE with the selector** — re-instantiating
  A-1 at a different selector cannot hold the member fixed. ∴ A-1@`endsσρ` ≠ the needed `hφ`.

  *(2) Why the `congr_ends` shortcut fails on the SEAM framework `G−v₁` (NOT just `G−vᵢ`).* The landed
  `rigidityRows_ofNormals_congr_ends` (`Realization.lean:49`) gives `span (ofNormals G ends q).rows = span
  (ofNormals G ends' q).rows` WHEN `ends`/`ends'` agree on every LINK of `G`. So `hφ@endsσρ = hφ@ends₀` for FREE
  iff `endsσρ` agrees with `ends₀` on every link of `G−v₁`. It does NOT: the support of `shiftEdgePerm i`
  contains `edge 2,…,edge i` (the interior + top chain edges), and these AVOID `v₁` so they ARE surviving links
  of `G−v₁`. **PROBE B (typechecked):** `(G−v₁).IsLink (edge 2)(vtx 2)(vtx 3)` (from `cd.link` + `vtx_inj`) — a
  moved base-graph link; **PROBE C (typechecked):** `shiftEdgePerm i (edge 0) = e₀` (the cycle is genuinely
  non-trivial on the support). So `endsσρ` is a GENUINE relabel of `G−v₁`'s links, not a `congr_ends`-equal
  selector. [N.B. I.8.15's PROBE C/D located the load-bearing discrepancy at `edge 0` on `G−vᵢ`; on the SEAM
  framework `G−v₁` `edge 0 = v₀v₁` is DELETED (`removeVertex_isLink` forbids the `v₁` endpoint — PROBE1, typechecked),
  so the seam-framework discrepancy rides on `edge 2…edge i` instead — same conclusion, via a different link.]
  ∴ no member-free transport: B1 of I.8.15 is genuinely the member-mapping wall (4th touch).

  *(3) THE CLEANEST MECHANISM — `hφ`-at-source = re-thread A-1's candidate-row output to the relabelled
  selector (the I.8.15 fallback, now scoped at signatures).* A-1@`endsσρ` is the wrong member because its
  `e₀`-splice member moves with the selector. To land `hingeRow v₀ v₂ ρ₀` at `endsσρ`, A-1's candidate-row
  output must be stated against the relabelled selector while pinning the member endpoints to the BASE chain
  vertices. Two concrete shapes (the second is cleaner and is the recommendation):
  - **(3a) An A-1 output-type augment** — give A-1 a SECOND `hρGv`-form conclusion at a *supplied* relabelled
    selector `ends'` with a *supplied* member-endpoint pair `(x,y)`, under a hypothesis pinning the
    transport (`ends'` agrees with `ends` off the cycle support / the edge-grouped `hcomb` transports). This
    is the most surgical, but it BAKES the relabel into A-1 (the candidate-reduction layer's concern) — a
    layering smell, and it still needs the member-bridge argument B1 names (the edge-grouped `hcomb`'s `rⱼ ∈
    block(σ_e eⱼ)` mismatch, I.8.12 R-2(iii)).
  - **(3b) RECOMMENDED — produce `hφ@endsσρ` in the W6b producer, beside the existing `hφ@ends₀`, via a
    DIRECT span re-derivation at `endsσρ` (B1 done inside the producer where the rigidity data lives).** The
    producer `chainData_split_w6b_gates` (`Realization.lean:771`) already has, in scope, the IH-generic base
    realization `Q` (`:821`), its selector `Q.ends` (= the arm's `ends₀`), the rigidity-on `hrig'` (`:839`),
    and A-1's edge-grouped output (`hρGv'`/`_hedgeGv`, `:888`). Add ONE new output conjunct: `hingeRow a b ρ ∈
    span (ofNormals (G−v) (relabel Q.ends) q).rows` for the arm's `endsσρ` relabel. The re-derivation is the
    B1 span-transport: A-1's edge-grouped `hcomb` (`∑ⱼ cⱼ hingeRow uⱼvⱼ rⱼ = hingeRow a b ρ`, `rⱼ ∈ (base).block(eⱼ)`)
    transported across `ofNormals_supportExtensor_relabel_perm` (`Relabel.lean:63`) — which relates `(endsσρ).block(eⱼ)
    = (ends₀).block(σ_e eⱼ)` — needs each `rⱼ ∈ (endsσρ).block(eⱼ)`, i.e. `rⱼ ∈ (ends₀).block(σ_e eⱼ)`, the
    WRONG edge (B1's hard core). **This is the make-or-break the recon CANNOT pre-discharge** — see (5).

  *(4) THE EXACT CHAIN↔ENTRY CONTRACT DELTA.* Either mechanism CHANGES the producer's `hφ`-shape output, which
  is the third lockstep decl of the contract (C.0). **The delta touches the `hφ`/redundancy slot of the
  producer→arm bundle, NOT the `ChainData` record (C.1) and NOT the dispatch's `hdispatch` consume-shape (C.3).**
  Concretely:
  - **C.0 third lockstep decl** (`chainData_split_w6b_gates` output `:789–815`, and any per-`i` re-thread of it):
    gains a relabelled-selector `hφ` conjunct (or A-1's output type gains it, propagating up). This is the FIRST
    contract-touching change the CHAIN arm forces — the prior `hφ@endsσρ`-as-carried-hypothesis shape (the
    landed arm) is replaced by a producer-supplied one.
  - **The `ChainData` record (C.1) is UNCHANGED** — the chain data is purely combinatorial; the relabel is
    derived from it (`shiftPerm`/`shiftEdgePerm`), not a new field.
  - **The CHAIN-5 dispatch signature (C.3) is UNCHANGED** — `hdispatch` consumes a `ChainData` + the
    deficiency-0 fact + the IH-generic base realization; the producer-internal `hφ` re-thread is BELOW the
    dispatch interface (exactly as the perp half STEP 1∘STEP 2 is). The dispatch never sees `hφ@endsσρ`.
  - **C.6 (no motive/IH change) IS PRESERVED** — the re-derivation runs at the SAME 0-dof IH realization `Q`
    the `d=3` producer already pulls (`Realization.lean:821`); no higher-dof seed, no conditioned-pair data, no
    new IH conjunct. The relabelled-selector `hφ` is a fact ABOUT the existing `Q`, not a stronger IH demand.
  - **`d=3` zero-regression (C.4) holds** — M₃ is `i=2`, no `hφ` slot, no general fold (the M₃ `hρGv` goes
    through W9a on the single candidate row); the producer's new conjunct is consumed only by the general-`i`
    arm, dead at `d=3`.

  *(5) THE COST + THE RESIDUAL RISK (the honest unknown).* The MECHANISM is scoped, but its make-or-break — the
  B1 span re-derivation at `endsσρ` (the member-mapping wall, 4th touch) — is NOT pre-dischargeable in a
  docs-only recon. `σ⁻¹ v₀ = v₀`, `σ⁻¹ v₂ = v₁` for `i ≥ 2` (Lean-verified across I.8.10–I.8.15) mean any
  *apparatus* transport of `hcomb` lands on the WRONG member `hingeRow v₀ v₁ ρ₀`; B1 needs a genuinely-new DIRECT
  argument (re-derive the redundancy at `endsσρ` from the relabelled framework's OWN rigidity, NOT by transporting
  A-1's `ends₀` combination). **If B1 closes: ~3–5 commits** (the producer conjunct + the B1 re-derivation lemma +
  the slot-core/arm re-thread to consume `hφ@endsσρ` from the producer instead of as a carried hyp + the arm
  shell + 2c-iii). **If B1 does NOT close** (the member-mapping wall is genuinely impassable at `endsσρ`), the
  `hρGv` slot at general `d` has NO source — and the honest fallback is to RESHAPE the slot core itself so it
  never demands `hφ@endsσρ` (B2(ii)/I.8.15, which collapses back to B1) OR to re-architect KT eq. 6.62's
  realization at general `d` away from the seed-advancing fold (a deeper, ASSEMBLY-level change). **The recon
  CANNOT certify B1 closes without a build spike** — that spike IS the contract-touching change, hence the
  user gate.

  **BOTTOM LINE — READY FOR USER SIGN-OFF: the build is CONTRACT-TOUCHING (the first the CHAIN arm forces — it
  changes the producer's `hφ`/redundancy output conjunct = C.0's third lockstep decl + A-1's output type; the
  `ChainData` record C.1, the `hdispatch` consume-shape C.3, the motive/IH C.6, and `d=3` C.4 are ALL
  unchanged); ~3–5 commits IF the B1 span re-derivation at `endsσρ` closes, which is the residual member-mapping
  risk (4th touch) the recon cannot pre-discharge.** The recommended shape is (3b): a producer-internal B1
  re-derivation supplying `hφ@endsσρ` beside the landed `hφ@ends₀`. **The single decision for the user:** approve
  the contract-touching producer/A-1 output re-thread (3b) + a B1 build spike as its first step, OR direct the
  deeper slot-core/ASSEMBLY re-architecture if the producer re-thread is judged the wrong layer. Until then,
  `chainData_relabel_arm_hρGv` stays a CORRECT carried-hypothesis lemma; nothing reverts; `d=3` is unaffected.

  **CLAUSE (ii) HONESTY.** This CONVERGES on a grounded verdict (feasible-with-contract-delta-X, ~3–5c, gated on
  the B1 spike) rather than deferring with another open recon: it names the exact contract delta (C.0 third
  lockstep decl + A-1 output type; C.1/C.3/C.4/C.6 invariant), Lean-grounds the infeasibility of the
  re-instantiation shortcut (PROBE A: A-1@`endsσρ` is the wrong member) and the `congr_ends` shortcut (PROBE B/C:
  `endsσρ` genuinely relabels `G−v₁`'s surviving links), and honestly flags the ONE residual risk (the B1
  member-mapping wall) as not-pre-dischargeable-in-docs rather than asserting it closes. No Lean landed (probes
  were `lean_multi_attempt`, in-memory; tree byte-clean).

**(I.8.17) B1 SPIKE — BLOCKED (the de-risk worked): the B1 span re-derivation at `endsσρ` does NOT close, and
the root cause is an ARTIFACT framework the slot core demands. Every LOCAL `hφ`-seam route is now exhausted;
the unblock is a DEEPER slot-core/ASSEMBLY re-architecture — PENDING USER ADJUDICATION (2026-06-21, opus
build spike, user-sanctioned B1-spike-first; tree byte-clean, NOTHING committed — the probe lemma was added
then removed verbatim).** Per the user-approved plan (build 3b, B1 spike first as a standalone lemma; no
contract change unless B1 closes), the spike stated B1 standalone (`hingeRow v₀ v₂ ρ₀ ∈ span (ofNormals
(G−v₁) endsσρ q).rigidityRows` from A-1's `hφ@ends₀`) and LSP-probed it: the statement type-checks, `exact
hφ0` fails (base/relabelled frameworks not defeq), and the only free route `rigidityRows_ofNormals_congr_ends`
needs `endsσρ = ends₀` on every link of `G−v₁`, which is FALSE.

  *(a) THE ARTIFACT ROOT CAUSE (coordinator-confirmed, `Relabel.lean:4671`).* The slot core / arm consumes `hφ`
  at `ofNormals (G−v₁) endsσρ q` — the **relabelled selector `endsσρ` with the UN-advanced BASE seed `q`**.
  This is a Lean-artifact of the fold (the slot core holds the selector fixed at `endsσρ` while the fold
  advances the seed `q → qρ`): it is NEITHER the base `(ends₀, q)` (A-1's genuine output) NOR the engine
  `(endsσρ, qρ)` (the conclusion). No KT geometry corresponds to `(endsσρ, q)`, which is precisely why no
  rigidity / redundancy fact exists for it.

  *(b) BOTH SANCTIONED B1 SOURCES ARE DEAD.* (i) "The relabelled framework's OWN rigidity" is unavailable — no
  theorem establishes `ofNormals (G−v₁) endsσρ q` rigid, and `ofNormals_relabel_perm` transports rigidity only
  when the seed is co-relabelled to `qρ` AND the graphs are `(ρ,σ)`-iso, neither of which holds for `(endsσρ,
  q)` on `G−v₁`. (ii) "A-1's edge-grouped data re-grouped at `endsσρ`" is dead — each summand's block
  constraint `rⱼ ∈ block_ends₀(eⱼ)` does not transfer to `block_endsσρ(eⱼ)` (the support extensors read `q` at
  shifted vertices), and re-grouping only rearranges summands, not their fixed block constraints. The `d=3`
  precedent `rigidityRows_ofNormals_relabel` only relates frameworks where the seed is ALSO relabelled (`qρ`),
  and its image map `(funLeft ρ).dualMap` permutes the member to `hingeRow v₀ v₁ ρ₀` (since `σ⁻¹ v₂ = v₁`) —
  the WRONG member, exactly the wall (4th touch).

  *(c) VERDICT — every LOCAL route exhausted; the unblock is a DEEPER re-architecture.* ROUTE α (per-step
  fold) infeasible (I.8.15); transport (T-1/T-2, B1) = the member-mapping wall; source-production (A-1
  re-thread) = B1 does not close (this entry). The remaining route is a **slot-core / ASSEMBLY-level
  re-architecture of KT eq. (6.62)'s seed-advancing fold** so it never demands `hφ` at the artifact `(endsσρ,
  q)` — i.e. make the fold consume `hφ` at a KT-real geometry. The two directions (both UNCERTAIN, neither
  pre-dischargeable): (1) advance selector AND seed in lockstep so the start framework is the genuine base
  `(ends₀, q)` and the relabel is absorbed step-by-step — but this is ROUTE α's intent, which the gate's
  `edge(s+1)/(s+2)`-only per-step move blocks (I.8.15), so it needs a NON-gate fold mechanism; (2) re-shape
  the fold so the `hφ` it consumes sits at the engine `(endsσρ, qρ)` or base `(ends₀, q)` directly. **This is
  a fundamental re-architecture decision, not a next-leaf — PENDING USER ADJUDICATION.**

  **CLAUSE (ii) HONESTY.** A clean BLOCKED with a Lean-grounded diagnosis (coordinator independently confirmed
  the arm's `hφ` framework is `(endsσρ, q)` at `Relabel.lean:4671`); the de-risk did its job — NO contract /
  producer edit was made, tree byte-clean. `chainData_relabel_arm_hρGv` stays a CORRECT carried-hypothesis
  lemma; the orphaned ROUTE-α leaf 1 `shiftEndsAdv` + `_zero`/`_succ` (+ T-1/T-2) await confirm-and-delete at
  the re-architecture-settle commit; `d=3` M₃ unaffected (`i=2`, no `hφ` slot).

**(I.8.18) SLOT-CORE / ASSEMBLY RE-ARCHITECTURE ADJUDICATION — VERDICT: BOTH local fold re-shapes are DEAD
against the landed machinery; the artifact `(endsσρ, q)` is a Lean-modelling choice (the seed-advancing
materialized-fold) that NO KT-faithful re-shape removes WITHOUT touching the slot-core/fold machinery — and
the only re-shape that does dissolve it (model KT's row-correspondence (6.62) as a whole-matrix reframe
rather than a per-step fold over `d−1` intermediate `ofNormals` frameworks) is an ASSEMBLY-LEVEL re-write of
the eq.-(6.60→6.64) Lean realization, NOT a leaf and NOT a contract/motive change — FLAG-DON'T-FORCE, FOR
USER ADJUDICATION (2026-06-21, opus design-pass; every load-bearing claim re-derived from the landed
`def`/`theorem` bodies — the prompt's summary and the prior pins were treated as something to re-verify, not
inherit; docs-only, no Lean landed, tree byte-clean).** Re-verified against the engine
`case_III_arm_realization` (`Arms.lean:72`, the slot bindings `:74/81/82/91/96/114`), the slot core
`chainData_freshEdge_slot_mem` (`Relabel.lean:4158`, its single `ends` + `hφ`@`(ends,q)` `:4161/4165–4168` +
conclusion@`(ends,qρ)` `:4174–4177`), the arm `chainData_relabel_arm_hρGv` (`:4647`, `hφ`@`(endsσρ,q)`
`:4671`), the seed-fixed fold `shiftBodyListAsc_foldl_mem_span_rigidityRows` (`:1807`, single `ends` `:1809`),
the single-step gate `funLeft_dualMap_sub_acolumn_seedAdvance_mem_span_rigidityRows` (`:1201`, `hends'_off`
`:1204`), A-1 `exists_candidateRow_bottomRows_of_rigidOn` (`Candidate.lean:400`, output@`(ends,q)`, member tied
to `(ends e₀)`, blocks@`block_ends(eⱼ)` `:420/431/442`), the genuine-row `hwmem` brick `chainData_bottom_relabel`
(`:1961`, input@`(ends₀,q)` `:1972`, output = the WHOLE-relabel image `(funLeft σ⁻¹).dualMap φ`@`(endsσρ,qρ)`
`:1982–1986`), the perp transport `chainData_freshEdge_perp_transport_base_to_candidate` (`:4534`, a SCALAR
`=0` transport via `ofNormals_supportExtensor_relabel_perm`), and KT 2011 §6.4.2 eqs. (6.54)–(6.67), pp.
694–698 (`.refs/katoh-tanigawa-2011-molecular-conjecture.pdf`, read end-to-end).

  *(0) THE LOAD-BEARING PREMISE — RE-CONFIRMED AGAINST THE LANDED SOURCE: the slot core genuinely consumes
  `hφ` at the artifact `(endsσρ, q)`, NOT at `(ends₀, q)` / `(endsσρ, qρ)`.* Three INDEPENDENT levels force
  it (each Lean-read, not inherited):
  - **Engine (the ROOT constraint).** `case_III_arm_realization` (`Arms.lean:74`) takes ONE `(Gv, ends, q)`
    and binds `hρGv` (`:91`), `hwmem` (`:96`), `hends_Gv` (`:81`), `hne_Gv` (`:82`), and the rank
    certification (`:114`) ALL at the single `ofNormals Gv ends q`. The arm supplies `(Gv,ends,q) =
    (G−vᵢ, endsσρ, qρ)`, FORCED by the `hwmem` leaf `chainData_bottom_relabel` whose output lands at
    `(endsσρ, qρ)` (`:1982–1986`). ∴ the engine's `hρGv` is required at `(endsσρ, qρ)` — not negotiable.
  - **Slot core.** `chainData_freshEdge_slot_mem` (`:4158`) is parametric over a SINGLE `ends` (`:4161`):
    `hφ` is consumed at `ofNormals (G−v₁) ends (shiftSeedAdv q 0)` = `(ends, q)` (`:4165–4168`,
    `shiftSeedAdv q 0 = q`), and the conclusion is at `(ends, shiftSeedAdv q (i−1))` = `(ends, qρ)`
    (`:4174–4177`). To land the engine's `(endsσρ, qρ)` conclusion, it MUST be called with `ends := endsσρ` —
    which pins its `hφ` slot at `(endsσρ, q)`. The arm does exactly that (`:4709`, `ends := endsσρ`).
  - **A-1.** `exists_candidateRow_bottomRows_of_rigidOn` (`:400`) produces `hingeRow (ends e₀).1 (ends e₀).2 ρ`
    at `ofNormals Gv ends q` (`:420`), member TIED to `(ends e₀)` (it MOVES with the selector), blocks at
    `block_ends(eⱼ)` (`:431/442`). So A-1@`ends₀` gives the genuine `(ends₀, q)` (right member, wrong
    framework for the slot core); A-1@`endsσρ` gives `(endsσρ, q)` but at the WRONG member `hingeRow
    (endsσρ e₀)…` (`endsσρ e₀ = (σ⁻¹ vᵢ, σ⁻¹ vᵢ₊₁)`, since `shiftEdgePerm i e₀ = edge i`). Neither is
    `hingeRow v₀ v₂ ρ₀`@`(endsσρ, q)`. ∴ `(endsσρ, q)` is the fold's start slot and NOTHING in tree concludes
    a membership in it — the artifact is REAL. **The premise stands; the seam is not dissolved by re-reading.**

  *(a) DIRECTION (1) — advance selector AND seed in lockstep (genuine `(ends₀, q)` start, relabel absorbed
  step-by-step). VERDICT: DEAD — the named obstruction is the per-step gate's edge-support restriction, and
  it is STRUCTURAL, not a proof-shape gap.* This is ROUTE α's intent (§I.8.13–I.8.15) and the prompt's clause
  (1)(c)'s "needs a NON-gate fold mechanism" — re-derived here against the landed gate. The membership fold
  runs `i−1` steps `s = 0,…,i−2`; at step `s` the gate `funLeft_dualMap_sub_acolumn_seedAdvance_mem_span_
  rigidityRows` (`Relabel.lean:1201`) permits the per-step selector move `ends → ends'` ONLY via `hends'_off :
  ∀ f, f ≠ edge(s+1) → f ≠ edge(s+2) → ends' f = ends f` (`:1204`). So the ACCUMULATED selector can differ
  from `ends₀` only on `⋃ₛ {edge(s+1), edge(s+2)} = {edge 1,…,edge i}`. But `endsσρ = σ⁻¹ ∘ ends₀ ∘
  shiftEdgePerm i` differs from `ends₀` on the support of `shiftEdgePerm i = formPerm [edge 0, e₀, edge i,
  edge 1,…,edge(i−1)]`, which INCLUDES `edge 0` and `e₀` — both OUTSIDE `{edge 1,…,edge i}` (I.8.15 PROBE
  A/B/E, Lean-verified: `shiftEdgePerm i e₀ = edge i`, `shiftEdgePerm i (edge 0) = e₀`). And `edge 0 = v₀v₁`
  is a SURVIVING link of `G−vᵢ` for `i ≥ 2` (I.8.15 PROBE C/D), so the discrepancy is load-bearing on the
  span, not free-on-non-links. **THE LEAN CONSTRUCT + WHY:** the gate's `hends'_off` edge-support window
  `{edge(s+1), edge(s+2)}` cannot accumulate to a cycle that moves `edge 0`/`e₀`; `shiftEdgePerm i` is an
  `(i+2)`-cycle threading the fresh `e₀`/top `edge i` with NO ascending-adjacent-swap factorization (no
  `shiftEdgePerm_eq_swap_mul` analogue of the vertex `shiftPerm_eq_swap_mul`, `Operations.lean:1522`; the
  vertex side telescopes precisely because `shiftPerm i.castSucc` is the consecutive-vertex cycle, a product
  of adjacent swaps — the edge cycle is not). "A non-gate fold mechanism" is exactly the ask, but a fold
  whose per-step membership transport is NOT the landed gate is a from-scratch span-transport machine for the
  relabel — which is no longer a "fold over the gate" at all; it is the whole-relabel transport of (b)/(2)
  applied to a span membership, where the member-mapping wall lives. So direction (1) is not a leaf re-shape:
  it either uses the gate (DEAD by the edge-support window) or abandons the fold for whole-relabel transport
  (= (2)'s wall). **DEAD.**

  *(b) DIRECTION (2) — re-shape the fold so the consumed `hφ` sits at `(endsσρ, qρ)` or `(ends₀, q)` DIRECTLY.
  VERDICT: DEAD as a fold re-shape — both targets fail against the landed machinery; the named obstruction is
  the same member-mapping wall, now pinned at the seed-coupling level.* Two sub-targets, each Lean-checked:
  - **(2-engine) consume `hφ` at the engine `(endsσρ, qρ)` directly.** The slot core's conclusion IS at
    `(endsσρ, qρ)`; consuming `hφ` there would make the fold trivial (`hφ` = the conclusion). But there is no
    source for `hingeRow v₀ v₂ ρ₀ ∈ span (ofNormals (G−vᵢ) endsσρ qρ)`: that is a redundancy at the CANDIDATE
    framework, and KT's redundancy lives at the BASE `(G₁,q₁)` (eq. 6.66 establishes `r` against
    `R(G₁,q₁)`). The genuine-row brick `chainData_bottom_relabel` DOES reach `(endsσρ, qρ)` — but by applying
    the WHOLE relabel `(funLeft σ⁻¹).dualMap` to the member (`:1982`), which MOVES the member off `hingeRow
    v₀ v₂ ρ₀` (to `hingeRow v₀ v₁ ρ₀`, since `σ⁻¹ v₂ = v₁` for `i ≥ 2`). The slot core needs the member held
    FIXED at `hingeRow v₀ v₂ ρ₀` (it is the eq.-(6.66) `r̂` carried across the panels). **THE LEAN CONSTRUCT +
    WHY:** `hφ` is a row-SPAN membership of a SPECIFIC functional; the only landed `(ends₀,q)→(endsσρ,qρ)`
    transport (`chainData_bottom_relabel` / `rigidityRows_ofNormals_relabel`) is the relabel-image map, which
    by construction transforms the member — it cannot deliver a FIXED member at the relabelled framework. The
    member-mapping wall (4th–5th touch, I.8.12 R-2(iii) / I.8.17(b)) is exactly this.
  - **(2-base) consume `hφ` at the base `(ends₀, q)` directly while landing the conclusion at `(endsσρ, qρ)`.**
    This is the IDEAL (it is what the perp half achieves). It requires a fold whose START framework is
    `(ends₀, q)` and whose END is `(endsσρ, qρ)` — i.e. the selector must move `ends₀ → endsσρ` ACROSS the
    fold. That is precisely direction (1), which is DEAD by (a). The seed-fixed fold (`:1807`) holds the
    selector CONSTANT, so starting at `ends₀` lands the conclusion at `(ends₀, qρ)`, NOT `(endsσρ, qρ)` — the
    wrong framework for the engine (R-2(iv)'s candidate-TOP failure, I.8.12: `ends₀` does not record `G−vᵢ`'s
    interior links, so even the conclusion framework is ill-recorded). **THE LEAN CONSTRUCT + WHY:** the fold
    lemma takes ONE `ends` used at BOTH start and conclusion (`:1809`); the ONLY landed way to make start and
    conclusion selectors DIFFER is the per-step gate, whose edge window forbids the `edge 0`/`e₀` move (=(a)).
    **DEAD.** Why the PERP half escapes and `hφ` cannot (the asymmetry, re-confirmed): the perp transport
    `chainData_freshEdge_perp_transport_base_to_candidate` (`:4534`) carries a SCALAR `ρ₀ ⊥ supportExtensor
    (edge s) = 0` — support extensors are GRAPH-INDEPENDENT (`ofNormals_supportExtensor_relabel_perm`,
    `:4552`), so the candidate's `edge s` extensor EQUALS the base's at `shiftEdgePerm i (edge s)`; a clean
    rewrite, no member. `hφ` is a span membership of a fixed functional; there is no member-free transport.
    The perp's success is NOT evidence the `hφ` transport is feasible — they are different objects.

  *(c) THE KT CROSS-CHECK — the artifact is a LEAN-MODELLING CHOICE a different (still KT-faithful) fold shape
  would NOT incur; KT NEVER forms `(endsσρ, q)`.* Read end-to-end, KT §6.4.2 eqs. (6.60)–(6.64) (pp. 696–697)
  has exactly TWO frameworks: the base `(G₁, q₁) = G−v₁` and the candidate `(G, pᵢ)`. The isomorphism `ρᵢ`
  (6.54) and the framework `(Gᵢ, qᵢ)` "which is exactly the same framework as `(G₁, q₁)`" (6.55) are a
  RELABELLING, not a third geometry. The mechanism (6.60→6.61): KT writes `R(G, pᵢ)` (eq. 6.60), performs
  COLUMN OPERATIONS (add `vᵢ`'s columns to `vᵢ₊₁`'s) and substitutes (6.59), and the result "contains
  `R(G₁, q₁)` as its submatrix" (eq. 6.61) — `R(G,pᵢ)` IS `R(G₁,q₁)` plus the `Mᵢ` block. The ROW
  CORRESPONDENCE (6.62) is then a bookkeeping map between WHICH ROWS of the SINGLE matrix `R(G,pᵢ)` correspond
  to which rows of its `R(G₁,q₁)` submatrix; "the column correspondence follows from the isomorphism `ρᵢ`."
  The redundant `(v₀v₂)ᵢ∗` row of `R(G₁,q₁)` corresponds to the `(v₀v₁)ᵢ∗` row of `R(G,pᵢ)` (6.62, last line),
  and KT carries the redundancy `±r` (6.66) by applying the SAME row operations (weights `λ`, eq. 6.63)
  WITHIN `R(G,pᵢ)`. **KT's "advancing" is the column-operation reframe of ONE matrix; there is no chain of
  `d−1` intermediate frameworks, no per-step seed-advance materialized as distinct `ofNormals` objects, and
  emphatically no `(relabelled-selector, un-advanced-seed)` hybrid.** The Lean's `(endsσρ, q)` arises ONLY
  because the Lean models the (6.62) row-correspondence as a SEED-ADVANCING FOLD over `d−1` genuinely-distinct
  `ofNormals (G−vₛ₊₁) ends (shiftSeedAdv q s)` frameworks (the W9a per-step `a`-column transport,
  `shiftBodyListAsc_foldl_mem_span_rigidityRows`), with the relabel PRE-APPLIED to the selector (`endsσρ`
  everywhere, including the start) while the seed advances inside the fold. The fold's start state
  `(endsσρ, q)` is an internal fold configuration, not a KT framework. **CONCLUSION: the artifact is a
  Lean-modelling choice of the eq.-(6.60→6.64) realization — KT's whole-matrix column-op-then-row-correspond
  shape does NOT incur it.** A Lean realization that mirrors KT's shape (build `R(G,pᵢ)`'s span ONCE, exhibit
  `R(G₁,q₁)`'s rows as a sub-span via the column-op identity, and carry the redundancy by row operations
  WITHIN that single span — never folding through intermediate seed-advanced frameworks) would consume `hφ`
  at the base `R(G₁,q₁)` = `(ends₀, q)` DIRECTLY, exactly where A-1 produces it.

  **VERDICT — for each direction, and the headline.**
  - **Direction (1): DEAD.** Named obstruction: the per-step gate `funLeft_dualMap_sub_acolumn_seedAdvance_
    mem_span_rigidityRows`'s `hends'_off` edge-support window `{edge(s+1), edge(s+2)}` cannot accumulate to
    the `(i+2)`-cycle `shiftEdgePerm i` (which moves `edge 0`/`e₀`, both load-bearing surviving links of
    `G−vᵢ` and outside the window); `shiftEdgePerm i` has no ascending-adjacent-swap factorization. A
    non-gate per-step fold is not a fold-over-the-gate; it degenerates to (2)'s whole-relabel transport.
  - **Direction (2): DEAD as a fold re-shape.** Named obstruction: both targets reduce to the member-mapping
    wall. `(endsσρ, qρ)` has no fixed-member source (the only landed transport, `chainData_bottom_relabel`,
    is the relabel-image map and MOVES the member to `hingeRow v₀ v₁ ρ₀`); `(ends₀, q)`-start-to-`(endsσρ,
    qρ)`-end requires a selector-advancing fold = direction (1).
  - **HEADLINE: NO LOCAL FOLD RE-SHAPE WORKS without a contract/motive change — and that is the honest,
    high-value verdict (it escalates, it is not a failure of the pass).** Crucially, it is NOT
    contract/motive-blocked either: the seam is a *machinery*-level Lean-modelling choice, BELOW the
    CHAIN↔ENTRY contract. The slot core / fold / engine-slot-binding are all infrastructure beneath the
    dispatch (C.3) and beneath the `ChainData` record (C.1); re-architecting them touches NEITHER. **What the
    fix requires is an ASSEMBLY-LEVEL re-write of the KT eq.-(6.60→6.64) Lean realization** — replace the
    seed-advancing materialized fold (`shiftBodyListAsc_foldl_mem_span_rigidityRows` + the slot core
    `chainData_freshEdge_slot_mem` + the W9a per-step gate, as the `hφ`-carrying spine) with a KT-faithful
    whole-matrix shape (exhibit `R(G₁,q₁)`'s span as a sub-span of `R(G,pᵢ)`'s via the column-op identity
    (6.60→6.61), carry the redundancy by in-matrix row operations (6.63), so `hφ` is consumed at the BASE
    `(ends₀, q)` directly). This is a genuinely-new realization architecture, NOT a next-leaf and NOT
    pre-dischargeable here. **CONTRACT/MOTIVE STATUS:** NO contract clause (C.0–C.6) and NO motive/IH change
    is *required* by the re-architecture itself — it is machinery below the contract. (The earlier I.8.16
    "C.0 third lockstep decl" delta was for the source-PRODUCTION fix, B1/3b, now DEAD by I.8.17; the
    whole-matrix re-architecture does not produce `hφ@endsσρ` at all, so that delta evaporates.) The decision
    for the user is therefore NOT a contract sign-off but a SCOPE call: **(A)** open an ASSEMBLY-level recon
    to re-shape the eq.-(6.60→6.64) realization to KT's whole-matrix form (the only route that dissolves the
    artifact; cost UNKNOWN — it re-touches the genuinely-new `hφ`-spine, est. a multi-leaf recon-first
    sub-phase, NOT a 3–5c build), or **(B)** carry `hφ@endsσρ` as a hypothesis on the arm/dispatch (the
    landed `chainData_relabel_arm_hρGv` shape) and confront the wall at ENTRY where the base realization is
    in scope — flagged LIKELY-DEAD already (I.8.12 ROUTE β, I.8.15 B3: the hybrid re-derives via A-1 at the
    wrong member, needing a member-bridge = the same wall, likely circular). **RECOMMENDATION: (A), as a
    recon-first ASSEMBLY-level re-architecture, treated as its own scoping sub-phase** — it is the single
    route that attacks the root cause (the materialized-fold modelling of KT (6.62)) rather than the symptom.

  **CLAUSE (ii) HONESTY.** This is a FLAG-DON'T-FORCE close: both local directions are pinned DEAD with the
  precise Lean construct naming each obstruction (the gate's edge-support window; the member-mapping wall),
  at the §I.8.15/I.8.17 standard, and the load-bearing artifact premise was RE-DERIVED from the landed engine
  / slot-core / A-1 bodies rather than inherited. It does NOT manufacture a buildable route: the only route
  that dissolves the artifact (the KT whole-matrix re-architecture) is named as genuinely-new architecture
  with UNKNOWN cost and explicitly NOT scoped into leaves here — that is the honest escalation. No
  contract/motive change is forced (the seam is machinery below C.0–C.6), so the user decision is a SCOPE
  call (A vs B), not a contract sign-off. No Lean landed; `chainData_relabel_arm_hρGv` stays a CORRECT
  carried-hypothesis lemma; the orphaned ROUTE-α leaf 1 `shiftEndsAdv` + `_zero`/`_succ` (+ T-1/T-2) await
  confirm-and-delete at the re-architecture-settle commit; `d=3` M₃ unaffected (`i=2`, no `hφ` slot).

---

## WHOLE-MATRIX RE-ARCHITECTURE — leaf-decomposition attempt + LEAF-C REFUTATION (§(o‴)(I.8.19))

> **⚠ SUPERSEDED HEADLINE — read the §(I.8.19)-ADDENDUM (end of this sub-section) FIRST.** The "BUILDABLE"
> verdict below is RETRACTED: LEAF C ("re-fire A-1 at the candidate") is UNSOUND — it re-introduces the
> design-rejected Fix B (per-`i` re-seed), because A-1 is EXISTENTIAL in `ρ` and the landed dispatch requires
> a SINGLE shared `ρ₀` (KT eq. 6.66). The §I.8.19(a) "no member-mapping transport, so the seam never arises"
> claim is RETRACTED. The corrected crux + the live open question are in the ADDENDUM. The (0)–(e) body below
> is kept as the recon trail that PRODUCED the refutation (F1/F2 survive as necessary-not-sufficient; LEAF A
> survives; the "confirmed orphans" claim is downgraded to "candidate" by the ADDENDUM).

**(I.8.19) WHOLE-MATRIX RE-ARCHITECTURE DESIGN-PASS — original (RETRACTED) VERDICT: BUILDABLE leaf
decomposition, with the
genuinely-new crux (LEAF B, the column-op submatrix-containment span identity) flagged P=3-route-but-
de-risk-first. The unblock §(I.8.18) named (re-shape the eq.-(6.60→6.64) realization to KT's whole-matrix
form so `hφ` is consumed at the BASE `(ends₀,q)` directly) decomposes into a concrete ordered leaf sequence
with exact signatures + a reuse/orphan map + a named FIRST leaf + a commit-count estimate (2026-06-21, opus
design-pass; every load-bearing claim re-derived from the landed `def`/`theorem` bodies — A-1
`Candidate.lean:400`, the engine/rank-cert `Arms.lean:72`/`Candidate.lean:1472`, the d=3 M₃ arm
`Relabel.lean:2537`, CHAIN-1 `RigidityMatrix/Basic.lean:872–1446`, the slot-core/fold/gate spine, KT §6.4.2
eqs. (6.59)–(6.67) pp. 694–698 read directly — NOT inherited from the prior pins; docs-only, no Lean, tree
byte-clean).**

  *(0) THE FOUR SOURCE-VERIFIED FACTS THIS DECOMPOSITION RESTS ON (each Lean-read this pass, line-cited):*

  - **F1 — A-1 is fully parametric in `(Gab, Gv, ends, q)`, NOT pinned to the base graph.**
    `exists_candidateRow_bottomRows_of_rigidOn` (`Candidate.lean:400`) takes generic `{Gab Gv}`, a split
    relation (`hle`/`hsplit`/`he₀`), the rigid-on hyp `hrig` at `ofNormals Gab ends q`, and the eq.-(6.22)
    lower bound, and produces the candidate redundancy `ρ`, the bottom rows `w`, AND the edge-grouped form
    `hingeRow (ends e₀).1 (ends e₀).2 ρ = ∑ⱼ cGv j • hingeRow (uvGv j)(vvGv j)(rvGv j)` at `ofNormals Gv
    ends q` (`:420/444`). The member `hingeRow (ends e₀).1 (ends e₀).2 ρ` is TIED to `(ends e₀)` — it moves
    with the selector. **Consequence:** A-1 can be invoked at the CANDIDATE data `(Gab := G.splitOff at vᵢ,
    Gv := G−vᵢ, ends := endsσρ, q := qρ)` directly — IF its hypotheses (rigid-on at the candidate, the
    eq.-(6.22) lower bound at the candidate) can be discharged there. This is the whole-matrix route's spine:
    produce the candidate `hρGv`/`hwmem` at the candidate framework directly, never transporting a base
    span membership through a fold.
  - **F2 — the engine + rank-cert bind ALL slots at ONE `(Gv, ends, q)`, and `hρGv`/`hwmem` are exactly
    A-1's outputs.** `case_III_arm_realization` (`Arms.lean:72`) / `case_III_rank_certification`
    (`Candidate.lean:1472`) take `(G Gv ends q v a b e_a e_b)` and consume `hρGv : hingeRow a b ρ ∈ span
    (ofNormals Gv ends q).rigidityRows` (`:91`/`:1486`) + `hwmem` (the `D(|Gv|−1)` bottom rows, `:96`/`:1491`).
    These are BYTE-MATCHED to A-1's outputs (`ρ ≠ 0`, `ρ(C(e₀)) = 0`, `hingeRow … ρ ∈ span Gv-rows`, `w`
    independent + per-tagged). So if A-1 fires at the candidate `(G−vᵢ, endsσρ, qρ)`, its outputs feed the
    engine at the candidate with NO transport. **The engine/rank-cert are already general-`k` and already
    parametric in `(Gv, ends, q)` — they need NO change for the whole-matrix route.**
  - **F3 — at d=3 the M₃ arm produces the candidate `hρGv` by a SINGLE-STEP W9a transport, and the member
    MOVES — there is no `hφ@endsσρ` artifact at d=3.** `case_III_arm_realization_M3` (`Relabel.lean:2537`)
    takes `hρGv` at the BASE `ofNormals (G−v) ends₀ q` (`:2562`), and produces the engine's candidate-side
    `hρGv` (at `G−a, ends₃, qρ`) via `funLeft_dualMap_sub_acolumn_mem_span_rigidityRows` (the carrier-level
    single-step W9a, `Relabel.lean:865`) applied to `φ := hingeRow a b ρ` (`:2699–2706`): the image is
    `hingeRow v b ρ` (member MOVED by the swap `a↔v`), and the arm recombines with the genuine `e_b`-row by
    `Submodule.sub_mem`. **The single swap moves the member and the arm absorbs the moved part into a genuine
    row — exactly KT's row-correspondence (6.62) at d=3.** The general-`d` slot core's artifact is that it
    pre-applies the relabel to the selector and runs a SEED-ADVANCING fold whose start framework is
    `(endsσρ, q)`; the d=3 arm never does this (the single step uses base `ends₀` at the start and the W9a
    `funLeft` carries the relabel as it moves the member).
  - **F4 — CHAIN-1 supplies the LI-side column-op machinery, NOT a span-membership submatrix identity.**
    `RigidityMatrix/Basic.lean` gives: `columnOp hva` (the `≃ₗ` `col_a += col_v`, eqs. 6.14–6.16, `:884`),
    `hingeRow_comp_columnOp_apply` (the candidate row → pure `v`-column under `Φ`, `:956`),
    `linearIndependent_sumElim_candidateBlock_swap` (the eq.-(6.62) row-correspondence as LINEAR
    INDEPENDENCE preservation: correcting candidate rows by old/new-block-span elements preserves LI,
    `:1328`), and `linearIndependent_sum_augment_candidateRow_block` (the column-operated block-triangular
    `+|ιc|` augment, `:1371`). **What CHAIN-1 does NOT supply:** a lemma exhibiting `span (R(G₁,q₁))-rows ⊆
    span (R(G,pᵢ))-rows` (the (6.60→6.61) submatrix containment AS A SPAN INCLUSION), nor the transport of
    the redundancy MEMBERSHIP `hingeRow v₀v₂ ρ₀ ∈ span(base)` into a membership `hingeRow v₀v₁ ρ₀ ∈
    span(candidate)` via the column op. CHAIN-1's lemmas are about INDEPENDENCE (the rank-lift `+1`/`+|ιc|`),
    used by `case_III_rank_certification` INTERNALLY; they are NOT the span-membership identity the
    whole-matrix `hρGv` route needs. **This is the prompt's clause-(i) warning, confirmed: do not assume
    CHAIN-1 supplies the column-op span identity — it supplies the LI half, not the span-membership half.**

  *(a) THE RE-ARCHITECTURE SHAPE — produce `hρGv` AT THE CANDIDATE, not transport from base.* By F1/F2, the
  cleanest KT-faithful Lean shape is: **drop the seed-advancing fold spine entirely and re-derive the
  candidate redundancy + bottom rows at the candidate framework `(G−vᵢ, endsσρ, qρ)` by invoking A-1 there.**
  A-1's outputs ARE the engine's `hρGv`/`hwmem` slots (F2), so the arm becomes a direct
  `case_III_arm_realization` application with A-1@candidate filling the slots — no member-mapping transport,
  so the `hφ@endsσρ` seam never arises (it was an artifact of the transport-from-base fold, §I.8.18). The
  ONLY new obligations are A-1's hypotheses AT THE CANDIDATE: (i) the candidate framework is rigid-on its
  vertex set (`hrig`), and (ii) the eq.-(6.22) nested-IH rank lower bound holds at the candidate
  (`h622lb`). Both are KT's, and both are already discharged at the BASE by the dispatch (the d=3 dispatch's
  `hrig'`/`h622lb` at `Realization.lean:390–391`). **The whole-matrix re-write = transport the RIGIDITY +
  the RANK-BOUND (graph/seed facts, member-free) base→candidate, then fire A-1 at the candidate.** This is
  the asymmetry §I.8.18(b) named: the perp half escaped because it transports a member-free SCALAR; rigidity
  and the rank bound are likewise member-free (a `finrank`/`IsInfinitesimallyRigidOn` fact), so they
  transport cleanly across the relabel — UNLIKE the fixed-member span membership the dead fold tried to move.

  *(b) THE LEAF SEQUENCE (dependency-ordered; exact signatures; REUSE / NEW / ADAPT tagged). All under
  `CaseIII/Relabel.lean` unless noted; all `[Finite α] [Finite β] [DecidableEq α/β]` per the arm idiom; `cd
  : G.ChainData n`, `i : Fin cd.d`, `h2i : 2 ≤ (i:ℕ)`, the relabelled `endsσρ`/`qρ` as in
  `chainData_relabel_arm_hρGv` `:4688–4691`.*

  - **LEAF A — candidate rigid-on transport (the rigidity half; ADAPT of the d=3 GP-seed pattern).**
    `chainData_candidate_rigidOn`: from the BASE framework's rigid-on / general-position fact (the dispatch's
    `hrig'`, the IH-generic base realization) produce the candidate framework's rigid-on:
    ```
    (hrigBase : (ofNormals (G.splitOff (vtx 1)(vtx 0)(vtx 2) e₀) ends₀ q).toBodyHinge.IsInfinitesimallyRigidOn …)
      → (ofNormals (G.splitOff (vtx i.succ)(vtx (i−1))(vtx (i+1)) e₀') endsσρ qρ).toBodyHinge.IsInfinitesimallyRigidOn …
    ```
    Mechanism: `IsInfinitesimallyRigidOn` is a `finrank (span rigidityRows) ≥ D(|V|−1)` fact (member-free);
    the candidate framework is the base RELABELLED by `(shiftPerm i.castSucc)`, and the relabel is a `≃ₗ` on
    the screw assignments, so the row-span finrank is invariant. REUSES the landed
    `ofNormals_supportExtensor_relabel_perm` + `removeVertex_genuine_shiftRelabel` (the genuine-link
    transport, already landed for `chainData_bottom_relabel`) + the rank-invariance-under-relabel
    (`funLeft … ≃ₗ`). **P=2** (the transport machinery is the same already-landed relabel-image kit; this is
    its rank/rigidity restatement, member-free). This is the rigidity analogue of the d=3 dispatch's
    `hGPva`/`hrig'` (`Realization.lean:577`).
  - **LEAF B — candidate eq.-(6.22) rank lower bound transport (the rank-bound half; the GENUINELY-NEW
    crux — see (c)).** `chainData_candidate_h622lb`: from the base eq.-(6.22) nested-IH lower bound
    (`case_III_nested_rank_lower_all_k`, landed, `Realization.lean:616`) at `(G−v₁, ends₀, q)`, produce the
    same bound at the candidate `(G−vᵢ, endsσρ, qρ)`:
    ```
    (hlbBase : D(|V(G₁)|−1) − (D−2) ≤ finrank (span (ofNormals (G−v₁) ends₀ q).rigidityRows))
      → D(|V(Gᵢ)|−1) − (D−2) ≤ finrank (span (ofNormals (G−vᵢ) endsσρ qρ).rigidityRows)
    ```
    Mechanism: again a member-free `finrank` fact transported across the `(shiftPerm i.castSucc)` relabel
    (`|V(G−vᵢ)| = |V(G−v₁)|`, vertex counts preserved by the cycle). **The crux** is whether the
    relabel-image row-span at the candidate has the SAME finrank as the base — i.e. whether the relabel
    `≃ₗ` carries `(ofNormals (G−v₁) ends₀ q).rigidityRows` to a SPANNING set of `(ofNormals (G−vᵢ) endsσρ
    qρ).rigidityRows` (so the spans are isomorphic). This is the (6.60→6.61) submatrix-containment expressed
    as a SPAN EQUALITY-UP-TO-RELABEL — the column-op identity in span form. **P=3** (no landed lemma; the
    de-risk question in (c)).
  - **LEAF C — the candidate-framework A-1 invocation (the assembly; NEW but mechanical given A/B).**
    `chainData_relabel_arm_hρGv_wholeMatrix` (REPLACES `chainData_relabel_arm_hρGv`): fire A-1
    (`exists_candidateRow_bottomRows_of_rigidOn`) at `(Gab := G.splitOff at vᵢ, Gv := G−vᵢ, ends := endsσρ,
    q := qρ, e₀ := the candidate fresh edge)` with LEAF A's `hrig` + LEAF B's `h622lb`, and read off `hρGv`
    (the candidate-side `hingeRow vᵢ₊₁ vᵢ₋₁ (−ρ₀) ∈ span (ofNormals (G−vᵢ) endsσρ qρ).rigidityRows` — the
    M₃-sign `−ρ₀`, after the `hingeRow_swap`/sign normalization the d=3 dispatch does at
    `Realization.lean:412–427`). Same conclusion type as the current `chainData_relabel_arm_hρGv` `:4680`,
    so the dispatch wiring (2c-iii) is unchanged. **P=2** (mechanical: A-1's signature is the consumer's,
    F1/F2; the splice-edge/recorded-orientation bookkeeping mirrors the d=3 `hsupp_e₀`/`hrec'` dance,
    `Realization.lean:397–427`).
  - **LEAF D (STAYS, reused as-is) — the genuine-row `hwmem` half.** `chainData_bottom_relabel`
    (`:1961`, landed). Either it is kept (the bottom rows transported base→candidate), OR — cleaner — A-1 at
    the candidate (LEAF C) ALSO outputs the candidate bottom rows `w` directly (A-1's `w`/`hwmem` outputs,
    F1), making `chainData_bottom_relabel` itself orphanable. **DECISION FLAG (c′):** keep
    `chainData_bottom_relabel` for the first build (it is landed, axiom-clean, and the bottom-row transport
    is genuinely member-moving-but-fine because the engine's `hwmem` ALLOWS the moved `(ab)`-block tag); fold
    it into LEAF C only if the candidate-A-1 `w` proves cleaner. **P=2 either way (no new math).**

  *(c) THE HARDEST LEAF = LEAF B, and its de-risk-first plan (FLAG-DON'T-FORCE).* LEAF B asks: does the
  relabel `(shiftPerm i.castSucc)`-image of `(ofNormals (G−v₁) ends₀ q).rigidityRows` SPAN the same subspace
  (up to the `funLeft` `≃ₗ`) as `(ofNormals (G−vᵢ) endsσρ qρ).rigidityRows`? KT's (6.60→6.61) says YES in
  matrix terms (the column op + (6.59) substitution makes `R(G₁,q₁)` literally a submatrix of `R(G,pᵢ)`,
  and the row correspondence (6.62) is a bijection of the surviving rows). The Lean question is whether this
  is a clean `≃ₗ`-image span equality or whether it hides the SAME member-mapping difficulty. **The de-risk
  signal (POSITIVE):** LEAF A already transports rigid-on (a `finrank ≥` fact) across the SAME relabel, and
  `chainData_bottom_relabel` (landed) already transports the WHOLE row-disjunction (genuine rows +
  `(ab)`-block tag) across this relabel per-member — so the relabel-image of the base rows IS the candidate
  rows (genuine ↦ genuine, fresh-pair ↦ fresh-pair), which is exactly the span equality LEAF B needs, at the
  SPAN level rather than per-member-with-fixed-member. **Why LEAF B is NOT the dead `hφ` seam:** the `hφ`
  seam was DEAD because it needed a FIXED member (`hingeRow v₀v₂ ρ₀`) held still across the relabel; LEAF B
  needs only that the relabel-image of the base ROW SET spans the candidate ROW SET — a member-FREE span
  equality (the members are allowed to move, as `chainData_bottom_relabel` already shows they do). **So LEAF
  B inherits the asymmetry §I.8.18(b) identified as the escape hatch.** Still flagged **P=3** because no
  landed lemma states the span equality and the `finrank`-transport-across-`≃ₗ` over the relabelled
  `ofNormals` carrier may hit the §38 defeq trap; **DE-RISK FIRST** (build a single `i=3` instance of the
  span-equality before pinning LEAF B's general-`i` signature — the row-321 discipline, the same gate that
  caught ROUTE α). **If the de-risk spike shows the span equality re-hides the member-mapping wall** (e.g.
  the relabel-image span is provably a PROPER subspace because the candidate has interior links the base
  lacks at the relabelled selector), LEAF B is the genuine obstruction — STOP and escalate at the
  §I.8.15/I.8.18 standard; the whole-matrix route then also fails and the residue is route B (carry to
  ENTRY, likely-dead). **This is the honest P=3 flag the clause-(ii) bar requires: LEAF B has a
  de-risk-able route (the relabel-image span equality, supported by the landed per-member transport) but NOT
  a guaranteed close.**

  *(d) REUSE / ORPHAN MAP.*
  - **REUSE AS-IS (member-free transport + the carrier kit + A-1/engine):** A-1
    `exists_candidateRow_bottomRows_of_rigidOn` (fired at the candidate, F1); the engine
    `case_III_arm_realization` + `case_III_rank_certification` (parametric in `(Gv,ends,q)`, F2); the
    single-step carrier W9a `funLeft_dualMap_sub_acolumn_mem_span_rigidityRows` (`:865`, the d=3 building
    block); `ofNormals_supportExtensor_relabel_perm` (`:63`); `removeVertex_genuine_shiftRelabel`;
    `chainData_bottom_relabel` (LEAF D); `case_III_nested_rank_lower_all_k` (the base h622lb,
    `Realization.lean:616`); the perp leaves (`chainData_freshEdge_perp_of_baseRedundancy`,
    `_transport_base_to_candidate`, `_slot_perp`) IF the perp half is still needed by the candidate-A-1
    route — **re-check at LEAF C build:** if A-1@candidate produces `hρGv` directly as a span membership
    (not via the slot-core peel), the per-edge perp obligations evaporate (they were the slot core's
    `hperp` slot), and the whole perp sub-tree (`_slot_perp`, `_perp_of_baseRedundancy`, the LEAF-1–4 chain
    induction, the telescope `wstep_foldl_hingeRow_telescope`) becomes orphanable TOO. **FLAG:** the perp
    sub-tree's fate is decided at LEAF C — list it as a confirm-and-delete CANDIDATE, not a confirmed
    orphan, until LEAF C's A-1@candidate shape is built.
  - **CONFIRMED ORPHAN (confirm-and-delete at the re-architecture-land commit, `git grep` zero callers):**
    the seed-advancing `hφ`-spine subtree, whose ONLY caller is the to-be-replaced arm: (1) the slot core
    `chainData_freshEdge_slot_mem` (`:4158`, sole caller = `chainData_relabel_arm_hρGv` `:4709`); (2) the
    fold spine `shiftBodyListAsc_foldl_mem_span_rigidityRows` (`:1807`, sole caller = the slot core
    `:4213`); (3) the seed-advancing gate `funLeft_dualMap_sub_acolumn_seedAdvance_mem_span_rigidityRows`
    (`:1201`, sole caller = the fold spine `:1226`) + its `seedAdvance_wstep_hstep` bundle + the
    `shiftBodyFrameworkAscTotal`/`_eq`/`shiftBodyListAsc`/`shiftBodyFrameworkAsc`/`shiftSeedAdv` fold
    scaffolding (callers within the orphaned subtree only — verify with `git grep` at the delete commit);
    (4) `chainData_relabel_arm_hρGv` itself (`:4647`, replaced by LEAF C); (5) the ALREADY-ORPHANED ROUTE-α
    leaf 1 `shiftEndsAdv`/`_zero`/`_succ` (`:1731`) + T-1/T-2 (`:4427`/`:4464`). **The perp sub-tree (above)
    is a SEPARATE confirm-and-delete decision at LEAF C.**
  - **STAYS (untouched):** everything the d=3 M₃ arm uses (`case_III_arm_realization_M3`,
    `case_III_bottom_relabel`, the single-step W9a, the dispatch `case_III_candidate_dispatch`); the CHAIN-1
    LI machinery (`columnOp` + the augment lemmas — used by `case_III_rank_certification` internally, NOT by
    the `hρGv` route); CHAIN-3/4 (the discriminator). **`d=3` M₃ (`i=2`) MUST stay zero-regression** — it
    has no `hφ` slot, no fold, no seam (F3); the re-architecture touches ONLY the general-`d` chain arm
    (`i ≥ 2` with `cd.d ≥ 3`), and the `d=3`/`k=2` wrapper instantiates the unchanged M₃ arm.

  *(e) FIRST CONCRETE LEAF + COMMIT ESTIMATE.* **FIRST = LEAF A** (`chainData_candidate_rigidOn`, the
  member-free rigid-on transport, P=2) — it is the leaf-most (depends only on the landed relabel kit), it
  de-risks the "member-free facts transport cleanly across the relabel" premise the whole route rests on,
  and it is the rigidity analogue of an already-landed d=3 pattern. **COMMIT ESTIMATE: 5–8 commits** for the
  whole sub-effort — LEAF A (1, P=2), LEAF B de-risk spike (1) + LEAF B general-`i` (1–2, P=3), LEAF C
  (1, P=2), the perp-subtree orphan decision + confirm-and-delete (1), the arm-shell + dispatch wire-up
  (1) — **PLUS** the contingency that LEAF B's de-risk spike fails (then STOP, escalate, ~1 commit to
  document the obstruction). **NO contract/motive change** (C.0–C.6 untouched, §I.8.18 confirmed: this is
  machinery below the dispatch C.3 + record C.1). The arm-shell + 2c-iii dispatch close stays as the
  §I.8.18 *Hand-off* names (`refine case_III_arm_realization` at `Gv=G−vᵢ`, `endsσρ`, `qρ`, the M₃-sign
  `ρ:=−ρ₀`, `hwmem ← chainData_bottom_relabel` OR candidate-A-1 `w`).

  **CLAUSE (i) HONESTY.** Every load-bearing claim was re-derived from the landed bodies this pass: F1 from
  A-1's actual `∃`-conclusion (`Candidate.lean:414–445`), F2 from the engine/rank-cert slot types
  (`Arms.lean:91/96`, `Candidate.lean:1486/1491`), F3 from the d=3 M₃ arm's actual `hρGv` derivation
  (`Relabel.lean:2562/2699–2710`), F4 from CHAIN-1's actual lemma statements (`Basic.lean:1328/1371` — LI,
  not span membership), and KT's mechanism from pp. 694–698 read directly. **CLAUSE (ii) HONESTY.** The
  hardest leaf (LEAF B) is flagged P=3 with a de-risk-first plan and an explicit STOP-and-escalate branch if
  the de-risk fails; it is NOT given a manufactured buildable-looking signature — its signature is stated as
  a TARGET with the open question (the span-equality-up-to-relabel) named, and the positive de-risk signal
  (the landed per-member transport already does the member-moving version) is distinguished from a
  guaranteed close. The route is BUILDABLE-MODULO-LEAF-B-de-risk; if LEAF B's spike refutes the span
  equality, the whole-matrix route fails and ENTRY-carry (route B) is the residue.

**(I.8.19)-ADDENDUM — LEAF C REFUTED: the decomposition re-introduces the design-rejected Fix B; the
"BUILDABLE" verdict + the §I.8.19(a) "no member-mapping transport" claim are RETRACTED (2026-06-21, opus
adversarial self-check, coordinator-verified verbatim against the landed dispatch).** An adversarial soundness
pass on LEAF C — try to REFUTE "fire A-1 fresh at the candidate" against the LANDED consumer — succeeded.
Grounded in the verbatim dispatch `case_III_candidate_dispatch` (`CaseIII/Realization.lean`):

  *(A) THE LANDED DISPATCH ESTABLISHES A SINGLE SHARED `ρ₀`, ONCE, AT THE BASE — verbatim.* A-1 fires ONCE
  (`:388–391`, `obtain ⟨ρ, w, …⟩ := exists_candidateRow_bottomRows_of_rigidOn (Gab := Gab)(Gv := Gv)(ends :=
  Q.ends)(q := q) …`); its single existential `ρ` is normalized ONCE to `ρ0` (`:404–411`, the `obtain ⟨ρ0,
  hρ0ne, hρ0e₀, hρ0Gv, hw0mem⟩` block — `ρ0 := ρ` or `−ρ` by the recorded `e₀`-orientation); the discriminator
  runs ONCE on that `ρ0` (`:439–441`, `exists_complementIso_ne_zero_of_homogeneousIncidence hρ0ne hp hn …`,
  returning `⟨u, n', hpair, hgate⟩`); and the SAME `ρ0` is threaded into EVERY arm across `fin_cases u`
  (`:502` `u=0` `exact hρ0Gv`, `:514` `u=1` identical, `:592` `u=2`/M₃ `hgate hρ0e₀ hρ0Gv`). The discriminator
  capstone `exists_complementIso_ne_zero_of_homogeneousIncidence_gen` (`Claim612.lean:1462`) takes ONE
  `{r : Module.Dual ℝ (ScrewSpace k)} (hr : r ≠ 0)` and returns `∃ u, … r (complementIso …) ≠ 0` — KT (6.65)/
  (6.67): one redundancy tested against all `d` panels. **Single-`r` is REQUIRED** (KT eq. (6.66) `±r` carry;
  matches the FIX-FORK Fix-B-infeasible ruling §(o‴)(H) and F3 — the d=3 M₃ arm at `u=2` does NOT re-fire A-1,
  it TRANSPORTS the shared `ρ0` via the single-step W9a, `Relabel.lean:2562/2699–2710`).

  *(B) THEREFORE LEAF C IS UNSOUND.* A-1's conclusion is `∃ ρ, …` (`Candidate.lean:414`); firing it at
  candidate `i` yields a FRESH `ρ_cand_i` satisfying candidate `i`'s conditions but NOT pinned to the
  discriminator-selected `ρ₀`. The chain dispatch must establish ONE `ρ₀`, run the discriminator on `ρ₀` to
  pick `i`, then build candidate `i`'s realization WITH `ρ₀`'s row `hingeRow v₀v₂ ρ₀ ∈ span (candidate i)` —
  the discriminator's full-rank guarantee is about `ρ₀(C(Lᵢ)) ≠ 0`, not `ρ_cand_i(C(Lᵢ)) ≠ 0`. Tying
  `ρ_cand_i` to `ρ₀` needs either (a) the fixed-member identity `hingeRow v₀v₂ ρ₀ ∈ span (candidate i)` = the
  dead member-mapping wall (the only landed transport `chainData_bottom_relabel` MOVES the member), or (b) a
  `ρ_cand_i = ±ρ₀` uniqueness/carry = KT's (6.66), the eq.-(6.44) chain-cancellation the now-orphan-candidate
  `hφ`-spine perp/telescope was built to encode. **LEAF C does not dissolve the seam — it RELOCATES it** (from
  the slot core's `hφ@endsσρ` to "tie `ρ_cand_i` to `ρ₀`"), and both ties are the wall or the (6.66) carry.
  This is structurally the rejected Fix B (per-`i` re-seed). **RETRACTED:** §I.8.19(a)'s "no member-mapping
  transport, so the seam never arises" — the single-`r` coupling FORCES exactly that transport (or the (6.66)
  carry); F1/F2 are necessary, not sufficient, and missed the discriminator's single-`r` coupling.

  *(C) THE CORRECTED CRUX (honest, not oversold) — and the LIVE OPEN QUESTION (do NOT pre-judge).* The
  genuinely-new obligation is producing `hingeRow v₀v₂ ρ₀ ∈ span (R(G,pᵢ).rigidityRows)` for the FIXED shared
  `ρ₀` via KT's column-op / row-correspondence (6.60→6.64) — a NEW span-inclusion lemma `span
  (R(G₁,q₁)-rows) ⊆ span (R(G,pᵢ)-rows)` that CHAIN-1 does NOT supply (F4: CHAIN-1's `columnOp` +
  `…candidateBlock_swap` + the `+|ιc|` augment are LINEAR-INDEPENDENCE preservation, used by the rank-cert
  internally — not span membership). **This is the SAME fixed-member transport §(o‴)(I.8.18) ruled dead in the
  FOLD form.** THE OPEN QUESTION: *can the column-op / whole-matrix shape carry the FIXED `ρ₀` membership where
  the seed-advancing fold could not — or does it too reduce to moving a fixed member across the relabel, in
  which case the whole-matrix route SHARES the wall and route B (carry `hφ@endsσρ`/`ρ₀` to ENTRY) is the
  residue?* This is a DESIGN question pending coordinator/user adjudication, stated NEITHER as buildable NOR as
  dead — the column-op submatrix-containment (6.61: `R(G,pᵢ)` literally CONTAINS `R(G₁,q₁)`) is a genuinely
  different shape from the fold (it does not advance a seed through `d−1` intermediate frameworks), so it MIGHT
  carry the fixed member; but it has not been shown to, and the F4 gap (CHAIN-1 gives LI, not span inclusion)
  means the span-inclusion lemma is unbuilt and its feasibility unknown.

  *(D) WHAT SURVIVES.* F1 (A-1 parametric in `(Gab,Gv,ends,q)`) and F2 (A-1's outputs match the engine's
  `hρGv`/`hwmem` slot types) are TRUE but NECESSARY-NOT-SUFFICIENT — they do not establish the single-`r`
  coupling. **LEAF A** (`chainData_candidate_rigidOn`, the member-free rigid-on transport) is independently
  fine and needed by any candidate-side route, but does NOT rescue LEAF C. **The reuse/orphan map's "CONFIRMED
  ORPHAN" claim (§I.8.19(d)) is now PREMATURE and DOWNGRADED to "confirm-and-delete CANDIDATE, pending the
  corrected-crux resolution":** the seed-advancing `hφ`-spine (slot core / fold spine / seed-advancing gate /
  `chainData_relabel_arm_hρGv`) CANNOT be declared orphaned while the route is unsettled — if the corrected
  crux reduces to the (6.66) carry, the telescope/perp machinery that encodes (6.44) is REUSED, not deleted.
  Confirm-and-delete only at a route-SETTLE commit, not before. The single-step carrier W9a
  (`funLeft_dualMap_sub_acolumn_mem_span_rigidityRows`, `:865`) STAYS regardless (d=3 building block); d=3 M₃
  (`i=2`) zero-regression unaffected.

  **CLAUSE (ii) HONESTY (the refutation is the high-value finding).** This ADDENDUM is a FLAG-DON'T-FORCE
  RETRACTION of a route the SAME design-pass proposed — the adversarial self-check caught that LEAF C
  re-introduces the design-rejected Fix B before any build was dispatched on it. The corrected crux is stated
  as an OPEN DESIGN QUESTION (column-op carries the fixed `ρ₀` vs. shares the wall), pre-judged NEITHER way;
  no buildable-looking signature is manufactured for it. The NEXT step is NOT "build LEAF A" — it is resolving
  that design question (coordinator/user adjudication). No Lean landed; no decl declared orphaned; `d=3`
  unaffected.

**(I.8.20) THE COLUMN-OP / WHOLE-MATRIX SPAN-INCLUSION QUESTION — ADJUDICATED: ROUTE DIES, IT IS THE WALL.
The (I.8.19)-ADDENDUM(C) open question is SETTLED AGAINST the route: KT's column-op submatrix-containment
(6.60→6.64) is NOT a fixed-`ρ₀` span-inclusion — it is the relabel-IMAGE inclusion, and KT's own (6.62) says
so verbatim. So the genuinely-new obligation (`hingeRow v₀v₂ ρ₀ ∈ span (R(G,pᵢ).rigidityRows)` for the FIXED
shared `ρ₀`) is unreachable by the column-op; the whole-matrix route SHARES the member-mapping wall. The
residue is route B (carry `ρ₀`/`hφ@endsσρ` to ENTRY, flagged LIKELY-DEAD) or a more fundamental rethink —
re-pointed to that fork for USER adjudication (2026-06-21, opus design-pass; every load-bearing claim
re-derived from the landed `def`/`theorem` bodies AND KT pp. 696–698 read directly from the PDF, NOT inherited
from the prior pins; docs-only, no Lean landed, tree byte-clean).** Verified against CHAIN-1
(`RigidityMatrix/Basic.lean`: `columnOp` `:884`, `hingeRow_comp_columnOp_apply` `:956`,
`linearIndependent_sumElim_candidateBlock_swap` `:1328`, `linearIndependent_sum_augment_candidateRow_block`
`:1371`), `chainData_bottom_relabel` (`Relabel.lean:1961`), the slot core `chainData_freshEdge_slot_mem`
(`:4158`), the arm `chainData_relabel_arm_hρGv` (`:4647`), the d=3 M₃ arm's `hρGv` derivation (`:2699–2724`),
the dispatch's single-`ρ0` block (`Realization.lean:404–441`), the discriminator capstone
`exists_complementIso_ne_zero_of_homogeneousIncidence_gen` (`Claim612.lean:1462`), and KT 2011 §6.4.2 eqs.
(6.60)–(6.67) pp. 696–698 (`.refs/katoh-tanigawa-2011-molecular-conjecture.pdf`, pdf pp. 50–52, read directly
this pass).

  *(0) THE QUESTION, RESTATED PRECISELY.* The arm's engine `hρGv` slot is required at the candidate framework
  `(G−vᵢ, endsσρ, qρ)` (F2; `Arms.lean:91`, FORCED by the `hwmem` leaf `chainData_bottom_relabel` whose output
  lands there, `:1982–1986`). The dispatch establishes a SINGLE shared `ρ₀` and threads its membership into
  every arm (re-confirmed: `Realization.lean:404–411` normalizes A-1's single existential `ρ` to one `ρ0`;
  `:439–441` runs the discriminator ONCE on `ρ0`; the capstone `Claim612.lean:1462–1470` takes ONE
  `{r} (hr : r ≠ 0)` and returns the discriminating panel `u` *for that one `r`* — single-`r` is structural).
  So the genuinely-new obligation is `hingeRow v₀v₂ ρ₀ ∈ span (ofNormals (G−vᵢ) endsσρ qρ).rigidityRows` for the
  FIXED `ρ₀` (M₃ sign aside). The question: does KT's column-op submatrix-containment (6.61) deliver this as a
  span-inclusion `span (base rows) ⊆ span (candidate rows)` carrying the FIXED `ρ₀`-member — or, made concrete
  against the relabelled `ofNormals` carrier, does the only available transport remain the relabel-IMAGE map
  (which moves the member off `hingeRow v₀v₂ ρ₀`)?

  *(a) F4 RE-CONFIRMED (CHAIN-1 = LI-preservation, NOT span-membership) — overturn FAILED, the claim STANDS.*
  Read against the actual conclusions: `linearIndependent_sumElim_candidateBlock_swap` (`:1328`) concludes
  `LinearIndependent ℝ (Sum.elim (Sum.elim rn cand') ro)` — its `Submodule.span` appears ONLY in the hypothesis
  `hdiff : ∀ i, cand' i - cand i ∈ span (range (Sum.elim rn ro))` (the correction lies in a span), never in the
  conclusion. `linearIndependent_sum_augment_candidateRow_block` (`:1371`) likewise concludes
  `LinearIndependent ℝ (…)`. `columnOp` (`:884`) is the `≃ₗ` change-of-variables; `hingeRow_comp_columnOp_apply`
  (`:956`) is the vanishing/pure-`v`-column fact `hingeRow v a ρ (columnOp hva S) = ρ (S v)`. NONE states a
  span-inclusion `span A ⊆ span B`, NONE states a fixed-member span membership. F4(b) holds: the whole-matrix
  span-inclusion lemma the route needs is genuinely UNBUILT by CHAIN-1 — CHAIN-1 supplies the rank/LI half (the
  `+1`/`+|ιc|` augment `case_III_rank_certification` consumes internally), not the `hρGv` span half.

  *(b) `chainData_bottom_relabel` RE-CONFIRMED to MOVE the member — and it is the ONLY landed base→candidate
  span transport.* Read against the actual statement (`Relabel.lean:1982–1994`): its conclusion applies
  `(LinearMap.funLeft ℝ (ScrewSpace k) (cd.shiftPerm i.castSucc).symm).dualMap` to `φ`. In the fresh-pair
  branch the input member `hingeRow (vtx 2)(vtx 0) ρ'` lands as `hingeRow (vtx i.succ)(vtx (i−1)) ρ'` — the
  vertices are MOVED by `shiftPerm`; in the genuine branch the link `(f,x,y)` lands at the relabelled
  `(σ⁻¹f, ρ⁻¹x, ρ⁻¹y)`. This is the relabel-IMAGE map by construction; it transforms the member. There is no
  fixed-member transport in tree. (The d=3 M₃ arm `:2699–2724` is the SAME mechanism at length 1: the
  single-step W9a sends `hingeRow a b ρ ↦ hingeRow v b ρ` (member moved `a↦v`, `:2708`) and absorbs the moved
  part into the *genuine* candidate `e_b`-row `hingeRow v b ρ` via `sub_mem` — KT's (6.62) at d=3, member-moving
  and fine because the moved member is a surviving candidate row there.)

  *(c) THE KT SOURCE SETTLES IT — KT's column-op IS the relabel-image inclusion, and KT says the member MOVES,
  verbatim (the deciding lines, read directly pp. 696–697).* KT (6.60) starts at the CANDIDATE matrix
  `R(G,pᵢ)`, performs the column operations (add col_vᵢ to col_vᵢ₊₁ for each `1≤j≤D`), substitutes (6.59), and
  (6.61) "contains `R(G₁,q₁)` as its submatrix." But the containment is **relabel-mediated on BOTH axes**: KT
  states the **row correspondence (6.62)** between `R(G,pᵢ;E∖{vᵢvᵢ₊₁},V∖{vᵢ})` and `R(G₁,q₁)` — `e⇔e`,
  `vⱼ₋₁vⱼ ⇔ vⱼvⱼ₊₁` (`2≤j≤i`), `vⱼ'vⱼ'₊₁ ⇔ vⱼ'vⱼ'₊₁` — and adds parenthetically: *"the column correspondence
  follows from the isomorphism `ρᵢ` defined in (6.54)."* So the `R(G₁,q₁)`-submatrix sits inside `R(G,pᵢ)`
  ONLY after rows AND columns are identified by the relabel `ρᵢ` — i.e. the inclusion is exactly
  `span ((funLeft ρᵢ).dualMap '' R(G₁,q₁)-rows) ⊆ span (R(G,pᵢ)-rows)`, the relabel-IMAGE inclusion, which is
  `chainData_bottom_relabel`'s map at the span level. And the redundant-row member moves, in KT's own words:
  *"the row associated with `(v₀v₂)ᵢ∗` in `R(G₁,q₁)` corresponds to the row associated with `(v₀v₁)ᵢ∗` in
  `R(G,pᵢ)`"* (p. 696, last sentence before the recall). The redundant functional carried into the candidate
  sits on the `(v₀v₁)ᵢ∗` row — the relabel-image of the base `(v₀v₂)ᵢ∗` row, NOT the fixed `v₀v₂` row. **This
  is the member-mapping wall stated in KT's notation.** It is precisely the difficulty §I.8.18(b) named: a
  fixed-functional span membership has no member-free transport; the only transport KT offers (and the only one
  in tree) carries the relabel and moves the member.

  *(d) THE (6.66) `±r` CARRY IS NOT AN ESCAPE — it is the seed-advancing telescope (the orphan-candidate
  subtree), which DELIVERS the MOVED member, not the fixed one.* KT (6.63)→(6.64): following the row
  correspondence (6.62), apply the base redundant-row operations (weights `λ`, `λ_(v₀v₂)i∗ = 1`) to the
  `(v₀v₁)ᵢ∗` row of `R(G,pᵢ)`; by (6.52) the `V∖{vᵢ}` part is identically zero and the survivor is the `Mᵢ`
  bottom-block entry `∑ⱼ λ_(vᵢvᵢ₊₁)ⱼ rⱼ(q₁(vᵢvᵢ₊₁))`. KT (6.66) then proves this entry equals `±r` (the ONE
  `r := ∑ⱼ λ_(v₀v₂)ⱼ rⱼ(q(v₀v₂))`) "due to the fact that `vᵢ` is a vertex of degree two in `G₁` … (cf.
  (6.44))." This (6.44)-via-degree-2 cancellation is EXACTLY what the landed perp/telescope subtree encodes
  (`wstep_foldl_hingeRow_telescope` = the eq.-(6.66) closed form; chain-induction LEAVES 1–4 = the eq.-(6.44)
  regroup; the slot core `chainData_freshEdge_slot_mem` peels the result). And its OUTPUT is the MOVED member:
  the slot core concludes `hingeRow (vtx i−1)(vtx i+1) ρ₀ ∈ span (candidate)` (`Relabel.lean:4174`) — the
  candidate-edge endpoints, with the same `ρ₀`. What the telescope needs as INPUT is the FIXED member
  `hingeRow v₀v₂ ρ₀` at `(endsσρ, q)` (`:4165`) — and the seed-advancing fold holds that member's IDENTITY
  fixed only because it starts at the artifact framework `(endsσρ, q)` and advances the seed, never moving the
  member across the selector relabel. The `(6.66)` carry is the seed-advancing fold; it is not a second,
  member-fixing transport. So both candidate "ties" of the ADDENDUM(C) — (a) the fixed-member identity and (b)
  the `(6.66)` carry — collapse to the same object: a transport that either holds the member fixed (no source:
  the wall) or moves it with the relabel (the landed `chainData_bottom_relabel` / W9a, lands the wrong member).

  *(e) THE CONCRETE OBSTRUCTION, AT THE §I.8.15/I.8.18 STANDARD.* Made concrete against the relabelled
  `ofNormals` carrier, a column-op span-inclusion lemma must be one of two shapes, and BOTH fail:
  - **Relabel-image inclusion** `span ((funLeft (shiftPerm i.castSucc)⁻¹).dualMap '' (ofNormals (G−v₁) ends₀
    q).rigidityRows) ⊆ span (ofNormals (G−vᵢ) endsσρ qρ).rigidityRows`. THIS is buildable (it is the span-level
    statement of `chainData_bottom_relabel`, the genuine rows ↦ genuine, fresh-pair ↦ fresh-pair). But feeding
    the base member `hingeRow v₀v₂ ρ₀ ∈ span(base)` through it yields `(funLeft …).dualMap (hingeRow v₀v₂ ρ₀) =
    hingeRow v₀v₁ ρ₀ ∈ span(candidate)` (since `(shiftPerm i.castSucc)⁻¹ v₂ = v₁` for `i ≥ 2`, the Lean-verified
    relabel action) — the MOVED member, NOT the FIXED `hingeRow v₀v₂ ρ₀` the engine slot/dispatch require. This
    is the LEAF-C mistake refuted at §I.8.19-ADDENDUM, and the §I.8.18(b) "(2-engine)" target, re-confirmed.
  - **Fixed-member inclusion** `span ((ofNormals (G−v₁) ends₀ q).rigidityRows) ⊆ span (ofNormals (G−vᵢ) endsσρ
    qρ).rigidityRows` with NO relabel on the members. This WOULD carry the fixed `hingeRow v₀v₂ ρ₀`. But it is
    FALSE in general and unbuilt: the two carriers live over the SAME body type `α` but record DIFFERENT graphs
    (`G−v₁` vs `G−vᵢ`) and different selectors/seeds; a base rigidity row `hingeRow x y r` (for `x,y` a `G−v₁`
    link at the base selector) is NOT a `(G−vᵢ, endsσρ, qρ)` rigidity row unless `x,y` is ALSO a `G−vᵢ` link
    recorded by `endsσρ` — and the load-bearing surviving link `edge 0 = v₀v₁` is recorded at the relabelled
    selector `endsσρ`, not at `ends₀` (I.8.15 PROBE C/D, I.8.18(a): the discrepancy `endsσρ ≠ ends₀` on
    `{edge 0, e₀}` is load-bearing on the span over `G−vᵢ`). KT's containment is NOT this fixed-member shape —
    KT's is the relabel-mediated (6.62) shape (c). No landed lemma states the fixed-member inclusion, and the
    KT source shows it is the wrong shape (KT's submatrix sits via `ρᵢ` on both axes). So the fixed-member
    inclusion is neither KT's nor buildable — exactly the §I.8.18(b) "(2-base)" wall.

  **VERDICT — ROUTE DIES; IT IS THE WALL.** The column-op / whole-matrix submatrix-containment, made concrete
  against the relabelled `ofNormals` carrier, offers ONLY the member-MOVING relabel-image transport — there is
  no fixed-member inclusion (KT's own (6.62) is relabel-mediated on both axes and moves the redundant row from
  `(v₀v₂)` to `(v₀v₁)`; the only landed transport `chainData_bottom_relabel` is that relabel-image map; the
  fixed-member shape is FALSE/unbuilt and is NOT KT's shape). The (6.66) `±r` carry is the seed-advancing
  telescope, which delivers the moved member, not a member-fixing second transport. So the whole-matrix route
  SHARES the member-mapping wall §(o‴)(I.8.15)/(I.8.18) ruled dead in the FOLD form — the column-op did NOT
  escape it. **This is the honest "it's the wall" verdict the clause-(ii) bar calls high-value: no
  buildable-looking span-inclusion signature is manufactured that quietly relies on the member moving (the
  LEAF-C mistake). The single structurally-different mechanism (KT's column-op) has now been probed and reduces
  to the same wall.** RESIDUE / NEXT FORK (USER adjudication):
  - **Route B — carry `ρ₀`/`hφ@endsσρ` as a hypothesis to ENTRY** (the landed `chainData_relabel_arm_hρGv`
    shape, `:4671`), confronting the wall where the chain's base realization is in scope. FLAGGED LIKELY-DEAD
    (I.8.12 ROUTE β, I.8.15 B3, I.8.18(B)): at ENTRY the hybrid must still bridge `ρ₀`'s membership from
    `(ends₀,q)` to `(endsσρ,q)` for the FIXED member — the same wall, just relocated to where more context is
    in scope; no new transport mechanism appears at ENTRY that is not already in tree (the wall is a property of
    the relabel-image map, not of what is in scope). It is NOT obviously circular only if ENTRY can re-derive
    the redundancy *natively* against `endsσρ` (e.g. a base split whose selector IS `endsσρ`) — but that is a
    different graph-construction question, not a transport, and it is unexplored.
  - **A more fundamental rethink of the general-`d` Case-III arm's Lean architecture** — abandon the
    seed-advancing materialized-fold modelling of KT (6.62) entirely and find a Lean shape where the redundancy
    is NEVER a fixed dual-vector transported across the relabel (e.g. carry the abstract `r ∈ ℝ^D` of (6.66)
    and the `Mᵢ`-block FORM rather than the row-membership; this is closer to KT's matrix bookkeeping but is a
    genuinely-new realization architecture, cost UNKNOWN, and was the §I.8.18 recommendation (A) before LEAF C
    was refuted — note (A)'s LEAF-C assembly is now known unsound, so (A) itself needs re-scoping).
  The recommendation is for the USER to choose between (B) (cheap to state, likely-dead, but bounds the
  obstruction at ENTRY) and a re-scoped architecture rethink; this pass does NOT pre-decide between them.

  **CONTRACT/MOTIVE/ORPHAN STATUS (unchanged by this pass).** NO C.0–C.6 / motive / IH change (the wall is
  machinery below the dispatch C.3 + record C.1, §I.8.18 confirmed). NO decl is declared orphaned by THIS pass:
  the seed-advancing `hφ`-spine + the perp/telescope subtree stay confirm-and-delete CANDIDATEs — under the
  "route dies" verdict they are dead-for-this-route, but the route-SETTLE commit is the user's fork decision
  above (route B may reuse the telescope at ENTRY; an architecture rethink decides their fate freshly), so
  confirm-and-delete fires only at THAT commit, not here. STAYS regardless: the single-step carrier W9a
  (`funLeft_dualMap_sub_acolumn_mem_span_rigidityRows`, `:865`); the engine/rank-cert (parametric in
  `(Gv,ends,q)`); `chainData_bottom_relabel`; CHAIN-1's LI machinery; CHAIN-3/4; `d=3` M₃ (`i=2`)
  zero-regression (no `hφ` slot, no fold, no seam — F3).

  **CLAUSE (i) HONESTY.** Every load-bearing claim re-derived this pass from the landed bodies AND the KT PDF,
  not inherited: F4 from CHAIN-1's actual conclusions (`Basic.lean:1328/1371` conclude `LinearIndependent`, span
  only in `hdiff`); the member-move from `chainData_bottom_relabel`'s actual conclusion (`:1982–1994`, the
  `(funLeft …).dualMap` image) and the d=3 M₃ arm (`:2708`); the single-`ρ0` coupling from the dispatch
  (`Realization.lean:404–441`) and the capstone (`Claim612.lean:1462–1470`, one `r`); and KT's relabel-mediated
  (6.62)/(6.61) + the verbatim "row `(v₀v₂)ᵢ∗` ⇔ row `(v₀v₁)ᵢ∗`" + the column correspondence "follows from the
  isomorphism `ρᵢ`" from pp. 696–697 read directly. **CLAUSE (ii) HONESTY.** This is a FLAG-DON'T-FORCE "it's
  the wall" close, NOT a manufactured route: the one shape that would carry the fixed member (the fixed-member
  inclusion) is named as FALSE/unbuilt-and-not-KT's, not as a buildable leaf; the relabel-image inclusion is
  named as buildable BUT member-moving (the LEAF-C trap, explicitly NOT re-proposed). The residue is the
  user-adjudication fork (route B likely-dead / architecture rethink), pre-judged neither way between them. No
  Lean landed; tree byte-clean; `chainData_relabel_arm_hρGv` stays a CORRECT carried-hypothesis lemma.

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
