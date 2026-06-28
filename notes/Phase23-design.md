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

  ### (4.18)–(4.30) THE GENUINE-ROW BASE-BLOCK FAMILY — ALL WALL ON ONE OBSTRUCTION (settled; full kernel traces in git)

  Five+ feasibility passes, all read-only compiler-checked spikes (opus, 2026-06-24), converged on a
  single verdict: **the member-mapping wall (the redundant/wrap row cannot enter the corner-overridden
  `caseIIICandidate` span) is intrinsic to KT, not a formalization artifact, and is invariant under
  every base-block re-targeting.** Per-arc one-line verdicts (decl/§-labels other arcs cite preserved):

  - **(4.18) Option (A) (static-`W` block-additivity) — INFEASIBLE.** The base block `W` must satisfy
    `hWS ∧ hWcard ∧ hW` jointly; the redundancy carry is a row THROUGH `vᵢ`, so no such `W` exists
    (kernel: any `W` with the through-`vᵢ` rep + `hW` forces `ρ₀ = 0` ⊥ the gate). The d=3 engine
    `case_III_rank_certification` (`Candidate.lean:1508`) needs NO submodule `W` — it uses a FLAT
    OPERATED FAMILY with the collapsed corner + `hρGv` (eq. 6.27, the wall). Surfaced options (A′)/(B′).
  - **(4.19) Option (B′) (operated-frame block-rank) — INFEASIBLE.** The d=3 separator
    `linearIndependent_sum_restriction_block` (`RigidityMatrix/Basic.lean:1189`) needs the top block
    pure-`v`-column (`htopvanish`), but the genuine `±r` corner `hingeRow u v ρ₀` reads `ρ₀(S u−S a) ≠ 0`
    — NOT pure-`v` (counterexample, not a `sorry`'able gap). The `±r` escape works at the ARM/corner
    level but NOT in the rank cert.
  - **(4.20) Option (A′) (re-derive the chain cert generically) — INFEASIBLE, IS the member-mapping wall
    (§I.8.18–20).** The W9a generalization is LANDED (`chainData_relabel_arm_hρGv`,
    `Relabel/ChainColumn.lean:1390`); the wall is its lone residual `hφ`, a span MEMBERSHIP the cycle
    relabel `(funLeft (shiftPerm i.castSucc)⁻¹).dualMap` provably MOVES (`vtx2 ↦ vtx1` for `i≥3`; equal ⟹
    `ρ₀=0` ⊥ gate). `d=3`/`i=2` closes only because `shiftPerm 2 = (v₁v₂)` is a single swap (masking
    degeneracy). `hρe₀` dissolved because it is an ANNIHILATION (framework-free); `hφ` is framework-
    dependent, no value-read form. → phase STOP.
  - **(4.21) KT §6.4.2 source recon — the STOP is UPHELD.** KT certifies the rank by whole-matrix
    bookkeeping with the member MOVING (eqs. 6.44/6.51/6.62–6.67, Claim 6.11, printed pp. 685/690–691/
    696–698): block rank-additivity (6.64) + union-dimension (6.67, closed by Lemma 2.1, `(d+1 choose
    d−1)=D`), `r` carried `±r` across panels (6.66). KT's (6.62) relabel correspondence IS realized in
    Lean as the member-moving transport = the wall. NO missed KT route; the genuinely-new direction is the
    §I.8.21(α) matrix-level block-rank infra.
  - **(4.22) A1 §I.8.21(α) feasibility spike — INFEASIBLE.** The first FEASIBLE pass was UNSOUND (carried
    the crux `W`/`hWS`/`hWcard`/`hW` as hypotheses; a route-COMPOSITION verdict mis-read as a
    dischargeability one). The construct-or-concede resume CONCEDED with kernel re-derivations:
    `hWS ∧ hWcard ∧ hW` jointly unsatisfiable on the redundancy member (3rd confirmation). **Lesson** (a
    spike answers composition, not dischargeability; CONSTRUCT-OR-CONCEDE is the discriminating test) →
    DESIGN.md *Constructibility recon* + model-experiment Findings.
  - **(4.23) §I.8.21(α) row-operation spike — INFEASIBLE; the wall is intrinsic to KT's row op ITSELF.**
    KT's pure-`vᵢ` corner row-op `Σλ rⱼ` reduces (eq. 6.27) to the genuine `hingeRow vᵢ b ρ₀` (via `hρe₀`,
    no wall) PLUS the residual `hingeRow a b ρ₀ ∈ span` = `hρGv` = the wall. The Phase-22g
    `exists_redundant_panelRow_ab_decomposition` (`Candidate.lean:191`) already documents KT's row op and
    `hρGv` as the SAME fact (4th confirmation).
  - **(4.24) Geometry-aware-transport recon — RELOCATES-TO-WALL.** The transport is ALREADY geometry-aware
    (`shiftPerm i` IS KT's `ρᵢ`, 6.54; `rigidityRow_relabel_to_genuine` `Relabel/Basic.lean:308` absorbs
    6.59). A LINEARITY IMPOSSIBILITY closes the dual-span transport class: `T(Σcⱼgⱼ)=Σcⱼ T(gⱼ)` lands the
    redundant row at its MOVED `ρᵢ`-image, ≠ the member-fixed target. The only escape is non-linear /
    explicit-`Matrix` (5th confirmation). Transport layer is CORRECT — nothing to rework.
  - **(4.25) Route B (genuine-basis) architecture — B-WORKS at the two kernel spikes, pending LEAF-B1.**
    The inversion faithful to KT (6.64): `W` = GENUINE rows only (off-`vᵢ`, transport works; card
    `D(|V|−2)`), corner = `D−1` panel rows + the `±r` row (`hρe₀`-sourced). Q1/Q2 kernel-spiked sorry-free
    (`q1A_corner_value_equality_constructed`). LEAF-B1 (genuine-basis extraction from the IH) was the
    carried crux + top risk; flagged for de-risk-before-build.
  - **(4.26) Route B interior `hS` GAP — BLOCKED.** LEAF-B2's universal `hS` must hold for the wrap-edge
    `edge i` base row, whose relabel image is the dead `(a,b)`-block tag (needs the unsatisfiable
    `hG_eb_cand`, kernel-`False`; or difference-collapse needing `ρ' ∈ block(edge i)` = the gate). The
    project already documents this as the wall (`funLeft_dualMap_pmR_group_mem_span_caseIIICandidate`,
    `Chain.lean:491`). Root cause = wrong base-block target framework (the candidate OVERRIDES `e_c = edge
    i`); the KT-faithful fix is the seed framework.
  - **(4.27) Option-A `W`-production scoping — the seed-framework (route 4) is the wall-free route.** The
    engine route (`case_III_arm_realization`, `Arms.lean:310`) takes `hρGv` as a hypothesis = the wall;
    per-`i` `chainData_split_realization` (`Realization.lean:1046`) needs the out-of-scope interior split +
    a per-`i` W6b `ρᵢ ≠ ρ₀`. The wall-free candidate: `W :=` the candidate's own seed rows (`hWS`/`hW`
    close mechanically); residual `hseedrank` from the relabel rank-iso.
  - **(4.28) Route 4-BARE WALLS — `hseedrank` PROVABLY FALSE for the BARE seed (3rd wrap-edge appearance).**
    The base wrap edge relabels to a row on `(vtx(i−1),vtx(i+1))`, which has NO `G`-edge (interior `deg_two`
    closure), so `R(G−vᵢ)` is MISSING the wrap-edge image — strict subspace, `finrank < D·(|Gv|−1)`. The
    landed `d=3` `rigidityRows_ofNormals_relabel` (`Relabel/Basic.lean:648`) is stated for SPLITOFF
    frameworks, where the fresh edge carries the wrap image — exactly what the bare seed lacks. **Lesson:**
    verify a "generalization of a landed lemma" against the landed lemma's ACTUAL framework form.
  - **(4.29) Route 4-SPLITOFF WALLS at the `e₀'`-row containment (4th wrap-edge appearance).** Q1 (the
    splitOff↔splitOff relabel rank-iso at the non-involutive cycle `σ`) is WALL-FREE, verified sorry-free
    (`hingeRow_funLeft_dualMap` `RigidityMatrix/Basic.lean:549`, involution-free; bricks
    `rigidityRow_chainData_relabel` `Relabel/Basic.lean:460`, `rigidityRow_relabel_perm` `:203`). Q2 (the
    fresh `e₀'` short-circuit row ∈ candidate span) FAILS by the discriminator gate: the difference-collapse
    needs `ρ' ⊥ C(vᵢ₊₁,n')` (the OVERRIDDEN slot, `caseIIICandidate_supportExtensor_candidate`), and `n'`
    is chosen so `ρ₀ ⊥̸ C(vᵢ₊₁,n')` (`hgate`). **The load-bearing invariant: the wall is the gate condition
    `ρ₀ ⊥̸ C(vᵢ₊₁,n')` re-surfacing wherever the wrap content enters the candidate span — `hρGv` (A), `hS`
    (B), `hseedrank` (4-bare), `hWS` (4-splitOff) — intrinsic to the `caseIIICandidate` override, NOT to any
    base-block choice. No base-block re-targeting escapes it.** → route A (literal `Matrix`) or (C).
  - **(4.30) ROUTE-A FEASIBILITY SCOPING — ROUTE A IS GENUINELY-DIFFERENT + FEASIBLE (NOT the refuted
    §(4.22)/(4.23) work), but HEAVY (≈9–14 leaves A1–A6).** The §(4.22)/(4.23) refutation was option (i)
    (dual-space maneuvers); route A is option (ii) (a literal mathlib `Matrix R(G,p)`, rows
    `(edge, hinge-block-index)`, cols `α × Fin D`). KT's (6.61) submatrix-containment is then a structural
    EQUALITY after an explicit invertible column op (`Matrix.rank_mul_eq_right_of_isUnit_det`, confirmed in
    mathlib), NOT a span membership — the override-meets-gate collision never forms. The clause-(iii) bridge
    (`Matrix.rank` ↔ `finrank (span rigidityRows)` via `Matrix.rank_eq_finrank_span_row`) lands on the honest
    `HasGenericFullRankRealization` (`PanelHinge.lean:1035`). A3 (matrix block-additivity-as-inequality) + A4
    (the entrywise (6.61) column op) are the genuinely-new high-risk pieces. **The user chose route A over
    fallback (C) on cost.** No motive/IH/C.0–C.6 change (the wall is below the contract).

  ### (4.31)–(4.33) ROUTE-A INTEGRATION SPIKES — the matrix def, the rank bridge, the cert-shape reshape (settled; full per-probe traces in git)

  Three compiler-checked spikes (opus, 2026-06-24/25) sharpened the route-A leaf decomposition and landed
  the corrected index-map bricks. Per-arc verdicts (decl/§-labels other arcs cite preserved):

  - **(4.31) The A5 route-composition spike — A5 needs a preceding RE-COORDINATIZATION leaf (A4.5).** The
    flat `rigidityMatrix` columns (arbitrary `Module.finBasis` of the dual, `dualCoordEquiv`,
    `Concrete.lean`) do NOT factor as `α × Fin D`, so `hblock`'s `D×D` corner column split has no
    realization on it. The column op IS expressible over a coordinatized matrix (route A's "(6.61) is a
    column-op, never a span membership" escape holds at the kernel — `flatColumnOpEquiv`/`prodColumnOpEquiv`,
    `IsUnit U.det` a 4-liner; NO `ScrewSpace` unfold). Fix = a PRODUCT-column matrix `rigidityMatrixProd`
    (cols `α × Fin D`, same honest rank). Recommended A4.5d refactor: generalize `Matrix.rank_of_dualCoord`
    (`Concrete.lean`) to an arbitrary `coordEquiv`. Within route A, no phase-direction decision.
  - **(4.32) The A5c-assembly + A6 chain-data integration spike — the A4.5d/A2 bridges are mis-leveled
    (all-`β` rows; `hgp`/`hends` total-over-`β` jointly UNSATISFIABLE with non-edges `e₀ ∉ E(G)`).** The A6
    composition skeleton is sorry-free against the actual `caseIIICandidate` arm (the route-A `hrank` fires
    the A4 bridge `rank_ge_of_isUnit_mul_reindex_fromBlocks` `Rank.lean:376` on `rigidityMatrixProd`,
    bridges via A4.5d; `case_III_realization_of_rank` tail consumed verbatim, route-agnostic). Fix = A4.5e, a
    row-RESTRICTED matrix `rigidityMatrixEdge` indexed by `{e // e ∈ E(G)} × Fin (D−1)` (via
    `Matrix.rank_of_coordEquiv`, edge-restricted `span_range_rigidityRowFun`). The `Fin cd.d` dispatch match
    rests on the STATED `Graph.ChainData.d_eq_kAdd` (`Realization.lean:980`, field `d_eq : d = n`), NOT
    coincidence (the 23c LEAF-3 latent gap FIXED in the record). NOT a motive/IH/contract change. [SUPERSEDED
    by §(4.33): the §(4.32) corner index map is garbled.]
  - **(4.33) The corrected-`hblock` spike — the §(4.32) index map is GARBLED (corner pin is `v`, not `a`;
    `en := columnSplit v`), and a DEEPER cert-shape obstruction surfaces.** Three corrected index-map bricks
    LANDED sorry-free (`Concrete.lean`, `[propext, Classical.choice, Quot.sound]`):
    `rigidityMatrixEdge_mul_columnOp_apply_pin_zero` (the FIXED-pin `0`-block read),
    `…_apply_corner` (the `hA` corner panel-functional entry), `…_reindex_toBlocks₂₁_eq_zero` (the
    `columnSplit v` `toBlocks₂₁=0`, since superseded by the `.submatrix` form). **The obstruction:** the
    cert's `fromBlocks A B 0 D` with a TOTAL row bijection `em` + both diagonal blocks full-row-LI is
    UNSATISFIABLE for `D ≥ 3` — for isostatic `G` (deficiency `D(|V|−1)−(D−1)|E|=0`, `Deficiency.lean:236`)
    `em` is total, but the `2(D−1)` `v`-incident rows exceed the corner's `D`, forcing `D−2` surplus
    pure-`v` rows into `m₂` that break BOTH `toBlocks₂₁=0` AND `hD`. KT's (6.64) is a SUBSPACE statement
    (the surplus `D−2` rows IGNORED), which is why the dual cert uses `finrank_add_card_le_of_linear
    Independent_mkQ`. **Fix = option (4b′), reshape the cert to a row-SUBMATRIX block-additivity** (`em : m₁⊕m₂
    ↪ rows` an INJECTION, not `≃`; generalize A3's `rank_fromBlocks_zero₂₁_…` row side). No motive/IH/contract
    change. (`hD`/`hA` are ~1-leaf gate facts in the SUBSPACE shape; the blocker was the cert SHAPE.) (4a)
    (`D :=` the relabelled IH matrix) declined as HARD; (C) fallback unaffected.

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

### (4.34)–(4.41) ROUTE-A ARM SPINE, DISPATCH SCOPING, THE `R(Gab)`-BOTTOM RESHAPE, AND THE CERT-SHAPE OBSTRUCTION (settled; full per-spike traces in git + the *Current state* leaf table in `Phase23d.md`)

Eight compiler-checked spikes/landings (opus, 2026-06-24/25, sessions #34–#35) carried route A from the
arm spine through the `R(Gab)`-bottom reshape to the §(4.41) cert-shape fork (resolved at §(4.42)). Per-arc
one-line verdicts (decl/§-labels + KT eq. numbers other arcs cite preserved):

- **(4.34) A6 arm-assembly recon + arm-spine landing — `hA`/`hD` are TWO genuinely-new dual-space→matrix-row
  LI bridges, NOT ~1-leaf gate facts.** The arm spine `case_III_arm_realization_matrix` LANDED sorry-free
  (`ForkedArm.lean`, route-A sibling of `_chain`, carrying `(m₁,m₂,hm₁,hm₂,re,hbot,hA,hD)`, constructing
  `U`/`hU`/`en`/`hblock` in-body off the landed bricks). The residuals are matrix-row LI, not the dual-space
  LI all landed content provides (the A5b iff `linearIndependent_rigidityMatrixProd_row_iff` is for the FULL
  matrix `.row`). `hD` LANDED `linearIndependent_toBlocks₂₂_row_of_off_pin` (op-invariance:
  `submatrix_columnOp_toBlocks₂₂_eq` — the operated bottom IS the un-op'd `R(Gᵥ)` submatrix). `hA` LANDED
  `linearIndependent_toBlocks₁₁_row_of_corner_gate` (dual-space→matrix-row coordinate re-wrap via
  `Matrix.linearIndependent_row_of_coordEquiv`, `coordEquiv := (finScrewBasis k).dualBasis.equivFun`; §38
  whnf-guard held). No `mkQ`/quotient detour.
- **(4.35) Route-A dispatch spike — the interior arm composes; the wrap-edge wall DOES NOT re-surface;
  GAP-2 resolved; 5-leaf decomposition.** Kernel-probed: the `e_b` `±r` row's operated corner entry reads
  `blockBasisOn` at the pin — identical form to the `e_a` rows — so the `±r`/wrap content enters as a member
  of the corner block `A` (literal matrix row), NEVER a span membership. The §(4.18)–(4.29) discriminator
  gate never forms in the literal-`Matrix` model. GAP-2 resolved (the `Function.update` `ends₁` override =
  the landed `d=3` router `chainData_split_realization`, `Realization.lean:1159`). Leaves: (1) generalize
  `rigidityMatrixEdge_mul_columnOp_apply_corner` to `.2 ≠ v` ✅; (2) generalize
  `linearIndependent_toBlocks₁₁_row_of_corner_gate`'s `hc2` to `.2 ≠ v` ✅; (3)
  `exists_corner_blockBasisOn_linearIndependent` (3a+3b, the corner `hLI`, EXISTENCE-form; the mkQ-quotient
  lift was a RED HERRING — uniform `blockBasisOn`-family, gate → block-incomparability → fresh `j₀` →
  `linearIndependent_sumElim_candidateRow_iff` + 3a) ✅; (4) the bottom-row producer `dispatch_bottom_rowLI_of_IH`
  (genuinely-new, span-shaped `chainData_bottom_relabel` is the WRONG shape) — reshaped by §(4.42); (5) the
  `chainData_dispatch` wiring. No motive/IH/contract change.
- **(4.36) The bottom-block deficiency wall — route A's pure-`Gᵥ` `hD` is UNSATISFIABLE for the generic
  deficient interior split.** The arm pins `G.deficiency n = 0`, NOT `Gᵥ.deficiency n = 0`; the IH gives only
  `m₂ − k'` independent `Gᵥ`-rows (`k' = Gᵥ.deficiency n ∈ [0,D−2]`, generically `>0` for a degree-2 split,
  `Realization.lean:612`). `_chain` avoids this via `hwmem` (its bottom carries `k'` candidate `ρ'`-hinge
  rows, KT eq. 6.66 — abstract dual functionals, not edge rows). Q1 alignment RESOLVED (the rank-polynomial
  bridge `exists_rankPolynomial_of_IH_linking` `CaseI.lean:384`). Options flagged (USER-ADJUDICATION).
  [SUPERSEDED by §(4.37): both options wall.]
- **(4.37) Comparative spike — BOTH §(4.36) options WALL (reduce to the deficiency-fill span-membership).**
  Hybrid: no "landed `_chain` W-producer" exists (the arm CONSUMES `W`; every interior `W`-producer is walled,
  §4.26–4.28). Augmented matrix: the `k'` fill rows are not edge rows of `rigidityMatrixEdge`, so counting them
  re-triggers `W ≤ span(caseIIICandidate)`. **Route A escaped the CORNER (§(4.35)) but NOT the BOTTOM
  deficiency-fill.** Corner leaves (1,2,3) stay sound + reusable.
- **(4.38) Diverse-lens scoping pair — route A used the WRONG bottom graph.** KT's eq. 6.64 bottom is
  `R(G₁∖row, q₁)` with `G₁ = Gab = G.splitOff v a b e₀` — FULL rank `D(|Vᵥ|−1)` (zero deficiency, Lemma 4.8 /
  eq. 6.51), NOT the deficient `removeVertex`. On `R(Gab)` the `e₀=(a,b)` fill rows are GENUINE edge rows
  (literal), not span members — dissolving the wall. The make-or-break (then unspiked): KT's (6.61)→(6.62)
  row-correspondence sending `R(G,pᵢ)`'s genuine off-`vᵢ₊₁` rows to `R(Gab,q)`'s rows as a literal
  rank-preserving matrix op. The d=3 arm already uses `Gab` (`exists_candidateRow_bottomRows_of_rigidOn`,
  `Candidate.lean:401`). No motive change (IH consumed on `splitOff` instead of `removeVertex`).
- **(4.39) The (6.62) row-correspondence spike — the operated `e_a` row is ZERO off-`v` under the project's
  `columnOp`.** Mechanism: `columnOp hva S = update S v (S v + S a)`, so the `e_a` row (reads `S v − S a`)
  evaluates to `S v = 0` off-`v` — the op VACUUMS the `e_a` row into the corner (= why the corner works). The
  bottom off-`v` block is exactly the un-op'd deficient `R(Gv)` (`submatrix_columnOp_toBlocks₂₂_eq`). OPEN
  fork: is the project's `columnOp` faithful to KT's (6.61), or does (6.62) genuinely fail?
- **(4.40) FORK DECISION — FORK 1: KT's proof is SOUND, the `columnOp` IS KT's (6.61), the artifact is `hbot`
  excluding the `e_b` row.** KT (6.61) verbatim ("add column `vᵢ` to column `vᵢ₊₁`") = the project's
  `columnOp` (`Basic.lean:998`, docstring cites §6.4.1). The §(4.39) spike tested the CORNER edge `e_a`
  (correctly 0 off-`v`); KT routes the OTHER `v`-incident edge `e_b = vᵢ₋₁vᵢ` to the `e₀=(a,b)` bottom fill
  (KT 6.62). Kernel-proved: the operated `e_b` row off-`v` literally equals `R(Gab,q)`'s `ab` row, NO span
  membership. `R(Gab) = Gv + e₀` (split-off, minimal 0-dof) is full rank `D(|Vᵥ|−1)`; the `e₀` rows add the
  `k'=D−2` fill. Reshape steps 1–3 (the operated-`e_b` entry equality, the mixed-bottom matrix-shape +
  cross-label extensor bridge, the `hD` RANK route L-span/L-rank/L-hD) all LANDED (`Phase23d.md` leaf table);
  the matrix-equality form `submatrix_columnOp_toBlocks₂₂_eq_Gab` stays BLOCKED. No motive/IH/contract change.
- **(4.41) Step-4 design-pass — the operated `e_b` row CANNOT sit in the cert's bottom `m₂` (its PIN entry is
  a nonzero corner read), so the §(4.40) `fromBlocks A B 0 D` cert cannot carry the full-rank `R(Gab)`
  bottom.** Kernel-confirmed: `rigidityMatrixEdge_mul_columnOp_apply_corner` gives the operated `e_b` pin
  entry `(blockBasisOn)(finScrewBasis k c) ≠ 0`, so the mixed-bottom `toBlocks₂₁=0` is UNPROVABLE; and
  `e₀ ∉ E(G)`, so the only `E(G)`-selectable `ab`-fill row is the operated `e_b`. `e_b` is needed in BOTH the
  corner (`±r` pin) and the bottom (`ab` fill) but satisfies only one under a literal-`0` lower-left block
  (column-side re-confirmation of §(4.33)(3)). The step-3 RANK leaves are SOUND but ORPHANED (true about the
  off-`v` `toBlocks₂₂`) pending a cert shape tolerating the `e_b` pin entry. **THE GENUINE FORK (cert-shape):**
  option 1 (two-matrix / Schur-style (6.66) row op zeroing the corner-spanned `C`) — recommended at §(4.41)
  but REVERSED at §(4.42); option 2 (separate-`R(Gab)`-bottom cert) — CHOSEN at §(4.42); option 3 = fallback
  (C). No motive/IH/contract change under either.

### (4.42) COMPARATIVE CERT-SHAPE SPIKE — VERDICT: option 2 (separate `R(Gab)` bottom) CHOSEN; option 1 (Schur/(6.66) row-op) WALLS on the Schur-complement mutation. Kernel-grounded; REVERSES the §(4.41) option-1 recommendation. (User-directed deeper scoping, session #35.)

**Comparative compiler-checked spike (read-only; scratch reverted, tree clean).** Scoped both §(4.41)
options to ground; the user directed "scope which path is better, and at any wall figure out what's going
on to get further." It did, and the diagnosis REVERSES the §(4.41) coordinator recommendation (option 1).

**Option 1 (KT-(6.66) left row-op / Schur) WALLS.** Sub-question 1a (is `C` = the `e_b` pin block in
`rowspan(A)`?) is YES but VACUOUSLY: `A` is the `D×D` corner with `hA : LinearIndependent A.row` ⟹
invertible ⟹ its rows span the *entire* pin-column space, so every `C`-row is trivially corner-spanned.
That does not help. The wall (1b/1c): zeroing `C` by a LEFT unit-det row op is the LDU/Schur decomposition
(`Matrix.fromBlocks_eq_of_invertible₁₁`), and it **replaces the bottom block `D` by the Schur complement
`D − C·A⁻¹·B`, not `D`**. `B` (corner off-`v`) is nonzero only in the `e_b`-`j₀` row (the operated `e_a`
panel rows are 0 off-`v`, §(4.39)), so the Schur complement subtracts multiples of the `e₀`-block row from
the bottom. Whether `D − C·A⁻¹·B` is full row rank is a **genuinely-new fact** — the landed L-hD proves the
*un-row-op'd* bottom `D` (= the genuine `R(Gab)` block) is full rank, and says nothing about the Schur
complement (which inverts the `D×D` corner). The §(4.41) "(6.66) just zeros `C`" elided that the zeroing
*mutates the bottom away from* `R(Gab)`. So option 1 needs new Schur-complement-full-rank math.

**Option 2 (separate `R(Gab)` bottom) FEASIBLE, all-landed dependency set — CHOSEN.** The escape the user's
"get further" directive points at: `V(G.splitOff v a b e₀) = V(G) \ {v}` (`Operations.lean:606`) — **`Gab`
has no body `v`, so `R(Gab,q)`'s rows have no pin column at all** (they vanish on `{v}×Fin D` by
construction, the same blindness L-rank's `hzero` step exploits). So the corner (`R(F₀)*U` rows, on the pin
columns) and the bottom (`R(Gab)` rows, blind to `v`) live on **disjoint coordinate blocks** — `C = 0` for
free, no row op, no Schur complement. The sound bridge is a **functional-LI + `Φ⁻¹`-precompose** argument
(NOT a naive `rank N ≤ finrank span`, which fails because the corner rows are operated, not rigidity rows):
(1) corner functionals LI on the pin coords (`hA`, `D×D` invertible) + `R(Gab)` bottom functionals
pin-vanishing ⟹ the disjoint-block `Sum.elim` family is LI; (2) precompose the combined family with
`Φ⁻¹ = columnOp hva`: the corner rows `(R(F₀)∘Φ)∘Φ⁻¹ = R(F₀)` become genuine rigidity rows (∈ `span
F₀.rigidityRows`), the `R(Gab)` rows are unchanged (`Φ⁻¹` touches only the `v`-slot, invisible to rows
reading `a,b ≠ v`) and ∈ `span F₀.rigidityRows` via the landed cross-label bridge; `Φ⁻¹` is an
automorphism so LI is preserved ⟹ `#m₁ + #m₂ ≤ finrank (span F₀.rigidityRows)`. Dependencies ALL landed
(`hA` = leaf 2; `R(Gab)` row-LI from `hsplitGP`'s `HasGenericFullRankRealization`, def-0, `Q`-unpack
`Realization.lean:302`/`625`; the cross-label bridge `Basic.lean:701`; L-span `Basic.lean:735`; the `Φ`/
blindness facts). The step-3 RANK leaves are consumed here, not orphaned.

**The net diagnosis (the wall is `Φ`).** The column op `Φ` is what makes the surplus `e_b` rows' pin
entries nonzero (corner reads) while delivering their off-`v` `R(Gab)` content. Option 1 fights `Φ` with a
*second* (row) op and pays the Schur-complement price; **option 2 routes around `Φ`** by reading the bottom
off the `v`-free matrix `R(Gab)` and re-aligning the corner via the rank-preserving `Φ⁻¹`-precompose —
turning the obstruction into a one-leaf disjoint-block-LI fact.

**Buildable-leaf decomposition (option 2, in order):**
1. **LEAF-DBL ✅ LANDED (2026-06-26, `Basic.lean`).** `linearIndependent_sumElim_corner_bottom_of_disjoint_pin`:
   corner functionals LI on the pin column (`hcornerpin`) + `v`-blind bottom (`hbotblind`) + bottom LI
   (`hbotindep`) ⟹ the **de-operated** `Sum.elim (corner ∘ₗ Φ⁻¹) bottom` is LI. It turned out the disjoint-pin
   half is the *landed* `linearIndependent_sum_pinned_block` (the new lemma is NOT a synonym — it folds the
   `Φ⁻¹`-precompose in: the de-operated combined family is `Φ⁻¹.dualMap ∘ (Sum.elim corner bottom)`, `bottom`
   fixed by `Φ⁻¹` via `hbotblind`, LI-preserved by `LinearIndependent.map'`). So it directly yields the LI
   family LEAF-SEPCERT lands in span. Axiom/gate-clean.
2. **LEAF-SEPCERT** `case_III_rank_certification_matrix_sep` (`Candidate.lean`): the option-2 cert — replaces
   `(hblock = fromBlocks A B 0 D)` with `(corner `re`-rows + `hA`, the `R(Gab)` rows + their IH row-LI, the
   cross-label `hsupp`); body = the `Φ⁻¹`-precompose landing both families in `span F₀.rigidityRows`,
   LEAF-DBL keeping them LI, conclude `D(|V(G)|−1) ≤ finrank span`. The genuinely-new bridge; reuses L-span
   + the cross-label bridge. (Recommend a feasibility spike here first — the genuinely-new piece.)
3. **Wiring** (per §(4.41) "B = bypass the arm"): the general-`k` dispatch supplies `re` (corner only, no
   surplus-`e_b`-in-`m₂`), the `Q_ab` unpack, the `R(Gab)` row-LI from `hsplitGP`, and `hsupp` from
   `caseIIICandidate_supportExtensor_reproduced` at `t=0`. Then CHAIN-5 + ENTRY/ASSEMBLY.

**No motive/IH/contract change** (IH consumed on `splitOff` via the landed RANK count, as §(4.40)/(4.41)).
The arm spine `case_III_arm_realization_matrix` stays a `removeVertex`/pure-`Gv` sibling (do NOT relax its
`hbot`). This SUPERSEDES the §(4.41) option-1 recommendation; option 1's Schur wall is documented above (do
not re-attempt it without the new Schur-complement-full-rank fact). Fallback (C) is NOT forced.

### (4.43) END-TO-END SCOPE OF THE REMAINING 23d PATH — VERDICT: CLEAR (no new-math wall); LEAF-SEPCERT BUILT sorry-free; ONE C.3 interface obligation (`hIH`); recommend splitting the dispatch + CHAIN-5 into sub-phase 23e. (User-asked "is the path clear to the end of the phase?"; breadth-first read-only scope, session #35, row 499.)

**Breadth-first compiler-checked scoping recon (read-only; both scratch probes reverted, tree clean).**
Scoped the whole remaining Phase-23d (CHAIN-layer) path — LEAF-SEPCERT + the general-`k` dispatch + CHAIN-5
— to answer whether it is clear to a coherent close. **Verdict: CLEAR, no new-math wall**, with one
under-scoped interface obligation surfaced (flag-don't-force).

**LEAF-SEPCERT composes sorry-free (kernel-verified).** The recon WROTE `case_III_rank_certification_matrix_sep`
per §(4.42) and built its body with zero `sorry` (inputs = the dispatch-supplied hyps): LEAF-DBL → LI of the
de-operated `Sum.elim`; the span memberships lift into `span F₀.rigidityRows`; `LinearIndependent.of_comp …
subtype` + `fintype_card_le_finrank` + the `_chain` count tail close `D·(|V(G)|−1) ≤ finrank`. The ONLY
residual is a `maxHeartbeats` bump (default 200k → ~1–2M; the `Sum.elim`-over-`ScrewSpace`-carrier whnf, the
known carrier-opacity friction) — NOT a math gap.

**The general-`k` dispatch — structurally clear; the prior `k=2`-tangle worry REFUTED.** `HasGenericFullRankRealization`
is fully `k`-parametric; the `obtain ⟨Q,…⟩ := hsplitGP` unpack typechecks at general `k` (verified in the
interior-arm spike); the `k=2` in `case_III_candidate_dispatch` (`Realization.lean:302`) is *consumer
hardcoding* (the `d=3` 3-panel discriminator), not an unpack wall, and the general-`k` routers
`chainData_split_w6b_gates`/`chainData_split_realization` are landed. The interior split tuple + the
interior `hsplitGP` (via `splitOff_isMinimalKDof` + `hIH`) + `hsupp` (via `caseIIICandidate_supportExtensor_reproduced`
at `t=0` + the cross-label bridge) + `hA` (leaves 2/3) + the geometric hyps (`interior_hρe₀_of_baseWidening`
+ the `d=3` `hne_F₀` pattern) all compose (spike-verified).

**§(4.35) supersessions confirmed.** Leaf 4 (`dispatch_bottom_rowLI_of_IH`, the pure-`Gv` row-LI producer)
and the landed arm spine `case_III_arm_realization_matrix` are SUPERSEDED for the interior: the arm calls the
OLD literal-`0`-block cert whose pure-`Gv` `hD` §(4.36) proved unsatisfiable when `Gv.deficiency > 0`
(generic interior). Hence LEAF-SEPARM (the new arm on LEAF-SEPCERT) / bypass-the-arm, NOT the landed arm.

**THE ONE INTERFACE OBLIGATION (flag-don't-force; adjudicate at 23e-open).** The frozen contract **C.3**
states the dispatch as taking `hsplitGP` at the BASE `v₁`-split, but the interior arm needs `hsplitGP` at the
INTERIOR split `G.splitOff vᵢ …` — a different graph, derivable only from `hIH` (via `splitOff_isMinimalKDof`),
which is NOT in the C.3 signature. The landed floor router `chainData_split_realization` already carries `hIH`
(line ~1051) AND a per-`i` `hsplitGP` (line ~1059) separately, confirming the dispatch signature must carry
`hIH` (or the full inductive context). This is a **one-field addition to the C.3 consume-shape** (touching the
C.0 producer/consumer/ENTRY lockstep trio) — NOT a motive/IH change. §(3257) noted "the IH at the interior
split … NOT in scope (C.3 hands only the base)" but framed it as a dual-space-route issue; it is in fact a
standing signature requirement for ANY interior route.

**CHAIN-5 = the C.0 lockstep reshape** of `hdispatch`/`hcand` (currently the `(v,a,b,c,…)` 8-tuple, fed by
`exists_chain_data_of_noRigid`) to the frozen `cd : G.ChainData n` shape, + the `d=3` zero-regression adapter
(`case_III_candidate_dispatch` stays byte-reachable via the C.4 map `vtx = ![b,v,a,c]`). No obstruction; the
`d=3` adapter is the only fiddly part.

**Buildable-leaf decomposition (~5–7 commits):** (1) LEAF-SEPCERT (1 commit; body verified, `maxHeartbeats`);
(2) LEAF-SEPARM (1–2); — *these two close 23d's rank-cert scope* — then **23e:** (3) `chainData_dispatch`
(2; signature carries `hIH`; interior `hsplitGP` via `splitOff_isMinimalKDof`; routes base→`chainData_split_realization`,
interior→LEAF-SEPARM); (4) CHAIN-5 (1–2; the C.0 lockstep reshape + `d=3` adapter).

**23e-split recommendation.** LEAF-SEPCERT + LEAF-SEPARM close 23d's stated scope (the general-`d` rank cert,
route A) cleanly. The dispatch + CHAIN-5 are a distinct body — the `Fin cd.d` router, the C.3 `hIH`-field
addition, and the C.0 lockstep reshape touching the frozen CHAIN↔ENTRY contract + three decls in lockstep —
naturally their own sub-phase (`23e`), which also unblocks ENTRY. Flag the `hIH`-on-C.3 addition for user
adjudication at 23e-open.

## (4.44)–(4.54) THE 23e RANK-CERTIFICATE ARC — closed; cited verdicts (full blow-by-blow in git)

> **Compressed at the 23e close (2026-06-26).** §(4.44)–(4.54) were the re-scope + de-risking +
> cert-build recon arcs that resolved the bottom-deficiency wall into the **A3-transposed `fromBlocks A 0 C D`
> cert**, landed axiom-clean. They are now closed; the verdict headers below are the durable record, the
> per-spike blow-by-blow is in git (commits `323fd78`/`a02b8c5`/`d61bb63`/`87f6728`/`7edff2d`/`cd4ad06`/
> `a3e4a55`/`351fdec`/`1d69932`/`a262781`/`0114eb7`/`3199378`). The **live 23f plan** (the geometry arm
> that constructs the cert block data) lives in `notes/Phase23f.md` (forward home), not here. **PRESERVED
> above:** §(4.43) (the frozen CHAIN↔ENTRY contract C.0–C.6 + the approved C.3 `hIH` obligation) and §C.0–C.6.

**The arc, in one synthesis (cited).** The §(4.41)/(4.44) walls (the option-2 cert's `hbotmem` unsatisfiable
with `bottom = R(Gab)`; `R(Gab) ⊄ span F₀` because G lacks the `a—b` edge) and the §(4.47) literal-`Matrix`
finding (the project's `columnOp hva`, `Basic.lean:1087`, gives 0 in the LOWER-left, stranding the operated
`e_b` `ab`-fill in the discarded upper-right) were all surface manifestations of one obstruction: **a
block-triangular `fromBlocks` cert over G's own edges cannot express KT's NON-block-triangular argument**
(KT eqs. 6.65–6.67, *Discrete & Comput. Geom.* 45(4) 2011 pp. 696–698 share the `e_b` `(D−1)`-block between the
corner `Mᵢ`'s `±r` row and the `e₀`-fill via union-dimension). NOT open math — a formalization
representation-mismatch (KT 2011 is a complete refereed proof). **User decision (§(4.48), session #37):** pursue
the genuinely-new KT-faithful certificate (fallback (C)/freeze-at-`d=3` declined). The resolution (§(4.49)): a
THIRD, un-examined cert shape `fromBlocks A 0 C D` (zero UPPER-right, A3-transposed via `det_fromBlocks_zero₁₂`,
mathlib `Determinant/Basic.lean:723`) — the bottom is the LANDED full-rank `mixedBottom` block (UNCHANGED), a
LEFT row op zeros the corner's off-`v` `B` (NOT §(4.42)'s Schur, which zeros `C` and mutates the bottom), and
the only genuinely-new content localizes to the corner `Mᵢ`-invertibility. That last (§(4.51)) is **ALREADY
LANDED at general `d`** — the union-dimension discriminator + callees are `{k:ℕ}`, `Claim612.lean` sorry-free,
fired by `exists_shared_redundancy_and_matched_candidate` (Phase 23c). §(4.50)/(4.52)'s "remaining = ASSEMBLY"
was twice-corrected (§(4.53)/(4.54)): the row-op facts were never tracked Lean, and the geometry arm carries two
genuinely-new bridges.

**What landed (23e cert layer, all axiom-clean — cite directly):** the A3-transposed cert chain
`rank_ge_of_isUnit_mul_submatrix_fromBlocks_zero₁₂` (`Rank.lean`) / `finrank_span_rigidityRows_ge_of_edge_submatrix_fromBlocks_zero₁₂`
(`Concrete.lean`) / `case_III_rank_certification_zero₁₂` (`Candidate.lean`), all consuming
`(Lrow, hLrow, U, hU, re, en, hblock, hA, hD)` with `hblock : (Lrow * M * U).submatrix re en = fromBlocks A 0 C D`
(rank-invariant via mathlib `rank_mul_eq_right_of_isUnit_det`); the row-op LA facts `rowOp_isUnit_det`
(via `det_fromBlocks_zero₂₁`) + `rowOp_zeroes_upperRight` (via `fromBlocks_multiply`) + the matrix-algebra half
`Matrix.of_eq_mul_of_row_comb`, all in `Rank.lean`; the corner gate `corner_hA'_of_gate` (`Concrete.lean:620`,
the ρ₀-augmented `[blockBasisOn(e_a); ρ₀]` family); the `mixedBottom` family +
`linearIndependent_toBlocks₂₂_row_mixedBottom_of_finrank_eq` (`Concrete.lean:1685`, supplies `hD`);
`rigidityMatrixEdge_mul_columnOp_apply_pin_zero`/`_apply_corner`/`_apply_eB_off_pin`/`_apply_off_pin`. The
end-to-end §(4.54) spike (kernel-confirmed) showed the cert is invokable at the abstract framework level +
SATISFIABLE for the real interior arm — **no fourth wall**.

**What 23f owes (the geometry arm — re-pointed hand-off, full plan in `notes/Phase23f.md`):** the cert's block
data is constructed from the IH-fed `cGv` widening (W6b producer `exists_candidateRow_bottomRows_of_rigidOn`,
takes `hrig`/`h622lb`), so it is genuinely 23f-arm-coupled. Three new leaves + assembly, in dependency order:
(i) the `cGv`→`w` re-key leaf (`Gv.IsLink`→`m₂` membership + `of_eq_mul_of_row_comb` — a RANK-route weight, so
the §(4.44) `hbotmem` wall does NOT reform); (ii) the `Lrow`-on-`p` reindex unit-det bridge (`Lrow` is on the
full edge index `p ≠ m₁⊕m₂`; carry via `reindex e e (fromBlocks 1 (−L₀') 0 1)` + mathlib `det_reindex_self`,
genuinely-new); (iii) the post-row-op corner-`hA` bridge (after the op `A' = A − L₀C` mutates `blockBasisOn(e_b,j₀)`
into `ρ₀`; read `A' = toBlocks₁₁(Lrow*M*U)` as `[blockBasisOn(e_a); ρ₀]`, close via `corner_hA'_of_gate` — the
landed `linearIndependent_toBlocks₁₁_row_of_corner_gate` reads the un-op'd corner, so a new bridge is owed,
genuinely-new). **Coupling note:** zeroing `B` (off-`v`) and mutating `A→A'` are ONE row op — `ρ₀` is `A`-pin
minus `L₀·C`-pin, NOT a free choice; leaves (ii)/(iii) share the same `L₀`. The `re`/`m₂` split is
FRAMEWORK-determined (corner/bottom predicates reference only `ends`/`v`/`a`/`e_a`/`e_b`); the single
arm-coupling is `L₀` (= the `cGv` weights).

The per-spike verdict headers (for git-archaeology cross-reference):
- **(4.44)** LEAF-4 satisfiability — WALL: option-2 `hbotmem` unsatisfiable with `bottom = R(Gab)` (session #36).
- **(4.45)** comparative bottom-architecture (R1/R2/R3) — all three WALL on the §(4.29) override-gate (session #36).
- **(4.46)** KT source-faithfulness recon — the wall is a dual-span-representation ARTIFACT, not a KT obstruction; KT certifies via a literal block-triangular submatrix (session #36).
- **(4.47)** A4 de-risk spike — the literal-`Matrix` route does NOT escape the wall (project `columnOp` = 0 lower-left); genuinely-new core = an `R(Gab)`-reproduction bottom (session #36).
- **(4.48)** R(Gab)-reproduction feasibility — kernel-grounded NO-GO (dual-orientation single-row impossibility); representation-mismatch, not open math; **USER DECISION: pursue the KT-faithful cert; 23e re-scoped** (session #37).
- **(4.49)** cert-shape recon — GO: the A3-transposed `fromBlocks A 0 C D` shape dodges all four walls + §(4.42)'s Schur (session #37).
- **(4.50)** step-2 de-risk — A3-transposed scaffolding sorry-free, genuinely-new content relocates intact into the corner `hA'` (session #37).
- **(4.51)** step-2b structural recon — GO: KT's union-dimension `Mᵢ`-invertibility is ALREADY LANDED general-`d`; §(4.50)'s "hardest argument" framing stale (session #37).
- **(4.52)** step-2c wiring spike — GO: the §(4.46) hedge discharged; the §(4.50) concede dissolved by the `Gv`-row pin-zero fact (session #37).
- **(4.53)** step-3b matrix-assembly spike — WALL→route (A) adjudicated: the cert needs a LEFT row op `Lrow`; two LEAF-RowOp leaves + a `Lrow`-reshape owed (session #38).
- **(4.54)** end-to-end composition spike — GO, cert scope COMPLETE: the reshaped cert is satisfiable, no fourth wall; two leaves the §(4.53) plan elided surfaced (the `Lrow`-on-`p` reindex + the post-row-op corner-`hA` bridges), both 23f (session #39).

## (4.55) THE BIJECTION-vs-INJECTION `re` SHAPE — VERDICT: (b) STRICT INJECTION. Leaves (ii)/(iv) do NOT serve the general arm; a strict-injection unit-det bridge + `hblock` reducer are genuinely-new owed leaves. (Compiler-checked recon, session #40; scratch reverted, tree clean.)

**The question (23f recon, `notes/Phase23f.md` *Current state*).** The 23e cert
`case_III_rank_certification_zero12` fires with a row injection `re : m1 + m2 -> p`,
`p := {e // e in E(G)} x Fin (D-1)` the FULL edge-row index (`D := screwDim k`). The cert TYPE
allows any function `re` (its rank step is `rank_submatrix_le`, `Rank.lean:529`), but landed leaves
(ii) `reindex_rowOp_isUnit_det` and (iv) `reindex_rowOp_submatrix_eq_fromBlocks_zero12` fix
`e : (m1 + m2) ~= p` a **bijection** with `re := up e` (the matrix API `det_reindex_self` /
`submatrix_mul_equiv` needs a bijective middle index). A bijection forces
`card m1 + card m2 = card p`. Earlier prose (the cert's own proof comment, `Candidate.lean:2492`;
leaf (ii)'s docstring; SS(4.33)) described `re` as a strict **injection dropping the surplus
`v`-rows** -- a weaker, sub-`card p` bound. Decide which is the real arm's shape.

**Verdict: (b) strict injection.** The decisive cardinality relation is an **inequality `<=`, not an
equality** -- a bijection is NOT grounded and is generically FALSE. Every line below is
compiler-checked or traced to a stated lemma:
- `card m1 + card m2 = D*(|V(G)|-1)` (cert `hm1 : = D`, `hm2 : = D*(|V(Gv)|-1)`; the `D + D(mv-1) =
  D*mv` arithmetic, `Candidate.lean:2503`; `|V(Gv)| = |V(G)|-1`).
- `card p = (D-1)*|E(G)|` (`Fintype.card_prod` + `Fintype.card_fin`; `rigidityMatrixEdge` row index
  is `{e // e in E(G)} x Fin (D-1)`, `Concrete.lean:732`).
- **The grounded relation is `card m1 + card m2 <= card p`**, i.e. `D*(|V(G)|-1) <= (D-1)*|E(G)|`,
  from the in-tree chain `rank(M(G~)) = D*(|V|-1)` (def-0, `rank_matroidMG_of_isKDof_zero`) **and**
  `rank(M(G~)) <= (D-1)*|E(G)|` (the matroid rank bound `rk_le_card`, `Operations.lean:882`-885;
  `bodyHingeMult n = D-1`). **Equality is NOT a stated fact** -- the project's own
  `exists_isLink_of_isMinimalKDof_card_three` (`Operations.lean:856`-893) USES exactly this `<=`
  (deriving `|E| >= 3` from `rank = 2D <= (D-1)|E|`), never an `=`. A minimal-0-dof graph is **not**
  forced `(D,D)`-tight: a base of `M(G~)` meets every edge-fiber (size `D-1`) but need not saturate
  it, so `(D-1)|E| > D(|V|-1)` (excess fiber edges) and hence `card m1 + card m2 < card p` is the
  generic case.
- Therefore a **bijection `(m1 + m2) ~= p` does not exist in general** (it needs the un-grounded
  equality, `Fintype.card_congr`), while a **strict injection `m1 + m2 ↪ p` always exists** (from
  `card <= card`, `Function.Embedding.nonempty_of_card_le`). The cert MUST tolerate the strict case;
  leaves (ii)/(iv)'s bijection serves only the measure-zero isostatic-tight `G`.

**Why leaves (ii)/(iv) do NOT serve, and what is owed (route (b)).** Leaf (iv)'s engine is
`submatrix_mul_equiv`, which splits `(Lrow * M').submatrix re en` through the **middle index by an
`Equiv`** (`e`), collapsing `Lrow.submatrix e e` to `[1,-L0;0,1]`. With a strict (non-surjective)
injection `re` there is **no `Equiv` to split through** (`submatrix_mul` needs a bijective middle
index), so neither the `Lrow`-on-`p` reindex (leaf (ii) `reindex e e`) nor the `hblock` reduction
(leaf (iv)) applies. Owed, genuinely-new (P~=3, dependency order):
- **B1 -- strict-injection unit-det / rank-invariance bridge.** The `Lrow` row op must act on the
  `re`-selected `m1 + m2` rows and leave `M.rank` invariant *without* a `det_reindex_self` through a
  full `p`-`Equiv`. Sig (carrier/field-agnostic): given `re : m1 + m2 -> p` injective and the block
  op `[1,-L0;0,1]`, exhibit a unit-det `Lrow : Matrix p p K` (the block op on `range re`, identity
  on the complement `p \ range re`) with `IsUnit Lrow.det`, `(Lrow * M).rank = M.rank`, and
  `Lrow.submatrix re re = [1,-L0;0,1]`. Build it via the EXTENDED equiv
  `e' : (m1 + m2) + (p \ range re) ~= p` (`Equiv.Set.sumCompl` on `range re` + `re.toEmbedding`
  injective image-equiv) and `det_reindex_self` on `[1,-L0;0,1] (+) 1` -- the equiv is on the
  enlarged index `(m1+m2)+(complement)`, NOT on `m1+m2` alone, so it is genuinely a new lemma.
- **B2 -- strict-injection `hblock` reducer.** The `_zero12` analogue of leaf (iv) for B1's `Lrow`:
  from `hM' : M'.submatrix re en = fromBlocks A B C D`, `hB : B = L0*D`, conclude
  `(Lrow * M').submatrix re en = fromBlocks (A - L0*C) 0 C D`. Split through the extended middle
  equiv `e'` (`re = up e' o Sum.inl`); the `p \ range re` rows are projected out by `re`/`en` and
  `rowOp_zeroes_upperRight L0 hB` closes the selected block. (This is the honest cost the SS(4.54)
  bijection elided.)

**Why the SS(4.54) "GO, SATISFIABLE, no fourth wall" verdict was under-specified, not wrong.** That
spike checked the cert is INVOKABLE at the **abstract** framework level (`refine ... (m1 := ...) ?...`
elaborates with abstract `m1`/`m2`/`p`, where a bijection type-checks vacuously) and that the count
arithmetic `D + D(mv-1) = D*mv` grounds out. It did **not** instantiate `card p = (D-1)|E(G)|` at the
real arm and compare it to `card m1 + card m2` -- so it did not surface that the relation is `<=`,
not `=`. The cert IS satisfiable for the real arm (via a strict injection); what was elided is that
the *bijection mechanism leaves (ii)/(iv) ride on* is the wrong one. No fourth wall; the geometry-arm
leaf count is +2 (B1, B2) over the SS(4.54) plan.

**Compiler-checked spike evidence (scratch, `lake env lean`, all green):**
- `card m1 + card m2 = D*(|V(G)|-1)` and `card p = (D-1)*|E(G)|` (the `Fintype.card` reads), and
  `V(Gab) = V(Gv) = V(G)\{v}` (`vertexSet_splitOff`/`removeVertex` -- the same vertex set).
- a strict injection `m1 + m2 ↪ p` exists from `card <= card`
  (`Function.Embedding.nonempty_of_card_le`); a bijection forces `card =` (`Fintype.card_congr`);
  and `card m < card p` ⟹ `IsEmpty (m ~= p)` -- so leaf (iv)'s required `e : (m1+m2) ~= p` is
  inapplicable in the strict case.
- (For completeness: when `G` *is* isostatic-tight (`(D-1)|E| = D(|V|-1)`) the bijection DOES exist,
  and the `D-2` surplus rows are the `a`-shifted `R(Gab)` deficiency-fill (`mixedBottom`, SS(4.40)),
  so leaves (ii)/(iv) serve *that* sub-case. But the arm must cover the general `<` case, so (b) is
  the real shape -- and a route handling `<` also handles `=`, so B1/B2 subsume leaves (ii)/(iv).)

**Consequence for the build.** Build owed leaves **B1** then **B2** (sigs above), then the
framework-level wrapper supplies the strict injection `re` (corner `e_a`-panel + `+-r` slot, and the
`mixedBottom` Gv / `a`-shifted-`e_b` bottom, packaged into disjoint `p`-rows), `M' =
rigidityMatrixEdge * U`, `hM'`, `L0 := cGv`-weights (leaf (i)), `hblock` (B2), `hA` (leaf (iii)),
`hD` (`mixedBottom`); fire `case_III_rank_certification_zero12`. Leaves (i)/(iii) are unaffected
(they do not touch `re` bijectivity); the single arm-coupling stays `L0` (the `cGv` widening).
**Clause-(iii) note:** the `card m1 + card m2 <= card p` inequality IS a stated chain of in-tree
facts (`rank_matroidMG_of_isKDof_zero` + `rk_le_card`), so B1's strict-injection existence is
grounded; the un-grounded thing is the *equality* the bijection would have needed.

## (4.56) THE FRAMEWORK-LEVEL CERT-FIRING WRAPPER — DECOMPOSITION. Compiler-checked end-to-end spike: the wrapper SKELETON (B1+B2+U+en firing the cert) builds sorry-free + axiom-clean; the remaining gaps decompose into 5 named sub-leaves with EXACT kernel-checked signatures. BANKED: `case_III_arm_realization_rowOp` (`ForkedArm.lean`). (Session #41; scratch reverted, tree clean.)

**What was kernel-confirmed.** A scratch `.lean` instantiated `case_III_rank_certification_zero₁₂`
for the real interior arm and the full firing — B1 (`exists_rowOp_of_strictInjection`) → `Lrow`, B2
(`rowOp_strictInjection_submatrix_eq_fromBlocks_zero₁₂`) → `hblock`, `U`/`hU` via
`prodColumnOpEquiv_transpose_toMatrix'_det_isUnit`, `en := (columnSplit v).symm`, leaf (iii) → `hA`,
mixedBottom → `hD` — **composes sorry-free** once `(re, hre, L₀, hM'eq, hB, hA, hD)` are supplied.
This is now BANKED as `case_III_arm_realization_rowOp` (the `_zero₁₂` sibling of
`case_III_arm_realization_matrix`/`_sep`; carries the row-op (4b″) block data, constructs
`Lrow`/`U`/`en`/`hblock` in-body, fires the cert, runs `case_III_realization_of_rank`). Axiom-clean
(`propext`/`Classical.choice`/`Quot.sound`), build + lint green, zero-regression. So the §(4.55)
"build B1 then B2 then the wrapper" plan is **kernel-validated end-to-end** — no fourth wall.

**The kernel-confirmed composition facts (the load-bearing seams).**
- **`M' = M * U`, cert wants `Lrow * M * U`; B2 gives `(Lrow * M').submatrix`. Bridge = `Matrix.mul_assoc`.**
  `(Lrow * M) * U` (cert) vs `Lrow * (M * U)` (B2). `conv_lhs => rw [Matrix.mul_assoc]` matches them
  (kernel-checked). NOT a free `rfl`; the wrapper carries the one-line `conv`.
- **The cert's `A` slot = the OPERATED corner `A − L₀ C`, not `A`.** B2 outputs `fromBlocks
  (A − L₀ C) 0 C D`, so the wrapper passes `(A := A − L₀*C)` and `hA : LinearIndependent ℝ
  (A − L₀*C).row` — which is EXACTLY leaf (iii)'s conclusion (the operated `±r` row reads `ρ₀`).
  Kernel-confirmed: passing `(A := A)` is a type mismatch; `(A := A − L₀*C)` fires.
- **The DEFEQ SEAM is real but `rfl`-bridgeable — and `set F := caseIIICandidate …` SPLITS it.**
  `Lrow`/`hM'eq` types display `caseIIICandidate.graph.edgeSet`; `re`'s codomain displays `{e // e ∈
  E(G)}`. They compose because `caseIIICandidate_graph = rfl`. **But `set F := caseIIICandidate …`
  rewrites the candidate occurrence inside `re`'s type and SHADOWS `re` (`re✝` vs `re`), so the
  bricks then reject `hbot`/`hM'eq` (type mismatch).** Kernel-reproduced. **The wrapper MUST use the
  literal `caseIIICandidate …` everywhere, never `set F` / `set M`** — the cert's own proof comment
  (`Candidate.lean:2483`) warns the same about `set F₀`. The banked wrapper takes `Fintype α` (not
  `Finite α`) as a class binder so the signature's `rigidityMatrixEdge`/edge-Fintype elaborate.
- **The lower-left `C` is NONZERO in general (this is WHY `_zero₁₂`, not `_matrix`).** With the
  mixedBottom `e_b`-fill row (first endpoint `= v`, `hbot1`'s `= v` arm) in `m₂`, its pin-column read
  is NOT zero (`_apply_pin_zero` needs `v ≠ (ends).1`, false for `e_b`) — so `toBlocks₂₁ = C ≠ 0`,
  the exact §(4.41) wall that killed the OLD lower-left-zero `_matrix` cert. The `_zero₁₂` cert zeros
  the UPPER-right `B` (via `Lrow`), leaves `C` free — kernel-confirmed it accepts nonzero `C`. (Only
  the pure-`Gv` bottom — both endpoints `≠ v`, `hbotpin` — gives `C = 0`, via
  `rigidityMatrixEdge_mul_columnOp_submatrix_toBlocks₂₁_eq_zero`; that brick is for the `_sep`/pure-Gv
  sub-case, NOT the mixed bottom.)

**The 5 owed sub-leaves (the wrapper's carried hypotheses; the chain dispatch discharges these next).**
All are arm-coupled to the `ChainData` interior split `(v=vtx i.castSucc, a=vtx i.succ, b=vtx (i−1),
e_a=edge i, e_b=edge (i−1))`. Sigs are the wrapper's hypothesis types (kernel-checked), with
`F := caseIIICandidate G ends q e_a e_b (q(a,·)) n' (q(b,·)) 0`, `M := F.rigidityMatrixEdge ends hgp`,
`U := (toMatrix' (prodColumnOpEquiv (columnOp hva).symm))ᵀ`, `en := (columnSplit v).symm`,
`p := {e // e ∈ F.graph.edgeSet} × Fin (D−1)`:

- **RE — the strict row injection + its injectivity (the genuinely-owed, NO PRECEDENT in tree).**
  `re : m₁ ⊕ m₂ → p` with `hre : Function.Injective re`, `m₁ := Fin (screwDim k)`,
  `m₂ := Fin (screwDim k * (V(Gv).ncard − 1))` (so `hm₁`/`hm₂` are `Fintype.card_fin`, TRIVIAL — the
  card pins are NOT the obstacle, the choice of `Fin`-types discharges them). The `m₁` corner splits
  `Fin D ≃ Fin (D−1) ⊕ Unit`: the `e_a`-panel rows `(e_a, j)` (`edgeRowSplit` corner, card `D−1`,
  `edgeRowSplit_corner_card`) + the ONE `±r` slot `(e_b, j₀)` (KT 6.66). The `m₂` bottom maps to the
  `Gv`-edge rows + the `a`-shifted `e_b`-fill rows (the W6b `w`-family rows). **Injectivity is the
  real content**: `e_b` is reused (corner `±r` slot AND bottom fill) at DISTINCT `Fin(D−1)`
  second-coords (`e_b` has `D−1` rows). Cardinality grounds (existence by
  `Function.Embedding.nonempty_of_card_le` off `D·(|V(G)|−1) ≤ (D−1)·|E(G)|`, §(4.55)), but a SPECIFIC
  `re` reading the right rows is the framework work. **No `re`-builder exists in tree** (neither
  `_chain` nor `_matrix` built it — both carry it; `_matrix` is superseded/unused). FLAG: this sub-leaf
  is genuinely-new and is the wrapper's hardest owed piece.
- **HMEQ — the column-op'd block read.** `hM'eq : (M * U).submatrix re en = fromBlocks A B C D`, with
  `A : Matrix m₁ ({body=v}×Fin D')`, `B : Matrix m₁ ({body≠v}×Fin D')`, `C : Matrix m₂ ({body=v}×Fin D')`,
  `D : Matrix m₂ ({body≠v}×Fin D')` (`D' := finrank ℝ (ScrewSpace k)`). Discharged by `(fromBlocks_toBlocks _).symm`
  taking `A/B/C/D := the four toBlocks`; the substance is then in HB/HA/HD reading those toBlocks via
  the operated-entry bricks (`_apply_corner` for `A`=toBlocks₁₁, `_apply_eB_off_pin` for `B`=toBlocks₁₂,
  `submatrix_columnOp_toBlocks₂₂_eq_mixedBottom` for `D`=toBlocks₂₂; `C`=toBlocks₂₁ is the `e_b`-row pin
  reads). Both `_submatrix_toBlocks₂₁_eq_zero` (pin-zero, pure-Gv) and `submatrix_columnOp_toBlocks₂₂_eq_mixedBottom`
  (mixed) verified to apply to the literal candidate (no `set F`).
- **HB — `B = L₀ * D` (leaf (i)'s `cGv`→`w` re-key + the still-owed `μ`-matching).** `hB : B = L₀ * D`
  with `L₀ := Matrix.of (cGv-fiberwise weights)`. Leaf (i) (`matrix_eq_mul_of_dual_row_comb`,
  axiom-clean) produces the matrix-algebra core from `hcomb : φ i = ∑ⱼ cGv • χ(μ i j)`. STILL OWED
  (deferred at leaf (i), as designed): the `Gv.IsLink → re`-image membership building `μ`, and the
  `φ`/`χ` matching of the corner `±r` off-`v` read (`_apply_eB_off_pin`) to the mixedBottom block —
  fed by the W6b producer's eq.-(6.66) `hingeRow a b ρ = ∑ⱼ cGv j • hingeRow (uvGv j) (vvGv j) (rvGv j)`.
  The `cGv`/`evGv`/`uvGv`/`vvGv` come from `exists_candidateRow_bottomRows_of_rigidOn`
  (`Candidate.lean:401`, keyed over `ofNormals Gv ends q`; the W6b producer needs `hrig`/`h622lb`).
- **HA — `LinearIndependent ℝ (A − L₀*C).row` (leaf (iii)'s `hAeq` + the gate).** `hA` for the
  OPERATED corner. Leaf (iii) (`corner_hA_zero₁₂_of_gate`, axiom-clean) closes it from the entrywise
  read `hAeq` (operated corner = `coordEquiv`-coordinate matrix of `[blockBasisOn(e_a,·); ρ₀]`
  reindexed by `em₁ : m₁ ≃ Fin(D−1) ⊕ Unit`) + the candidate-slot gate `hρe₀ : ρ₀(F.supportExtensor
  e_a) ≠ 0`. STILL OWED at the assembly: the entrywise `hAeq` (operated-entry bricks `_apply_corner`
  for the `e_a`-panel rows + the operated `±r` row = `ρ₀` via the `L₀`-subtraction = `−L₀ C` term
  built from `cGv`) and the `em₁`/`coordEquiv` packaging. The gate `hρe₀` is fired by Phase 23c's
  `exists_shared_redundancy_and_matched_candidate`.
- **HD — `LinearIndependent ℝ D.row` (the mixedBottom family, IH-`hrank`-conditional).**
  `hD : LinearIndependent ℝ D.row` for the bottom block. `linearIndependent_toBlocks₂₂_row_mixedBottom_of_finrank_eq`
  (`Concrete.lean:1729`, axiom-clean) closes it from `hrank : finrank (span (a-shifted bottom
  functionals)) = card m₂`, given `hbot2`/`hbot1`. The `hrank` is the IH full-rank fact: the bottom
  rows are `R(Gab, q)`'s genuine rows (`|V(Gab)| = |V(Gv)|`, so `card m₂ = D·(|V(Gab)|−1)` matches W6b's
  `w` index `Fin (D·(Gab.vertexSet.ncard − 1))`, and `LinearIndependent ℝ w` is a W6b conclusion). The
  arm supplies `hrank` from the split-off realization, via `splitOff_isMinimalKDof` off the interior
  `hsplitGP` (the C.3 `hIH` addition, APPROVED 2026-06-26).

**THREE DESIGN-PASS CLAUSES — verdicts.**
- **(i) verified against LANDED source.** Read B1/B2 (`Rank.lean:685`/`749`), leaf (i)
  (`Concrete.lean:1820`), leaf (iii) (`Concrete.lean:657` + `corner_hA'_of_gate:620`), the cert
  (`Candidate.lean:2446`), the mixedBottom family (`Concrete.lean:1579`/`1637`/`1729`), the
  operated-entry bricks (`_apply_pin_zero:1326`/`_apply_corner:1358`/`_apply_off_pin:1478`/
  `_apply_eB_off_pin:1514`/`_submatrix_toBlocks₂₁_eq_zero:1422`), the W6b producer
  (`Candidate.lean:401`), and the arm precedents `case_III_arm_realization_matrix`/`_sep`/`_chain`
  (`ForkedArm.lean`). All sigs are as relied on.
- **(ii) FLAG-DON'T-FORCE.** No motive/IH change, no new genuinely-unanticipated lemma, no
  wrong-level brick: the cert fires sorry-free. **FLAGGED:** sub-leaf RE (the strict-injection `re`)
  has NO in-tree precedent and is the hardest owed piece — its injectivity (with `e_b` reused across
  corner + bottom) and its row-reads (feeding HMEQ/HA/HD) are the genuinely-new framework content;
  the card PINS are NOT a blocker (trivial off `Fin`-types). The C.3 `hIH` addition (for HD's `hrank`
  via `splitOff_isMinimalKDof`) is APPROVED, not new.
- **(iii) cardinalities traced to GROUND.** `card m₁ + card m₂ = D·(|V(Gv)|) = D·(|V(G)|−1)`
  (`hVcard` + the cert's `D + D(mv−1) = D·mv` arithmetic, `Candidate.lean:2503`); `card p =
  (D−1)·|E(G)|`; `D·(|V(G)|−1) ≤ (D−1)·|E(G)|` is the STATED chain `rank_matroidMG_of_isKDof_zero` +
  `rk_le_card` (`Operations.lean:880`–885, the same `≤` `exists_isLink_of_isMinimalKDof_card_three`
  uses). `card m₂ = D·(|V(Gab)|−1)` matches W6b's `w` index since `V(Gab) = V(Gv) = V(G)∖{v}`
  (`removeVertex`/`splitOff` vertex sets). Mutually compatible by stated contract facts, not API
  existence alone.

**Consequence for the build (re-pointed).** The wrapper SKELETON is BANKED
(`case_III_arm_realization_rowOp`). The next concrete commit is sub-leaf **RE** (the strict
injection `re` + `hre` from the `ChainData`), the make-or-break framework piece; then HMEQ (the
`fromBlocks_toBlocks` read) wired to HB (leaf (i) + the owed `μ`-matching), HA (leaf (iii) + the owed
`hAeq`), HD (mixedBottom + the IH `hrank` via `hsplitGP`). On those landing, the dispatch wires
`case_III_arm_realization_rowOp` for the interior arm, the CHAIN layer closes, and ENTRY (23g) opens.

**RE SPLIT corner-first (Phase 23f, landed).** RE decomposes corner / bottom: the **corner half** is
carrier-agnostic and free-standing (the `e_a`-panel + `(e_b, j₀)` `±r` slot, KT (6.64)/(6.66)) — LANDED
axiom-clean as `cornerRowInjection`/`cornerRowInjection_injective`/`finScrewDimSplitCorner` (`Concrete.lean`,
A5d). The **bottom half** is W6b-coupled (the `w`-rows come back as dual functionals, not `(e,j)`-indexed, so
the realize-as-`p`-rows bridge is unbuilt) and is the harder remaining piece; the full `re := Sum.elim (corner ∘
finScrewDimSplitCorner) bottom` + `hre` (via `Function.Injective.sumElim`, cross-disjointness = the `e_b` reuse
at distinct `Fin(D−1)` coords) follows once the bottom lands. See `notes/Phase23f.md` *Decisions made*.

## (4.57) THE RE BOTTOM HALF + `Sum.elim` ASSEMBLY — DECOMPOSITION + the W6b-coupling CORRECTION. Compiler-checked recon (two scratch probes, reverted, tree clean). HEADLINE: HD's `hrank` does NOT touch the W6b `w`-family (the design doc's "realize-`w`-as-`(e,j)`-rows bridge" framing was WRONG); it is a basis-pick from full-rank `R(Gab)`. The W6b coupling is REAL but localized to HB's `μ`-matching. Cardinalities ground by stated facts. ONE flagged open decision (the bottom sub-arc shape) — **ADJUDICATED in §(4.58): route (b), no wrapper-signature change, BOT-3 dissolves.** (Session under `/coordinate-phase`.)

**Method.** Read the LANDED row-op wrapper `case_III_arm_realization_rowOp` (`ForkedArm.lean:315`, the
5 carried hyps `re`/`hre`/`L₀`/`hM'eq`/`hB`/`hA`/`hD`), the mixedBottom family
(`submatrix_columnOp_toBlocks₂₂_eq_mixedBottom` `Concrete.lean:1633` /
`rank_columnOp_toBlocks₂₂_eq_finrank_span_mixedBottom` `:1691` /
`linearIndependent_toBlocks₂₂_row_mixedBottom_of_finrank_eq` `:1783`), `rigidityMatrixEdge` +
`rigidityRowFunEdge` (`:716`/`:730`), the `e_b`-fill brick `..._apply_eB_off_pin` (`:1568`), the W6b
producer (`exists_candidateRow_bottomRows_of_rigidOn` `Candidate.lean:401`,
`chainData_split_w6b_gates` `Realization.lean:771`), leaf (i)/HB (`matrix_eq_mul_of_dual_row_comb`
`Concrete.lean:1874`), the landed corner half (`cornerRowInjection`/`_injective`/
`finScrewDimSplitCorner` `Concrete.lean:1063`–1095), and the `_sep`/`_matrix` arm precedents
(`ForkedArm.lean:130`/`234`). Two scratch probes (deleted): PROBE-A read the EXACT `hrank` residual;
PROBE-B compiled the full `Sum.elim` injectivity.

### (4.57.A) THE HEADLINE CORRECTION — HD's `hrank` is `w`-FREE (PROBE-A, kernel-read goal).

The §(4.56) / `Phase23f.md` hand-off framed the bottom half as "the W6b producer hands `w` back as
dual functionals, not `(e,j)`-indexed, so the realize-as-`p`-rows bridge is unbuilt — the harder
remaining piece." **PROBE-A refutes this for HD.** Applying
`linearIndependent_toBlocks₂₂_row_mixedBottom_of_finrank_eq` to the wrapper's `hD` goal leaves the
*exact* residual (kernel-read, verbatim modulo display):
```
⊢ Module.finrank ℝ (Submodule.span ℝ (Set.range fun i : m₂ =>
    BodyHingeFramework.hingeRow
      (if (ends (re (Sum.inr i)).1.1).1 = v then a else (ends (re (Sum.inr i)).1.1).1)
      (ends (re (Sum.inr i)).1.1).2
      ((F.blockBasisOn hgp _) (re (Sum.inr i)).2))) = Fintype.card m₂
```
This mentions ONLY `re`, `ends`, `a`, `v`, `F.blockBasisOn` — **no `w`, no `cGv`, no W6b producer**.
HD asks: *the `card m₂` a-shifted edge-restricted functionals selected by `re ∘ Sum.inr` are
linearly independent (span finrank = card)*. That is a **basis-pick / full-rank fact about
`R(Gab, q)`**, fed from `hsplitGP` (the split-off generic full-rank realization, def-0), NOT a
realization of the W6b `w`. The a-shift sends `Gv`-edge rows to themselves (`if = v` false →
genuine `R(Gv)` rows) and the `e_b`-fill row (`(ends e_b).1 = v`) to `hingeRow a b (blockBasisOn)`
= the `R(Gab)` `(a,b)`-fill row (`..._apply_eB_off_pin`, landed). So the a-shifted family IS
`R(Gab, q)`'s rows.

### (4.57.B) THE REAL W6b COUPLING — localized to HB's `μ`-matching, NOT to `re`'s bottom selection.

`cGv`/`w` enter via **HB** (`hB : B = L₀ * D`), through leaf (i)
(`matrix_eq_mul_of_dual_row_comb`, sig `Concrete.lean:1874`): it takes `φ`/`χ`/`cols` + a per-row
combination `hcomb : φ i = ∑ⱼ cGv i j • χ (μ i j)` and yields `B = L₀ * D` with `L₀ i i' =
∑_{μ i ·=i'} cGv i j`. Here `φ` = the corner `±r` off-`v` read (= `hingeRow a b ρ₀` content), `χ`
= the mixedBottom block `D`'s rows. The W6b eq.-(6.66) widening
`hingeRow a b ρ₀ = ∑ⱼ cGv j • hingeRow (uvGv j) (vvGv j) (rvGv j)` (a `chainData_split_w6b_gates`
conclusion, `Realization.lean:825`–831) supplies `hcomb` — provided **each `cGv`-summand's
`Gv`-link row `(evGv j, ·)` is one of `re`'s SELECTED bottom rows** (so the matching `μ : Fin nGv →
m₂` lands). THIS is the genuine coupling: `re`'s bottom selection must *contain* the W6b `cGv`-widening
support rows. It is a containment/`μ`-construction obligation on the chosen `re`, NOT a "realize each
abstract `w j` as a distinct `(e,j)` row" bijection. (`nGv` is the arbitrary `cGv`-summand count — it
need not equal `card m₂`; `μ` maps `Fin nGv → m₂`, fiberwise-summed, so multiple summands can share a
bottom row and not every bottom row need be hit.)

### (4.57.C) CARDINALITIES TRACED TO GROUND (clause iii).

`m₂ := Fin (screwDim k * (V(Gv).ncard − 1))` (the wrapper's `hm₂` pin; `card m₂` TRIVIAL off the
`Fin`-type). `V(Gab) = V(G.splitOff v a b e₀) = V(G) \ {v} = V(G.removeVertex v) = V(Gv)`
(`vertexSet_splitOff` `Operations.lean:606` = `rfl`; `vertexSet_removeVertex`). So `card m₂ =
D·(|V(Gv)|−1) = D·(|V(Gab)|−1)`. With `Gab.deficiency n = 0` (the interior `hdef_Gab`),
`finrank (span R(Gab).rigidityRows) = D·(|V(Gab)|−1) = card m₂` (the def-0 rigid-on identity,
`Realization.lean:854`–858 `hQrig` route). So HD's `hrank` target `card m₂` EQUALS the full
`R(Gab)` row rank — the a-shifted `re`-bottom family must be a MAXIMAL (spanning) LI selection. The
existence of such a selection rests on the a-shifted FULL edge family spanning `span
R(Gab).rigidityRows` (the un-landed spanning identity, see (4.57.E)). The `w` index `Fin
(D·(|V(Gab)|−1))` (W6b) coincides in count with `card m₂` — but they are NOT the same object (`w` =
dual functionals, `re∘Sum.inr` = `(e,j)` indices), and HD does not relate them.

### (4.57.D) THE `Sum.elim` ASSEMBLY — a CLEAN buildable leaf (PROBE-B, compiled sorry-free).

Given the bottom map `bottom : m₂ → ({e // e ∈ E(G)}) × Fin (D−1)` with `hbotinj` and the
cross-disjointness `hdisj : ∀ c i, cornerRowInjection e_a e_b j₀ c ≠ bottom i`, the full strict
injection composes (compiled, only PROBE-A's `sorry` + style warnings):
```
example (hne : e_a ≠ e_b) (hbotinj : Function.Injective bottom)
    (hdisj : ∀ c i, cornerRowInjection (k := k) e_a e_b j₀ c ≠ bottom i) :
    Function.Injective
      (Sum.elim ((cornerRowInjection e_a e_b j₀) ∘ finScrewDimSplitCorner) bottom) :=
  Function.Injective.sumElim
    ((cornerRowInjection_injective hne j₀).comp finScrewDimSplitCorner.injective) hbotinj
    (fun c i h => hdisj _ i h)
```
So the assembly is exactly the hand-off's predicted `Function.Injective.sumElim` shape. `hdisj`
reduces to: a `Gv`/`e_b`-fill bottom row never collides with the `e_a`-panel (`e_a ∉ E(Gv)`, `e_a ≠
e_b`) nor with the `(e_b, j₀)` corner slot (the `e_b`-fill bottom rows use `Fin(D−1)` coords `≠ j₀`
— the "`e_b` reused at distinct coords" fact). This is small, no new math.

### (4.57.E) DECOMPOSITION OF THE BOTTOM SUB-ARC + the FLAGGED OPEN DECISION.

The bottom half is **not one leaf** — it is a sub-arc (3–5 commits). Buildable order:

- **BOT-1 — the a-shifted full-edge spanning identity (genuinely-new, the keystone; NO precedent).**
  Target: the FULL family of a-shifted edge-restricted functionals over `Gv`-edges + the `e_b`-fill
  spans `span (R(G.splitOff v a b e₀, q).rigidityRows)`. This is the a-shifted analogue of the
  landed `span_range_rigidityRowFunEdge` (`Concrete.lean:766`), with the `e_b` row carrying the
  `if = v then a` shift to `hingeRow a b`. Needs the `e_b`-fill panel-functional matching to
  `R(Gab)`'s genuine `(a,b)`-row (the reproduced support extensor at `t=0`,
  `caseIIICandidate_supportExtensor_reproduced` `Candidate.lean:972` + the cross-label bridge
  `hingeRow_mem_caseIIICandidate_rigidityRows_of_ofNormals_link` `:1011`). **This is the keystone:
  without it, the basis-pick of size `card m₂` is not guaranteed to exist.**
- **BOT-2 — the index-level basis-pick (`(e,j)`-selection of size `card m₂`).** From BOT-1's
  spanning family (finite, indexed by `{e // e ∈ E(Gv)} × Fin(D−1) ⊎ Fin(D−1)` for the `e_b`-fill)
  reaching finrank `card m₂`, extract an LI sub-selection of exactly `card m₂` indices reindexed by
  `m₂ = Fin (D·(|V(Gv)|−1))`. Engine: `Matrix.exists_linearIndependent_rows_specialize` /
  `exists_submatrix_det_ne_zero_of_linearIndependent_rows` (`Rank.lean:200`/`265`) or mathlib's
  `exists_linearIndependent'` reindexed — a basis extraction from a spanning indexed family. Yields
  `bottom : m₂ → p` (an `(e,j)` map) with `hbot2`/`hbot1` discharged structurally (Gv-rows: both
  endpoints `≠ v`; the `e_b`-fill: first endpoint `= v`, second `= b ≠ v`) and `hrank` = BOT-1's
  finrank rewritten + the LI selection's `finrank_span_eq_card`.
- **BOT-3 — the `μ`-matching for HB (the W6b coupling discharge).** Build `μ : Fin nGv → m₂` from the
  W6b `cGv`-widening's `evGv`/`uvGv`/`vvGv` (`chainData_split_w6b_gates`) into BOT-2's `bottom`
  selection, so `hcomb` (leaf (i)'s input) holds. CONSTRAINT this places on BOT-2: the selection must
  CONTAIN every `cGv`-summand's `Gv`-link row. (Open: whether BOT-2's basis-pick can be steered to
  include a prescribed finite set of `Gv`-rows while staying LI of full rank — a "extend a partial LI
  set to a basis" rather than a free pick. See FLAG below.)
- **BOT-4 — `Sum.elim` assembly + `hre`** (4.57.D, the clean leaf) + the wrapper-level `hM'eq` via
  `(fromBlocks_toBlocks _).symm` (HMEQ) instantiating `A/B/C/D` as the four `toBlocks`, so `D` IS the
  mixedBottom `toBlocks₂₂` PROBE-A discharges.

**FLAGGED OPEN DECISION (flag-don't-force; needs a build-spike or user note at the bottom-arc open).**
The tension between **BOT-2** (a free maximal-rank `(e,j)` basis-pick → cleanest `hrank`) and
**BOT-3** (HB's `μ` needs `bottom` to CONTAIN the W6b `cGv`-support rows). Two routes:
  (a) **Steered basis-pick** — extend the (finite) W6b `cGv`-support `Gv`-rows to a full-rank LI
      `card m₂`-selection (mathlib `LinearIndependent.extend` / `exists_linearIndependent` from a
      partial LI set). Risk: the `cGv`-support rows need to BE linearly independent to seed the
      extension (true if the W6b `w`-family they relate to is LI, a W6b conclusion — but the `cGv`
      *widening* `evGv`/`uvGv` summands are a `Finset.sum`, NOT a priori LI). NEEDS A SPIKE.
  (b) **Decouple HB from `re`'s exact selection** — re-examine whether leaf (i)'s `μ` can map into a
      LARGER bottom index (all `Gv`-rows, with the basis-pick applied only for `hrank`), i.e. split
      `B = L₀·D` so `D`'s rows are the W6b support and a SEPARATE rank argument feeds `hrank`. This
      may need an HB/HD reconciliation the §(4.56) wrapper signature (which ties both to the SAME
      `re`/`D`) does not currently permit — a possible **wrapper-signature revisit** (the `B`/`D` of
      `hB` and the `D` of `hD` are the same matrix in `case_III_arm_realization_rowOp`).
This is a genuine sub-arc-level decision, NOT a single-leaf detail. It does **not** touch the cert,
the motive/IH, or the frozen C.0–C.6 contract; it is entirely below the wrapper. Recommend a BOT-3
feasibility spike (route (a)) BEFORE committing BOT-1/BOT-2, since route (b) would reshape the
wrapper's carried `(hB, hD)` interface.

**THREE DESIGN-PASS CLAUSES — verdicts.**
- **(i) verified against LANDED source.** Every load-bearing object read at the cited line (the
  wrapper sig, the mixedBottom `hrank` shape via PROBE-A's kernel goal, `rigidityRowFunEdge`,
  `..._apply_eB_off_pin`, leaf (i)'s `hcomb` shape, the W6b `(nGv, cGv, evGv)` conclusion, the
  corner half). The §(4.56) "realize-`w`-as-rows" framing was treated as a hypothesis and FOUND
  WRONG for HD (PROBE-A).
- **(ii) FLAG-DON'T-FORCE.** No motive/IH/contract change. The bottom half is a 3–5-commit SUB-ARC
  with a keystone genuinely-new lemma (BOT-1) and ONE flagged open decision (BOT-2-vs-BOT-3 `μ`
  steering, with a possible wrapper `(hB,hD)` revisit under route (b)). FLAGGED, not forced — recon
  recommends a BOT-3 spike first.
- **(iii) cardinalities to GROUND.** `card m₂ = D·(|V(Gv)|−1) = D·(|V(Gab)|−1) = finrank (span
  R(Gab).rigidityRows)` by `vertexSet_splitOff` (=`rfl`) + the def-0 rigid identity — a STATED chain,
  not API existence. `w`/`re∘Sum.inr` coincide in COUNT (`D·(|V(Gab)|−1)`) but are distinct objects;
  HD relates neither to `w`. The `nGv`/`cGv`-widening count is ARBITRARY (`μ` fiberwise), not
  `card m₂`.

**Consequence for the build (re-pointed).** Next concrete commit = **BOT-3 feasibility spike** (does
the W6b `cGv`-support extend to a full-rank `card m₂` `(e,j)`-selection? — adjudicates route (a)/(b)),
then **BOT-1** (the a-shifted spanning identity, the keystone), **BOT-2** (the index basis-pick →
`bottom`/`hbot2`/`hbot1`/`hrank`), **BOT-3** (the `μ`-matching for HB), **BOT-4** (the `Sum.elim`
assembly, the clean 4.57.D leaf, + HMEQ). Then HA's `hAeq` (leaf (iii) + the operated-entry bricks),
the dispatch wires `case_III_arm_realization_rowOp`, item 3c, item 4 / CHAIN-5.

## (4.58) THE BOT-3 OPEN DECISION — VERDICT: **route (b), and it costs NO wrapper-signature change.** Route (a) is REFUTED (the `cGv`-support rows are NOT stated LI, so they cannot seed `LinearIndependent.extend`); route (b)'s `B = L₀·D`-from-span-membership mechanism is KERNEL-CHECKED (`probe_matrix_eq_mul_of_span_mem`, compiled sorry-free, reverted). HB does NOT need the `cGv` widening AT ALL: when `D` is the full-rank basis-pick, `span(D-rows) = span R(Gab).rigidityRows ⊇ hingeRow a b ρ₀`, so a generic span repr supplies `L₀`. (Session under `/coordinate-phase`; scratch reverted, tree clean.)

**Method.** Read the LANDED source verbatim: the W6b producer's full conclusion (`exists_candidateRow_bottomRows_of_rigidOn` `Candidate.lean:401`; its `chainData_split_w6b_gates` re-export `Realization.lean:771`, the `cGv`-widening clause `:825`–831), leaf (i)'s `hcomb`/`μ` types (`matrix_eq_mul_of_dual_row_comb` `Concrete.lean:1874` + its engine `of_eq_mul_of_row_comb` `Rank.lean:608`), the wrapper's `(hB,hD)` binding (`case_III_arm_realization_rowOp` `ForkedArm.lean:315`, the `B`/`C`/`D` block decls `:346`–349 + `hB`/`hD` `:358`/`362`), the mixedBottom `B`-row read (`..._apply_eB_off_pin` `Concrete.lean:1568`) and `D`-block (`submatrix_columnOp_toBlocks₂₂_eq_mixedBottom` `:1633`), the candidate-row span facts (`hingeRow_mem_caseIIICandidate_rigidityRows_reproduced` `Candidate.lean:2133`, `..._of_ofNormals_link` `:1011`), and the mathlib LI-extension hypotheses (`Basis.extend` `Basis/VectorSpace.lean:52`; `exists_linearIndependent`/`exists_linearIndepOn_id_extension` `LinearIndependent/Lemmas.lean:750`/756; the span-repr `Submodule.mem_span_range_iff_exists_fun` `Finsupp/LinearCombination.lean:381`). One scratch probe (`probe_matrix_eq_mul_of_span_mem`, deleted): compiled route (b)'s core.

### (4.58.A) THE PIVOTAL QUESTION SETTLED — the `cGv`-support rows are NOT (stated) LI (clause iii, traced to GROUND).

The W6b producer's final existential (both `Candidate.lean:440`–446 and the gate-bundle `Realization.lean:825`–831) carries about the `cGv`-widening summands EXACTLY three facts and no more:
```
∃ (nGv : ℕ) (cGv : Fin nGv → ℝ) (evGv : Fin nGv → β) (uvGv vvGv : Fin nGv → α)
    (rvGv : Fin nGv → Module.Dual ℝ (ScrewSpace k)),
  (∀ j, Gv.IsLink (evGv j) (uvGv j) (vvGv j)) ∧
  (∀ j, rvGv j ∈ … .hingeRowBlock (evGv j)) ∧
  hingeRow a b ρ = ∑ j, cGv j • hingeRow (uvGv j) (vvGv j) (rvGv j)
```
There is **NO `LinearIndependent` clause** on the `cGv`-summand family `fun j ↦ hingeRow (uvGv j) (vvGv j) (rvGv j)`, **no distinctness** of the summands, and **`nGv` is arbitrary** (an existential `ℕ`, not pinned to any rank). The `LinearIndependent ℝ w` clause earlier in the conclusion (`Candidate.lean:423` / `Realization.lean:804`) is about the **separate** `w`-family `Fin (screwDim k·(|V(Gab)|−1)) → Dual` — a DIFFERENT existential object, NOT the `cGv`-summands (PROBE-A / §(4.57.A) already noted HD never relates `w` to `re`). **Verdict:** the coordinator's refutation hypothesis is CONFIRMED from the stated conclusion (its ABSENCE, per clause iii). The `cGv`-support `Gv`-rows are generically a `Finset.sum` over a non-LI, possibly-repeating, `nGv`-can-exceed-`dim R(Gv)` family — a single vector `hingeRow a b ρ` expanded over a spanning set, exactly as hypothesized.

### (4.58.B) ROUTE (a) IS REFUTED AT ITS PRECONDITION (clause ii, against landed mathlib API).

Route (a) (steer the basis-pick to CONTAIN the `cGv`-support rows via `LinearIndependent.extend` / `exists_linearIndependent`) needs the seed set to BE linearly independent: every mathlib extension API requires it. `Basis.extend (hs : LinearIndepOn K id s)` (`Basis/VectorSpace.lean:52`) and `exists_linearIndepOn_id_extension (hs : LinearIndepOn K id s) (hst : s ⊆ t)` (`LinearIndependent/Lemmas.lean:750`) both take `LinearIndepOn` of the seed as a HYPOTHESIS; `exists_linearIndependent` (`:756`) seeds from `∅` and so does NOT let you *prescribe* the `cGv`-support inclusion. By (4.58.A) the `cGv`-support rows have no stated LI guarantee — so the seed hypothesis is unavailable and route (a) **fails as stated**. (One could try to first reduce the `cGv` widening to an LI sub-family spanning the same vector, but the W6b producer hands back no such sub-family and re-deriving one is strictly more work than route (b).) **Route (b) is forced — and it is the SIMPLER route.**

### (4.58.C) ROUTE (b) NEEDS NO WRAPPER-SIGNATURE CHANGE — `hB`/`hD` already share `D`; that is fine (clause i, the load-bearing correction to §(4.57.E)/the FLAG).

§(4.57.E)'s route-(b) sketch feared a `case_III_arm_realization_rowOp` `(hB,hD)`-signature revisit (decouple `hB`'s `D` from `hD`'s `D`). **This is NOT needed.** The wrapper binds ONE `D : Matrix m₂ ({body ≠ v} × Fin D) ℝ` (`ForkedArm.lean:349`), with `hB : B = L₀ * D` (`:358`) and `hD : LinearIndependent ℝ D.row` (`:362`) — the SAME `D`. Route (b) keeps them the same, because the real obligation `B = L₀ · D` only needs **each `B`-row functional to lie in the ROW-SPAN of `D`** — NOT that each `cGv`-summand equal a single `D`-row (that was the over-strong BOT-3 containment §(4.57.B) read into leaf (i)). When the `re`-bottom selection is the full-rank `card m₂` basis-pick (BOT-2, what HD's `hrank` demands anyway, §(4.57.A)), `span (D-row functionals) = span R(Gab).rigidityRows` (a full-rank LI selection of size = total rank spans the whole space, `finrank_span_eq_card` + the def-0 identity §(4.57.C)). And the `B`-row functionals lie in that span:
- the `±r` corner slot's `B`-row is `hingeRow a b ρ₀` (`..._apply_eB_off_pin` `Concrete.lean:1568`, FIRST-endpoint-`v` a-shift), which `hingeRow_mem_caseIIICandidate_rigidityRows_reproduced` (`Candidate.lean:2133`) + `hρGv ∈ span R(Gv) ⊆ span R(Gab)` (`hle` edge-inclusion) puts in `span R(Gab).rigidityRows`;
- the `e_a`-panel `B`-rows are the a-shifted `hingeRow a (ends e_a).2 (blockBasisOn e_a ·)` — the same a-shifted family `D`'s rows are drawn from (`rank_columnOp_toBlocks₂₂_eq_finrank_span_mixedBottom` `:1691` proves `D`'s rank = the a-shifted family's span finrank), so they too sit in `span R(Gab).rigidityRows`.
Hence each `B`-row ∈ `span (range χ)` and `B = L₀·D` follows from a generic span repr — **no `cGv`, no `μ`, no containment.**

**KERNEL-CHECKED (the route-(b) core).** `probe_matrix_eq_mul_of_span_mem` (scratch, compiled sorry-free, reverted): given `χ : m₂ → Dual`, `φ : m₁ → Dual`, `cols`, and `hmem : ∀ i, φ i ∈ span (range χ)`, it produces `∃ L₀, (of fun i x ↦ φ i (single (cols x).1 (finScrewBasis k (cols x).2))) = L₀ * (of fun i' x ↦ χ i' (single …))`. Proof: `choose c hc := mem_span_range_iff_exists_fun.1 (hmem i)` (per-row weights, `[Fintype m₂]` ✓), `refine of_eq_mul_of_row_comb …`, evaluate `hc i` at the single-body column (`congrArg` + `LinearMap.sum_apply`/`smul_apply`), `rfl`. Two-line core; the only instance need is `[DecidableEq α]` (for `Pi.single`, already on the wrapper). This is leaf (i)'s engine (`of_eq_mul_of_row_comb`) fed a SPAN-MEMBERSHIP repr instead of a `cGv` widening — strictly simpler than leaf (i) itself.

### (4.58.D) THE WIN: BOT-3 DISSOLVES; the W6b coupling is OFF the `re`-bottom critical path.

Under route (b) the §(4.57.E) sub-arc collapses. BOT-3 (the `μ`-matching that made `re`'s bottom CONTAIN the `cGv`-support — the "genuine coupling" of §(4.57.B)) **vanishes**: HB is discharged by span-membership of the `B`-rows in the full-rank `D`, which BOT-1/BOT-2 already establish. The W6b `cGv` widening is no longer load-bearing for the geometry arm's `hB` (it remains the IH→candidate-row producer feeding `hρGv`, but `hingeRow a b ρ₀ ∈ span R(Gv)` is ALL HB needs of it, NOT the per-edge expansion). Leaf (i) `matrix_eq_mul_of_dual_row_comb` stays in tree (correct, general) but is NOT the HB route for the basis-pick `D`; the wrapper's `hB` is fed by the simpler span-repr leaf instead.

### (4.58.E) RE-SCOPED BOTTOM SUB-ARC (the EXACT next-leaf signatures for the winning route).

The sub-arc is now **4 leaves, all below the wrapper, none reshaping any frozen interface**:

- **BOT-1 — the a-shifted full-edge → `span R(Gab)` spanning identity (the keystone, NO precedent; UNCHANGED from §(4.57.E)).** The a-shifted edge family (`Gv`-rows + the `e_b`-fill a-shifted to `(a,b)`) spans `span (caseIIICandidate …).rigidityRows`. Engine in tree: `span_range_rigidityRowFunEdge` (`Concrete.lean:766`, the un-shifted analogue) + the per-row membership bricks `hingeRow_mem_caseIIICandidate_rigidityRows_of_ofNormals_link` (`Candidate.lean:1011`, the `Gv`-link rows) and `..._reproduced` (`:2133`, the `e_b`-fill→`(a,b)` row). Target sig (a-shifted family `wfun i := hingeRow (if (ends …).1 = v then a else …) (ends …).2 (blockBasisOn …)`):
  `Submodule.span ℝ (Set.range wfun) = Submodule.span ℝ (caseIIICandidate G ends q e_a e_b … 0).rigidityRows`.
- **BOT-2 — the index basis-pick (UNCHANGED).** From BOT-1's spanning family reaching finrank `card m₂` (the def-0 identity §(4.57.C)), extract an LI sub-selection of exactly `card m₂` `(e,j)`-indices → `bottom : m₂ → p` with `hbot2`/`hbot1` structural and `hrank` = `finrank_span_eq_card`. Engine: `exists_linearIndependent'` (`LinearIndependent/Lemmas.lean:763`, reindexed) or the project's `Rank.lean` selectors. NO steering needed (route (a)'s constraint is gone), so this is a FREE maximal-rank pick — the cleanest form.
- **BOT-3′ — HB via span-membership (REPLACES the old BOT-3 `μ`-match; the route-(b) leaf, sig below).** A `BodyHingeFramework`-level leaf: each corner `B`-row functional ∈ `span (range (D-row functionals))`, then the `probe_matrix_eq_mul_of_span_mem` mechanism gives `hB : B = L₀ * D`. Exact signature to land (the generalized leaf-(i) sibling, carrier-agnostic):
  ```
  theorem …matrix_eq_mul_of_span_mem [DecidableEq α] {m₁ m₂ n : Type*} [Fintype m₂]
      (χ : m₂ → Module.Dual ℝ (α → ScrewSpace k)) (φ : m₁ → Module.Dual ℝ …)
      (cols : n → α × Fin (Module.finrank ℝ (ScrewSpace k)))
      (hmem : ∀ i, φ i ∈ Submodule.span ℝ (Set.range χ)) :
      ∃ L₀ : Matrix m₁ m₂ ℝ,
        (Matrix.of fun i x => φ i (Pi.single (cols x).1 (finScrewBasis k (cols x).2)))
          = L₀ * Matrix.of (fun i' x => χ i' (Pi.single (cols x).1 (finScrewBasis k (cols x).2)))
  ```
  At the wrapper this consumes BOT-1's spanning identity + each `B`-row's candidate-rigidity-row membership (the two bullets in (4.58.C)) to hand `hB` the existential `L₀`. (It lives next to `matrix_eq_mul_of_dual_row_comb` in `Concrete.lean`; leaf (i) stays as the `cGv` form for any future consumer that wants the explicit weights.)
- **BOT-4 — `Sum.elim` assembly + `hre` + HMEQ (UNCHANGED, the clean §(4.57.D) leaf compiled in PROBE-B).** `re := Sum.elim (cornerRowInjection ∘ finScrewDimSplitCorner) bottom`, `hre` via `Function.Injective.sumElim` + the cross-disjointness; `hM'eq` via `(fromBlocks_toBlocks _).symm`.

Then HA's `hAeq` (leaf (iii) + the operated-entry bricks), the dispatch wires `case_III_arm_realization_rowOp`, item 3c, item 4 / CHAIN-5.

**THREE DESIGN-PASS CLAUSES — verdicts.**
- **(i) verified against LANDED source.** Every load-bearing object read at the cited line: the W6b conclusion (no LI clause on `cGv`-summands), leaf (i)'s `hcomb`/`μ` + `of_eq_mul_of_row_comb`, the wrapper's SINGLE-`D` `(hB,hD)` binding, the mathlib extension API's `LinearIndepOn`-seed hypothesis, the span-repr API, the candidate-row membership bricks. The §(4.57.E) FLAG's feared wrapper revisit was treated as a hypothesis and FOUND UNNECESSARY.
- **(ii) FLAG-DON'T-FORCE → nothing forced.** Route (b) wins and reshapes NO signature — not the wrapper, not leaf (i) (which stays as-is; BOT-3′ is a NEW sibling, not an edit). No consumer of `case_III_arm_realization_rowOp` is touched (grep: the wrapper has zero in-tree callers yet — the dispatch that will call it is itself owed, item 4). The frozen C.0–C.6, the motive/IH, and the cert are untouched.
- **(iii) traced to GROUND.** The pivotal LI claim is REFUTED from the STATED W6b conclusion's *absence* of an LI clause (4.58.A), not asserted. Route (b)'s `(hB,hD)` composition stays valid: same `D` block type `Matrix m₂ ({body ≠ v} × Fin (finrank (ScrewSpace k))) ℝ` feeds B2 and the cert exactly as the wrapper already wires it; the route-(b) core is kernel-checked (4.58.C).

**Consequence for the build (re-pointed).** Next concrete commit = **BOT-1** (the a-shifted spanning identity, the keystone — route adjudicated, spike done). The BOT-3 spike is DISCHARGED: route (b), no wrapper change, BOT-3 dissolves into a span-membership leaf (BOT-3′). Buildable order: BOT-1 → BOT-2 (free basis-pick) → BOT-3′ (`matrix_eq_mul_of_span_mem` + the `B`-row membership) → BOT-4 (`Sum.elim` + `hre` + HMEQ). Then HA's `hAeq`, the dispatch, item 3c, item 4 / CHAIN-5.

## (4.59) BOT-1 LANDED axiom-clean — the keystone built; the "partly BLOCKED" framing was a CONFLATION; §(4.58.E)'s RHS was wrong. (Session under `/coordinate-phase`; kernel-checked + full build/lint green.)

**Verdict.** BOT-1 BUILDS sorry-free, axiom-clean, as `BodyHingeFramework.span_range_hingeRow_crossFramework_eq_rigidityRows` (`Basic.lean`, right after the L-span leaf `span_range_hingeRow_blockSpanning_eq_rigidityRows`). The coordinator's strong prior (BOT-1 is buildable; the "BLOCKED" cite was a conflation) is CONFIRMED.

### (4.59.A) THE CONFLATION, RESOLVED (clause i — verified against landed source).
The §(4.58.E)/`Phase23f.md` framing — "BOT-1 needs the term-distinct `R(Gab)`-row matching the design flags as partly BLOCKED in matrix form (`rank_columnOp_toBlocks₂₂_eq_finrank_span_mixedBottom` docstring)" — conflated TWO distinct objects:
- **The BLOCKED thing** = the matrix-EQUALITY `submatrix_columnOp_toBlocks₂₂_eq_Gab` (`notes/Phase23d.md` *Current state*/step 3), whose residual needs equal *chosen* basis vectors `F₁.blockBasisOn = F₂.blockBasisOn` — false for `finBasisOfFinrankEq` on term-distinct submodules. The project AVOIDED it via the RANK route (L-span/L-rank/L-hD). The L-rank docstring (`Concrete.lean:1678`) is about that matrix-equality being blocked, NOT about BOT-1.
- **BOT-1** = a span SET-equality `span (range wfun) = span (R(Gab)).rigidityRows`, proven by `le_antisymm`. Span equality is robust to basis choice — it needs equal BLOCKS (the support-extensor match), not equal basis VECTORS — so the term-distinct wall never reforms. Built straightforwardly.

### (4.59.B) THE RHS CORRECTION — `span (R(Gab)).rigidityRows`, NOT the candidate (clause iii, traced to ground).
§(4.58.E)'s BOT-1 sig wrote RHS `= span (caseIIICandidate G ends q e_a e_b … 0).rigidityRows`. **That is WRONG.** `finrank (span candidate.rigidityRows) = D·(|V(G)|−1)` (the cert's own conclusion, `case_III_rank_certification_zero₁₂`), which is LARGER than the bottom block's `card m₂ = D·(|V(Gab)|−1) = D·(|V(G)|−2)`. HD's consumer `linearIndependent_toBlocks₂₂_row_mixedBottom_of_finrank_eq` (`Concrete.lean:1783`) needs `finrank (span (a-shifted family)) = card m₂`, so the RHS must be a space of finrank `D·(|V(Gab)|−1)` = `span (R(Gab)).rigidityRows` (`F₂ = Q.toBodyHinge`, the IH split-off framework, def-0 rigid). This matches the **Phase-23d *step 4* hand-off** intent verbatim: "compose L-span [bottom-row span = `span F₂.rigidityRows`] with `finrank (span F₂.rigidityRows) = D·(|V_Gab|−1) = #m₂` from `hsplitGP`". `F₂ ≠ F₁`, so the single-framework L-span does NOT apply directly — BOT-1 is the genuinely-new cross-framework generalization, not redundant.

### (4.59.C) THE LANDED SHAPE.
```
theorem span_range_hingeRow_crossFramework_eq_rigidityRows
    (F₁ F₂ : BodyHingeFramework k α β) {ι : Type*} (ends₁ : β → α × α)
    (remap : {e // e ∈ F₁.graph.edgeSet} → {e // e ∈ F₂.graph.edgeSet})
    (hremap_surj : Function.Surjective remap)
    (B : (e : {e // e ∈ F₁.graph.edgeSet}) → ι → Module.Dual ℝ (ScrewSpace k))
    (hspan : ∀ e, Submodule.span ℝ (Set.range (B e)) = F₂.hingeRowBlock (remap e))
    (hlink₁ : ∀ e, F₂.graph.IsLink (remap e).1 (ends₁ e.1).1 (ends₁ e.1).2) :
    Submodule.span ℝ (Set.range fun p : {e // e ∈ F₁.graph.edgeSet} × ι =>
        hingeRow (ends₁ p.1.1).1 (ends₁ p.1.1).2 (B p.1 p.2))
      = Submodule.span ℝ F₂.rigidityRows
```
`F₁` = candidate, `F₂ = R(Gab)`; `remap` = the surjective `Gv↔Gv`/`e_b↔e₀` edge relabel; `ends₁` carries the `if (ends e).1 = v then a else …` a-shift; `B = F₁.blockBasisOn`. Proof = `le_antisymm` structurally identical to L-span: `≤` routes each row into `F₂`'s rows via `hlink₁` + `hspan`'s `⊆ block`; `≥` transfers a section `s` of `remap` to pull each `F₂`-generator's block row into `span {B (s e') i}` (`hspan` + `Function.RightInverse`), then `span_induction` over the `screwDiff`-`dualMap` linearity, matching endpoints up to swap (`hingeRow_swap`). Carrier/coordinatization-agnostic, NO `ScrewSpace` unfold; axioms = `[propext, Classical.choice, Quot.sound]` only.

### (4.59.D) FLAG-DON'T-FORCE → nothing forced (clause ii). OWED at the wrapper (not blocked, leaf-level).
The hypotheses `hremap_surj`/`hspan`/`hlink₁` are the cross-framework matching, DEFERRED to the wrapper/dispatch (the same idiom as the membership bricks + L-span, which all take their matching as hypotheses). They are dischargeable from in-tree facts at the candidate→`R(Gab)` instantiation: `hspan` from the cross-label support-extensor match `hingeRow_mem_rigidityRows_of_supportExtensor_eq` (the block depends only on the support extensor — `ofNormals · ends q`'s supportExtensor reads ONLY `ends`/`q`, not the graph, `PanelHinge.lean:95` — so candidate-off-slot and `R(Gab)` blocks coincide when endpoints/normals match) + `caseIIICandidate_supportExtensor_reproduced` at `t=0` for the `e_b→e₀` slot; `hlink₁` from `Q.ends` recording `Gab`-links (orientation-free, `hlink₁` is swap-robust). The wrapper's `hrank` then = BOT-1 + `finrank (span (R(Gab)).rigidityRows) = #m₂` (def-0) + BOT-2's basis-pick. No motive/IH/contract change; the cert is untouched; the wrapper signature is unchanged.

**Consequence for the build.** Next concrete commit = **BOT-2** (the FREE index basis-pick: BOT-1's spanning family reaches finrank `card m₂`, extract an LI `card m₂`-selection → `bottom`/`hbot2`/`hbot1`/`hrank` via `finrank_span_eq_card`). Then BOT-4 (`Sum.elim` + HMEQ), HA's `hAeq`, the dispatch (which discharges BOT-1's owed concrete `remap`/`hspan`/`hlink₁`), item 3c, item 4 / CHAIN-5. BOT-1 + BOT-3′ done.

## (4.60) BOT-2 LANDED axiom-clean (both the abstract free-pick engine AND the candidate-level bridge); the concrete BOT-1 instantiation's `e_a`-row breaks `hlink₁` and is the EXACT residual. (Session under `/coordinate-phase`; kernel-checked, full build/lint green, zero-regression.)

**Verdict.** BOT-2 BUILDS sorry-free, axiom-clean, in TWO pieces — the free basis-pick *engine* and the candidate-level *bridge* that wires BOT-1's conclusion to the wrapper's `hD` data. The remaining item-1 piece (the concrete `remap`/`hspan`/`hlink₁` instantiation of BOT-1) hits a **genuine obstruction** flagged by the coordinator: BOT-1's family ranges over ALL of `E(F₁)` including `e_a`, whose `a`-shifted row `hingeRow a a` cannot satisfy `hlink₁` against any `F₂`-edge. The honest residual is below.

### (4.60.A) THE TWO LANDED LEMMAS (clause i — verified against landed source).
- **The abstract free-pick engine** `exists_finCard_linearIndependent_selection` (`Mathlib/LinearAlgebra/Matrix/Rank.lean`, top-level, before `namespace Matrix`). Sig: `(χ : ι → V) [Finite ι] [AddCommGroup V] [Module ℝ V] {N} (hrank : finrank ℝ (span ℝ (range χ)) = N) : ∃ sel : Fin N → ι, Function.Injective sel ∧ LinearIndependent ℝ (χ ∘ sel)`. The indexed-family / fixed-cardinality companion of `exists_linearIndependent'`: where `exists_submatrix_det_ne_zero_of_linearIndependent_rows` extracts a basis of the *whole* coordinate space `m → K` (span `= ⊤`), this extracts a selection spanning a *proper* finite-dim submodule, so the selection is a basis of that submodule (`Module.Basis.mk` on the co-restricted family). Carrier-agnostic, no matrix structure. The `Fintype κ`-from-`exists_linearIndependent'` detour is logged (FRICTION Open *fixed-cardinality index selection*).
- **The candidate-level bridge** `BodyHingeFramework.bottom_selection_of_crossFramework_span` (`Concrete.lean`, right after `linearIndependent_toBlocks₂₂_row_mixedBottom_of_finrank_eq`). Sig: takes the framework `F`/`ends`/`hgp`, `{v a}`, `{m₂}[Fintype]`, the IH split-off framework `F₂`, and THREE hypotheses — `hspan_id` (BOT-1's concrete conclusion: the `a`-shifted FULL candidate edge family over `p = {e // e ∈ E(F.graph)} × Fin (screwDim k − 1)` spans `span F₂.rigidityRows`), `hfr` (`finrank (span F₂.rigidityRows) = card m₂`, the def-0 count), `hbot2_all` (∀ candidate edge, SECOND endpoint ≠ v) — and produces `∃ re : m₂ → p, (hbot2)(hbot1)`(`finrank (span (range (a-shifted family ∘ re))) = card m₂`)`, EXACTLY the `(re, hbot2, hbot1, hrank)` the consumer `linearIndependent_toBlocks₂₂_row_mixedBottom_of_finrank_eq` needs for the wrapper's `hD`. `hbot1` is discharged as the excluded-middle TAUTOLOGY (`x ≠ v ∨ x = v`); `hbot2` from `hbot2_all`; `hrank` via `finrank_span_eq_card` of the LI selection. `[Finite β]` (edge index finite), NOT `[Fintype α]` (unused — the bridge is column-blind).

### (4.60.B) THE `e_a`-ROW OBSTRUCTION — the concrete BOT-1 instantiation needs a RESTRICTED-edge variant (clause ii FLAG-DON'T-FORCE; clause iii traced to ground).
The coordinator's flagged subtlety RESOLVES as a genuine obstruction to instantiating `span_range_hingeRow_crossFramework_eq_rigidityRows` (BOT-1) over the FULL `E(F₁)` family. Traced to ground:
- BOT-1's `hlink₁ : ∀ e, F₂.graph.IsLink (remap e).1 (ends₁ e.1).1 (ends₁ e.1).2`. The candidate `ends₁` carries the `a`-shift: `ends₁ e = (if (ends e).1 = v then a else (ends e).1, (ends e).2)`.
- For `e = e_a` (`ends e_a = (v, a)`): the shift gives `ends₁ e_a = (a, a)`. So `hlink₁` at `e_a` demands `Gab.IsLink (remap e_a) a a` — a self-loop, **FALSE** in the loopless `Gab` for every choice of `remap e_a`. So BOT-1 is NOT instantiable as-stated over the full `E(G)` family.
- WHY THE BRIDGE IS STILL FINE: `e_a`'s `a`-shifted row `hingeRow a a r = r (S a − S a) = r 0 = 0` is the ZERO functional, so dropping the `e_a`-rows leaves `span (range wfun_FULL) = span (range wfun_restricted)` unchanged. The bridge's `hspan_id` (over the full `p`) is thus EQUIVALENT to the restricted spanning identity (over `Gv`-edges + `e_b` only). The basis-pick never selects a zero row, so the produced `re` lands on genuine `Gv`/`e_b`-fill rows automatically.
- `card m₂ = D·(|V(Gv)|−1) = D·(|V(Gab)|−1) = finrank (span R(Gab).rigidityRows)` (`vertexSet_splitOff` = `rfl`, def-0) holds exactly as §(4.57.C). The bottom edges sit at the `Gv`/`R(Gab)` level (not G's `e_a` corner — `e_a` ∈ `m₁`).

### (4.60.C) THE EXACT RESIDUAL (the only un-built item-1 piece).
Discharge `hspan_id` for the bridge (i.e. instantiate BOT-1 concretely). TWO routes, both leaf-level, neither touching the cert / motive / IH / frozen C.0–C.6 / wrapper signature:
- **Route (R1) — a RESTRICTED-edge BOT-1 variant.** Re-state `span_range_hingeRow_crossFramework_eq_rigidityRows` over a SUBSET of `E(F₁)` (the `Gv`-edges + `e_b`, excluding `e_a`), so `remap`/`hspan`/`hlink₁` are quantified only over edges with a genuine `Gab`-image. Then the full-family `hspan_id` follows from this + the zero-`e_a`-row drop (`span_range_eq_of_subset_of_zero`-style: adding zero vectors to a spanning family preserves the span). Needs: a small new `Basic.lean` lemma (restricted-index cross-framework span), then the zero-row span lemma.
- **Route (R2) — full-family with a harmless `e_a`-image, accepting the `hlink₁` cannot hold.** REJECTED: `hlink₁` is a hard hypothesis of BOT-1 as landed; no `remap e_a` satisfies it. Would require WEAKENING BOT-1's `hlink₁` to "links OR the row is zero" — a BOT-1 signature edit, more invasive than R1.
RECOMMEND **R1**. The concrete data at the dispatch (where `Q`/`Gab = G.splitOff v a b e₀`/`e₀`/`q` are bound after `obtain ⟨Q, …⟩ := hsplitGP`, `Realization.lean:302`): `remap` = `Gv`-edge↦itself, `e_b`↦`e₀`; `hspan` from the cross-label support match `hingeRow_mem_rigidityRows_of_supportExtensor_eq` (block depends only on the support extensor — `ofNormals · ends q`'s supportExtensor reads ONLY `ends`/`q`, `PanelHinge.lean:95`) + `caseIIICandidate_supportExtensor_reproduced` at `t=0` for the `e_b→e₀` slot; `hlink₁` from `Q.ends` recording `Gab`-links (swap-robust). `hbot2_all` from `hsplitG`/`hends` (G's edges record `v` first, never second — degree-2 split body). This is the dispatch-level assembly the whole CHAIN layer has deferred "to the wrapper"; it needs the bound `Q`/`Gab`/`e₀`, so it is NOT a clean standalone lemma — it lands inside the dispatch (item 4) with R1's restricted BOT-1 as its only new brick.

**Consequence for the build.** Next concrete commit = **R1** (the restricted-edge cross-framework BOT-1 variant in `Basic.lean` + the zero-`e_a`-row span-drop) — the only remaining bottom-sub-arc brick before the wrapper's `hD` is fully fed. Then BOT-4 (`Sum.elim` + HMEQ), HA's `hAeq`, the dispatch wires `case_III_arm_realization_rowOp` (consuming `bottom_selection_of_crossFramework_span` + R1 for `hspan_id`), item 3c, item 4 / CHAIN-5. BOT-1 + BOT-2 + BOT-3′ done.

**R1 LANDED (axiom-clean, full build/lint green, zero-regression).** Route R1 chosen. The restricted variant + the zero-`e_a` drop fold into ONE lemma `BodyHingeFramework.span_range_hingeRow_crossFramework_eq_rigidityRows_of_off` (`Basic.lean`, after BOT-1): the cross-framework matching (`remap` surjective / `hspan` / `hlink₁`) is quantified over the genuine `{e // P e}`, and a separate `hoff : ∀ e, ¬P e → ∀ i, hingeRow (ends₁ e).1 (ends₁ e).2 (B e i) = 0` discharges the corner `e_a` row to zero (so the FULL `E(F₁)×ι` family spans `span F₂.rigidityRows`). The `≤` branch splits on `P` (P-row → `F₂` via `hlink₁`+`hspan`; off-P → `0` via `hoff`); `≥` is BOT-1's section transfer over the `P`-subtype. Plus `hingeRow_self` (`@[simp]`, `hingeRow a a r = 0`). A compile-checked spike confirmed R1 produces the bridge's `hspan_id` shape directly (`ends₁ := if (ends e).1 = v then a else …`, `B := blockBasisOn`), then was removed — the concrete `remap`/`hspan`/`hlink₁`/`hoff` land at the dispatch (item 4). Next = BOT-4 + HMEQ.

## (4.61) THE `(e_b, j₀)` JOINT-SATISFIABILITY TENSION — VERDICT: the collision is **REAL** (Q1 = YES); the fix is route **(a) EXCLUSION-STEERING** (route (c) "drop injectivity" REJECTED at the B1/B2 API; route (b) "steer `j₀`" does not escape it). It **partly CONTRADICTS §(4.58)'s "free pick, no steering"** — the bottom pick must AVOID the single index `(e_b, j₀)` and carries a redundancy hypothesis `hred`, which is the SAME fact as HB (`B = L₀·D`), grounded in the W6b redundancy but a genuinely STRONGER instantiation than §(4.58.A)'s `hingeRow a b ρ₀ ∈ span R(Gv)`. The wrapper-firing feasibility pass found the 7 carried hyps JOINTLY dischargeable, the `hM'eq` `D`-block consistent, and NO unsatisfiable hyp. BANKED: the carrier-agnostic exclusion-steered engine `exists_finCard_linearIndependent_selection_avoiding` (`Rank.lean`, axiom-clean). (Session under `/coordinate-phase`, kernel-checked; scratch reverted, tree clean; full build/lint green, zero-regression.)

**Method.** Read the LANDED source for every object: the corner half (`cornerRowInjection`/`_injective`/`finScrewDimSplitCorner`, `Concrete.lean:1063`–1095), the BOT-2 bridge (`bottom_selection_of_crossFramework_span` `Concrete.lean:1830` + the engine `exists_finCard_linearIndependent_selection` `Rank.lean:88`), the wrapper (`case_III_arm_realization_rowOp` `ForkedArm.lean:315`), the cert (`case_III_rank_certification_zero₁₂` `Candidate.lean:2446`), the mixedBottom bricks (`submatrix_columnOp_toBlocks₂₂_eq_mixedBottom` `:1633` / `rank_columnOp_toBlocks₂₂_eq_finrank_span_mixedBottom` `:1691` / `linearIndependent_toBlocks₂₂_row_mixedBottom_of_finrank_eq` `:1783`), the entry bricks (`…_apply_corner` `:1412` / `…_apply_eB_off_pin` `:1568` / `…_apply_pin_zero` `:1380`), the OPERATED-corner gate (`corner_hA'_of_gate` `:620` / `corner_hA_zero₁₂_of_gate` `:657`), the W6b producer (`exists_candidateRow_bottomRows_of_rigidOn` `Candidate.lean:401`; `chainData_split_w6b_gates` `Realization.lean:771`–835), `B1`/`B2` (`exists_rowOp_of_strictInjection` `Rank.lean:747`, `rowOp_strictInjection_submatrix_eq_fromBlocks_zero₁₂` `:811`), the discriminator (`exists_shared_redundancy_and_matched_candidate` `Realization.lean:1416`–1486), and the dispatch shape (`chainData_arm_realization_sep` `Realization.lean:1226`). Four scratch probes (deleted, tree clean): (P1) confirmed the `Sum.elim` `hdisj` is NOT derivable from the BOT-2 bridge's outputs (stuck at `sorry`); (P2) compiled the abstract route-(a) span-equality grounding; (P3) compiled the full exclusion-steered engine `exists_finCard_LI_selection_avoiding`; (P4) `#print axioms` on the banked engine. One brick BANKED.

### (4.61.A) Q1 — THE COLLISION IS REAL AND PICKABLE (clause i, traced to ground).
The full `re : m₁ ⊕ m₂ → p`, `p = {e // e ∈ E(candidate)} × Fin (D−1)`, has corner `re ∘ Sum.inl = cornerRowInjection e_a e_b j₀ ∘ finScrewDimSplitCorner` (the `D−1` panel slots `(e_a, j)` + the ONE `±r` slot `(e_b, j₀)`, `Concrete.lean:1076`–1079 read off `rfl`) and bottom `re ∘ Sum.inr` = the BOT-2 free pick `sel ∘ em` over the FULL `p` (`bottom_selection_of_crossFramework_span`, `Concrete.lean:1859`–1861 — `sel` from `exists_finCard_linearIndependent_selection`, NO range control). The index `(e_b, j₀)` is in `p` and in the bottom family's range. Its a-shifted `χ`-value is `hingeRow a b (blockBasisOn e_b j₀)` (since `(ends e_b).1 = v`, the `if … then a` branch, `_apply_eB_off_pin`) — a NONZERO row of `R(Gab)`'s `(a,b)`-fill block `hingeRowBlock e₀`, hence pickable by a free LI selection. (The `(e_a, j)` corner slots are safe: `e_a`'s a-shift is `hingeRow a a = 0` `hingeRow_self`, never selected.) **So the free pick CAN select `(e_b, j₀)`** — kernel-confirmed by P1: `hdisj : ∀ i, re i ≠ (e_b, j₀)` is NOT derivable from `(hbot2, hbot1, hrank)` (the bridge's outputs), it sits at `sorry`. **Q1 = YES.** §(4.57.D)/PROBE-B's `hdisj` (cross-disjointness) was ASSUMED, never produced; §(4.56)'s RE note "`e_b` reused at DISTINCT `Fin(D−1)` second-coords" is exactly the un-grounded assumption.

### (4.61.B) Q2 — THE FIX IS ROUTE (a); routes (c) and (b) are REJECTED (clause ii, FLAG-DON'T-FORCE; against landed API).
- **Route (c) "the corner and bottom `(e_b, j₀)` rows are the SAME / one is zero/dependent, so injectivity is unneeded" — REJECTED.** The corner `±r` row (un-op'd) reads `blockBasisOn e_b j₀` at the PIN columns (`A`-block, `_apply_corner`); the bottom `(e_b, j₀)` row reads `hingeRow a b (blockBasisOn e_b j₀)` at the OFF-`v` columns (`D`-block, `_apply_eB_off_pin`). Different functionals, different blocks — but `re` injectivity is about the INDEX, and B1/B2 GENUINELY need it: `exists_rowOp_of_strictInjection` (`Rank.lean:747`, `(hre : Function.Injective re)`) builds the extended equiv `e' := (Equiv.ofInjective re hre).sumCongr …` (`:763`) and `hreEq : e'.symm (re x) = Sum.inl x` (`:766`) — both load-bearing; `rowOp_strictInjection_submatrix_eq_fromBlocks_zero₁₂` (`:811`) takes `hre` too. A non-injective `re` makes `e'`/`hreEq` false. So `re` MUST be injective.
- **Route (b) "choose `j₀`/the corner coord so it never coincides with a bottom-selected `e_b`-fill coord" — REJECTED as insufficient.** `j₀` and the bottom pick are BOTH free over `Fin(D−1)`; with no coupling they can collide for every `j₀`. Steering `j₀` alone does not remove the obligation; it folds into route (a)'s `hred`.
- **Route (a) "EXCLUSION-STEER the bottom pick to avoid `(e_b, j₀)`, with the redundancy `hred`" — the FIX.** Run the bottom selection over `{p // p ≠ (e_b, j₀)}`; the produced `re ∘ Sum.inr` then lands off `(e_b, j₀)` by construction, and `Function.Injective.sumElim`'s `hdisj` holds (corner range `{(e_a,j)} ∪ {(e_b,j₀)}` vs bottom range ⊆ `p ∖ {(e_b,j₀)}`, disjoint since `e_a ∉` bottom-nonzero and `(e_b,j₀) ∉` bottom by construction). The restricted family still spans iff `hred : χ(e_b,j₀) ∈ span (range (χ over {p ≠ (e_b,j₀)}))`. **Kernel-checked (P2/P3, compiled sorry-free):** given `hred`, the restricted family's span = the full family's span (`le_antisymm` + add-back-the-redundant-row), so its finrank is still `card m₂` and a FREE LI `card m₂`-selection avoiding `(e_b,j₀)` exists. BANKED as `exists_finCard_linearIndependent_selection_avoiding`.

### (4.61.C) THE CONTRADICTION WITH §(4.58), STATED PRECISELY (clause ii — this is a FINDING, not a failure).
§(4.58.E)/§(4.60)'s BOT-2 verdict was "a FREE maximal-rank pick — the cleanest form, NO steering (route (a)'s constraint is gone)". **That is now PARTLY OVERTURNED:** the pick is NOT free — it must avoid the single index `(e_b, j₀)`, which is a (mild) EXCLUSION-steering. The §(4.58) sense of "route (a) refuted" was about a DIFFERENT route (a) (steer the pick to CONTAIN the `cGv`-support to seed `LinearIndependent.extend`), correctly refuted because the `cGv`-summands are not stated-LI. This §(4.61) route (a) is the OPPOSITE — EXCLUDE one index — and is feasible because the excluded row is REDUNDANT, not because a seed is LI. So §(4.58.A)'s refutation stands for its own route; §(4.61)'s exclusion is a new, distinct mild steering that the §(4.58.D)/§(4.60.A) "free pick" framing did not anticipate. The landed `bottom_selection_of_crossFramework_span` (the free-pick bridge) therefore **does need an exclusion-parameter sibling** (BOT-2′ below); the landed engine `exists_finCard_linearIndependent_selection` stays correct (the avoiding-engine is a new sibling, not an edit).

### (4.61.D) `hred` IS THE SAME FACT AS HB — and that GROUNDS it without new geometry (clause iii, traced to ground).
The decisive reconciliation: `hred` (the bottom-avoiding family spans, i.e. `hingeRow a b (blockBasisOn e_b j₀) ∈ span(bottom rows)`) is **literally HB** (`hB : B = L₀ · D` — the off-`v` `±r` row `B`-row factors through the bottom `D`-rows). The row op `Lrow` subtracts `L₀·(bottom)` from the corner `±r` row: the off-`v` part zeroes (`B − L₀D = 0`, HB) and the pin part reads `ρ₀` (HA, `corner_hA_zero₁₂_of_gate`). The off-`v` zeroing SAYS `hingeRow a b (blockBasisOn e_b j₀) = L₀ · (bottom D-rows) ∈ span(bottom)` = `hred`. So HB and the exclusion-redundancy are ONE obligation, discharged together. **Grounding (clause iii):** the `(a,b)`-fill block `hingeRowBlock e₀` is `(D−1)`-dim and is covered in the candidate's a-shifted family ONLY by `e_b`'s `D−1` rows `{hingeRow a b (blockBasisOn e_b j)}` (no other edge maps to `e₀`'s block: `Gv`-edges → themselves, `e_a` → 0). The W6b producer gives `hingeRow a b ρ₀ ∈ span R(Gv)` (`Realization.lean:802`–803) with `ρ₀ = ∑ lamAB j • rab j`, `rab j ∈ hingeRowBlock e₀` (`:1454`–1456) — so the `(a,b)`-block has a `1`-dim dependency mod `span R(Gv)` (rank `D−2` of its `D−1` rows; consistent with the W6b bound `D·(|V(Gab)|−1) − (D−2) ≤ finrank(span R(Gv))`, `Candidate.lean:412`–414). `hred` for the LITERAL `(e_b, j₀)` then holds iff that `1`-dim dependency genuinely involves the `j₀`-coordinate (the dependency's `j₀`-coefficient is nonzero) — i.e. the corner's `±r` index `j₀` lands in the redundancy's support. This is the STRONGER instantiation: §(4.58.A) gives `hingeRow a b ρ₀ ∈ span R(Gv)` (the redundancy DIRECTION); §(4.61) needs `hingeRow a b (blockBasisOn e_b j₀) ∈ span R(Gv) + (other e_b rows)` (the literal INDEX-`j₀` row). The clean discharge: the dispatch picks `j₀` so that the `±r` slot's reproduced row, under the op, IS `ρ₀` — i.e. couple the corner-injection's `j₀` to the redundancy support (the `lamAB`/`rab` data the discriminator already produces). NOT a new geometric lemma — a re-keying of the SAME W6b `cGv`/`lamAB` data already feeding HB.

### (4.61.E) THE WRAPPER-FIRING FEASIBILITY PASS — 7 hyps JOINTLY dischargeable; `hM'eq`'s `D` IS HB/HA/HD's `D`; NO unsatisfiable hyp (the SECONDARY PASS).
The wrapper `case_III_arm_realization_rowOp` carries `(re, hre, L₀, hM'eq, hB, hA, hD)` (plus `hgp`/`hends`/the chain link data). Read against the landed wrapper body (`ForkedArm.lean:365`–395):
- **`hM'eq` block-read consistency (the flagged question) — CONFIRMED.** The wrapper binds ONE `D : Matrix m₂ ({body ≠ v} × Fin D) ℝ` (`:349`); `hM'eq : (M*U).submatrix re en = fromBlocks A B C D` (`:350`–356) instantiates `A`/`B`/`C`/`D` as the four `toBlocks` (the dispatch supplies it via `(fromBlocks_toBlocks _).symm`, HMEQ), and the SAME `D` feeds `hB : B = L₀*D` (`:358`), `hD : LinearIndependent ℝ D.row` (`:362`), and the cert call `(D := D)` (`:388`). So HB/HA/HD's `D` IS the mixedBottom `toBlocks₂₂` the bridge produces `re` for — `D = (M*U).submatrix re en |>.toBlocks₂₂`, exactly `linearIndependent_toBlocks₂₂_row_mixedBottom_of_finrank_eq`'s subject. NO mismatch.
- **The 7 hyps, jointly dischargeable for the REAL interior arm** (`v=vtx i.castSucc, a=vtx i.succ, b=vtx (i−1).castSucc, e_a=edge i, e_b=edge (i−1)`, the `chainData_arm_realization_sep` tuple `Realization.lean:1274`–1278), from the landed bricks: `re` = BOT-4 `Sum.elim (cornerRowInjection ∘ finScrewDimSplitCorner) (BOT-2′ bottom)`; `hre` = `Function.Injective.sumElim (cornerRowInjection_injective heab j₀).comp …` + `hdisj` (from BOT-2′'s avoiding conclusion); `L₀` = the `cGv`/`lamAB`-weights (BOT-3′); `hM'eq` = HMEQ; `hB` = BOT-3′ `matrix_eq_mul_of_span_mem` fed each `B`-row's `span(D)`-membership (= `hred`); `hA` = leaf (iii) `corner_hA_zero₁₂_of_gate` + the entrywise `hAeq` + gate `hρe₀`; `hD` = `linearIndependent_toBlocks₂₂_row_mixedBottom_of_finrank_eq` + BOT-2′'s `hrank`. **NO hyp is unsatisfiable** — the one that LOOKED like a trap (`hdisj`, P1) is dischargeable once BOT-2 carries the exclusion (BOT-2′), and that exclusion's `hred` IS HB (already owed, §(4.58.D)), so the net new content is the exclusion plumbing, not a new geometric obstruction.

### (4.61.F) THE EXACT NEXT-LEAF DECOMPOSITION (the re-scoped bottom sub-arc tail).
- **BOT-2′ (NEW, owed) — the exclusion-steered candidate bridge.** `bottom_selection_of_crossFramework_span_avoiding` (`Concrete.lean`, next to BOT-2): same as `bottom_selection_of_crossFramework_span` but takes an excluded index `p₀ : {e // e ∈ E(F.graph)} × Fin (D−1)` + a redundancy hypothesis `hred : χ p₀ ∈ span (range (χ over {p // p ≠ p₀}))`, runs the BANKED `exists_finCard_linearIndependent_selection_avoiding` over the subtype, and produces `(re, hbot2, hbot1, hrank)` PLUS `havoid : ∀ i, re i ≠ p₀`. Near-mechanical mirror of BOT-2; the banked engine does the rank work. (The free BOT-2 stays in tree for any consumer that does not need exclusion.)
- **BOT-4 (UNCHANGED, next) — `Sum.elim` + `hre` + HMEQ.** `re := Sum.elim (cornerRowInjection e_a e_b j₀ ∘ finScrewDimSplitCorner) bottom`; `hre` via `Function.Injective.sumElim ((cornerRowInjection_injective heab j₀).comp finScrewDimSplitCorner.injective) hbotinj hdisj`, where `hdisj` is built from BOT-2′'s `havoid` (the `(e_b,j₀)` slot) + the `(e_a,·)` panel disjointness (bottom rows are nonzero ⟹ not `e_a`; `e_a ≠ e_b`); `hM'eq` via `(fromBlocks_toBlocks _).symm`.
- **HA's `hAeq` (UNCHANGED) — the entrywise operated-corner read.** Compose `_apply_corner` (the `e_a`-panel + `±r` pin reads) with `Lrow`'s `cGv`-subtraction to get the operated `±r` row = `ρ₀`; feed `corner_hA_zero₁₂_of_gate` with `em₁ := finScrewDimSplitCorner` + the gate `hρe₀` (from the discriminator `:1470`).
- **The dispatch (item 4) — discharges `hred`/`havoid`'s coupling.** Where `Q`/`Gab`/`e₀`/`q`/`ρ₀`/`j₀`/`cGv`/`lamAB` are bound (off `exists_shared_redundancy_and_matched_candidate` + `chainData_split_w6b_gates`), instantiate BOT-2′'s `hred` from `hingeRow a b ρ₀ ∈ span R(Gv)` + the `j₀`↔redundancy-support coupling (pick `j₀` in the redundancy support, or carry the row-op identity that makes the `(e_b,j₀)` row factor through the bottom). This is the SAME W6b `cGv`/`lamAB` data feeding HB (§(4.61.D)); the dispatch already obtains it. Then `case_III_arm_realization_rowOp` fires.
- Then item 3c (gate bridge), item 4 / CHAIN-5.

**THREE DESIGN-PASS CLAUSES — verdicts.**
- **(i) verified against LANDED source.** Every object read at the cited line; `re` injectivity's B1/B2 dependence, the operated-corner `ρ₀` read, the single-`D` `(hM'eq,hB,hD)` binding, the W6b `ρ₀`/`cGv`/`lamAB` conclusion, and the `(a,b)`-block-covered-only-by-`e_b` fact all confirmed in source, not from §(4.5x) prose. P1 kernel-confirmed the `hdisj` gap; P2/P3 compiled route (a)'s engine sorry-free; P4 confirmed it axiom-clean.
- **(ii) FLAG-DON'T-FORCE.** The `(e_b,j₀)` collision FORCES a BOT-2 sibling (BOT-2′, an exclusion parameter + `hred`) — FLAGGED precisely. It **partly contradicts §(4.58)'s "free pick, no steering"** (a FINDING, recorded in §(4.61.C), not a failure). It does NOT touch the cert / motive / IH / frozen C.0–C.6 / the wrapper signature (the wrapper already carries `hre`/`hB`; BOT-2′ feeds them). No hyp is unsatisfiable.
- **(iii) traced to GROUND.** The `(a,b)`-block is `(D−1)`-dim, covered only by `e_b`'s `D−1` a-shifted rows; the W6b dependency is `1`-dim mod `span R(Gv)` (the `D·(|V(Gab)|−1) − (D−2) ≤ finrank(span R(Gv))` bound). The family-minus-`(e_b,j₀)` reaches finrank `card m₂` iff `hred` (the `j₀`-row is in that dependency / `span(others)`) — proven equivalent to HB, grounded in W6b, NOT asserted.

**Consequence for the build (re-pointed).** Next concrete commit = **BOT-2′** (the exclusion-steered candidate bridge `bottom_selection_of_crossFramework_span_avoiding`, off the BANKED engine `exists_finCard_linearIndependent_selection_avoiding`), then **BOT-4** (`Sum.elim` + `hre` via `hdisj` from BOT-2′'s `havoid` + HMEQ), HA's `hAeq`, the dispatch (which discharges `hred` from the W6b `ρ₀`/`cGv` + the `j₀`↔redundancy coupling), item 3c, item 4 / CHAIN-5. **BANKED this commit:** `exists_finCard_linearIndependent_selection_avoiding` (`Rank.lean`, axiom-clean, the route-(a) rank engine).

## (4.62) THE `C = 0` HA ROUTE IS INVALID — VERDICT: `C = toBlocks₂₁ ≠ 0` for the Case-III arm; `hbot` (both bottom endpoints ≠ v) is UNSATISFIABLE for the consumer; the designed `ρ₀`-route (leaf (iii) `corner_hA_zero₁₂_of_gate` + the entrywise `hAeq`) is the REAL HA. Settles the recon question on commit d5a2e1d's "simpler HA / `ρ₀` over-engineered / `C=0`" prose — it is **FALSE**. Compiler-checked (4-part scratch spike, sorry-free, deleted before commit; tree clean).

**The error.** Commit d5a2e1d's HA leaf `linearIndependent_toBlocks₁₁_sub_mul_toBlocks₂₁_row_of_corner_gate` (`Concrete.lean`) discharges the wrapper's `hA : LinearIndependent ℝ (A − L₀*C).row` by proving `C = toBlocks₂₁ = 0`, via the carried hyp `hbot : ∀ i : m₂, v ≠ (ends (re (Sum.inr i)).1.1).1 ∧ v ≠ (ends (re (Sum.inr i)).1.1).2` (BOTH bottom endpoints ≠ v) fed to `…_submatrix_toBlocks₂₁_eq_zero` / `…_apply_pin_zero`. The prose claimed "the row op leaves the corner un-mutated since `C=0`". This is wrong because **`hbot` is unsatisfiable at the dispatch.**

**Q1 — `hbot` UNSATISFIABLE / `C ≠ 0` (compiler-checked, sorry-free).** The wrapper `case_III_arm_realization_rowOp` (`ForkedArm.lean:315`) binds ONE `re`, ONE `D`, and feeds the SAME `re` to BOTH `hA` and `hD`. The only landed `hD` producer is `linearIndependent_toBlocks₂₂_row_mixedBottom_of_finrank_eq` (`Concrete.lean:1825`), which needs `hrank : finrank (span (a-shifted bottom family)) = card m₂`, with the a-shift `if (ends …).1 = v then a else …` (the mixedBottom, which TOLERATES first-endpoint = v, the `e_b` family — `hbot2`/`hbot1`, NOT `hbot`). Spike chain:
- (part 1) Under `hbot`, the a-shift `if` is ALWAYS the `else` branch (`if_neg`), so the bottom family is the UN-shifted `hingeRow ((ends …).1) ((ends …).2) (blockBasisOn …)` — the `e₀=(a,b)` fill never appears.
- (part 3) `hbot` FORCES every bottom edge to be a genuine `Gv`-edge: the candidate is on `E(G)`, `hsplitG` (`ForkedArm.lean:324`) sends each `G`-edge to `e_a ∨ e_b ∨ Gv`, and both `e_a`/`e_b` are v-incident (`hG_ea : G.IsLink e_a v a`, `hG_eb : G.IsLink e_b v b`), so `IsLink.left_eq_or_eq` + `hbot` (both endpoints ≠ v) rules them out. Bottom rows ⊆ `span R(Gv)`.
- (part 2) `Gv = G − v` is genuinely deficient (`removeVertex_deficiency_ge`: `def(G̃ᵥ) ≥ def(G̃) = 0`, and §(4.61.D)'s "1-dim dependency mod span R(Gv)"), so `finrank (span R(Gv)) < card m₂`. The bottom then spans `≤ finrank R(Gv) < card m₂` (`Submodule.finrank_mono`), CONTRADICTING `hrank = card m₂` (`omega`).
- (part 4) Since the bottom MUST include `e_b` rows to reach `card m₂` (the `e₀=(a,b)` block is covered ONLY by `e_b`'s a-shifted rows, §(4.61.D)), and `e_b` is v-incident (first endpoint v), the pin entry reads `(blockBasisOn …) (finScrewBasis k c) ≠ 0` (`…_apply_corner`, the FIRST-endpoint-= v case, NOT `…_apply_pin_zero`) — so `C = toBlocks₂₁ ≠ 0` entrywise.

So HA-via-`C=0` and HD-via-mixedBottom demand CONTRADICTORY bottoms for the same `re`: HA wants no v-incident bottom row, HD's `hrank` forces v-incident `e_b` rows in. **`C ≠ 0`; the C=0 HA leaf can NEVER discharge the wrapper's `hA` at the dispatch.** (The HA leaf is sorry-free *in isolation* — it correctly proves `hbot → C=0 → hA` — but its `hbot` premise is never derivable for the consumer, so it is DEAD: no real special-case consumer, unlike leaves (ii)/(iv) which serve the isostatic-tight bijection case.)

**Q2 — the designed `ρ₀`-route is the correct HA (CONFIRMED).** Leaf (iii) `corner_hA_zero₁₂_of_gate` (`Concrete.lean:657`, KEPT) handles `C ≠ 0` correctly: the row op `Lrow` subtracts `L₀·(bottom D-rows)` from the corner's `±r` row. The operated `±r` row reads, off the pin, `B − L₀D = 0` (HB) and, AT the pin, `ρ₀ = (corner `e_b` `±r` pin read `blockBasisOn(e_b,j₀)`) − L₀·(C-pin reads)` (KT (6.66)'s redundancy). So the operated corner's `m₁` rows are the `D`-member family `[blockBasisOn(e_a,·); ρ₀]` (NOT all-`blockBasisOn`), and leaf (iii) reads them as the `coordEquiv`-coordinate matrix and closes via `corner_hA'_of_gate` (the `[blockBasisOn(e_a); ρ₀]` family is LI iff the gate `hρe₀ : ρ₀ (supportExtensor e_a) ≠ 0`). Leaf (iii)'s `hAeq` shape — operated corner = coordinate matrix of `[blockBasisOn(e_a,·); ρ₀]` reindexed by `em₁ := finScrewDimSplitCorner` — is dischargeable for the arm: compose `…_apply_corner` (the `e_a`-panel + `e_b` `±r` pin reads) with `Lrow`'s `cGv`-subtraction (the SAME `L₀` weights HB uses), feeding `em₁ := finScrewDimSplitCorner` + the gate `hρe₀` from the discriminator (`Realization.lean:1470`). This is exactly §(4.61.D)'s "the off-`v` zeroing IS HB, the pin part IS HA(`ρ₀`)" — HA and HB share ONE row op, ONE `L₀`.

**Q3 — `C=0` is NOT achievable (route REJECTED, design change would be required).** Re-steering BOT-2′ to avoid ALL `e_b` rows (not just `(e_b,j₀)`) would make the bottom pure-`Gv`-rows, which by part 2/part 3 span only `< card m₂` — so `hD`'s `hrank` becomes UNREACHABLE. The `(D−2)`-many `e₀=(a,b)` fill rows are MANDATORY in the bottom and are realized (in the candidate, on `E(G)`) as v-incident `e_b` rows. There is no way to keep `card m₂` rank while excluding them. So `C=0` is genuinely unavailable for the arm; the cert's `_zero₁₂` shape (which zeros the UPPER-right `B`, leaving `C` free/nonzero) is precisely what the arm needs.

**Corrective action (this commit).** REMOVE `linearIndependent_toBlocks₁₁_sub_mul_toBlocks₂₁_row_of_corner_gate` (dead — `hbot` never holds for the arm). Revert `Phase23f.md`'s "HA done / `ρ₀` over-engineered / `C=0`" prose; re-point *Current state* + *Hand-off* so **HA is OWED via the `ρ₀`-route** (leaf (iii) + the entrywise `hAeq`) as the next real HA build. Keep the correct supporting bricks (`…_submatrix_toBlocks₂₁_eq_zero` etc. — they serve the genuine Gv-only `toBlocks₂₁=0` reduction where every bottom row IS off-`v`; that is the un-operated `_matrix` cert's lower-left-zero, a DIFFERENT, valid use). Leaf (iii) + `corner_hA'_of_gate` + the gate `exists_corner_blockBasisOn_linearIndependent` stay.

**THREE DESIGN-PASS CLAUSES — verdicts.**
- **(i) verified against LANDED source.** The wrapper's single-`re`/single-`D` binding (`ForkedArm.lean:341`/`349`/`360`/`362`), the HA leaf's `hbot` (`Concrete.lean:2267`), the HD producer's mixedBottom `hbot2`/`hbot1` + `hrank` (`:1831`–1838), `…_apply_corner` (FIRST-endpoint-= v nonzero pin read, `:1454`) vs `…_apply_pin_zero` (both-≠ v zero, `:1422`), `hsplitG`/`hG_ea`/`hG_eb` (`ForkedArm.lean:321`/`324`), and leaf (iii)'s `hAeq` (`:657`) all read at source. The 4-part spike compiled sorry-free against `Concrete.lean`'s landed API.
- **(ii) FLAG-DON'T-FORCE.** No motive/contract/wrapper-signature change is needed: the wrapper already carries `hA` as a hypothesis and already fires `case_III_rank_certification_zero₁₂` (which leaves `C` free) — only the *discharger* of `hA` was mis-chosen. The fix is local (swap the C=0 leaf for leaf (iii)). The d5a2e1d prose's claim that the `ρ₀`-route was "over-engineered" is the inversion of the truth and is FLAGGED as the propagated error.
- **(iii) traced to GROUND.** `card m₂ = D·(|V(Gv)|−1)`; `R(Gv)` deficient (`removeVertex_deficiency_ge`, def-≥); the `e₀=(a,b)` block `(D−1)`-dim, covered only by `e_b`'s a-shifted rows; `e_b` v-incident (`hends_eb = (v,b)`). The contradiction is sharp at the general-`d` interior arm `D = screwDim k ≥ 3` (the `d=3` floor `D=2` uses the separate `_matrix`/M₃ path per the frozen cert FORK, where `D−2=0` and the argument is vacuous — but that path does not use this arm).

## (4.63) HD LANDED axiom-clean — the wrapper's `hD` is a thin defeq restatement of the mixed-bottom producer over the `Sum.elim`-`re`. (Session under `/coordinate-phase`; full build/lint green, zero-regression.)

`linearIndependent_toBlocks₂₂_row_sumElim_mixedBottom_of_finrank_eq` (`Concrete.lean`, right after BOT-2′) is the wrapper's `hD : LinearIndependent ℝ D.row` for the full strict row injection `re = Sum.elim (cornerRowInjection e_a e_b j₀ ∘ finScrewDimSplitCorner) bottom` (**BOT-4**). It is a ONE-line restatement of the §(4.57.A)/§(4.59) HD producer `linearIndependent_toBlocks₂₂_row_mixedBottom_of_finrank_eq` instantiated at `m₁ := Fin (screwDim k)` and that `re`: the `Sum.elim` makes `re (Sum.inr i) = bottom i` **definitional**, so the producer's per-`Sum.inr` `hbot2`/`hbot1`/`hrank` ARE BOT-2′'s bottom-only outputs verbatim (no rewrite/`simp`/coercion). Confirms §(4.57.A)'s "HD is `w`-free, a basis-pick from full-rank `R(Gab)`" end-to-end at the wrapper's `re` shape: the dispatch obtains `bottom`/`hbot2`/`hbot1`/`hrank` from BOT-2′ and feeds `hrank`'s `card m₂ = D·(|V(Gab)|−1)` from the split-off framework's def-`0` full-rank realization (`isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows` off `hsplitGP` / `splitOff_isMinimalKDof`, the C.3 `hIH` add). Only slot subtlety: the edge-subtype-product reads `(bottom i).1.1` (edge for `ends`) / `(bottom i).1.2` (membership proof for `blockBasisOn`) / `(bottom i).2` (the `Fin (D−1)` coord) must copy the producer's reads exactly. Axiom-clean (`propext`/`Classical.choice`/`Quot.sound`). **Owed at the wrapper now reduces to HMEQ + HB + HA** (HD done); the dispatch (item 4) wires them where `Q`/`Gab`/`e₀`/`ρ₀`/`j₀`/`cGv`/`lamAB` are bound.

## (4.64) ITEM-4 DISPATCH DECOMPOSITION + JOINT-SATISFIABILITY VERDICT — Q1 = YES (kernel-confirmed at the CONCRETE binding, ONE shared `?L₀`); the dispatch decomposes into 8 ordered buildable steps; HMEQ + HD now CLOSE at the wrapper-fire with ZERO sorry; CHAIN-5 is separable. Q3: no cert/motive/wrapper-signature change beyond the already-APPROVED C.3 `hIH` add; ONE flagged decision (the `j₀`↔`hred` coupling shape, ADJUDICATED route-(a)-feasible, build-deferred). (Session under `/coordinate-phase`; compiler-checked dispatch-level spike, sorry-fed, deleted before commit; tree clean; full build/lint green, zero-regression.)

The §(4.61) feasibility pass argued joint satisfiability by *route-composition prose* + a 7-hyp checklist. §(4.62)'s C=0 episode showed prose can propagate a JOINTLY-unsatisfiable obligation that "looks dischargeable". So before any more building, this recon **fired `case_III_arm_realization_rowOp` at the concrete `caseIIICandidate G ends q e_a e_b (q(a,·)) n' (q(b,·)) 0` binding in a dispatch-level scratch spike** — instantiating `(re, hre, L₀, hM'eq, hB, hA, hD)` from the named leaves, sharing ONE `re` (BOT-4 over BOT-2′'s `bottom`) and ONE `?L₀` metavariable, `sorry`-ing only the genuinely-open entrywise gaps, and reading the kernel-checked residual goals. The spike **builds** (`Build completed successfully`, only `sorry` + cosmetic long-line/`end` warnings).

### (4.64.A) Q1 — JOINT SATISFIABILITY: YES, with TWO obligations now CLOSING at the fire (stronger than §(4.61)).
The wrapper fired (the structural args `re`/`hre`/`hm₁`/`hm₂` all accepted) and left exactly these kernel-checked residual goals:
- **`hM'eq` CLOSES with `(Matrix.fromBlocks_toBlocks M').symm`** — NO sorry. Setting `M' := (R(F) * Uᵀ).submatrix re (columnSplit v).symm` and `A,B,C,D := M'.toBlocks₁₁/₁₂/₂₁/₂₂` makes HMEQ a pure mathlib `fromBlocks_toBlocks`. So `A/B/C/D` are PINNED to the four `toBlocks` of the operated submatrix — no abstract-`D` decoupling risk (the §(4.58.C) single-`D` concern is fully discharged: `B`/`D` are `M'.toBlocks₁₂`/`M'.toBlocks₂₂` of ONE `M'`).
- **`hD` CLOSES with `exact hD`** — NO sorry. The HD leaf `linearIndependent_toBlocks₂₂_row_sumElim_mixedBottom_of_finrank_eq` (§(4.63)) outputs `LinearIndependent ℝ ((R(F)*Uᵀ).submatrix (Sum.elim (cornerRowInjection …) bottom) (columnSplit v).symm).toBlocks₂₂.row`, which is **DEFEQ** to `M'.toBlocks₂₂.row` (same operated submatrix, `re = Sum.elim …`). `exact hD` closed it with no rewrite/coercion — the §(4.63) defeq claim verified END-TO-END at the wrapper.
- **`hA` residual: `⊢ LinearIndependent ℝ (M'.toBlocks₁₁ − ?L₀ * M'.toBlocks₂₁).row`** (leaf (iii)).
- **`hB` residual: `⊢ M'.toBlocks₁₂ = ?L₀ * M'.toBlocks₂₂`** (BOT-3′).
- **`?L₀` is ONE shared metavariable** across the `hA`/`hB`/`L₀` goals — kernel-confirmed: the `?L₀` in `hA`'s goal is *literally the same metavar* as `hB`'s. So the coordinator's Q1 crux ("the `hAeq` ρ₀-read and the `hmem`/`hred` must hold for the SAME `L₀`") holds by construction — any `L₀` instantiation propagates to both; **no two obligations are jointly contradictory over the shared `re`/`L₀`** (they are coupled through ONE metavar, exactly the row-op semantics). Contrast §(4.62)'s `C=0` failure: there an obligation was unsatisfiable *given* the others; here every residual is a standard leaf application with the binding already consistent.

**Net Q1 result:** at the wrapper-fire the owed obligations REDUCE from §(4.61)'s "7 carried hyps" to: BOT-2′'s 4 inputs (`hspan_id`/`hfr`/`hbot2_all`/`hred`), BOT-4's 2 inputs (bottom-injective, bottom-≠-`e_a`), `hA`'s `hAeq`, `hB`'s `hmem`, and `?L₀`'s definition — **HMEQ + HD are GONE** (closed in the fire). The §(4.61) "the `hM'eq` `D`-block consistent" hope is now a theorem of the fire, not a hope.

### (4.64.B) Q2 — ITEM-4 DECOMPOSED INTO 8 ORDERED BUILDABLE STEPS (exact signatures; standalone-leaf vs inline-dispatch tagged).
All land in `Realization.lean` (where `cd`/`Q`/`Gab = G.splitOff v a b cd.e₀`/`e₀`/`q`/`ρ₀`/`j₀`/`cGv`/`lamAB` are bound off `exists_shared_redundancy_and_matched_candidate` `:1416` + `chainData_split_w6b_gates` `:771`), EXCEPT D2 (a `Concrete.lean` leaf). `F := caseIIICandidate G ends q e_a e_b (q(a,·)) n' (q(b,·)) 0`, `Gv = G.removeVertex v`, `j₀` from the corner injection.

- **D1 (FIRST buildable, standalone leaf, `Realization.lean`) — `interior_hsplitGP`.** From the C.3 `hIH` data produce the interior split-off framework's def-0 full-rank realization. Sig: `(cd : G.ChainData n) (i) (hi : 0 < i) (hG : G.IsMinimalKDof n 0) (hnp : ∀ H, ¬H.IsProperRigidSubgraph G n) (hIH : ∀ G', G'.IsMinimalKDof n 0 → 2 ≤ V(G').ncard → V(G').ncard < V(G).ncard → (G'.Simple → HasGenericFullRankRealization k n G') ∧ …) (hSimple : G.Simple) (hV3 : 3 ≤ V(G).ncard) … : HasGenericFullRankRealization k n (G.splitOff (cd.vtx i.castSucc) (cd.vtx i.succ) (cd.vtx ⟨i−1,_⟩.castSucc) cd.e₀)`. Body **EXACTLY the `:670`–671 precedent for `G.removeVertex v`**, but at the split-off graph `Gab`: `(hIH _ Gab (splitOff_isMinimalKDof …) hGabne hGablt).1 hGabSimple`. The `IsMinimalKDof n 0` input is `splitOff_isMinimalKDof` (`Reduction.lean:161`, takes exactly `hD/hV3/hav/hbv/haV/hbV/hvG/heab/hla/hlb/hdeg2/he₀/hG/hnp`, all read off the `ChainData` accessors as in `chainData_arm_realization_sep:1280`–1287); `hGabne`/`hGablt`/`hGabSimple` from `vertexSet_splitOff` (`V(Gab) = V(G)∖{v}`, so `ncard < |V(G)|`) + `hSimple.mono`. This is the ONE genuinely-new thing the dispatch needs that no prior leaf supplies; it feeds BOT-2′'s `hfr` (D3, via `isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows` `GenericityDevice.lean:532`) AND the discriminator's `hsplitGP` input (D-binding). **NO** wrapper/cert/motive change — it consumes the already-APPROVED C.3 `hIH` add (the same `hIH` shape the Case-III spine already threads).
- **D2 (standalone leaf, `Concrete.lean`) — `hbot_ne_ea` from `hingeRow_self`.** BOT-4's `hbot_ne_ea : ∀ i, (bottom i).1 ≠ ⟨e_a,_⟩`. The `e_a`-row's a-shift is `hingeRow a a = 0` (`hingeRow_self`, `@[simp]`), excluded from any LI pick. Build as a corollary of BOT-2′ carrying `havoid`-style exclusion of `e_a` too, OR (cleaner) re-thread BOT-2′'s `χ`-family to be zero at `e_a` and conclude `bottom` lands only on nonzero rows. Sig: an `∀ i, (bottom i).1 ≠ e_a` companion of `havoid`. (Smallest of the eight; could fold into D3.)
- **D3 (inline dispatch step) — BOT-2′ inputs `hspan_id`/`hfr`/`hbot2_all`/`hred`.** Instantiate `bottom_selection_of_crossFramework_span_avoiding` (`Concrete.lean:1940`) at `F`/`Gv`/`p₀ = (⟨e_b,_⟩, j₀)`. `hspan_id` ← R1 `span_range_hingeRow_crossFramework_eq_rigidityRows_of_off` (`Basic.lean:912`) with `remap = Gv↦itself / e_b↦e₀`, `hspan` from `hingeRow_blockBasisOn_mem_rigidityRows_of_supportExtensor_eq` (`Concrete.lean:701`) + `caseIIICandidate_supportExtensor_reproduced` at `t=0`, `hlink₁` from `Q.ends`, `hoff` from `hingeRow_self` at `e_a`; `hfr` ← D1's `hsplitGP` via `isInfinitesimallyRigidOn…_iff_finrank_span_rigidityRows`; `hbot2_all` ← `hsplitG`/`hends`; **`hred`** ← D4.
- **D4 (inline dispatch step, the ONE flagged decision — `j₀`↔redundancy coupling) — BOT-2′'s `hred`.** `hred : (a-shifted `(e_b,j₀)` row) ∈ span (a-shifted family over {p ≠ p₀})`. From the W6b `cGv`-widening `hingeRow a b ρ₀ = ∑ cGv j • hingeRow (uvGv j) (vvGv j) (rvGv j)` (`exists_shared_redundancy_and_matched_candidate:1461`–1467, the `∃ nGv cGv evGv uvGv vvGv rvGv` block) + `ρ₀ = ∑ lamAB j • rab j`, `rab j ∈ hingeRowBlock e₀` (`:1454`–1456). Discharge route: **pick/couple `j₀` so the `±r` slot's a-shifted row IS the redundancy `ρ₀`-direction** — i.e. the corner injection's `j₀` lands in the `lamAB`/`rab` support (§(4.61.D)'s "couple the corner-injection's `j₀` to the redundancy support"). FLAG: this is the only step whose *shape* is not yet a single named in-tree lemma; the §(4.61) verdict adjudicated it route-(a)-feasible (the excluded row is REDUNDANT, the `cGv`/`lamAB` data is in hand), but the concrete `hred` proof is build-deferred. **NOT** a contract change — it re-keys the SAME W6b data D-binding already holds. Likely a small new `Realization.lean` lemma `interior_hred_of_widening` (the §(4.61.D) re-key).
- **D5 (inline dispatch step) — BOT-4 `re`/`hre`.** `re := Sum.elim (cornerRowInjection ⟨e_a,_⟩ ⟨e_b,_⟩ j₀ ∘ finScrewDimSplitCorner) bottom`; `hre := cornerRowInjection_sumElim_injective (heab-subtype) j₀ bottom (bottom-inj from BOT-2′'s `sel` inj) havoid (D2)`. Pure assembly, no new content (verified in the spike: `hre` accepted modulo the bottom-inj + D2 sorries).
- **D6 (inline dispatch step) — `hB` via BOT-3′.** Goal `M'.toBlocks₁₂ = ?L₀ * M'.toBlocks₂₂`. `matrix_eq_mul_of_span_mem` (`Concrete.lean:2160`) consumes `hmem : ∀ i, (B-row functional) i ∈ span (range (D-row functionals))`; the `hmem` come from R1's spanning identity (= D3's `hspan_id`, giving `span(D-rows) = span R(Gab)`) + each corner-`B`-row ∈ `span R(Gab)` (the off-`v` corner read, `_apply_eB_off_pin`). BOT-3′'s `choose` outputs `?L₀` — **this fixes the shared metavar** (D7 reads the same `?L₀`). Owed: the per-`B`-row `hmem` (each `M'.toBlocks₁₂` row functional ∈ `span(M'.toBlocks₂₂ rows)`), reshaped from R1.
- **D7 (inline dispatch step) — `hA` via leaf (iii).** Goal `LinearIndependent ℝ (M'.toBlocks₁₁ − ?L₀ * M'.toBlocks₂₁).row`. `corner_hA_zero₁₂_of_gate` (`Concrete.lean:657`) with `hρe₀` ← the discriminator gate `ρ₀ (panelSupportExtensor (q(candidateVtx i)) n') ≠ 0` (`:1469`–1470) bridged by `caseIIICandidate_supportExtensor_candidate` (`:960`, `F.supportExtensor e_a = panelSupportExtensor (q(a,·)) n'`) + `candidateVtx_succ_eq` (`Operations.lean:2824`, `rfl`-level `candidateVtx i = vtx i.succ = a`, **NOT** Fin-arithmetic) — confirmed against ground. Owed: the entrywise `hAeq` (operated `M'.toBlocks₁₁ − L₀·M'.toBlocks₂₁` = `coordEquiv` of `[blockBasisOn(e_a,·); ρ₀]` reindexed by `em₁ := finScrewDimSplitCorner`) — compose `rigidityMatrixEdge_mul_columnOp_apply_corner` (`:1454`, the `e_a`-panel + `e_b` `±r` pin reads) with `Lrow`'s `cGv`-subtraction (the SAME `?L₀` D6 fixed). The shared-`?L₀` confirms D6/D7 are ONE row op.
- **D8 (inline dispatch step) — item 3c + the fire.** The candidate-matching gate bridge (D7's `hρe₀` route IS item 3c) + `case_III_arm_realization_rowOp` fired with `(re, hre, ?L₀, hM'eq=(fromBlocks_toBlocks M').symm, hB(D6), hA(D7), hD)`. Verified sorry-free-modulo-D-residuals in the spike. Then the `chainData_dispatch` router wraps base/`d=3`→`chainData_split_realization`, interior→this. **CHAIN-5** (the C.0 lockstep reshape of `hdispatch`/`hcand` to the frozen `ChainData` record + `d=3` zero-regression adapter) is **SEPARABLE** — it is the `ChainData`-record plumbing AROUND a firing dispatch, not part of firing the interior arm; scope it as the LAST step (or a 23f-closing micro-commit) after D1–D8 land.

### (4.64.C) Q3 — FLAGS (no force).
- **No cert / motive / wrapper-signature change.** The wrapper `case_III_arm_realization_rowOp` fired UNCHANGED; the cert is consumed as-is; the motive/IH are untouched. The ONLY interface change is the **already-user-APPROVED C.3 `hIH` add** (D1 needs `hG : IsMinimalKDof` + `hnp` to reach `splitOff_isMinimalKDof`); this was adjudicated 2026-06-26 (session #36) and is not a new decision.
- **The ONE flagged decision: D4's `hred` coupling shape.** Whether `hred` discharges by (i) *picking* `j₀` in the `lamAB`/`rab` support up front, or (ii) carrying a row-op identity that factors the literal `(e_b,j₀)` row through the bottom. §(4.61) adjudicated route-(a) FEASIBLE (the excluded row is redundant by the W6b widening); the *concrete* proof is build-deferred to D4. This does NOT block D1–D3/D5; it is the genuinely-new content of the bottom-arc, isolated to one `Realization.lean` lemma. FLAGGED, not forced.
- **Traced to ground:** `card m₁ + card m₂ = D + D·(|V(Gv)|−1) = D·(|V(G)|−1) ≤ (D−1)·|E(G)| = card p` (the §(4.55) inequality; strict injection, no bijection). `candidateVtx i = vtx i.succ = a` is `rfl`-level (`candidateVtx_succ_eq`), the `d = k+1` `ChainData` fact (`d_eq_kAdd`) routes the discriminator's `Fin (k+1)` panel to `Fin cd.d` (`exists_shared_redundancy_and_matched_candidate:1483`). The SAME `?L₀` serves `hA`/`hB` (one metavar, §(4.64.A)). `splitOff_isMinimalKDof` (`Reduction.lean:161`) supplies the interior `hsplitGP` from `hIH`.

**FIRST buildable step = D1 `interior_hsplitGP`** (`(hIH _ Gab (splitOff_isMinimalKDof …) hGabne hGablt).1 hGabSimple` — the `:670`–671 IH-route precedent at the interior split-off graph, off the C.3 `hIH`) — the leaf both BOT-2′'s `hfr` (D3) and the discriminator's `hsplitGP` input depend on; no other leaf supplies the interior def-0 realization. The rest of item 4 = D2–D8 + the separable CHAIN-5, in order.

## (4.65) D4 `hred` ADJUDICATION — VERDICT: **STOP, decision for the human.** Route (b) (free `j₀`, discharge `hred` from the W6b widening) is **REFUTED** at the kernel: `hred` for the LITERAL `(e_b, j₀)` row is NOT discharerable from the widening data, because `blockBasisOn` is an opaque `finBasisOfFinrankEq` and the widening lives in a *different edge's block* (`e₀`, not `e_b`). The §(4.61.D)/§(4.64.C) "route-(a)-feasible" adjudication was **over-optimistic** — same failure shape the §(4.62) C=0 episode warned of (prose adjudicating a jointly-unsatisfiable obligation "feasible"). The only routes that close `hred` change `blockBasisOn` / the `_zero₁₂` certificate's row family or its corner construction — a foundational-def / certificate change. NOT made here. (Compiler-checked spike: the literal `hred` stated + kernel-read residual goal, sorry-fed, deleted before commit; tree clean; full build green, zero-regression.)

**RESOLVED 2026-06-27 — route (α) CHOSEN (user-adjudicated).** The next session starts the route-(α)
decomposition design-pass (§(4.65.E)); the live hand-off is in `notes/Phase23f.md` *Current state* /
*Hand-off*. Route (β) was rejected (it re-opens the §(4.18)–(4.30) walled arc). The rest of this section
is the compiler-checked verdict that motivated the decision.

This recon built the LITERAL `hred` obligation BOT-2′ consumes at the concrete dispatch binding (`F := caseIIICandidate G ends q e_a e_b (q(a,·)) n' (q(b,·)) 0`, `p₀ := (⟨e_b, he_b⟩, j₀)`), fed it the W6b widening exactly as `exists_shared_redundancy_and_matched_candidate` produces it (`hcomb : hingeRow a b ρ₀ = ∑ⱼ cGv j • hingeRow (uvGv j)(vvGv j)(rvGv j)`), and **read the kernel-checked residual goal**. It then traced every load-bearing claim against the LANDED source (not the §(4.61.D) prose).

### (4.65.A) The kernel-checked residual (Q2 — what `hred` ACTUALLY reduces to).
After `rw [hends_eb]; simp only [↓reduceIte]` (the `(ends e_b).1 = v` branch decides `a`), the goal is verbatim:
```
hingeRow a b (blockBasisOn hgp he_b j₀)  ∈
  span (range fun p : {p // p ≠ (⟨e_b,he_b⟩, j₀)} =>
    hingeRow (if (ends p.1.1.1).1 = v then a else (ends p.1.1.1).1) (ends p.1.1.1).2
             (blockBasisOn hgp p.1.1.2 p.1.2))
```
The available hypothesis is `hcomb : hingeRow a b ρ₀ = ∑ⱼ cGv j • hingeRow (uvGv j)(vvGv j)(rvGv j)`. **There is no derivation.** The residual asks that a SPECIFIC basis vector `blockBasisOn hgp he_b j₀` of `e_b`'s hinge-row block, pushed through `hingeRow a b`, lie in the span of the OTHER a-shifted rows; `hcomb` speaks only of `ρ₀`, an UNRELATED functional.

### (4.65.B) WHY route (b) cannot close — three grounded facts (Q1, traced to LANDED source).
1. **`blockBasisOn` is OPAQUE** (`Concrete.lean:510`–517): `Module.finBasisOfFinrankEq ℝ (F.hingeRowBlock e) (finrank_hingeRowBlock …)` — an *arbitrary* basis with no constructive relation to any named functional. There is NO "the dependency involves the `j₀`-coordinate" lever — `j₀` indexes an unknown basis, so no choice of `j₀ : Fin (D−1)` can be shown to align with `ρ₀`. (§(4.61.D)'s "pick `j₀` in the redundancy support" presupposes a coordinate structure `blockBasisOn` does not expose.)
2. **`ρ₀` lives in a DIFFERENT block.** The W6b producer gives `rab j ∈ hingeRowBlock e₀` / `ρ₀ = ∑ⱼ lamAB j • rab j ∈ hingeRowBlock e₀` (`Realization.lean:1519`–1521; `Candidate.lean:432`), where `e₀ = cd.e₀` is the **fresh short-circuit edge `e₀ ∉ E(G)`** (`Operations.lean:577`/`667`) of the SPLITOFF framework `Gab`. `hred` needs `blockBasisOn hgp he_b j₀ ∈ hingeRowBlock e_b` of the CANDIDATE `caseIIICandidate G … .graph = G` (`Candidate.lean:954`), the PREDECESSOR chain edge `e_b = vᵢvᵢ₋₁` (`G.IsLink e_b v b`). `hingeRowBlock` is per-edge, keyed on `supportExtensor e` (`Basic.lean:431`); `e₀ = (a,b)` and `e_b = (v,b)` have different endpoints ⟹ generically different support extensors ⟹ different blocks. **NO landed fact gives `ρ₀ ∈ hingeRowBlock e_b`** — so even the `1`-dim redundancy `hcomb` carries (`hingeRow a b ρ₀ ∈ span R(Gv)`) is a dependency on `ρ₀`, NOT on any `blockBasisOn he_b j` direction.
3. **The whole `_zero₁₂` cert reads `blockBasisOn`, never `ρ₀`.** Every row of the A3-transposed cert — corner panel (`…_apply_corner`), `±r` slot (`…_apply_eB_off_pin`, `Concrete.lean:1620`), and mixed bottom (`submatrix_columnOp_toBlocks₂₂_eq_mixedBottom`, `:1691`) — reads `blockBasisOn hgp (re …).1.2 (re …).2` at its index. The matrix entry at an INTEGER index `(e_b, j₀)` is FORCED to be `blockBasisOn he_b j₀`; there is no integer index whose row reads `ρ₀`. So the corner injection's `j₀` is "free" only as an *index into an opaque basis* — exactly the freedom that does NOT help.

### (4.65.C) The §(4.61.D) "couple `j₀` to `ρ₀`" idea forces a `blockBasisOn` / cert change (Q3 — the named decision).
The escape §(4.61.D)/§(4.64.B)-option-(i) gestures at is: make the `±r` corner slot read `ρ₀` (the genuine redundancy direction), so that the row op turns it into the perp the cert needs and `hred` becomes `hcomb` directly. But the cert reads `blockBasisOn` at integer indices (4.65.B-3); to make the `(e_b, j₀)` row read `ρ₀` one must EITHER (a) re-define `blockBasisOn e_b` so that one of its basis vectors IS `ρ₀` (a *non-opaque, ρ₀-aligned* basis — a change to the foundational def `BodyHingeFramework.blockBasisOn`, `Concrete.lean:510`), OR (b) replace the `_zero₁₂` cert's `blockBasisOn`-keyed `±r` row with a genuine-functional `±r` row `hingeRow a b ρ₀` (a change to the certificate's row family / corner construction `cornerRowInjection` + `case_III_rank_certification_zero₁₂`). **Both are the kind of cert/foundational-def change the design-pass clause (ii) says to FLAG, not force.** Per the task, I did not make either.

### (4.65.D) THE ARCHITECTURAL CONTEXT THE HUMAN NEEDS — option (b) above already EXISTS as a fully-landed, `hred`-free route (THE decision).
There is a **second, fully-landed, axiom-clean interior-arm architecture** that reads the `±r` corner row as the genuine `hingeRow b v ρ₀` (NOT `blockBasisOn`), so it has **NO `hred` obligation at all**: the **dual-space `mkQ`/quotient route** `case_III_arm_corner_assembly` (`ForkedArm.lean:906`) → `case_III_arm_realization_chain` (`:59`) → the `±r`-block-rank-additivity cert `case_III_rank_certification_chain` (`Candidate.lean:2197`), with corner independence via `linearIndependent_mkQ_corner_of_gate` (`Candidate.lean:2083`) and the `±r` row sourced as KT's GENUINE reproduced-slot row `hingeRow_mem_caseIIICandidate_rigidityRows_reproduced` (`:2133`, perp test `hρe₀`, the gate `interior_hρe₀_of_baseWidening` ALREADY produces from the SAME widening — `ForkedArm.lean:669`). All sorry-free, axiom-clean (`#print axioms` confirmed on `interior_hρe₀_of_baseWidening`). **This is the KT-faithful eq. (6.66) `±r` row** (a single genuine `hingeRow`, the abstract redundancy `r = ρ₀` carried while the member moves) — exactly the object the `_zero₁₂` route is trying to *simulate* with an opaque-basis index.

**BUT the dual-space route is the one §(4.18)–(4.30) ruled WALLED**, and the wall is the SAME `caseIIICandidate`-override gate `ρ₀ ⊥̸ C(vᵢ₊₁, n')` re-surfacing wherever the wrap content enters the candidate span (§(4.29)'s load-bearing invariant: `hρGv` route-A, `hS` route-B, `hseedrank` route-4-bare, `hWS` route-4-splitOff — "intrinsic to the `caseIIICandidate` override, NOT to any base-block choice; no base-block re-targeting escapes it"). Concretely: `case_III_arm_corner_assembly_via_leafB2` (`:1015`) BUILDS sorry-free but carries `hS` (`exists_genuine_relabelImage_base_block`'s universal per-row transport) as a hypothesis that **§(4.26) proved UNSATISFIABLE** for the interior dispatch (the wrap-edge `edge i` base row relabels to the dead `(a,b)`-block tag, needing the kernel-`False` `hG_eb_cand`). So the landed dual-space arm is the same "builds-but-unsatisfiable-hyp" trap (§(4.62)) — NOT a usable escape as-is. The user chose the literal-`Matrix` route (§(4.30)/(4.48)) precisely to escape this gate; the `_zero₁₂` route (§(4.49)) is its descendant — and it escapes the *gate* but has now hit the *opaque-basis* obstruction at `hred`.

### (4.65.E) THE TWO ROUTES THAT CLOSE — for human adjudication (cost estimates; do NOT pick without the user).
- **Route (α) — make the `_zero₁₂` `±r` row read `ρ₀` directly (replace the opaque-basis `±r` index with a genuine-functional row).** Change `cornerRowInjection`'s `±r` slot from an index `(e_b, j₀)` into the cert's row family to a row carrying `hingeRow a b ρ₀`, and re-shape the `_zero₁₂` cert (`case_III_rank_certification_zero₁₂`, `Candidate.lean`) + `case_III_arm_realization_rowOp` (`ForkedArm.lean:315`) so the corner's `m₁`-block is `[blockBasisOn(e_a,·) ; hingeRow a b ρ₀]` (a `D−1 + 1` mix of opaque-basis panel rows and ONE genuine functional). Then `hred`/`havoid` DISSOLVE (the `±r` row is no longer a member of the `blockBasisOn` family the bottom selects from), and HB/HA read `ρ₀` honestly. **This is the row-op analogue of what the dual-space `mkQ` route already does.** Impact: re-states the cert's `re`/`hblock`/`hM'eq`/HA(leaf iii)/HB(BOT-3′) against a non-uniform `m₁` family; `blockBasisOn` def UNCHANGED (only the `±r` row leaves the `blockBasisOn` family). Touches `Candidate.lean` (the cert) + `ForkedArm.lean` (the wrapper) + the RE/HA/HB leaves in `Concrete.lean`. The `_zero₁₂` cert chain's `Rank.lean` backbone (B1/B2/`rank_ge_…`) is row-family-agnostic and likely survives. **Rough estimate: 4–7 commits** (a cert re-shape + the 3 leaf re-states + the dispatch), most of the already-landed 23f bottom-arc (BOT-1/2/2′/R1/avoiding-engine/BOT-4/HD) being for the *uniform* `blockBasisOn` bottom and reusable; the **deleted** parts are BOT-2′/the avoiding-engine/`bottom_selection_ne_corner_edge`/`cornerRowInjection`'s `±r` slot (the machinery that existed ONLY to handle `(e_b, j₀)`). KEEPS the literal-`Matrix` escape from the §(4.29) gate.
- **Route (β) — re-attack the dual-space `mkQ` route's gate wall directly** (discharge `case_III_arm_corner_assembly`'s `(W, hWS, hWcard, hW)` from a wall-free `W`-producer). §(4.27)/(4.28)/(4.29) ruled the THEN-tried `W`-producers (LEAF-B2 `hS`, route-4-bare `hseedrank`, route-4-splitOff `hWS`) all walled on the gate; a NEW `W`-producer would need to dodge the §(4.29) invariant — **genuinely-open, possibly a real new-math wall** (the §(4.29) verdict was "no base-block re-targeting escapes it"). NOT recommended without a fresh feasibility recon; **estimate: unknown (≥ the §(4.18)–(4.30) arc that already failed)**.
- **Route (α) is the recommendation to put to the user** — it keeps the user-chosen literal-`Matrix` escape, makes a *local, bounded* cert re-shape (no `blockBasisOn` def change, no motive/IH/contract change), and aligns the `_zero₁₂` `±r` row with KT's eq. (6.66) genuine-`r` row (the same object the dual-space route reads). Route (β) re-opens a closed, walled arc. **→ The buildable Layer plan is §(4.66)** (route (α) SETTLED 2026-06-27); §(4.66.A) refines the realization shape (an AUGMENTED matrix, not a `re`-rekey into `rigidityMatrixEdge`) — spike-verified, and SIMPLER than this prose anticipated (no corner row op).

### (4.65.F) Q3 — the FLAGS (no force).
- **`blockBasisOn` def itself need NOT change under route (α)** — only the cert's `±r` ROW leaves the `blockBasisOn` family; the panel rows + the mixed bottom stay `blockBasisOn`-keyed. (A full `ρ₀`-aligned `blockBasisOn` redefinition — route (α)-variant — would touch `blockBasisOn` `Concrete.lean:510` + its 6 consumer decls across `Concrete.lean`/`Basic.lean` + the cert chain; strictly worse than the local `±r`-row swap, NOT recommended.)
- **No motive / IH / frozen-contract change** under either route (the obstruction is below C.0–C.6; the approved C.3 `hIH` add stands).
- **The §(4.61.D)/§(4.64.C) "route-(a)-feasible, build-deferred" adjudication is OVERTURNED** — `hred` for the literal `(e_b, j₀)` is not buildable from the widening; this section supersedes it. The §(4.61) exclusion-steering machinery (BOT-2′ / the avoiding-engine / `bottom_selection_ne_corner_edge`) is SOUND as Lean but serves a `hred` that has no producer; it is deletable under route (α) (it existed only to handle the `(e_b, j₀)` collision route (α) dissolves).

## (4.66) ROUTE-(α) DECOMPOSITION DESIGN-PASS — the *Layer plan* (αE1–αE6 + αD1–αD7), spike-verified.

> **⚠ CORRECTED 2026-06-27 — READ §(4.66.F)/§(4.66.G) FIRST.** §(4.66.A–E)'s central "route (α) needs NO
> row op" claim is WRONG (it re-derived the `C=0`/no-row-op shortcut the settled §(4.62) had already refuted).
> Route (α) STILL chosen (the augmented matrix correctly sources the genuine `ρ₀` corner row), but a row op
> `Lrow` is STILL mandatory (zeros the corner off-`v` `B` block; the interior bottom's v-incident `e_b`-fill
> rows make `C=toBlocks₂₁≠0`, so the backbone is `_zero₁₂`/`Rank.lean:622`, NOT `_zero₂₁`/`:528`). The
> corrected Layer plan + keep/delete map is §(4.66.F)/§(4.66.G). §(4.66.A–E) below are retained to show what
> the correction overturns; per-statement ⚠ markers point to §(4.66.F).

Route (α) is SETTLED (user-adjudicated 2026-06-27, §(4.65.E)). This pass orders the cert re-shape
into buildable commits with exact signatures, every load-bearing claim verified against the LANDED
`def`/`theorem` (clause i) and grounded to cardinalities + gate-satisfiability (clause iii). Three
PROBE lemmas were stated in a compiler-checked scratch spike (`Relabel/SpikeAlpha.lean`, sorry-fed
only where flagged, **deleted before commit; tree clean; full build green**) and read.

### (4.66.A) THE HEADLINE REFINEMENT — `re` cannot map the `±r` slot into `rigidityMatrixEdge`; the engine takes an AUGMENTED matrix. (Verified, supersedes §(4.65.E)'s phrasing.)
§(4.65.E) describes route (α) as "change `cornerRowInjection`'s `±r` slot ... into the cert's row
family to a row carrying `hingeRow a b ρ₀`" with `re` re-keyed and `hblock` re-stated. **Reading the
landed source, that phrasing is not quite buildable, and the FIX is cleaner, not harder:** the
`_zero₁₂` engine (`finrank_span_rigidityRows_ge_of_edge_submatrix_fromBlocks_zero₁₂`,
`Concrete.lean:934`) reads `M := F.rigidityMatrixEdge ends hgp`, whose rows are FORCED by the row
index type `{e // e ∈ E(G)} × Fin (D−1)` to be `blockBasisOn` reads (`rigidityRowFunEdge`,
`Concrete.lean:716`/`730`). There is **no index whose `rigidityMatrixEdge` row reads the genuine
`hingeRow a b ρ₀`** (this is exactly §(4.65.B-3)). So `re : m₁ ⊕ m₂ → {e // ...} × Fin (D−1)` cannot
carry the `±r` row, and `cornerRowInjection` (which returns `… × Fin (D−1)`) cannot host it either.
**Realization that DOES build (spike PROBE C, sorry-free): an AUGMENTED matrix**
`augM : Matrix ((({e // e ∈ E(G)} × Fin (D−1))) ⊕ Unit) (α × Fin D) ℝ`, with `inl` rows the
`rigidityMatrixEdge` rows and the single `inr ()` row the genuine `hingeRow a b ρ₀` (coordinatized by
`dualProductCoordEquiv`). The cert's `re : m₁ ⊕ m₂ → augM`-row-index sends the `D−1` `e_a` panel rows
to `inl (e_a, j)`, the ONE `±r` slot to `inr ()`, the bottom to `inl (e, j)`. The `Rank.lean`
backbone `rank_ge_of_isUnit_mul_submatrix_fromBlocks_zero₁₂` (`Rank.lean:622`) is **fully `M`-generic**
(reads `M : Matrix p q K`, never `rigidityMatrixEdge`) — verified by reading; it fires on `augM`
unchanged. The only engine-specific step is the rank-to-span bound, re-stated as
`augM.rank ≤ finrank (span F.rigidityRows)` (PROBE C, proved sorry-free via `Matrix.rank_of_coordEquiv`
+ `Submodule.finrank_mono` + each augmented row ∈ `span rigidityRows`). **This is the row-op analogue
of what the dual-space `mkQ` chain cert does** (`case_III_rank_certification_chain` takes
`g : ι → Dual` with `hg : ∀ j, g j ∈ span rigidityRows` — the augmented-matrix `inr`-row is the
literal-`Matrix` mirror of one `g`-member).

**⚠ CORRECTED by §(4.66.F) (2026-06-27): the "no row op" consequence below is WRONG.** Route (α) STILL
needs the row op `Lrow` (to zero the corner's off-`v` `B` block; `C = toBlocks₂₁ ≠ 0` for the interior arm
per §(4.62), so the `_zero₂₁` shape is unavailable and the backbone is `_zero₁₂`/`Rank.lean:622`, WITH `Lrow`).
The augmented matrix fixes only the `ρ₀`-row sourcing (§(4.65)), NOT the `B≠0` row op. Read §(4.66.F)/§(4.66.G)
for the corrected plan; the paragraph below is retained only to show what the correction overturns.

**Consequence — the corner needs NO row op:** because the augmented `±r` row reads `ρ₀` *directly*
(un-operated), the corner `m₁`-block of `augM.submatrix re en` reads `[blockBasisOn(e_a,·); ρ₀]`
already — so HA is the bare `corner_hA'_of_gate` (`Concrete.lean:620`, LANDED — `[blockBasisOn(e_a);
ρ₀]` LI iff `hρe₀`), **NOT** the operated leaf (iii) + its `hAeq`, and there is **NO HB/`L₀`/`Lrow`**
obligation at all. Route (α) is therefore SIMPLER than §(4.65.E) anticipated: it deletes the entire
row-op apparatus (`Lrow`, B1/B2, BOT-3′, leaf (iii), the `L₀`-coupling), not just the `(e_b, j₀)`
machinery. The genuine `±r` row's pin-`v` column is `−ρ₀` (nonzero, `reproducedSlot_pmR_acolumn_eq`,
`Candidate.lean:2161`), so it sits in the CORNER block (the `m₁` rows, KT's `Mᵢ`) where a nonzero pin
column is expected; the bottom `m₂` stays pin-zero, preserving the `fromBlocks A 0 C D` shape via the
landed `submatrix_columnOp_…_toBlocks₂₁_eq_zero` family (the column op is the SAME `U` as `_zero₁₂`).

### (4.66.B) KEEP / DELETE / RE-STATE map — each claim verified against the decl's actual signature (clause ii).
**KEEPS verbatim (verified row-family-agnostic by reading the signature):**
- `Matrix.rank_ge_of_isUnit_mul_submatrix_fromBlocks_zero₁₂` (`Rank.lean:622`) — `M : Matrix p q K`,
  no rigidity content. ✓ survives.
- `Matrix.rank_of_coordEquiv` (`Concrete.lean:99`) — generic coordEquiv→span-rank bridge. ✓ (used by αE1).
- The realization tail `case_III_realization_of_rank` (`Arms.lean:63`) — consumes only
  `hrank : D·(|V(G)|−1) ≤ finrank (span F₀.rigidityRows)`. ✓ row-family-agnostic; reused verbatim.
- D1 `interior_hsplitGP` (`Realization.lean`, LANDED) — feeds the IH bottom's `hrank`. ✓.
- `corner_hA'_of_gate` (`Concrete.lean:620`, LANDED) — the bare `[blockBasisOn(e_a); ρ₀]`-LI = αE-HA. ✓.
- `hingeRow_mem_caseIIICandidate_rigidityRows_reproduced` (`Candidate.lean:2133`, LANDED) — the genuine
  `±r` row's `span rigidityRows` membership (spike PROBE A, sorry-free). ✓.
- `span_range_rigidityRowFunEdge` (`Concrete.lean:766`) — every `blockBasisOn` row ∈ `span rigidityRows`
  (spike PROBE B, sorry-free). ✓.
- The uniform-`blockBasisOn` **bottom** machinery (BOT-1, BOT-2 free engine, R1, BOT-4 minus the `±r`
  slot, HD): these select the `m₂` bottom from `blockBasisOn` rows and are unaffected by the `±r`
  re-shape. ✓ BUT see DELETE below for the `±r`-only pieces inside them.
- The column op `U`, `columnSplit`, `submatrix_columnOp_toBlocks₂₁_eq_zero` /
  `submatrix_columnOp_toBlocks₂₂_eq_mixedBottom` family — these read entries of `M * U`; they apply to
  `augM * U` on the `inl` rows verbatim, with the `inr` `±r` row handled separately (it is a corner
  row, pin-nonzero, lands in `A`). ✓ reusable on the `inl` sub-block.

**DELETES (sound Lean, but exists only to feed the refuted `hred` / the now-unneeded row op):**
- BOT-2′ `bottom_selection_of_crossFramework_span_avoiding` (`Concrete.lean:1940`) — the avoiding bridge.
- the avoiding-engine `exists_finCard_linearIndependent_selection_avoiding` (`Rank.lean`).
- D2 `bottom_selection_ne_corner_edge` (`hbot_ne_ea`) — only needed because BOT-4's `±r` slot reused
  edge `e_b` *inside* the bottom's index space; gone once `±r` is the augmented `inr` row.
- `cornerRowInjection` + `cornerRowInjection_injective` + `cornerRowInjection_sumElim_injective` +
  `finScrewDimSplitCorner` (`Concrete.lean:1076`–1137) — the `±r`-as-`(e_b,j₀)`-index apparatus.
- B1 `exists_rowOp_of_strictInjection` + B2 `rowOp_strictInjection_submatrix_eq_fromBlocks_zero₁₂`
  (`Rank.lean:795`/`859`) — the `Lrow` row-op; **NOT needed** (no corner row op). KEEP as orphans only
  if a future route wants them; route (α) does not fire them. (Cleanup decision at αE-build: delete or
  annotate orphan.)
- BOT-3′ `matrix_eq_mul_of_span_mem` (`Concrete.lean:2195`) + leaf (i)
  `matrix_eq_mul_of_dual_row_comb` — the `B = L₀·D` re-key; gone with HB.
- leaf (iii) `corner_hA_zero₁₂_of_gate` (`Concrete.lean:657`) — the OPERATED-corner HA; gone with the
  row op (the un-operated `corner_hA'_of_gate` is the αE HA).
- leaves (ii)/(iv) (`reindex_rowOp_isUnit_det` / `reindex_rowOp_submatrix_eq_fromBlocks_zero₁₂`,
  `Rank.lean`) — already zero-caller orphans; delete in the same sweep.

**RE-STATES (the genuinely-new content):**
- the engine `finrank_span_rigidityRows_ge_of_edge_submatrix_fromBlocks_zero₁₂` (`Concrete.lean:934`)
  → an **augmented-matrix** sibling reading `augM` (αE1).
- the cert `case_III_rank_certification_zero₁₂` (`Candidate.lean:2446`) → an augmented-matrix sibling
  consuming the genuine `±r` row + its `hperp`/`hρe₀` gates (αE3).
- the wrapper `case_III_arm_realization_rowOp` (`ForkedArm.lean:315`) → an augmented-matrix sibling
  WITHOUT the `(L₀, hB, hA-operated, Lrow)` carries (αE4).

### (4.66.C) Cardinality + gate satisfiability traced to ground (clause iii).
- **Card unchanged:** `card m₁ + card m₂ = D + D·(|V(Gv)|−1) = D·(|V(G)|−1)` (the cert target), the
  same count `case_III_rank_certification_zero₁₂` proves (`hVcard`/`hVone`, `Candidate.lean:2498`–2503);
  the `re` injection now lands in `(({e//…}×Fin(D−1)))⊕Unit` whose card
  `(D−1)·|E(G)| + 1 ≥ card m₁+card m₂` (strict injection, §(4.55) inequality preserved).
- **Both gates are real discriminator outputs (jointly satisfiable, NOT just type-correct).**
  `exists_shared_redundancy_and_matched_candidate` (`Realization.lean:1481`) produces, for the SAME
  `ρ₀`: (a) `ρ₀ (panelSupportExtensor (q(a,·)) (q(b,·))) = 0` (`:1511`) — the membership `hperp` at
  `t=0` (`caseIIICandidate_supportExtensor_reproduced` = `panelSupportExtensor n_a n_b`,
  `Candidate.lean:972`); (b) `ρ₀ (panelSupportExtensor (q(candidateVtx i,·)) n') ≠ 0` (`:1535`) — the
  LI gate `hρe₀` at the candidate slot `e_a` (`caseIIICandidate_supportExtensor_candidate` =
  `panelSupportExtensor n_a n'`, `Candidate.lean:960`). These are over DIFFERENT extensors
  (`n_b` vs `n'`), so `ρ₀ ⊥ reproduced` ∧ `ρ₀ ⊥̸ candidate-slot` is consistent — the §(4.65.D)
  decoupling, now grounded in the discriminator's literal conclusions. `candidateVtx i = vtx i.succ = a`
  is `rfl`-level (`candidateVtx_succ_eq`, `Operations.lean:2824`).

### (4.66.D) THE LAYER PLAN — αE1…αE6 (re-state) + αD1…αD7 (dispatch), dependency-ordered.
**⚠ CORRECTED by §(4.66.G) on the `Lrow` question:** the αE2/αE3/αE4 "drop `Lrow`/`hLrow`/`L₀`/`hB`" claims
below are REVERSED — the row op is mandatory (the backbone is `_zero₁₂`/`Rank.lean:622`, not `:528`). The step
LIST + ordering stand; for the corrected signatures + keep/delete map read §(4.66.G).
All αE land in `Concrete.lean`/`Candidate.lean`/`ForkedArm.lean`; αD in `Realization.lean`. `F₀ :=
caseIIICandidate G ends q e_a e_b (q(a,·)) n' (q(b,·)) 0`; `augM` per (4.66.A).

- **αE1 (FIRST buildable, `Concrete.lean`) — the augmented edge matrix + its rank-to-span bound.**
  Two decls. (1) `def BodyHingeFramework.rigidityMatrixEdgeAug (F) (ends) (hgp) (rRow : Dual ℝ (α→ScrewSpace k)) :
  Matrix ((({e // e ∈ E(F.graph)} × Fin (screwDim k−1)))⊕Unit) (α × Fin (finrank ℝ (ScrewSpace k))) ℝ
  := Matrix.of (Sum.elim (fun p => dualProductCoordEquiv (F.rigidityRowFunEdge ends hgp p))
  (fun _ => dualProductCoordEquiv rRow))`. (2) `theorem rigidityMatrixEdgeAug_rank_le_finrank_span
  [Fintype α][DecidableEq α][Finite β] (F)(ends)[Fintype {e//e∈E(F.graph)}](hgp)(hends)
  {rRow}(hr : rRow ∈ span F.rigidityRows) : (F.rigidityMatrixEdgeAug ends hgp rRow).rank ≤
  finrank ℝ (span F.rigidityRows)`. Body = spike PROBE C verbatim (`rank_of_coordEquiv` +
  `finrank_mono` + `span_le`; `inl` rows via `span_range_rigidityRowFunEdge`, `inr` via `hr`).
  **Consumes:** `rank_of_coordEquiv`, `span_range_rigidityRowFunEdge` (both LANDED). **Produces:** the
  augmented-matrix rank bound the augmented engine (αE2) needs. ✓ spike-verified sorry-free.
- **αE2 (`Concrete.lean`) — the augmented engine.** `theorem finrank_span_rigidityRows_ge_of_aug_submatrix_fromBlocks_zero₁₂`
  (the augmented sibling of `:934`): same hyps but `re : m₁ ⊕ m₂ → (({e//…}×Fin(D−1)))⊕Unit`,
  `hblock : (Lrow * F.rigidityMatrixEdgeAug ends hgp rRow * U).submatrix re en = fromBlocks A 0 C D`,
  `hr : rRow ∈ span F.rigidityRows`, concludes `card m₁ + card m₂ ≤ finrank (span F.rigidityRows)`.
  Body = `rank_ge_of_isUnit_mul_submatrix_fromBlocks_zero₁₂` then `rwa [le-form of αE1]` (the EQUALITY
  `:955` becomes a `≤` via αE1). **NOTE:** route (α) needs no `Lrow` row op — but keep the `Lrow`
  param so the engine stays a drop-in; the wrapper passes `Lrow := 1`, `hLrow := isUnit_one`,
  collapsing the row op. **Consumes:** αE1 + the LANDED `Rank.lean:622`. **Produces:** the rank bound
  the cert (αE3) wraps.
- **αE3 (`Candidate.lean`) — the augmented cert.** `theorem case_III_rank_certification_aug`
  (sibling of `case_III_rank_certification_zero₁₂` `:2446`): drop the `Lrow` corner-op story, take the
  genuine `±r` row `rRow := hingeRow a b ρ₀` with its membership `hr` (αD-supplied via PROBE A) and
  its `en`/`hblock`/`hA`/`hD`; conclude `screwDim k * (V(G).ncard − 1) ≤ finrank (span F₀.rigidityRows)`.
  Body = the `:2446` body with `finrank_span_rigidityRows_ge_of_edge_submatrix_fromBlocks_zero₁₂`
  replaced by αE2 + the `hr` membership, and the same count tail (`hm₁`/`hm₂`/`hVcard`/`hVone`,
  unchanged). **Consumes:** αE2. **Produces:** `hrank` for the wrapper.
- **αE4 (`ForkedArm.lean`) — the augmented wrapper.** `theorem case_III_arm_realization_aug`
  (sibling of `case_III_arm_realization_rowOp` `:315`): DROP `(L₀, hB, hA-operated)`, take instead the
  genuine-row data `(rRow = hingeRow a b ρ₀, hr, hρe₀)` + the bottom block data `(re, hre, en/hblock,
  hA = corner_hA'_of_gate-shaped, hD)`. Body fires αE3 then `case_III_realization_of_rank` (the
  LANDED tail, verbatim). `hM'eq`/`hblock` ride on the column op `U` (same as `:350`) +
  `submatrix_columnOp_…toBlocks₂₁_eq_zero` on the `inl` sub-block; the `inr` `±r` row is the corner
  `A`-block's last row. **Consumes:** αE3 + the LANDED column-op + tail. **Produces:**
  `HasGenericFullRankRealization k n G`. **⚑ FLAG (the one residual to compiler-lock at αE4-build):**
  the spike verified the rank bound + `rank_ge` composition + both gates, but did NOT compiler-check the
  full `hblock = fromBlocks A 0 C D` decomposition of `augM * U` with the `inr` `±r` row in the corner.
  This is the αE4 crux — the `submatrix_columnOp_toBlocks₂₁_eq_zero` family is stated over a `re` into
  `{e//…}×Fin(D−1)` (the `inl` index); it must be re-derived (or the `inr` row handled by a one-row
  `toBlocks₂₁`-zero lemma proving the genuine `±r` row's pin-`v` column lands in the CORNER columns, not
  the bottom-zero block — which holds since the `±r` row is in `m₁`). NOT new math; a bounded matrix-
  bookkeeping re-state. If it does not fall to the landed bricks, STOP and re-flag.
- **αE5 (`Concrete.lean` / `Candidate.lean`) — DELETE the dead `±r`-collision + row-op apparatus.**
  Remove (or orphan-annotate) the (4.66.B)-DELETE list: BOT-2′, the avoiding-engine, D2, `cornerRowInjection`
  family, B1/B2, BOT-3′, leaf (i)/(iii), leaves (ii)/(iv). Same commit rewords their checklist
  annotations (the §17 per-slice gate: grep `blueprint/src/` for any `\lean{...}` pin first — these
  have none, so no blueprint restate needed). Mechanical; scope last among αE or fold into αE4.
- **αE6 (`ForkedArm.lean`) — retire the `_rowOp` wrapper + `_zero₁₂` cert.** Once αE4 is the live arm,
  `case_III_arm_realization_rowOp` + `case_III_rank_certification_zero₁₂` +
  `finrank_span_rigidityRows_ge_of_edge_submatrix_fromBlocks_zero₁₂` become dead; delete or mark
  `@[deprecated]`. Keep `rigidityMatrixEdge` (the αE engine still reads it on `inl`).
- **αD1 (FIRST dispatch step, `Realization.lean`) — the genuine-`±r` membership + gate bundle.** At the
  dispatch binding (off `exists_shared_redundancy_and_matched_candidate` `:1481`), package the two
  discriminator outputs for the genuine row: `hr := hingeRow_mem_caseIIICandidate_rigidityRows_reproduced`
  fed `hlink : G.IsLink e_b a b` (the candidate's `e_b` link — `caseIIICandidate.graph = G`) + the
  membership perp `hρ₀e₀ : ρ₀ (panelSupportExtensor (q(a,·)) (q(b,·))) = 0` (`:1511`), and the LI gate
  `hρe₀ : ρ₀ (F₀.supportExtensor e_a) ≠ 0` bridged from `:1535` via `caseIIICandidate_supportExtensor_candidate`
  (`:960`) + `candidateVtx_succ_eq`. Likely a small leaf `interior_genuineRowData`. Spike PROBE A
  proved the `hr` shape sorry-free. **Consumes:** the discriminator. **Produces:** `(rRow, hr, hρe₀)`
  for αE4.
- **αD2 — the bottom block `(re-inl, hre, hbot, hD)`.** REUSE the uniform-`blockBasisOn` bottom: BOT-1/
  BOT-2 (FREE engine, no avoiding now) → R1 `hspan_id` → the bottom selection; `hD` from HD (LANDED,
  fed `hrank` via D1 `interior_hsplitGP` + the def-0 split-off realization). The `re` is now
  `Sum.elim (the inl panel + ±r-as-inr) (bottom-as-inl)` into the augmented index (no `cornerRowInjection`,
  no avoiding). **Consumes:** BOT-1/2, R1, HD, D1 (all LANDED). **Produces:** the bottom half of αE4's args.
- **αD3 — the corner `hA`.** `corner_hA'_of_gate hgp ha hρe₀` (LANDED, `:620`) directly — the corner
  reads `[blockBasisOn(e_a,·); ρ₀]` un-operated. Plus the reindex `em₁`/`coordEquiv` wrap to match
  `augM.submatrix re en`'s `toBlocks₁₁` (a `linearIndependent_row_of_coordEquiv` re-wrap, the un-operated
  analogue of leaf (iii)). **Consumes:** `corner_hA'_of_gate`. **Produces:** αE4's `hA`.
- **αD4 — `hblock`/`hM'eq` for `augM`.** The `fromBlocks A 0 C D` equality (αE4's `⚑`-flagged crux at
  the wrapper, here assembled at the dispatch): `hM'eq = (fromBlocks_toBlocks …).symm` on `augM * U`,
  `toBlocks₂₁ = 0` via the (re-stated, αE4) column-op-pin-zero on the `inl` bottom + the `±r`-in-corner
  fact. **Consumes:** the αE4 bricks. **Produces:** αE4's `hblock`.
- **αD5 — fire `case_III_arm_realization_aug`** with `(rRow, hr, hρe₀, re, hre, hblock, hA, hD)` (αD1–αD4).
- **αD6 — the `chainData_dispatch` router** (base/`d=3`→`chainData_split_realization`, interior→αD5).
- **αD7 — CHAIN-5** (the C.0 lockstep reshape + `d=3` zero-regression adapter). SEPARABLE; scope LAST.
  On αD6/αD7 landing the CHAIN layer closes and ENTRY (23g) opens.

### (4.66.E) FLAGS (clause ii — flag, don't force).
- **NO `blockBasisOn`-def / motive / IH / frozen-contract change** — confirmed: §(4.65.F) holds, and the
  augmented-matrix realization keeps `blockBasisOn` for ALL `inl` rows; only the new `inr` row is a
  genuine functional, sourced by the LANDED `hingeRow_mem_…reproduced`. The approved C.3 `hIH` add stands.
- **The αE4 `hblock` decomposition is the ONE residual not yet compiler-locked** (the spike verified
  rank + gates, not the full `fromBlocks` column-op assembly with the `±r` row in the corner). It is a
  bounded matrix-bookkeeping re-state of the landed `submatrix_columnOp_…toBlocks₂₁_eq_zero` family, NOT
  new math; but it is the place to STOP and re-flag if the landed bricks do not cover the augmented
  index. Flagged precisely (αE4 ⚑).
- **B1/B2 + the row-op apparatus become orphans, not bugs** — route (α) fires no corner row op (`Lrow=1`),
  so the §(4.61)/§(4.64) row-op leaves are dead. Delete-vs-keep is a cleanup call at αE5; they are SOUND.
  **⚠ CORRECTED by §(4.66.F): FALSE.** The row op is mandatory (zeros the corner off-`v` `B`); B1/B2/BOT-3′/
  leaf(i)/leaf(iii) STAY (they discharge it). Only the `(e_b,j₀)`/`hred` machinery is orphaned.
- **The αE4 `hblock` residual is real but its SHAPE is `fromBlocks A 0 C D` (`_zero₁₂`, via `Lrow`), NOT
  producible "from the column op alone"** — §(4.66.F). It is the landed B2 reduction applied to `augM`.

### (4.66.F) CORRECTION — route (α) STILL needs the row op `Lrow`; the backbone is `_zero₁₂` (`Rank.lean:622`), NOT `_zero₂₁` (`:528`). The §(4.66.A/D/E) "no row op" claim is WRONG (it contradicts the settled §(4.62)). Source-confirmed + compiler-checked (spike `SpikeAlphaE4.lean`, 3 probes sorry-free, deleted before commit; tree clean). 2026-06-27.

**The error in §(4.66.A/D/E).** §(4.66.A) (lines 4090–4099) claims the augmented matrix lets the corner skip
the row op — "HA is the bare `corner_hA'_of_gate` … NO HB/`L₀`/`Lrow` obligation … the bottom `m₂` stays
pin-zero, preserving the `fromBlocks A 0 C D` shape via the landed `submatrix_columnOp_…_toBlocks₂₁_eq_zero`
family." **This is two conflated mistakes:**
1. **Block-shape conflation.** `…_submatrix_toBlocks₂₁_eq_zero` (`Concrete.lean:1604`) zeros `toBlocks₂₁`
   (bottom-LEFT), i.e. it produces `fromBlocks A B 0 D` — the `_zero₂₁` shape that fires
   `rank_ge_of_isUnit_mul_submatrix_fromBlocks` (`Rank.lean:528`, NO `Lrow`). It does **not** produce
   `fromBlocks A 0 C D` (the `_zero₁₂` shape, top-RIGHT zero, which fires `Rank.lean:622` and needs `Lrow`).
   The §(4.66.A) prose names the `_zero₂₁` brick but claims the `_zero₁₂` shape.
2. **`toBlocks₂₁ = 0` is UNAVAILABLE for the interior arm — the bottom is NOT pin-zero.** The
   `…_toBlocks₂₁_eq_zero` brick demands `hbot : ∀ i, v ≠ (ends (re (Sum.inr i)).1.1).1 ∧ v ≠ (…).2` (BOTH
   bottom endpoints ≠ v). §(4.62) PROVES (kernel-confirmed) this is **unsatisfiable** for the full-rank
   interior bottom: the `e₀=(a,b)` deficiency-fill block is covered ONLY by the v-incident `e_b`-fill rows
   (first endpoint `= v`), which read NONZERO at the pin column via `…_apply_corner` (FIRST-endpoint-= v case,
   `Concrete.lean:1540`) — so `C = toBlocks₂₁ ≠ 0`. The augmented matrix does NOT change this: moving the
   `±r` corner row to the `inr ()` slot leaves the `inl` BOTTOM rows (incl. the v-incident `e_b`-fill) intact,
   so `toBlocks₂₁ ≠ 0` still holds.

**Why the augmented matrix does NOT remove the row op.** Route (α)'s augmented matrix correctly fixes the
problem §(4.65) refuted — sourcing the genuine `ρ₀` corner row (no `rigidityMatrixEdge` index reads `ρ₀`,
§(4.65.B-3)), so the `(e_b,j₀)`/`hred` apparatus IS deletable. But that is a DIFFERENT obstruction from the
one the row op `Lrow` addresses. Per §(4.62.Q2/Q3), the row op `Lrow` (built from `L₀`) zeros the corner's
off-`v` **`B` block** (upper-right, `toBlocks₁₂`), which is nonzero because the `±r` corner row reads bodies
`a, b` (both ≠ v) — the column op `U` only zeros off-`v` content for the `e_a`-panel rows (where `v=(ends).1`,
`…_apply_eq_zero_of_ne` `:1454`), NOT for the genuine `±r`/`e_b` row (`…_apply_eB_off_pin` `:1696`, nonzero
off-`v`). So `B ≠ 0` regardless of whether the `±r` row is `blockBasisOn(e_b,j₀)` or the genuine `hingeRow a b
ρ₀`. **The row op is mandatory; route (α) only makes it SIMPLER** (it no longer has to convert an opaque
`blockBasisOn(e_b,j₀)` row into `ρ₀` — that part dissolves — but it still zeros `B`).

**Compiler-check (spike `Relabel/SpikeAlphaE4.lean`, 3 probes, sorry-free, deleted before commit).**
- `probe_aug_engine_zero₂₁` — the augmented engine in the `_zero₂₁` shape (`Rank.lean:528`, no `Lrow`) composes
  at the RANK level (both backbones are `M`-generic; this was never in doubt — the rank machinery is row-family-
  agnostic, the §(4.66) "spike PROBE C" point). ✓ builds.
- `probe_aug_engine_zero₁₂` — the augmented engine in the `_zero₁₂` shape (`Rank.lean:622`, WITH `Lrow`)
  composes at the RANK level. ✓ builds. (So the rank-machinery choice between the two is purely about which
  `hblock` the dispatch can GEOMETRICALLY produce, NOT about the backbones.)
- `probe_toBlocks₂₁_zero_needs_hbot` — the only column-op-ONLY producer of a `0` lower-left block
  (`…_submatrix_toBlocks₂₁_eq_zero`) goes through ONLY under `hbot` (both bottom endpoints ≠ v). ✓ builds —
  confirming the obstruction is satisfiability of `hbot`, which §(4.62) refutes.

**THE FOUR SUB-QUESTIONS (the recon's clause set) — verdicts.**
- **(i) which zero block the column op produces / does `toBlocks₂₁ = 0` follow for `augM`?** The column op
  ALONE produces `toBlocks₂₁ = 0` (LOWER-left, `_zero₂₁`) **only when both bottom endpoints ≠ v** — FALSE for
  the interior arm (the v-incident `e_b`-fill rows are mandatory for the full-rank count, §(4.62)). The `inr`
  `±r` row riding in the corner does not disturb this, but it doesn't help either: the obstruction is in the
  `inl` BOTTOM. So `toBlocks₂₁ ≠ 0`, `C` free/nonzero — the `_zero₂₁` shape is geometrically UNAVAILABLE.
- **(ii) which backbone fires?** `Rank.lean:622` (`rank_ge_of_isUnit_mul_submatrix_fromBlocks_zero₁₂`,
  `_zero₁₂`, upper-right zero, with the LEFT row op `Lrow`) — the SAME backbone the landed `_zero₁₂` cert fires.
  **NOT** `:528`. No new sibling needed. The original §(4.66.A) reference to `:622` was correct; its mechanism
  ("via the column op alone") was the error.
- **(iii) does the corner `hA` follow from `corner_hA'_of_gate`?** Indirectly — the cert's `hA` consumes the
  OPERATED corner `(A − L₀·C).row` (the row op subtracts the `cGv`-weighted bottom from the corner row), via
  leaf (iii) `corner_hA_zero₁₂_of_gate` (`Concrete.lean:657`, the `linearIndependent_row_of_coordEquiv`
  re-wrap), which itself closes via the bare `corner_hA'_of_gate` (`:620`). So `corner_hA'_of_gate` is the
  abstract dual-space fact, but the cert's hypothesis is leaf (iii)'s operated form, NOT the bare one. (FLAG:
  whether the augmented `inr` row lets `hA` simplify past leaf (iii) — since the genuine `ρ₀` row reads `ρ₀`
  at the pin already, the `A − L₀·C` mutation may reduce to identity-at-the-pin — is the one sub-leaf needing
  the αD-dispatch entry geometry; do not assume it, build leaf (iii)'s operated `hAeq` as the default.)
- **(iv) is ANY row op needed?** YES — `Lrow` (non-trivial, not `Lrow := 1`) is mandatory to zero the
  corner's off-`v` `B` block. This is the load-bearing correction.

**Net.** Route (α) STILL chosen (the augmented matrix is correct + needed for the `ρ₀` corner row). But the
αE-plan's "drop the `Lrow`/`hLrow`/`L₀`/`hB`/`hA-operated`" claim is REVERSED: the augmented wrapper is the
landed `case_III_arm_realization_rowOp` with its `rigidityMatrixEdge` swapped for `rigidityMatrixEdgeAug` and
its `±r` corner row sourced as the augmented `inr` slot (genuine `ρ₀`) — keeping `(Lrow, hLrow, L₀, hB,
hA-operated=leaf(iii), U, re, en, hM'eq, hD)`. The deletes are ONLY the `(e_b,j₀)`/`hred` machinery (BOT-2′,
the avoiding-engine, D2, `cornerRowInjection` family), NOT the row-op apparatus (B1/B2/BOT-3′/leaf(i)/(iii)
STAY — they discharge the still-required row op). See §(4.66.G) for the corrected Layer plan.

**THREE DESIGN-PASS CLAUSES — verdicts.**
- **(i) verified against LANDED source.** `Rank.lean:528` (`_zero₂₁`, no `Lrow`, `hblock = fromBlocks A B 0
  D`) vs `:622` (`_zero₁₂`, `Lrow`, `hblock = fromBlocks A 0 C D`, docstring: "the column op alone gives the
  lower-left-zero shape"); `…_submatrix_toBlocks₂₁_eq_zero` `:1604` (`hbot` both-≠-v ⟹ `toBlocks₂₁=0`);
  `…_apply_corner` `:1540` (FIRST-= v nonzero pin read); `…_apply_eB_off_pin` `:1696` (v-incident row nonzero
  off-`v`); the landed `_zero₁₂` cert `case_III_rank_certification_zero₁₂` (`Candidate.lean:2446`, `Lrow` param,
  docstring lines 2411–2418 + 2493: "the row op zeros the corner's off-`v` `B` block … the column op alone
  gives the lower-left-zero shape"); the landed wrapper `case_III_arm_realization_rowOp`
  (`ForkedArm.lean:315`, the `Lrow`/`L₀`/`hB`/`hA = (A−L₀C).row` carries); the αE1 landings `:855`/`:881`;
  §(4.62) Q1–Q3. All read at source, not prose.
- **(ii) FLAG-DON'T-FORCE.** Flagged the one un-locked sub-leaf (the (iii)→bare `hA` simplification under the
  genuine `inr` row, sub-question (iii)) — do NOT assume it; the safe default is leaf (iii)'s operated `hAeq`.
  No motive/IH/frozen-contract/`blockBasisOn`-def change. The correction is local (the αE-plan signatures +
  keep/delete map), not a route change.
- **(iii) traced to GROUND.** Card UNCHANGED: `card m₁ + card m₂ = D + D·(|V(Gv)|−1) = D·(|V(G)|−1)`. `card m₁
  = D` corner (the `D−1` `e_a`-panel `inl` rows + the ONE genuine `inr` `±r` slot); `card m₂ = D·(|V(Gv)|−1)`
  bottom (the v-incident `e_b`-fill `inl` rows + the `Gv` `inl` rows, `mixedBottom`). The genuine `inr` row's
  pin-`v` column is `−ρ₀` ≠ 0 (corner, expected); its off-`v` `B` content ≠ 0 (needs `Lrow`); the bottom's
  v-incident rows make `C = toBlocks₂₁ ≠ 0` (needs `_zero₁₂`, not `_zero₂₁`). The corner index reindex `m₁ ≃
  Fin (D−1) ⊕ Unit` is `finScrewDimSplitCorner` (leaf (iii)'s `em₁`), `D = screwDim k ≥ 3` at the interior arm.

### (4.66.G) CORRECTED LAYER PLAN — supersedes §(4.66.D) on the `Lrow` question. αE1 LANDED; αE2 = the augmented engine, `_zero₁₂` shape (WITH `Lrow`).

The αE/αD step LIST and ordering of §(4.66.D) stand; the CORRECTIONS (all from §(4.66.F)) are:
- **αE2** = `finrank_span_rigidityRows_ge_of_aug_submatrix_fromBlocks_zero₁₂` — the augmented sibling of the
  landed `…_of_edge_submatrix_fromBlocks_zero₁₂` (`Concrete.lean:1020`), NOT of the `_zero₂₁`
  `…_of_edge_submatrix_fromBlocks` (`:982`). Exact signature: `[Fintype α] [DecidableEq α] [DecidableEq β]
  [Finite β] (F) (ends) [Fintype {e//e∈E(F.graph)}] (hgp) (hends) {m₁ m₂ n₁ n₂} [Fintype m₁] [Fintype m₂]
  [Finite n₁] [Finite n₂] (Lrow : Matrix ((({e//…}×Fin(D−1)))⊕Unit) ((({e//…}×Fin(D−1)))⊕Unit) ℝ) (hLrow :
  IsUnit Lrow.det) (U) (hU) (re : m₁⊕m₂ → (({e//…}×Fin(D−1)))⊕Unit) (en : (n₁⊕n₂) ≃ (α×Fin D)) {A : Matrix m₁
  n₁ ℝ} {C : Matrix m₂ n₁ ℝ} {D : Matrix m₂ n₂ ℝ} (hblock : (Lrow * F.rigidityMatrixEdgeAug ends hgp rRow *
  U).submatrix re en = fromBlocks A 0 C D) {rRow} (hr : rRow ∈ span F.rigidityRows) (hA : LI A.row) (hD : LI
  D.row) : card m₁ + card m₂ ≤ finrank (span F.rigidityRows)`. Body = `rank_ge_of_isUnit_mul_submatrix_
  fromBlocks_zero₁₂` (`Rank.lean:622`) then `le_trans … (rigidityMatrixEdgeAug_rank_le_finrank_span … hr)`.
  KEEP the `Lrow`/`hLrow` params (mandatory now — NOT a drop-in collapse to `Lrow:=1`). Spike-confirmed
  composes (`probe_aug_engine_zero₁₂`).
- **αE3** = `case_III_rank_certification_aug` — clone of `case_III_rank_certification_zero₁₂`
  (`Candidate.lean:2446`) with `rigidityMatrixEdge → rigidityMatrixEdgeAug`, ADD `(rRow, hr)`, KEEP
  `(Lrow, hLrow, U, hU, re, en, A, C, D, hblock = fromBlocks A 0 C D, hA, hD)`. Body fires αE2.
- **αE4** = `case_III_arm_realization_aug` — clone of `case_III_arm_realization_rowOp` (`ForkedArm.lean:315`)
  with the matrix swapped to `rigidityMatrixEdgeAug` + the `±r` corner row sourced from the `inr` slot. KEEP
  `(re, hre, L₀, hM'eq, hB, hA = leaf(iii) operated, hD)`; B1/B2 still build `Lrow` in-body, B2 reduces
  `hblock`. The ⚑ residual: re-derive `hM'eq`/`hB`/`hblock` for the augmented matrix (the `inl` sub-block via
  the landed `submatrix_columnOp_*` family, the `inr` row's reads via the genuine functional). The §(4.66.F.iii)
  flag (leaf (iii) vs bare `hA`) is resolved here.
- **αE5 deletes** ONLY the `(e_b,j₀)`/`hred` machinery (BOT-2′, the avoiding-engine, D2, `cornerRowInjection`
  family + `finScrewDimSplitCorner`-as-`(e_b,j₀)`-host). **KEEPS** B1/B2/BOT-3′/leaf(i)/leaf(iii) (they
  discharge the still-required row op) — REVERSING §(4.66.B)'s "DELETE B1/B2/BOT-3′/leaf(iii)". `finScrewDim
  SplitCorner` (the `m₁ ≃ Fin(D−1)⊕Unit` corner reindex) is REUSED by leaf (iii)'s `em₁` — keep it.
- **αD3** = leaf (iii) `corner_hA_zero₁₂_of_gate` (the operated `(A−L₀C).row`-LI), NOT the bare
  `corner_hA'_of_gate` — REVERSING §(4.66.D)'s αD3.
- **αD4** = `hblock = fromBlocks A 0 C D` (the `_zero₁₂`, top-right zero, via `Lrow`), NOT `fromBlocks A 0 C D`
  "from the column op alone" — REVERSING §(4.66.D)'s αD4 mechanism. The `_zero₁₂` `hblock` is the landed
  B2 `rowOp_strictInjection_submatrix_eq_fromBlocks_zero₁₂` reduction (KEPT, not deleted) applied to `augM`.
- Everything else in §(4.66.D) (αE1 ✓, αE6, αD1, αD2, αD5, αD6, αD7) stands.

## (4.67) αD-DISPATCH ENTRY SATISFIABILITY — VERDICT: the αD plan's `±r` ROW IS THE WRONG ROW (`hingeRow a b ρ₀` reads `0` at the pin); the buildable corner is the LANDED dual-space chain arm (`case_III_arm_corner_assembly[_via_leafB2]`, the `W.mkQ` route, `rRow = hingeRow b v ρ₀`). The `_aug` operated-`hA` route is NOT a settled assembly; PIVOT the dispatch to the chain arm. Compiler-checked (spike `SpikeAlphaD{,2,Verify}.lean`, 3 probes sorry-free + 7 axiom-clean prints, deleted before commit; tree clean). 2026-06-27.

> **⚠ SUPERSEDED by §(4.68) (2026-06-27).** §(4.67)'s "PIVOT to the chain arm" recommendation is WRONG: it
> verified the chain-arm decls are axiom-clean (TYPE-checks with `hS` as a hypothesis) but did NOT verify
> `hS`'s VALUE is producible for ALL of `Fbase.rigidityRows` — the exact §(4.67)-error it named. §(4.68)
> compiler-confirms (PROBE A/B sorry-free) that the chain arm's `hS` IS the §(4.26)/(4.29) wall (the wrap-edge
> `edge i` base row needs the kernel-FALSE `hG_eb_cand`). With the `_aug` `hingeRow b v ρ₀` route ALSO blocked
> at the operated `hA` (§(4.68.B), the §(4.65) `hred` coupling), **route α is blocked on both faces** — §(4.68)
> is the live verdict (STOP, user adjudication of (α1)/(α2)/(C)). §(4.67) below is retained to show what §(4.68)
> overturns (the SUB-QUESTION 1/2 analysis of the `_aug` `hingeRow a b ρ₀` row STANDS — that row is still wrong;
> only the "chain arm is the fix" conclusion is superseded).

**The crux question (the operated-corner `hA` for `augM`), settled compiler-checked.** The αE4 wrapper
`case_III_arm_realization_aug` (`ForkedArm.lean:426`) carries `hA : LinearIndependent ℝ (A − L₀ * C).row`
with `A,B,C,D := (augM * Uᵀ submatrix re en).toBlocks₁₁/₁₂/₂₁/₂₂` (pinned by `hM'eq = fromBlocks_toBlocks.symm`,
the §(4.64.A) read), `augM := F₀.rigidityMatrixEdgeAug ends hgp rRow`, `U` keyed on the pin `v`, `re` =
`e_a`-panel `inl` rows + the `inr ()` `±r` row in `m₁`, `mixedBottom` `inl` rows in `m₂`. The §(4.66.D) αD1
plan sources the `inr` `±r` row as `rRow := hingeRow a b ρ₀` (the W6b-widened form, both endpoints `a, b ≠ v`).

**SUB-QUESTION 1 — what the operated corner reads. KERNEL VERDICT: `A`'s `inr`-row reads `0` at the pin —
NOT `ρ₀`.** PROBE 1 (`probe_aug_inr_corner_pin_zero`, sorry-free): the `inr ()` row of `augM * Uᵀ` with
`rRow = hingeRow a b ρ₀` at the pin column `(v, c)` is `0`. Mechanism: the column op `Φ.symm = columnOp hva`
is the identity on body `v`'s screw column (`columnOp_apply_single`), so the entry is `hingeRow a b ρ₀
(single v s) = ρ₀((single v s) a − (single v s) b) = ρ₀(0 − 0) = 0` (both `a, b ≠ v`). PROBE 2
(`probe_aug_inr_offpin`, sorry-free): off-pin the same row reads the genuine `hingeRow a b ρ₀` value (the
`B`-block content; `body ≠ v` was UNUSED — the `inr` row's endpoints `a, b ≠ v` so the column op is invisible
to it everywhere off `v`). **So the un-operated `A`'s `Unit` row is the ZERO functional, NOT `ρ₀`** — leaf
(iii)'s `hAeq` (operated corner's `Unit` row `= ρ₀`) does NOT hold for `A`, NOR (un-operated) for the bare
`corner_hA'_of_gate`. This is the structural INVERSION of the OLD `rigidityMatrixEdge` route, where the `±r`
row was `blockBasisOn(e_b, j₀)` (a `v`-incident edge `e_b = (v,b)` row reading NONZERO at the pin via
`_apply_corner`), so the row op turned a nonzero pin read into `ρ₀`.

**SUB-QUESTION 2 — is `(A − L₀C).row` LI? VERDICT: NOT from the named leaves; the route reintroduces the
refuted `hred`-flavored coupling.** With `A`'s `inr`-pin `= 0` (PROBE 1) and `hD` row-LI forcing `L₀` uniquely
via `hB : B = L₀·D` (off-pin), the operated `inr` row at the pin is `0 − (L₀·C)|_pin`. The W6b widening expresses
`hingeRow a b ρ₀ = ∑ cGv·hingeRow(uvGv, vvGv, rvGv)` over **`Gv`-rows only** (both endpoints `≠ v`, reading `0`
at the pin via `_apply_pin_zero`), so the `L₀` that `hB` forces puts no pin-weight there; the only pin-nonzero
bottom rows are the `v`-incident `e_b`-fill (`_apply_corner`, `blockBasisOn(e_b,·)`). For `(A − L₀C)|_pin = ρ₀`
one then needs `ρ₀ ∈ span(blockBasisOn(e_b,·) pin reads)` — the SAME opaque-`blockBasisOn`/`ρ₀`-in-a-different-
block obstruction §(4.65) REFUTED as `hred`. So `hA` via leaf (iii) is NOT a settled assembly for the
`hingeRow a b ρ₀` row; it has no producer among the named leaves. (Not proven impossible here — flagged as
the open coupling, per clause (ii); the §(4.62)/(4.65) lesson says do not adjudicate it "feasible" in prose.)

**THE FIX, and why the `_aug` route is a detour. The buildable corner is the LANDED dual-space chain arm.**
The correct genuine `±r` row is `hingeRow b v ρ₀` (head the re-inserted body `v`, `= hingeRow u vᵢ ρ₀`), NOT
`hingeRow a b ρ₀`. PROBE 1b (`probe_aug_inr_corner_pin_bv`, sorry-free): with `rRow = hingeRow b v ρ₀` the
`inr`-pin read is `−ρ₀(finScrewBasis k c)` — NONZERO, the corner gate content (this is the
`reproducedSlot_pmR_acolumn_eq` `−ρ₀` fact, `Candidate.lean:2161`). The αD1 plan's `hingeRow a b ρ₀` is exactly
the "support-panel-endpoint row that lands on the fresh pair (omitting `vᵢ`) and reads `0` at `single vᵢ`, the
wrong object" the `Candidate.lean:2110` docstring records as the failure mode of the four prior `±r`-sourcing
attempts. **And the project already has a complete, axiom-clean corner solution using the right row:** the
dual-space chain arm `case_III_arm_corner_assembly` (`ForkedArm.lean:1022`) sets `rRow := hingeRow b v ρ₀`,
proves the corner row-LI **mod `W`** (`linearIndependent_mkQ_corner_of_gate`, `Candidate.lean:2083`, via
`hrCol : rRow.comp (single v) = −ρ₀` + the two gates `hgate`/`hρe₀`), and fires `case_III_arm_realization_chain`
(`ForkedArm.lean:59`) → `case_III_rank_certification_chain`. **No row op, no operated `(A − L₀C)`, no `hred`.**
Its `W`-production wrapper `case_III_arm_corner_assembly_via_leafB2` (`ForkedArm.lean:1131`) is also landed,
taking the route-B LEAF-B2 inputs `(Fbase, σ, rhat, hrhat, hIH, hS, hvanish)`. All seven chain-route decls are
axiom-clean (standard triple `propext`/`Classical.choice`/`Quot.sound`, NO `sorryAx`; PROBE 3 / `SpikeAlphaDVerify`).

**JOINT-SATISFIABILITY of the `_aug` fire (sub-question 3) — MOOT under the verdict, but recorded.** The
§(4.64.A) Q1 read (HMEQ closes via `fromBlocks_toBlocks.symm`, HD via `exact hD`, ONE shared `?L₀` across
`hA`/`hB`) carries over verbatim to `_aug` (the wrapper's `hM'eq`/`hD` slots are byte-identical in shape).
But the `_aug` fire's joint satisfiability is BLOCKED at `hA` for the `hingeRow a b ρ₀` row (sub-question 2),
and is only RECOVERABLE by switching the row to `hingeRow b v ρ₀` AND re-deriving the operated `hAeq` against
a `−ρ₀` pin read — which is strictly more work than the landed chain arm already does mod `W`. So there is no
reason to fire `_aug`: the chain arm is the buildable interior corner.

**αD1–αD7 — RE-DECOMPOSED to the chain arm (supersedes §(4.66.D)/§(4.66.G)'s `_aug` αD3/αD4).** The interior
arm should route through `case_III_arm_corner_assembly_via_leafB2`, NOT `case_III_arm_realization_aug`. The
buildable leaves, in order:
- **αD1 (FIRST, `Realization.lean`) — the two discriminator gates + the genuine-row data.** Off
  `exists_shared_redundancy_and_matched_candidate` (`Realization.lean:1481`): `hgate := hρe₀` (`:1535`,
  bridged to `ρ₀ (F₀.supportExtensor e_a) ≠ 0` via `caseIIICandidate_supportExtensor_candidate` `:960` +
  `candidateVtx_succ_eq`), `hρe₀(assembly) := hρ₀e₀` (`:1511`). These are the two DIFFERENT-extensor gates
  (jointly satisfiable, §(4.66.C)). **Produces:** the `(hgate, hρe₀)` pair `case_III_arm_corner_assembly`
  consumes. (No `hr := hingeRow_mem_…reproduced` needed at the wrapper — the assembly builds the corner's
  `hg` internally with `hG_eb.symm`.) Likely no new leaf; the dispatch reads the discriminator directly.
- **αD2 — the LEAF-B2 `W`-production inputs `(Fbase, σ, rhat, hrhat, hIH, hS, hvanish)`.** `Fbase` = the base
  framework off the IH-fed def-0 split-off realization (D1 `interior_hsplitGP`, LANDED); `hIH` its rank
  `= D·(|V(Gv)|−1)`; `σ = (shiftPerm i.castSucc)⁻¹` the cycle relabel; `rhat`/`hrhat` the redundant base row
  (KT eq. (6.24)); `hS` from `Graph.ChainData.bottomRelabel_rigidityRows_mem_span_caseIIICandidate`, `hvanish`
  from `ofNormals_removeVertex_rigidityRow_comp_single_self` at `σ.symm v = vtx 1` (both named LANDED universal
  lemmas, §(4.25)-era). This is the bulk of the remaining dispatch wiring.
- **αD3 — fire `case_III_arm_corner_assembly_via_leafB2`** with `(hgate, hρe₀)` (αD1) + the LEAF-B2 inputs (αD2)
  + the structural args off the `ChainData` interior split.
- **αD4 — the `chainData_dispatch` router** (base/`d=3`→`chainData_split_realization`, interior→αD3).
- **αD5 — CHAIN-5** (the C.0 lockstep reshape + `d=3` zero-regression adapter). SEPARABLE; scope LAST.
  On αD4/αD5 landing the CHAIN layer closes and ENTRY (23g) opens.

**αE1–αE5 status under this verdict.** The αE1–αE4 `_aug` ladder (`rigidityMatrixEdgeAug` + engine + cert +
wrapper) is SOUND Lean but is NOT the interior-arm route — it joins `case_III_arm_realization_matrix`
(`_zero₂₁`, dead by the §(4.62) `hbot`-unsatisfiability) as a landed-but-unused arm. It is NOT deleted here
(docs-only session); the αE6 retirement (deferred to phase-close per the task) should fold the `_aug` ladder
into the dead-arm sweep alongside `_matrix`/`_rowOp`. αE5's `(e_b,j₀)`-machinery deletion STANDS (those leaves
were dead under every route). **No new math, no motive/IH/contract change** — the chain arm + LEAF-B2 are all
landed; the dispatch is pure wiring of the two gates + the W-production inputs.

**THREE DESIGN-PASS CLAUSES — verdicts.**
- **(i) verified against LANDED source.** `rigidityMatrixEdgeAug` (`Concrete.lean:855`), `_apply_corner`
  (`:1520`, FIRST-= v nonzero pin), `_apply_pin_zero` (`:1488`, both-≠ v zero), `columnOp_apply_single`
  (`Basic.lean:1312`), `hingeRow_apply` (`Basic.lean:495`); the αE4 wrapper's carried `hA : LI (A − L₀C).row`
  (`ForkedArm.lean:476`); the chain arm `case_III_arm_corner_assembly` (`:1022`) / `_via_leafB2` (`:1131`) /
  `case_III_arm_realization_chain` (`:59`); `linearIndependent_mkQ_corner_of_gate` (`Candidate.lean:2083`,
  `hrCol = −ρ₀`); `reproducedSlot_pmR_acolumn_eq` (`:2161`); the discriminator gates (`:1511`/`:1535`); the
  W6b widening `hedgeGv` (`:1526`–1532). All read at source; the 3 probes + 7 axiom prints compiled against them.
- **(ii) FLAG-DON'T-FORCE.** FLAGGED (not forced): the `_aug` operated-`hA` for `hingeRow a b ρ₀` is the
  refuted-`hred`-flavored coupling — NOT adjudicated "feasible" (the §(4.62)/(4.65) failure mode). The pivot to
  the chain arm is a route choice among LANDED arms, not a new build. **USER-ADJUDICATION-WORTHY decision:** the
  §(4.66) route-(α) `_aug` plan (chosen 2026-06-27 the same day) is superseded by the chain arm for the interior
  corner; this is a within-route correction (both are "literal vs dual-space cert" the project already carries),
  not a motive/contract change, but it reverses the αD3/αD4 plan and retires the αE1–αE4 ladder as dead — flag
  for the human as the second §(4.66) correction in one day.
- **(iii) traced to GROUND.** Card UNCHANGED: `card m₁ + card m₂ = D·(|V(G)|−1)`; the chain arm's `ι` corner
  (`hιcard = D`) + `W` bottom (`hWcard = D·(|V(Gv)|−1)`). The `−ρ₀` pin read (`reproducedSlot_pmR_acolumn_eq`,
  PROBE 1b) needs `b ≠ v` (`hvb`), present; the `0` pin read for `hingeRow a b ρ₀` (PROBE 1) needs `a ≠ v ∧ b ≠ v`,
  both present (`hav`/`hbv`). The two gates are on DIFFERENT extensors (`panelSupportExtensor (q a) n'` vs
  `panelSupportExtensor (q a)(q b)`), jointly satisfiable. `D = screwDim k ≥ 3` at the interior arm.

## (4.68) BOTH-ROUTE αD RECON — VERDICT: **BOTH ROUTES BLOCKED; route α is in trouble. STOP — decision for the human.** ROUTE A (the §(4.67) dual-space chain-arm pivot) walks straight back into the §(4.26)/(4.29) `hS` wall (compiler-CONFIRMED, NOT refuted); ROUTE B (the `_aug` literal-`Matrix` arm with the CORRECTED `±r = hingeRow b v ρ₀`) re-hits the §(4.65) opaque-`blockBasisOn` `hred` coupling at the operated `hA` (compiler-confirmed the structural reads). §(4.67)'s "pivot to the chain arm" recommendation is **SUPERSEDED** (it did NOT verify `hS` covers all of `Fbase.rigidityRows` — the same §(4.67)-error it warned against). Compiler-checked (4 probes sorry-free in `SpikeRouteA.lean`/`SpikeRouteB.lean`, full `lake build` green, deleted before commit; tree clean). 2026-06-27.

**The standing circularity, now closed on both sides (the headline).** §(4.65) refuted ROUTE B's `hred` and recommended route (α)=`_aug`; §(4.67) refuted `_aug`'s `hingeRow a b ρ₀` row and pivoted to the chain arm; §(4.65.D)/(4.26)/(4.29) had ALREADY ruled the chain arm WALLED on `hS`. So §(4.67)'s pivot returns to a wall §(4.65.D) explicitly flagged — the two "literal vs dual-space" arms are NOT independent escapes; they are two faces of the SAME `caseIIICandidate`-override obstruction (§(4.29)'s load-bearing invariant: "the wall is the gate `ρ₀ ⊥̸ C(vᵢ₊₁,n')` re-surfacing wherever the wrap content enters the candidate span; no base-block re-targeting escapes it"). This recon closes the loop with compiler-checked evidence on BOTH faces.

### (4.68.A) ROUTE A — `hS` is UNSATISFIABLE for the interior arm (§(4.26) CONFIRMED, compiler-checked).
`case_III_arm_corner_assembly_via_leafB2` (`ForkedArm.lean:1131`) carries `hS : ∀ φ ∈ Fbase.rigidityRows, (funLeft σ).dualMap φ ∈ span (caseIIICandidate …).rigidityRows`. The only landed `hS`-producer is `bottomRelabel_rigidityRows_mem_span_caseIIICandidate` (`ForkedArm.lean:956`), via `chainData_bottom_relabel` (`Chain.lean:316`) → `bottomRelabel_image_mem_span_caseIIICandidate` (`:873`). I read all three bodies. The mechanism: `chainData_bottom_relabel` routes a GENUINE base row through a 3-way classification (`removeVertex_genuine_shiftRelabel`, `:370`): (1) off-cycle/interior-chain-edge → `Or.inl` (clean); (2)/(3) **WRAP EDGE `edge i` → `Or.inr` (the `(a,b)`-block tag)** (`:382`/`:395`). The `Or.inr` tag is then carried into the candidate span by `bottomRelabel_image_mem_span_caseIIICandidate`'s `Or.inr` arm (`:919`–922), which calls `hingeRow_mem_caseIIICandidate_rigidityRows_reproduced` (`Candidate.lean:2133`) feeding **`hG_eb_cand : G.IsLink e_b (vtx i.succ) (vtx (i−1).castSucc)` as the `hlink`**. This is the §(4.26) wall lemma's load-bearing hypothesis (`hG_eb_cand`, `bottomRelabel_…:967`), and it is **kernel-FALSE for the interior dispatch**:
- **PROBE A (sorry-free):** for interior `i` (`0 < i`, `i+1 < d`), NO `e_b` links `vtx i.succ = vtx (i+1)` to `vtx (i−1)` — these are 2 chain steps apart, and `vtx (i+1)` is itself interior so `deg_two` at `i+1` forces every `G`-edge there to be `edge i` (→ `vtx i`) or `edge (i+1)` (→ `vtx (i+2)`), neither reaching `vtx (i−1)`. (`isLink_edge` + `IsLink.eq_and_eq_or_eq_and_eq` + `vtx_inj`; full `Fin`-arithmetic proof compiled.)
- **PROBE B (sorry-free, sharper):** the chain arm's OWN `e_b` (`hG_eb : G.IsLink e_b v b` with `v = vtx i.castSucc ≠ a = vtx i.succ`) cannot serve as the producer's `hG_eb_cand : G.IsLink e_b a b`: by `IsLink.right_unique`, one edge `e_b` linking both `(v,b)` and `(a,b)` forces `v = a`, contradiction.
So the wrap-edge base row (which IS in `Fbase.rigidityRows` — `edge i` survives `removeVertex (vtx 1)` for `i ≥ 2`) has NO landed route into the candidate span, and there is no integer index / alternate edge that supplies a TRUE `hG_eb_cand`. **`hS`'s ∀ fails precisely on the wrap-edge `edge i` row** — exactly §(4.26)/(4.29). The decls being axiom-clean (the §(4.67) claim) is the §(4.62)/(4.67) trap: it confirms the TYPE checks with `hS` as a hypothesis, NOT that `hS`'s VALUE is producible. **§(4.67)'s "hS comes from the landed bottomRelabel_…" claim is the unverified-coverage error it warned against.**

### (4.68.B) ROUTE B — the corrected-row `_aug` operated `hA` re-hits the §(4.65) `hred` coupling (compiler-confirmed reads).
With the CORRECTED `rRow = hingeRow b v ρ₀` (head the re-inserted body `v`), the `_aug` wrapper `case_III_arm_realization_aug` (`ForkedArm.lean:426`) carries `hA : LinearIndependent ℝ (A − L₀C).row`. I compiled the operated-corner structural reads:
- **(1) the un-operated corner `inr` row at the pin.** PROBE B1 (sorry-free): the `inr ()` row of `augM * U` at the pin `(v,c)` reads **`−ρ₀(finScrewBasis k c)`** — NONZERO, the genuine corner gate content (= `reproducedSlot_pmR_acolumn_eq`, `Candidate.lean:2161`). (Contrast §(4.67) PROBE 1: `hingeRow a b ρ₀` reads `0`.) So the corrected row fixes the `ρ₀`-SOURCING.
- **(2) is `(A − L₀C).row` LI? NO landed producer; the route re-hits `hred`.** The row op `L₀` is FORCED by `hB : B = L₀·D` (off-pin), and it is NONTRIVIAL: PROBE B2 (sorry-free) — the un-operated `inr` row reads `ρ₀` at body `b`'s off-pin column (`B ≠ 0`, so `L₀ = 0` is impossible). The bottom block `D`/`C` INCLUDES the v-incident `e_b`-fill row (read at SOURCE: `submatrix_columnOp_toBlocks₂₂_eq_mixedBottom`, `Concrete.lean:1741`–1774, the `hbot1` `Or.inr` "FIRST endpoint `= v`" branch — the `e₀=(a,b)` deficiency fill, mandatory for the full-rank count, §(4.62)), so `C = toBlocks₂₁ ≠ 0` and its pin content is `blockBasisOn(e_b,·)` (`_apply_corner`, FIRST-=v nonzero pin). Hence the OPERATED `inr` pin read is `−ρ₀ − (L₀·C)|_pin`, where `(L₀·C)|_pin` is the `hB`-forced `L₀`-combination of the OPAQUE `blockBasisOn(e_b,·)` pin reads. The only landed `hA` producer, leaf (iii) `corner_hA_zero₁₂_of_gate` (`Concrete.lean:657`), requires `hAeq`: the operated row `= ρ₀` (the coordinate matrix of `[blockBasisOn(e_a,·); ρ₀]`). That needs `−ρ₀ − (L₀C)|_pin = ρ₀`, i.e. `(L₀C)|_pin = −2ρ₀`, i.e. **`ρ₀ ∈ span(blockBasisOn(e_b,·) pin reads)`** — the §(4.65)-REFUTED `hred` (`blockBasisOn` is opaque `finBasisOfFinrankEq`; `ρ₀ ∈ hingeRowBlock e₀ ≠ hingeRowBlock e_b`). Nor does the gate `hgate` alone give LI: `−ρ₀ − (L₀C)|_pin ∉ span(blockBasisOn(e_a))` is NOT forced (`(L₀C)|_pin` is opaque `e_b`-block content, generically not in the `e_a` span; the gate only places `ρ₀` outside the `e_a` span). **No restated/sign-adjusted leaf (iii) closes it** — a sign flip only changes the target to `−ρ₀`, still demanding `(L₀C)|_pin ∈ span` it cannot reach. FLAGGED, not forced (the §(4.62)/(4.65) lesson — no prose "feasible" without a sorry-free `hA`).

### (4.68.C) RECOMMENDATION — route α (the literal-`Matrix` cert) for the interior arm is BLOCKED on both faces; escalate to the user. The two candidate escapes are NOT independent.
Both the dual-space chain arm (ROUTE A) and the `_aug` literal-`Matrix` arm (ROUTE B) are blocked by the SAME `caseIIICandidate`-override obstruction (§(4.29)), now compiler-confirmed on both faces — A at the base-block `W`-production `hS` (the wrap-edge row has no candidate-span home), B at the operated corner `hA` (the opaque `blockBasisOn(e_b)`/`ρ₀` coupling). Neither is buildable from the landed leaves; closing EITHER requires a change at or above the cert/foundational-def level:
- **(α1) the chain arm needs a WALL-FREE `W`-producer** — the §(4.65.E) route (β), re-attacking the `hS`/gate wall directly. §(4.27)–(4.29) ruled the then-tried producers (LEAF-B2 `hS`, route-4-bare `hseedrank`, route-4-splitOff `hWS`) all walled; this is genuinely-open, "possibly a real new-math wall" (≥ the §(4.18)–(4.30) arc that already failed). KT's own §6.4.2 certifies the rank by **whole-matrix** block-additivity with the member MOVING (eqs. 6.62–6.67), which the dual-space transport realizes AS the wall — so the wall is KT-intrinsic, not a formalization artifact (§(4.21)/(4.24)).
- **(α2) the `_aug` arm needs a `ρ₀`-aligned `±r` corner** that does NOT route the operated row through the opaque `blockBasisOn(e_b)` bottom — i.e. make the `±r` corner row carry `ρ₀` (or `−ρ₀`) DIRECTLY with the off-`v` `B`-block zeroable WITHOUT pulling in `e_b`-block pin content. The structural blocker is that the full-rank count FORCES the v-incident `e_b`-fill row into the bottom (§(4.62)), so `C ≠ 0` and the row op couples the corner to `e_b`'s opaque block. Escaping this is a cert-row-family / corner-construction change (the §(4.65.C) option-(b) class), NOT made here.
- **(C) fall back to a fundamentally different certification.** The user chose route A (literal `Matrix`) over fallback (C) on cost (§(4.30)); with BOTH faces of route α now blocked, (C) — or a KT-faithful whole-matrix block-additivity cert that does NOT decompose into a fixed-member corner+bottom split — is back on the table. This is the genuinely-new-math direction §(4.21) named (the §I.8.21(α) matrix-level block-rank infra).

**This is a STOP for human adjudication** (clause (ii)): route α is the user-chosen route, and both its arms are now compiler-confirmed blocked below the contract (no motive/IH/C.0–C.6 change involved — the obstruction is in the cert's corner/bottom split). The decision is which of (α1)/(α2)/(C) to attempt, each a multi-commit recon-first effort with real wall risk. **No αD leaf is buildable until this is resolved** — do NOT build αD1+ against either arm.

### (4.68.D) THREE DESIGN-PASS CLAUSES — verdicts.
- **(i) verified against LANDED source.** Read the full bodies of `case_III_arm_corner_assembly[_via_leafB2]` (`ForkedArm.lean:1022`/`1131`), `chainData_bottom_relabel` (`Chain.lean:316`), `bottomRelabel_image_mem_span_caseIIICandidate` (`:873`) + `bottomRelabel_rigidityRows_mem_span_caseIIICandidate` (`:956`), `hingeRow_mem_caseIIICandidate_rigidityRows_reproduced` (`Candidate.lean:2133`), the wall lemma `funLeft_dualMap_pmR_group_mem_span_caseIIICandidate` (`Chain.lean:512`), `corner_hA_zero₁₂_of_gate`/`corner_hA'_of_gate` (`Concrete.lean:657`/`620`), `submatrix_columnOp_toBlocks₂₂_eq_mixedBottom` (`:1741`), `rigidityMatrixEdge_mul_columnOp_apply_corner`/`_apply_pin_zero` (`:1520`/`:1488`), `rigidityMatrixEdgeAug` (`:855`), `ChainData.deg_two`/`link`/`vtx_inj` (`Operations.lean:1316`/`1310`/`1308`), the discriminator (`Realization.lean:1481`). The 4 probes compiled against them.
- **(ii) FLAG-DON'T-FORCE — fired on BOTH routes (the whole point).** ROUTE A's `hS` is compiler-REFUTED (not "looks unsatisfiable" — PROBE A/B sorry-free); ROUTE B's operated `hA` is FLAGGED as the refuted-`hred` coupling (the structural reads compiled; the `hA` itself has no producer — NOT adjudicated "feasible"). Surfaced for user adjudication: route α blocked on both faces (§(4.68.C)).
- **(iii) traced to GROUND.** Card unchanged (`card m₁ + card m₂ = D·(|V(G)|−1)`, both arms). ROUTE A: `hS`'s ∀ fails on the wrap-edge `edge i ∈ Fbase.rigidityRows` row (the EXACT element). ROUTE B: same `L₀` serves `hA`/`hB` (one row op); the operated `inr` pin read is `−ρ₀ − (L₀C)|_pin` (PROBE B1 `−ρ₀` + PROBE B2 `B≠0` ⟹ `L₀≠0` + `C≠0` from the mandatory `e_b`-fill bottom). `D = screwDim k ≥ 3`.

## (4.69) BROAD KT-FAITHFULNESS RECON / DESIGN-PASS — VERDICT: the wall is a faithful image of KT's own union-dimension obstruction, BUT it is sharpened by ONE project-specific device (the `caseIIICandidate` extensor-override) that KT does NOT use. RECOMMENDATION: **(C)/fresh — replace the corner+bottom *transport-into-candidate-span* cert with a cert whose bottom is the LITERAL full-rank IH framework's rigidity rows (KT's `R(G₁,q₁)` as a sub-family, no override-transport).** This is closest to KT and is the only direction that structurally dissolves the wall. But it needs a genuinely-new cert leaf (block-additivity over a UNION of two frameworks' rows, not one framework's span) — **FLAG-DON'T-FORCE: the recommended path needs a new-math cert leaf; STOP for the user to choose (C)/fresh vs (α1) vs (α2).** Source-grounded (KT §6.4.1/§6.4.2 read end-to-end, eqs. 6.44–6.67) + landed-Lean-verified (cert backbone `Rank.lean:480/574`, `finrank_span_rigidityRows_ge_of_corner` `Candidate.lean:1698`, the chain cert/arm, the realization tail `Arms.lean:63`, the discriminator `Realization.lean:1481`, the `mixedBottom`/`bottomRelabel` producers). 2026-06-27.

> **Scope.** This is the broad re-read the user asked for after the §(4.68) STOP: which path forward is CLOSEST to KT + feasible, cost de-emphasized, "tear out and rebuild" in scope. It re-verifies the three load-bearing claims (§(4.68) both-blocked, §(4.29) gate-invariant, §(4.21) "KT uses whole-matrix block-additivity") against KT's ACTUAL text and the LANDED decls, then maps each escape to KT and rates faithfulness + feasibility. **Floor delivered:** KT re-read + comparison + recommendation. The decomposition is FLAGGED (the recommended path crosses a new-math cert leaf), per the task's flag-don't-force clause.

### (4.69.1) KT SOURCE RE-READ — §6.4.1 (d=3) + §6.4.2 (general d), eqs. 6.44–6.67, read end-to-end against the primary source.

Read `katoh-tanigawa-2011-molecular-conjecture.pdf` pp.691–698 (pdf pages 45–52; the printed-page offset is `paper p.N = pdf page (N−646)`), cross-checked structurally against the 2009 arXiv version. **How KT certifies the Lemma-6.13 / Case-III general-`d` rank — precisely:**

KT's setup (6.46)–(6.59). `G` has a chain `v₀v₁…v_d` of length `d` (`deg_G(vᵢ)=2` for `1 ≤ i ≤ d−1`). The split-off `G₁ = G^{v₀v₂}_{v₁}` is a smaller minimal-0-dof graph (Lemma 4.8); by the IH (6.1)/(6.46) there is a generic nonparallel realization `(G₁,q₁)` with `R(G₁,q₁) = D(|V|−2)` (**full rank**). KT then builds `d` DISTINCT frameworks `(G,pᵢ)` for `0 ≤ i ≤ d−1` — each obtained from `(G₁,q₁)` by re-inserting `vᵢ` and placing the chain edges via (6.47)/(6.48)/(6.57)/(6.59), with the `vᵢvᵢ₊₁` edge carried by a free `(d−2)`-affine subspace `Lᵢ` (the moving member). **The member moves: `i = 0,…,d−1`.**

KT's certification (6.49)→(6.67), the load-bearing structure:
- **(6.49)/(6.60)** `R(G,pᵢ)` has the two chain-edge rows (`vᵢvᵢ₊₁`, `vᵢ₋₁vᵢ`) on top of `R(G,pᵢ; E∖{chain}, V∖{vᵢ})`.
- **(6.50)/(6.61)** — a COLUMN operation ("add the `vᵢ` columns to the `vᵢ₊₁` columns", then substitute (6.59)) brings `R(G,pᵢ)` to a matrix that **literally contains `R(G₁,q₁)` as its bottom-right block** — quote (6.61): "`R(G,pᵢ) = [ r(Lᵢ) , 0 ; r(q₁(vᵢvᵢ₊₁)) , 0 ; 0 , R(G₁,q₁) ]`", with the row correspondence (6.62) "for `e ∈ E∖{chain}`, the `e`-row of `R(G,pᵢ)` ⇔ the `e`-row (or relabeled `vⱼvⱼ₊₁`-row) of `R(G₁,q₁)`". The bottom block IS `R(G₁,q₁)`, the full-rank IH matrix — its rows ARE rows of `R(G,pᵢ)` (the substitution `pᵢ(e) = q₁(e)` on the common edges makes them the same vectors), not transported copies.
- **(6.63)/(6.64)** — a ROW operation using the eq.-(6.52) redundancy `∑ λ_{ej} R(G₁,q₁;eⱼ) = 0` (a redundant row `(v₀v₂)ᵢ∗` of `R(G₁,q₁)` exists by Claim 6.11) zeros the `V∖{vᵢ}` part of the `(v₀v₁)ᵢ∗` row, leaving its `vᵢ`-part `= ∑ λ_{(vᵢvᵢ₊₁)j} rⱼ(q₁(vᵢvᵢ₊₁))`. Result (6.64): `R(G,pᵢ) = [ r(Lᵢ) , 0 ; ∑λⱼrⱼ(q₁(vᵢvᵢ₊₁)) , 0 ; ∗ , R(G₁∖{(v₀v₂)ᵢ∗}, q₁) ]`, where `R(G₁∖row,q₁)` is `R(G₁,q₁)` with the one redundant row removed (still `rank = D(|V|−2)`, eq. (6.51)).
- **(6.64)/(6.65)** — the top-left `D×D` block is `Mᵢ := [ r(Lᵢ) ; ∑λⱼrⱼ(q₁(vᵢvᵢ₊₁)) ]`. **(6.65): "rank `R(G,pᵢ) ≥ rank Mᵢ + rank R(G₁∖row,q₁) = D + D(|V|−2) = D(|V|−1)`"** — block-rank ADDITIVITY as an INEQUALITY, the corner `Mᵢ` + the IH bottom.
- **(6.66)/(6.67)** — the disjunction. KT sets `r := ∑ⱼ λ_{(v₀v₂)j} rⱼ(q₁(v₀v₂)) ∈ ℝᴰ` (the redundancy direction). `Mᵢ` fails to have full rank ⟺ `r ⊥ C(Lᵢ)` (the `(d−1)`-extensor of `Lᵢ`); the degree-2 fact `deg(vᵢ)=2` gives (6.66) `∑ⱼ λ_{(vᵢvᵢ₊₁)j} rⱼ(q(vᵢvᵢ₊₁)) = ±r`. **(6.65) "at least one of `M₀,…,M_{d−1}` has full rank":** none full-rank ⟺ `r ⊥` the UNION `⋃_{0≤i≤d−1} ⋃_{Lᵢ⊂Πᵢ} C(Lᵢ)` (6.67), `Πᵢ = Π_{G₁,q₁}(vᵢ₊₁)`. KT closes by `dim span(6.67) = D` via Lemma 2.1 (`(d+1 choose d−1) = D` — the green Phase-17 `omitTwoExtensor_linearIndependent`), picking `d+1` affinely-independent points.

**KT structure summary (the answer to the task's question 1).** KT's cert is (a) a **per-`i` corner+bottom block split** — corner `Mᵢ` (`D×D`, the two chain rows reduced), bottom `R(G₁∖row,q₁)` (the FULL-RANK IH matrix), via block-rank additivity (6.65); (b) over a **MOVING member** `i = 0,…,d−1`; (c) with the choice of good `i` made by a **union-dimension argument** (6.67 = `D` by Lemma 2.1). **It is NOT a fixed-member single-framework cert** — the d candidates are essential, and the bottom is the literal IH matrix whose rows are literally rows of `R(G,pᵢ)` (no extensor override, no transport-into-a-different-span). **§6.4.1 (d=3) and §6.4.2 (general d) are the IDENTICAL argument** — d=3 uses `M₁,M₂,M₃` and the union `C(L)⊂Π(a)∪Π(b)∪Π(c)` (6.45) closed by `dim = 6 = D`; general d uses `M₀,…,M_{d−1}` and (6.67). Only the chain length grows. **This UPHOLDS the §(4.21)/(4.24)/(4.68.C) paraphrase** ("KT certifies the rank by whole-matrix block-additivity with the member MOVING, eqs. 6.62–6.67") — re-verified against the actual text, the claim holds verbatim.

### (4.69.2) HOW THE PROJECT REALIZES KT — and the ONE place it diverges (the root of the wall).

The project's architecture (all green at `d=3`, all verified at source this pass):
- **The moving-member disjunction is collapsed into the DISCRIMINATOR.** `exists_shared_redundancy_and_matched_candidate` (`Realization.lean:1481`) runs KT's union-dimension argument (6.67) ONCE, off the shared redundancy `ρ₀` (= KT's `r`, §I.8.21(0)) and the IH seed, and PICKS the good member `i` (`exists_chainData_discriminator_pick` off the alg-independence of the panel selector) — outputting the matched candidate vertex + an `n'` with the gate `ρ₀ (panelSupportExtensor (q(candidateVtx i)) n') ≠ 0` (`:1535`). This IS KT's "at least one `Mᵢ` full-rank" realized as "this picked `i`'s `Mᵢ` is full-rank". **Faithful** — and reusable by every escape (it is below the cert).
- **The single-candidate corner+bottom cert.** Per the picked `i`, the project certifies `rank R(candidate) ≥ D(|V|−1)` on ONE framework `F₀ = caseIIICandidate G ends q e_a e_b (q a) n' (q b) 0` via block additivity. Two cert shapes are landed: the **dual-space chain cert** `case_III_rank_certification_chain` (`Candidate.lean:2197`) = `finrank W + |ι| ≤ finrank(span F₀.rigidityRows)` via `finrank_span_rigidityRows_ge_of_corner` (`:1698`, = mathlib `Submodule.finrank_add_card_le_of_linearIndependent_mkQ`), `W` the bottom, `ι` the corner mod `W`; and the **literal-`Matrix` cert** `case_III_rank_certification_zero₁₂` (`Candidate.lean:2446`) via the `Rank.lean:574` backbone `rank_ge_of_isUnit_mul_submatrix_fromBlocks_zero₁₂` (`fromBlocks A 0 C D`, `A` = corner, `[C D]` = bottom). **The cert MACHINERY is KT-faithful** — `rank_fromBlocks_zero₁₂_ge_of_linearIndependent_rows` (`Rank.lean:480`-region) IS KT's (6.64)/(6.65) inequality; `finrank_span_rigidityRows_ge_of_corner` is its dual-space twin. The block additivity is NOT where the wall is.
- **THE DIVERGENCE (the root of the wall).** KT's bottom is `R(G₁,q₁)` whose rows ARE rows of `R(G,pᵢ)`. **The project's bottom must satisfy `W ≤ span F₀.rigidityRows`** (chain cert `hWS`) — i.e. the bottom rows must live in the CANDIDATE framework's span — and the candidate framework `caseIIICandidate` **OVERRIDES the support extensors at the two chain slots `{e_a, e_b}`** to the candidate meet `C(L) = panelSupportExtensor n_u n'` / the sheared meet (`Candidate.lean:940`, the eq.-(6.12) device of §6.4.1). KT performs NO such override — its slot rows are literal `q₁`-rows. So where KT's bottom rows are *automatically* rows of the target matrix, the project must **TRANSPORT** the IH bottom rows (genuine `R(G−vᵢ)` rows, relabeled by the cycle `shiftPerm i` = KT's `ρᵢ`) INTO `span(candidate.rigidityRows)` — and the override changes the slot extensors, so a transported row that lands on a chain slot must match the OVERRIDDEN extensor. **The wall is exactly that obligation:** the wrap-edge base row relabels to the `(a,b)`-block tag, whose candidate-span membership needs `ρ' ⊥ C(vᵢ₊₁,n')` at the OVERRIDDEN slot — but `n'` was chosen (by the discriminator, KT's 6.67 pick) so that `ρ₀ ⊥̸ C(vᵢ₊₁,n')` (`hgate`). The gate that PICKS the good member (KT 6.67) and the gate that BLOCKS the transport are the SAME `ρ₀ ⊥̸ C(vᵢ₊₁,n')` — this is §(4.29)'s load-bearing invariant, now seen as **two faces of KT's union-dimension obstruction**: it is the price of collapsing the moving-member disjunction into a single overridden candidate framework whose span must also host the bottom.

**So §(4.29) is KT-INTRINSIC in origin (it is KT's 6.67 obstruction) but is SHARPENED INTO A WALL by the project-specific `caseIIICandidate` override** — KT never has to put the bottom rows into the candidate's (overridden) span, because KT keeps the bottom as the literal IH matrix block. This is the precise faithfulness diagnosis the §(4.68.C) recommendation needed and did not yet state.

### (4.69.3) RE-VERIFICATION OF THE THREE LOAD-BEARING §(4.68) CLAIMS (clause i — against LANDED source, do not trust the paraphrase).

- **§(4.68) both-blocked — CONFIRMED structurally (re-read at source, not re-spiked; the §(4.68) 4 sorry-free probes stand).** ROUTE A: the ONLY `hS`/W-producer `bottomRelabel_rigidityRows_mem_span_caseIIICandidate` (`ForkedArm.lean:956`) takes `hG_eb_cand : G.IsLink e_b (vtx i.succ) (vtx (i−1).castSucc)` as a load-bearing hypothesis — **visible in the signature itself** (`:967`), and kernel-FALSE for interior `i` (the two vertices are 2 chain-steps apart; `vtx (i+1)` interior `deg_two` forbids it). The wrap edge `edge i ∈ Fbase.rigidityRows` routes through `chainData_bottom_relabel`'s `Or.inr` arm, so its candidate-span membership has no producer. CONFIRMED. ROUTE B: the `mixedBottom` (`Concrete.lean:1741`) mandatorily includes the v-incident `e_b`-fill rows (the `hbot1` `Or.inr` "FIRST endpoint `= v`" branch, lines 1772–1774) — these reconstruct the `(a,b)`-fill rows that make the bottom full-rank (= §(4.62), re-confirmed: the bottom IS `R(G−v)`-deficient + the a-shifted `e_b` fill, NOT a literal full-rank `R(Gab)` block). So `C = toBlocks₂₁ ≠ 0` and the operated `hA` needs `ρ₀ ∈ span(opaque blockBasisOn(e_b))` = the §(4.65) `hred`. CONFIRMED. **The §(4.68) verdict is sound.**
- **§(4.29) gate invariant — CONFIRMED, and now EXPLAINED (it is KT's 6.67).** Re-verified the gate is `ρ₀ ⊥̸ C(vᵢ₊₁,n')`: the discriminator's `hgate` (`Realization.lean:1535`) and the wall lemma `funLeft_dualMap_pmR_group_mem_span_caseIIICandidate` (`Chain.lean:512`, the `Q2 fails` of route-4-splitOff) both pivot on it. §(4.69.2) gives the why: it is KT's union-dimension obstruction (6.67) re-surfacing where the override forces transport-into-candidate-span. The "6+ walled routes" (A/B/4-bare/4-splitOff/`hred`/both-αD-arms) are all the SAME `caseIIICandidate`-override gate — CONFIRMED, and the recurring-wall heuristic is correct: the obstruction is in the shared downstream object, **and that object is precisely the `caseIIICandidate`-override cert (the corner+bottom *transport-into-candidate-span* split), not the corner+bottom split per se.** This is the key refinement of the §(4.68) "replace the split" hint: it is not the *block-additivity* split that must go (that is KT-faithful and landed); it is the *transport-into-the-overridden-candidate-span* requirement.
- **§(4.21) "KT uses whole-matrix block-additivity with the member moving" — CONFIRMED verbatim against KT's text** (§(4.69.1); eqs. 6.49–6.67 quoted). KT's bottom IS the literal full-rank IH matrix; the project's is NOT — that is the divergence, not a misreading.

### (4.69.4) PATH COMPARISON — each escape mapped to KT, rated for faithfulness + genuine feasibility, with the §(4.29)-gate analysis (the make-or-break).

**(α1) wall-free `W`-producer for the dual-space chain arm.**
- *KT-faithfulness:* MEDIUM-LOW. The chain cert `case_III_rank_certification_chain` IS the cleanest dual-space image of KT's (6.64)/(6.65) (corner mod bottom, `finrank W + |ι| ≤ …`). But the `W`-producer it needs (transport the IH bottom into `span(candidate.rigidityRows)`) is the project's override-transport device, which KT does not have.
- *Feasibility:* BLOCKED. The wall lemma `funLeft_dualMap_pmR_group_mem_span_caseIIICandidate` (`Chain.lean:512`) PROVES the wrap-edge row's transport hits the gate. §(4.27)–(4.29) ruled all then-tried producers (LEAF-B2 `hS`, route-4-bare `hseedrank`, route-4-splitOff `hWS`) walled; a NEW producer must dodge the §(4.29) invariant, "possibly a real new-math wall" (≥ the §(4.18)–(4.30) arc that already failed across 5+ passes).
- *Gate-escape:* NO. It works WITHIN `span(candidate.rigidityRows)`, so the override-meets-gate collision is unavoidable. **Does not escape the gate.**
- *Reuse/tear-out:* reuses everything (chain cert/arm landed); needs only the `W`-producer — but that IS the wall. Tears out nothing; builds the one thing that cannot be built.

**(α2) `ρ₀`-aligned `±r` corner for the `_aug` literal-`Matrix` arm.**
- *KT-faithfulness:* LOW-MEDIUM. The `_aug` matrix's `inr ()` row genuinely reads `±ρ₀` (KT's `r` carried `±r` across panels, eq. 6.66 — faithful at the corner row). But the bottom is the same `mixedBottom` = `R(G−v)`+fill, and the row op `Lrow` (forced by `B ≠ 0`) re-couples the corner to the opaque `e_b` block.
- *Feasibility:* BLOCKED as stated. §(4.68.B): the operated `hA` needs `ρ₀ ∈ span(blockBasisOn(e_b) pin reads)` = the §(4.65)-refuted `hred` (`blockBasisOn` is an opaque `finBasisOfFinrankEq`; `ρ₀ ∈ hingeRowBlock e₀ ≠ hingeRowBlock e_b`). A sign flip only re-targets to `−ρ₀`, same demand. **Escaping requires a cert-row-family / corner-construction change** that makes the off-`v` `B` block zeroable WITHOUT pulling in the `e_b`-block pin content — i.e. removing the mandatory v-incident `e_b`-fill from the bottom, which §(4.62) proved breaks the full-rank count (`hrank` becomes unreachable). So (α2) is feasible only via a deeper change that overlaps (C)/fresh.
- *Gate-escape:* PARTIAL — the `_zero₁₂` cert escapes the `hρGv` GATE (that is why it was chosen over the d=3 engine, §(4.49)), but it hits the OPAQUE-BASIS obstruction instead (`blockBasisOn` opacity at `hred`), which is the same gate wearing a different mask (the bottom row that must host `ρ₀` is the overridden `e_b` block). **Does not fully escape.**
- *Reuse/tear-out:* reuses the αE1–αE4 `_aug` ladder (landed); needs a new bottom construction. Overlaps (C).

**(C)/FRESH — the bottom is the LITERAL full-rank IH framework's rigidity rows (KT's `R(G₁,q₁)` as a sub-family), no override-transport.**
- *KT-faithfulness:* HIGHEST. This is KT's actual (6.61)/(6.64) structure: the bottom block IS `R(G₁,q₁)` (the IH full-rank realization, available as `hsplitGP` / D1 `interior_hsplitGP`), whose rows are literal rows of the target matrix — NOT transported into an overridden span. The corner is the two chain-edge rows (the `Mᵢ` `D×D` block). The block additivity is the LANDED `rank_fromBlocks_zero₁₂_ge_of_linearIndependent_rows` (KT 6.65) or `finrank_span_rigidityRows_ge_of_corner` (its dual twin).
- *Feasibility:* the cert backbone + block-additivity + realization tail are ALL reusable; the genuinely-new piece is **a block-additivity statement over a UNION of TWO frameworks' rows** (the candidate framework supplies the corner `Mᵢ` rows; the IH framework `Q_{Gab}` supplies the bottom `R(G₁,q₁)` rows) rather than ONE framework's span. Concretely: the target is `finrank(span (corner_rows ∪ bottom_rows)) ≥ D + D(|V|−2)` where corner_rows ⊆ candidate.rigidityRows and bottom_rows = `Q_{Gab}.rigidityRows` (a DIFFERENT framework). The realization tail wants `hrank` about `span(candidate.rigidityRows)` SPECIFICALLY (W6e re-extracts a panel-row family from it, `Arms.lean:155`), so the new cert must show the candidate span CONTAINS both families — which is the same transport wall UNLESS the cert is restructured so the bottom rows need only be IN-SPAN-via-a-row-correspondence (KT's 6.62) rather than literally relabel-transported. **This is the genuinely-new-math cut**, and it is where (C) earns its "fundamentally different" label: model KT's (6.61) column op + (6.62) row correspondence as a LITERAL `Matrix` containment (`R(G₁,q₁)` is a column-/row-submatrix of the operated `R(G,pᵢ)` after the explicit invertible column op), NOT as a span membership in the candidate framework. The §(4.30) route-A scoping already identified this ("KT's (6.61) submatrix-containment is a structural EQUALITY after an explicit invertible column op, NOT a span membership — the override-meets-gate collision never forms") and rated it "genuinely-different + feasible, but HEAVY (≈9–14 leaves A1–A6)". §(4.33) then found route-A's `_zero₂₁` cert SHAPE wrong (the surplus pure-`v` rows break `toBlocks₂₁=0`) and reshaped to the row-SUBMATRIX `_zero₁₂` — which is the LANDED backbone. **What was NOT done:** make the bottom block the literal `R(G₁,q₁) = R(G.splitOff …)` matrix (full rank by IH) instead of the `mixedBottom` reconstruction — that is the un-taken (C)/fresh core.
- *Gate-escape:* YES (the only one that does). If the bottom is the literal IH matrix block via KT's column-op/row-correspondence (a `Matrix` EQUALITY, `rank_mul_eq_*_of_isUnit_det`), the bottom rows are NEVER required to be in `span(candidate.rigidityRows)` — the override-meets-gate collision never forms (§(4.30)'s own diagnosis). **This is structurally the only direction that dissolves the wall.**
- *Reuse/tear-out:* REUSES — the `Rank.lean:480/574` backbones, `case_III_realization_of_rank` (`Arms.lean:63`, consumes only `hrank`), D1 `interior_hsplitGP` (the IH full-rank `R(Gab)`), the discriminator (the moving-member pick), `rigidityMatrixEdge` + the column op `U` + `rank_of_coordEquiv`. TEARS OUT — the `mixedBottom`/`R(G−v)`+fill bottom apparatus, the `bottomRelabel`/transport-into-candidate-span chain (`Chain.lean`), the `_aug` ladder, the chain arm's `W`-producer. The realization tail's W6e re-extraction (`Arms.lean:155`) is the one HARD coupling: it wants `hrank` about `span(candidate.rigidityRows)` — so (C) must EITHER prove `span(candidate.rigidityRows) ⊇` both families (recreating part of the transport) OR re-state W6e to consume the union-span rank. This is the load-bearing feasibility question (C) leaves open.

**FRESH path beyond (α1)/(α2)/(C)?** The cleanest framing is (C) sharpened: **"literal-`R(G₁,q₁)`-bottom block-additivity cert."** No other independent direction surfaced — every route either works inside `span(candidate.rigidityRows)` (→ the gate) or replaces the bottom with the literal IH matrix (→ (C)). The d=3 green path is NOT a fresh option for general d: it discharges `hρGv` only because `shiftPerm 2` is a single swap (§(4.20)), which does not generalize (`shiftPerm i` for `i ≥ 3` provably MOVES `vtx2 ↦ vtx1`, §(4.20)/(4.24)).

**Locating "§I.8.21(α) matrix-level block-rank infra".** It refers to the `Rank.lean` block-rank-additivity backbones — `rank_ge_of_isUnit_mul_submatrix_fromBlocks` (`:480`, `fromBlocks A B 0 D`), `rank_ge_of_isUnit_mul_submatrix_fromBlocks_zero₁₂` (`:574`, `fromBlocks A 0 C D`), and `rank_fromBlocks_zero₁₂_ge_of_linearIndependent_rows` — **ALL LANDED in tree** (Phase 23d/23e), axiom-clean. So the "§I.8.21(α) matrix-level block-rank infra" the §(4.21) recommendation named EXISTS. What does NOT exist is a cert wiring that feeds those backbones a `hblock` whose bottom `[C D]` is the literal `R(Gab)` IH matrix (every landed wiring feeds the `mixedBottom`/`R(G−v)`+fill bottom, which forces the `e_b`-block coupling).

### (4.69.5) RECOMMENDATION (cost de-emphasized; KT-faithfulness + genuine feasibility first).

**Closest to KT AND the only structural wall-escape: (C)/fresh — the literal-`R(G₁,q₁)`-bottom block-additivity cert.** Replace the `mixedBottom`/transport-into-candidate-span bottom with the literal full-rank IH framework's rigidity rows as the `[C D]` block (KT's actual (6.61)/(6.64)), via the LANDED `Rank.lean:480/574` backbones modelling KT's (6.61) column op as a unit-det right-multiply and (6.62) row correspondence as a literal `Matrix` submatrix containment. This is exactly KT §6.4.2 and is the one direction in which the §(4.29) gate provably never forms (§(4.30)/(4.69.4)). (α1) is BLOCKED (it IS the wall); (α2) is BLOCKED and its only escape overlaps (C). The "tear out the corner+bottom *transport* cert and rebuild on the literal IH-matrix bottom" the user put in scope is the right call — **but note it tears out the `mixedBottom`/`bottomRelabel`/`_aug`/chain-`W`-producer apparatus, NOT the block-additivity machinery (that is KT-faithful and stays) and NOT the discriminator (the moving-member pick stays) and NOT the realization tail (stays, modulo the W6e re-statement question).**

### (4.69.6) DECOMPOSITION — FLAGGED, NOT FORCED (clause ii). The recommended path needs a genuinely-new cert leaf; STOP for the user.

Per the task's decompose-only-if-buildable-without-a-new-math-wall clause, **the recommended (C)/fresh path is NOT decomposed here** — it crosses a genuinely-new-math leaf and a real open coupling, which the flag-don't-force discipline says to name and STOP on, not to manufacture a decomposition for:

1. **NEW-MATH LEAF — the literal-`R(G₁,q₁)`-as-bottom-submatrix bridge.** KT's (6.61)/(6.62): after the explicit invertible column op `U` (landed, `prodColumnOpEquiv`), the operated candidate matrix `R(G,pᵢ)*U` has `R(G₁,q₁)` (= `R(G.splitOff …)`, the IH framework's matrix) as a literal row-/column-submatrix block, with FULL ROW RANK by the IH (`hsplitGP`, `finrank(span Q_{Gab}.rigidityRows) = D(|V|−2)`). No landed leaf states this `Matrix`-level containment of the IH matrix in the operated candidate matrix — the landed `mixedBottom` route reconstructs the bottom from `R(G−v)`+a-shift-fill instead. This is the A3/A4-class "genuinely-new high-risk piece" §(4.30) flagged and §(4.33) confirmed the cert shape for, but the IH-matrix-as-bottom wiring was never built. **Risk: HIGH** — it is the crux of KT's whole §6.4.2, and the row correspondence (6.62) is non-trivial to realize as a `Matrix` index map (the cycle relabel `shiftPerm i` enters, but as a COLUMN reindex of a LITERAL matrix, not a dual-span transport — which is the point: a `Matrix.submatrix`/`reindex` is rank-preserving by `rank_reindex`, no span membership).

2. **W6e re-extraction coupling — VERIFIED BENIGN (reading (a) confirmed against the landed A2 bridge + the landed cert's own conclusion).** The realization tail's W6e re-extraction wants `hrank` about `span(candidate.rigidityRows)` specifically (`Arms.lean:155`, `exists_independent_panelRow_subfamily_of_le_finrank` at `F₀`). The literal-IH-bottom cert proves a bound on `rank R(candidate)` — but **the LANDED `_zero₁₂` cert (`Candidate.lean:2446`) ALREADY concludes `finrank(span candidate.rigidityRows) ≥ D(|V|−1)`** (verified at the signature), exactly W6e's input, and it does so via the A2 bridge `(rigidityMatrix Q).rank = finrank(span Q.rigidityRows)` (the `Matrix.rank_of_coordEquiv` family, `Concrete.lean:99/230`, LANDED). So whether `[C D]` is the `mixedBottom` reconstruction or a literal IH submatrix, the cert's CONCLUSION is still about `R(candidate)`'s rank = the candidate span finrank — the bottom being a literal submatrix does NOT change WHAT rank is bounded. **W6e is fed UNCHANGED; there is NO new W6e coupling for (C).** (This was the one place a "fresh cert needs a tail re-statement" risk could hide; it is closed by the A2 bridge being rank-route-agnostic. The ONE remaining open question is (3) — the bottom-block CONSTRUCTION, not the tail consumption.)

3. **FOUNDATIONAL-DEF question (FLAG): does the cert need a new `rigidityMatrixEdge`-style matrix carrying BOTH the candidate's overridden slot rows AND the IH framework's bottom rows in one index?** The landed `rigidityMatrixEdge` is one framework's matrix. KT's `R(G,pᵢ)` is one matrix whose rows are split (chain rows = corner, the rest = IH rows via 6.62). The project's candidate matrix `caseIIICandidate.rigidityMatrixEdge` already IS that one matrix (graph `G`, overridden slots) — so the question is whether its non-slot rows, after the column op, literally EQUAL the IH matrix `R(Gab)` rows (KT's 6.59 substitution `pᵢ(e)=q₁(e)`). At `t=0` the candidate's non-slot extensors agree with the seed `ofNormals G ends q` (`caseIIICandidate_supportExtensor_of_ne`), and the IH framework is `ofNormals Gab endsσ qσ` — so the non-slot rows agree up to the cycle relabel. Whether this is a `Matrix` EQUALITY (no transport) or still a relabel-transport is THE foundational question (C) must answer, and it determines whether (C) genuinely escapes the wall or relocates it. **This is the open decision for the user.**

**STOP — the open decision for the user.** The recommended path (C)/fresh is closest to KT and is the only structural wall-escape, but it needs (1) a new-math leaf (the IH-matrix-as-literal-bottom-submatrix bridge), gated on (3) a foundational question (is the non-slot row agreement a `Matrix` equality or a transport?). Per flag-don't-force, the agent does NOT manufacture an A1–A6 decomposition: the right next step is a **single compiler-checked feasibility spike** — does `(R(candidate)*U).submatrix (corner ⊕ bottom) en = fromBlocks Mᵢ 0 C R(Gab)` hold with `R(Gab)` the LITERAL IH matrix (full rank by `hsplitGP`), WITHOUT a relabel-transport span membership? — that settles (3) and hence whether (C) is the genuinely-different feasible path §(4.30) hoped or relocates the wall. **The user picks: (C)/fresh (recommended, recon-spike-first), or (α1) (re-attack the `W`-producer wall, lowest faithfulness, "possibly real new-math wall"), or (α2) (cert-row-family change, overlaps (C)).** No motive/IH/C.0–C.6 change is involved in ANY of them (the obstruction is below the contract; D1 + the discriminator + the realization tail + the block-additivity backbones are all reusable regardless).

### (4.69.7) THREE DESIGN-PASS CLAUSES — verdicts.
- **(i) verified against LANDED source + KT's actual text.** KT §6.4.1/§6.4.2 read end-to-end (pp.691–698, eqs. 6.44–6.67 quoted, not paraphrased); the §(4.68) both-blocked / §(4.29) gate-invariant / §(4.21) block-additivity claims re-verified at source (§(4.69.3)). Landed decls read at source: the cert backbones `rank_ge_of_isUnit_mul_submatrix_fromBlocks{,_zero₁₂}` + `rank_fromBlocks_zero₁₂_ge_of_linearIndependent_rows` (`Rank.lean:480/574`-region), `finrank_span_rigidityRows_ge_of_corner` (`Candidate.lean:1698`), the chain cert/arm (`Candidate.lean:2197`/`ForkedArm.lean:59`), the realization tail (`Arms.lean:63`, body read — consumes only `hrank` + does W6e re-extraction from `span F₀.rigidityRows`), the discriminator (`Realization.lean:1481`), `mixedBottom` (`Concrete.lean:1741`), the `hS`-producer `bottomRelabel_rigidityRows_mem_span_caseIIICandidate` (`ForkedArm.lean:956`, `hG_eb_cand` in-signature), `caseIIICandidate` (`Candidate.lean:940`), `HasGenericFullRankRealization` (`PanelHinge.lean:1035`).
- **(ii) FLAG-DON'T-FORCE — the headline.** The recommended (C)/fresh path crosses a genuinely-new-math cert leaf (the IH-matrix-as-literal-bottom bridge) gated on a foundational question (transport vs `Matrix` equality of the non-slot rows); per the task's clause, NOT decomposed — STOPPED with the open decision named (§(4.69.6)). No buildable A1–A6 manufactured. The §(4.68) "route α blocked on both faces" is re-confirmed, not overturned; this section ADDS the faithfulness diagnosis (the wall is the override-transport device, not the block-additivity split) and sharpens (C) into "literal-IH-bottom cert".
- **(iii) traced to GROUND.** Card target unchanged and consistent: `card m₁ + card m₂ = D + D·(|V(Gv)|−1) = D·(|V(G)|−1) ≤ (D−1)·|E(G)| = card p` (`Rank.lean` strict injection, `Realization.lean` `hVcard`/`hVone`). KT's blocks: corner `Mᵢ` is `D×D` (`r(Lᵢ)` = `D−1` rows + the `±r` row = `D`), bottom `R(G₁∖row,q₁)` is `D(|V|−2)`, sum `D(|V|−1)` (KT 6.65 arithmetic, matches the landed cert's `Nat.mul_succ` count). The block-rank lemma that EXISTS in tree (`rank_fromBlocks_zero₁₂_ge_of_linearIndependent_rows`) is exactly KT (6.65) as an inequality; the block-rank wiring that does NOT exist is the IH-matrix-as-`[C D]` bottom (the landed wiring feeds the `mixedBottom` reconstruction). `D = screwDim k = (k+2 choose 2)`, and the chain has length `d = k+1` (`ChainData.d_eq_kAdd`); the `d=3` floor is `k=2`, `D=6`, where the dispatch stays on the separate landed `_matrix`/M₃ engine (with the `hρGv` hypothesis, dischargeable only there via the single-swap `shiftPerm 2`, §(4.20)). The general-`d` INTERIOR arm (the blocked one) is `d ≥ 4`, `k ≥ 3`, `D ≥ 10`, with interior `2 ≤ i < d`; there `D−2 ≥ 8` surplus pure-`v` rows, so the §(4.33) cert-shape constraint (the surplus rows must NOT break `toBlocks₂₁=0`/`hD`) and the §(4.62) mandatory-`e_b`-fill (the bottom needs the v-incident fill to reach `card m₂`) both bind — which is precisely why the interior arm walls where the `d=3` floor does not.

---

## (4.70) THE COMPILER-CHECKED FEASIBILITY SPIKE for the §(4.69.6) foundational question — VERDICT: **(C) RELOCATES THE WALL.** The non-chain-row agreement is a SPAN-MEMBERSHIP transport, NOT a literal `Matrix` equality / rank-preserving reindex. STOP for user decision; (C)/fresh does NOT structurally dissolve the §(4.29) wall as §(4.30) hoped — it relocates it into the cert's bottom-block construction. (opus, 2026-06-27, kernel-checked spike `SpikeC.lean`, 3 probes, deleted before commit; tree clean, `d=3` fully green.)

**Scope.** This is the single make-or-break spike §(4.69.6) prescribed (the FLOOR; the (C) decomposition was the part to defer/flag if the verdict went the other way). It settles the one open foundational question gating escape (C): *after KT's invertible column op `U`, do the NON-CHAIN (`e ∉ {e_a, e_b}`) rows of the operated candidate matrix `rigidityMatrixEdge(F₀) * U` LITERALLY EQUAL — as a `Matrix`, via a rank-preserving submatrix/reindex, NO span membership — the rows of the literal IH matrix `R(Gab) = rigidityMatrixEdge(IH framework)`? Or is the agreement still a cycle-relabel / span-membership transport?* Per the §(4.69.6) dichotomy: a literal `Matrix` equality ⟹ (C) FEASIBLE (the override-meets-gate collision never forms; rank preserved by `rank_reindex`/`rank_submatrix`, no span membership); a residual span-membership transport ⟹ (C) RELOCATES THE WALL (STOP-for-user, not a build). **The kernel says the latter.**

### (4.70.1) THE SPIKE SETUP (the concrete objects, verified at LANDED source — clause (i)).

`SpikeC.lean` set up the §(4.69.6)-target objects and read three kernel residuals. The load-bearing decls (each re-read at source this pass, not trusted from §(4.69)'s prose):
- **The candidate framework** `caseIIICandidate G ends q e_c e_r n_u n' n_r t` (`Candidate.lean:940`): a `BodyHingeFramework` on graph `G` that OVERRIDES `supportExtensor` at exactly two slots (`Function.update … e_c (panelSupportExtensor n_u n') … e_r (panelSupportExtensor (n_u + t•n') n_r)`), keeping the seed `(ofNormals G ends q).toBodyHinge.supportExtensor` elsewhere. The non-slot agreement is `caseIIICandidate_supportExtensor_of_ne` (`Candidate.lean:983`, signature verified): at `e ≠ e_c, e ≠ e_r`, `(caseIIICandidate …).supportExtensor e = (ofNormals G ends q).toBodyHinge.supportExtensor e` (a `Function.update_of_ne ×2`, `t`-independent). **Verified:** the non-slot supports equal the SEED `ofNormals G ends q`'s — a framework on graph `G`, NOT on `Gab`.
- **The IH framework `R(Gab)`.** `interior_hsplitGP` (`Realization.lean:758`) concludes `HasGenericFullRankRealization k n (G.splitOff (vtx i.castSucc)(vtx i.succ)(vtx ⟨i−1⟩.castSucc) e₀)`. **PROBE 1 (`rfl`, sorry-free):** `HasGenericFullRankRealization k n Gab` unfolds DEFINITIONALLY to `∃ Q : PanelHingeFramework k α β, Q.graph = Gab ∧ Q.IsGeneralPosition ∧ (finrank ℝ (span ℝ Q.toBodyHinge.rigidityRows) = D·(|V(Gab)|−1) − def) ∧ (link-recording) ∧ AlgebraicIndependent …` (`PanelHinge.lean:1035`). **So the IH hands an EXISTENTIAL, OPAQUE framework `Q` plus a FINRANK-OF-SPAN fact — there is NO literal `R(Gab)` matrix object to reindex against.** `Q`'s `ends`, `normal`/`q`, `supportExtensor`, and (crucially) its `blockBasisOn` are all `∃`-chosen by the IH, with NO definitional/term relation to the candidate `F₀`'s. The `Matrix` `R(Gab) = Q.toBodyHinge.rigidityMatrixEdge` is built from `Q.blockBasisOn` — a SEPARATE opaque `finBasisOfFinrankEq`.
- **The column op `U`** = `(LinearMap.toMatrix' (prodColumnOpEquiv (columnOp hva).symm).toLinearMap)ᵀ` (`Concrete.lean:1259`/`1274`; `IsUnit U.det` by `prodColumnOpEquiv_transpose_toMatrix'_det_isUnit`). Confirmed: this is the landed `_zero₁₂` backbone's column op (`Rank.lean:574` region; the recon's "`prodColumnOpEquiv`").
- **The operated non-chain block, AT SOURCE.** `submatrix_columnOp_toBlocks₂₂_eq_mixedBottom` (`Concrete.lean:1741`, signature + body verified) proves the operated bottom block `((F₀.rigidityMatrixEdge ends hgp * U).submatrix re (columnSplit v).symm).toBlocks₂₂` equals `Matrix.of (fun i x ↦ hingeRow (if (ends …).1 = v then a else …) (ends …).2 (F₀.blockBasisOn hgp (re …).1.2 (re …).2) (Pi.single x.1 (finScrewBasis x.2)))` — i.e. the `a`-shifted `hingeRow` reads built from **`F₀`'s OWN block basis `F₀.blockBasisOn`** (`Concrete.lean:510`, `= Module.finBasisOfFinrankEq ℝ (F₀.hingeRowBlock e) …`, an OPAQUE `Classical.choice`-derived basis). The cycle relabel `shiftPerm i` (`Operations.lean:1575`) enters only through the candidate-`i` selector/seed `qρ := q ∘ shiftPerm i.castSucc` upstream, not the matrix read here.

### (4.70.2) THE THREE KERNEL RESIDUALS (clause (ii) — the residual you cannot close IS the verdict; reported, not forced).

- **PROBE 1 — `rfl`, CLOSED.** `HasGenericFullRankRealization k n Gab = (∃ Q, … finrank (span Q.rigidityRows) = …)`. Verdict: the IH is a finrank-of-span statement on an existential opaque `Q`, not a `Matrix`. **There is no literal `R(Gab)` matrix; "reindex the operated candidate's rows into `R(Gab)`" has no target object.** To USE `Q`'s full rank you go through `finrank (span Q.rigidityRows)` — a span statement — which is the span-membership route, not a `Matrix` reindex.
- **PROBE 2a — `rfl` FAILS (kernel-confirmed via `lean_multi_attempt`). THE MAKE-OR-BREAK.** Stated the minimal Matrix-row-equality prerequisite: for two frameworks `F₁, F₂` agreeing on an edge's support extensor (`hsupp : F₁.supportExtensor e₁ = F₂.supportExtensor e₂`, so the hinge-row BLOCKS are the same submodule up to that equality), is `(F₁.blockBasisOn hgp₁ he₁ j : Dual ℝ (ScrewSpace k)) = (F₂.blockBasisOn hgp₂ he₂ j : …)`? **Kernel residual, verbatim:**
  ```
  ⊢ ↑((finBasisOfFinrankEq ℝ ↥(F₁.hingeRowBlock e₁) ⋯) j) = ↑((finBasisOfFinrankEq ℝ ↥(F₂.hingeRowBlock e₂) ⋯) j)
  ```
  `rfl` error, verbatim: *"The left-hand side ↑((F₁.blockBasisOn hgp₁ he₁) j) is not definitionally equal to the right-hand side ↑((F₂.blockBasisOn hgp₂ he₂) j)."* `simp [blockBasisOn]` and `unfold blockBasisOn; rfl` both leave the same irreducible `finBasisOfFinrankEq … = finBasisOfFinrankEq …` goal; `subst hsupp` fails (`hsupp` is not of subst shape — the two sides are reads of DISTINCT framework terms, not a variable). **Verdict: even at the BEST case (equal support extensors), the candidate's block basis and the IH framework's block basis are NOT defeq and not provably equal — they are two independent `Classical.choice` picks of two term-distinct submodules.** A literal `Matrix`-row equality `(operated F₀ block) row = R(Gab) row` REDUCES to exactly this `blockBasisOn`-equality (the operated block reads `F₀.blockBasisOn`; `R(Gab) = Q.rigidityMatrixEdge` reads `Q.blockBasisOn`), so it is UNAVAILABLE.
- **PROBE 3 — sorry-free, CLOSED (the only available bridge IS a transport).** The LANDED `hingeRow_blockBasisOn_mem_rigidityRows_of_supportExtensor_eq` (`Concrete.lean:701`) carries the operated-block read INTO the IH framework: `hingeRow u w (F₁.blockBasisOn hgp₁ he₁ j) ∈ F₂.rigidityRows` from `hlink : F₂.graph.IsLink e₂ u w` + `hsupp`. **This conclusion is a SET MEMBERSHIP (`∈ F₂.rigidityRows`) — a span/transport, NOT a `Matrix`-row equality.** It is the project's ONLY landed bridge between the operated candidate block and the IH framework, and it is precisely a transport. Built sorry-free in one line from `(F₁.blockBasisOn …).property` (the basis vector lies in the block submodule, which equals `F₂`'s block by `hsupp`) — confirming the transport route is the available one.

**Corroborating LANDED source (clause i, not a probe):** `rank_columnOp_toBlocks₂₂_eq_finrank_span_mixedBottom` (`Concrete.lean:1799`) — the lemma the cert actually USES for the bottom block — equates the operated block's `Matrix.rank` to `finrank (span (range (a-shifted F₀.blockBasisOn functionals)))`, a SPAN FINRANK. Its own docstring states it explicitly (`Concrete.lean:1786`): *"the matrix-equality form is BLOCKED on un-provable equal chosen basis vectors — notes/Phase23d.md."* The project ALREADY took the finrank-of-span (transport) route here in Phase 23d precisely because the literal-`Matrix`-equality form (`submatrix_columnOp_toBlocks₂₂_eq_Gab`, the §(4.69.6) target) is blocked. PROBE 2a re-confirms the block is `blockBasisOn`-defeq-failure, at the kernel.

### (4.70.3) THE VERDICT — (C) RELOCATES THE WALL (not "feasible").

**The §(4.69.6) foundational question is answered: the non-chain-row agreement is a SPAN-MEMBERSHIP / cycle-relabel TRANSPORT, NOT a `Matrix` equality / rank-preserving reindex.** Therefore, per the §(4.69.6) dichotomy, **escape (C)/fresh RELOCATES the wall — it does NOT structurally dissolve it.** The precise relocation: (C) tears out the `mixedBottom`/`bottomRelabel`/transport-into-candidate-span apparatus and tries to make the bottom `[C D]` block the LITERAL IH matrix `R(Gab)`. But `R(Gab)` is not a fixed object the IH hands over (PROBE 1) — it is an existential opaque framework's rigidity-row span — and to identify the operated candidate's non-chain rows WITH that framework's rows you need either (a) a literal `Matrix` row equality, which PROBE 2a kernel-refutes (the two `blockBasisOn` opaque bases are not defeq even with equal support extensors), or (b) the landed transport bridge (PROBE 3), which is a `∈ rigidityRows` SPAN MEMBERSHIP — exactly the `W ≤ span(candidate.rigidityRows)` shape (`hWS`) whose discharge re-hits the §(4.29) gate `ρ₀ ⊥̸ C(vᵢ₊₁, n')` (the override-meets-gate collision, §(4.69.2)). **So §(4.30)'s hope — "KT's (6.61) submatrix-containment is a structural EQUALITY after an explicit invertible column op, NOT a span membership; the override-meets-gate collision never forms" — does NOT hold at the kernel for the project's `caseIIICandidate`-with-opaque-`blockBasisOn` model.** The "structural equality" KT enjoys (eq. 6.61: the bottom rows ARE rows of `R(G,pᵢ)` because `pᵢ(e) = q₁(e)` on common edges makes them the SAME vectors) relies on the IH framework and the candidate framework SHARING the SAME concrete normals/extensors AND the SAME basis of each hinge block. The project's two frameworks share the support EXTENSOR (via `caseIIICandidate_supportExtensor_of_ne` at `t=0`, hence the same hinge-row block SUBMODULE), but NOT the same chosen BASIS of that block (`finBasisOfFinrankEq` is non-canonical), and the IH framework is `∃`-opaque — so KT's "same vectors" becomes the project's "same submodule, transported via span membership," which is the wall.

**This is a STOP-for-user outcome, per the §(4.69.6)/task flag-don't-force clause — NOT a build.** (C)/fresh is not the genuinely-different feasible path §(4.30) hoped; it is the SAME §(4.29) wall, relocated from the `mixedBottom` transport into the literal-IH-bottom identification. No (C) A1–A6 decomposition is manufactured (there is no buildable leaf — the foundational identification is blocked). **All three named escapes now have a verdict:** (α1) BLOCKED (it IS the wall, §(4.69.4)); (α2) BLOCKED (its only escape overlaps (C), §(4.69.4)); **(C)/fresh RELOCATES THE WALL (this section).** What remains genuinely-different and unblocked is a path that does NOT exist among (α1)/(α2)/(C) as scoped: it would require either (1) making `blockBasisOn` a CANONICAL/shared basis so the two frameworks' block bases coincide (a foundational-def change to `blockBasisOn` — the `Concrete.lean:510` `finBasisOfFinrankEq` becomes a named, framework-independent basis of the hinge block keyed only on the support extensor), enabling the literal `Matrix` equality; or (2) re-architecting the candidate so its non-chain rows ARE literally the IH framework's rows (KT's 6.59 substitution `pᵢ(e) = q₁(e)`, which the override + the opaque-basis model does not currently realize — a deeper change to how `caseIIICandidate` relates to the split-off framework). **Both are foundational-def changes the task's flag-don't-force clause says to NAME for the user, not to build.**

### (4.70.4) THE OPEN DECISION FOR THE USER (the named foundational change).

Route α is blocked on both faces (§(4.68)); (C)/fresh relocates the wall (this section). The path that would genuinely escape — and the decision the user must adjudicate — is a **foundational-def change** below the cert, of one of two shapes:

- **(D-canonical) Make the hinge-block basis CANONICAL / framework-independent.** Replace `BodyHingeFramework.blockBasisOn` (`Concrete.lean:510`, the per-framework opaque `finBasisOfFinrankEq ℝ (F.hingeRowBlock e)`) with a basis keyed ONLY on the support extensor `F.supportExtensor e` (so two frameworks with equal support extensor get the LITERALLY SAME basis vectors). Then PROBE 2a's residual `F₁.blockBasisOn = F₂.blockBasisOn` becomes `rfl` (given `hsupp`), the operated candidate's non-chain block LITERALLY equals `R(Gab)`'s rows (a `Matrix` reindex, rank-preserving, no span membership), and (C)/fresh becomes the genuinely-different feasible path §(4.30) hoped. **Scope:** touches the `blockBasisOn` def + every consumer (the `_zero₁₂` cert chain reads `blockBasisOn` at every corner/`±r`/bottom row; the corner `hA` leaf (iii) `corner_hA_zero₁₂_of_gate`; the `mixedBottom`/`Gab`-bridge family). The hinge-row block `hingeRowBlock e = (span C(supportExtensor e))^⊥` (`Basic.lean:431`) already depends only on the support extensor, so a support-extensor-keyed basis is mathematically well-defined; the question is the Lean cost of re-keying a `finBasisOfFinrankEq` to a function of the extensor (likely via `Module.Basis.ofEquivOfFinrankEq` or a chosen basis stored per-extensor in a global table — a real foundational-def refactor, multi-commit, with re-state of the whole cert chain). **Risk: this is below the C.0–C.6 contract but it is a genuine foundational-def change** (the task's "needs a motive/IH/C.0–C.6/foundational-def change ⟹ FLAG it, name the decision, STOP" clause fires here).
- **(D-substitution) Re-architect `caseIIICandidate` to literally REUSE the split-off framework's rows.** Instead of overriding the seed `ofNormals G ends q`'s extensors at two slots, BUILD the candidate so its non-chain edges carry LITERALLY the IH framework `Q`'s support extensors + basis (KT's 6.59 `pᵢ(e) = q₁(e)`). Then the non-chain rows ARE `Q`'s rows by construction (no transport). **Scope:** this changes the candidate's DEFINITION to depend on the (existential, opaque) `Q` from the IH — which is awkward in Lean (the candidate currently is a closed-form `t`-family independent of `Q`; threading `Q` in is a motive/producer reshape). Likely HARDER than (D-canonical) and overlaps the C.3 `hIH`-consume reshape.

**Recommendation for the user (cost de-emphasized, as §(4.69) was):** if the project pursues general-`d` Case III at all, **(D-canonical)** is the cleaner of the two foundational changes — it is a localized refactor of ONE def (`blockBasisOn`) + its consumers, it makes the §(4.30) "structural equality after a column op" literally true at the kernel, and it dissolves the wall at its actual root (the non-canonical opaque basis) rather than relocating it. But it IS a foundational-def change and so is the user's call. **Until the user picks a foundational change, no general-`d` interior-arm cert leaf is buildable.** `d=3` stays fully green (zero-regression); the discriminator, the realization tail, D1 `interior_hsplitGP`, and the block-additivity backbones remain reusable under any choice.

### (4.70.5) THREE DESIGN-PASS CLAUSES — verdicts.
- **(i) verified against LANDED source.** Every load-bearing object re-read at source this pass (not trusted from §(4.69) prose): `caseIIICandidate` (`Candidate.lean:940`) + `caseIIICandidate_supportExtensor_of_ne` (`:983`, signature confirmed `e ≠ e_c, e ≠ e_r ⟹ = ofNormals seed`); `interior_hsplitGP` (`Realization.lean:758`, output `HasGenericFullRankRealization k n (G.splitOff …)`); `HasGenericFullRankRealization` (`PanelHinge.lean:1035`, the `∃ Q + finrank-of-span` def, PROBE-1-`rfl`-confirmed); `blockBasisOn` (`Concrete.lean:510`, opaque `finBasisOfFinrankEq`); the column op `prodColumnOpEquiv` (`Concrete.lean:1259`) + `U` (`:1274`); `submatrix_columnOp_toBlocks₂₂_eq_mixedBottom` (`:1741`, the operated block reads `F₀.blockBasisOn`); `rank_columnOp_toBlocks₂₂_eq_finrank_span_mixedBottom` (`:1799`, the finrank-of-span route + its "matrix-equality BLOCKED" docstring); the transport bridge `hingeRow_blockBasisOn_mem_rigidityRows_of_supportExtensor_eq` (`:701`, conclusion `∈ rigidityRows`); `shiftPerm` (`Operations.lean:1575`). The spike compiled (`Build completed successfully`, 2785 jobs) with only the intended `sorry` on PROBE 2a + a cosmetic long-line.
- **(ii) FLAG-DON'T-FORCE — the headline.** The kernel residual PROBE 2a (`blockBasisOn` defeq-failure) IS the verdict, reported verbatim, not papered over. The §(4.69.6) target (`Matrix` equality) is UNAVAILABLE at the kernel; (C)/fresh relocates the wall. No (C) A1–A6 decomposition manufactured — the foundational identification is blocked, so there is no buildable first leaf. The genuinely-different escape is a foundational-def change (D-canonical / D-substitution), NAMED for the user, STOPPED on — the task's "needs a foundational-def change ⟹ FLAG, name, STOP" clause fires exactly here. A pin that honestly names "(C) relocates the wall" beats a confident "feasible" that costs a dead rebuild.
- **(iii) traced to GROUND.** Card / rank targets re-confirmed consistent (unchanged from §(4.69.7)(iii)): `card m₁ + card m₂ = D + D(|V(Gab)|−1) = D(|V|−1) ≤ (D−1)|E|`; `R(Gab)` has the full rank `D(|V|−2)` the bottom needs (the IH's finrank-of-span fact, `HasGenericFullRankRealization`'s third conjunct at def `= D(|V(Gab)|−1) − def(Gab) = D(|V|−2)` since `Gab` is def-0 minimal-`k`-dof by `splitOff_isMinimalKDof`, `|V(Gab)| = |V|−1`). The row-index correspondence (KT 6.62) is a concrete `Fin`/edge-index map only on the MATRIX-SHAPE half (`submatrix_columnOp_toBlocks₂₂_eq_mixedBottom`'s `re`/`columnSplit`, both `Fin`/`Subtype` index maps) — but the PANEL-FUNCTIONAL half (which functional each row reads) is where the opaque-basis transport enters and the `Fin`-index correspondence does NOT suffice (PROBE 2a). `D = screwDim k = (k+2 choose 2)`; the blocked interior arm is `d ≥ 4`, `k ≥ 3`, `D ≥ 10`; `d=3`/`k=2`/`D=6` stays on the separate landed `_matrix`/M₃ engine, green.

---

## (4.71) THE (D-canonical) FEASIBILITY RECON + COMPILER-CHECKED SPIKE — VERDICT: **(D-canonical) is FEASIBLE; it genuinely UNBLOCKS escape (C).** A support-extensor-keyed canonical hinge-block basis makes the cross-framework basis-vector equality PROVABLE (`subst hsupp; rfl`) AND — the make-or-break — that equality TRANSPORTS across the `Matrix.of`/`hingeRow`/`Pi.single` boundary to the literal `Matrix`-row equality the (C) bottom block needs (the `submatrix_columnOp_toBlocks₂₂_eq_Gab`-style equality §(4.70) found BLOCKED under the opaque basis). Blast radius is CONTAINED (the def + its consumers live almost entirely in `Concrete.lean`; the change is a drop-in at the same signature/type, so every basis-interface consumer is unaffected; `d=3` is untouched). Plan below. (opus, 2026-06-27, kernel-checked spike `SpikeDCanonical.lean`, 4 probe groups + 1 negative control, **`Build completed successfully (2392 jobs)`**, deleted before commit; tree clean.)

> **Scope.** The FLOOR the task set: a compiler-checked feasibility verdict on the §(4.70.4) (D-canonical) re-keying — *does it make PROBE 2a provable, does that suffice to close the literal `Matrix`-row equality, and is the blast radius tractable?* All three are settled YES at the kernel. The full ordered refactor plan (§(4.71.4)) is delivered too — it fit the sitting because the blast radius turned out small. Supersedes §(4.70)'s "(C) relocates the wall" *for the (D-canonical)-augmented model*: §(4.70) is correct that (C) relocates the wall **under the opaque `blockBasisOn`**; (4.71) shows the relocation DISSOLVES once `blockBasisOn` is re-keyed.

### (4.71.1) THE SPIKE — the concrete objects (clause i: every claim verified against LANDED source, not §(4.70) prose).

`SpikeDCanonical.lean` (in `RigidityMatrix/`, `public import …RigidityMatrix.Concrete`) defined the proposed (D-canonical) machinery and read the kernel residuals. Load-bearing source facts, re-read this pass:
- **`hingeRowBlock` depends ONLY on the support extensor** — `Basic.lean:431`: `F.hingeRowBlock e = (Submodule.span ℝ {F.supportExtensor e}).dualAnnihilator`, with `F.supportExtensor e : ScrewSpace k` (NOT `Dual` — the span is in the primal `ScrewSpace`, the annihilator lands in `Dual ℝ (ScrewSpace k)`). So the block is a FUNCTION of the single extensor `s := F.supportExtensor e`. **Kernel-confirmed:** `example (F e) : F.hingeRowBlock e = canonBlock (F.supportExtensor e) := rfl` compiles, where `canonBlock s := (span ℝ {s}).dualAnnihilator`. The §(4.70.4)/§(4.30) premise ("the block already depends only on the extensor, so a support-extensor-keyed basis is well-defined") is CORRECT at the kernel. **`hingeRowBlock` itself does NOT need restating** — it is already extensor-keyed; only the BASIS (`blockBasisOn`) is per-framework.
- **`blockBasisOn` is the only non-canonical link** — `Concrete.lean:510`: `blockBasisOn F hgp he := finBasisOfFinrankEq ℝ (F.hingeRowBlock e) (F.finrank_hingeRowBlock (hgp e he))`, an opaque `Classical.choice`-derived basis of the (per-framework-typed) block submodule. Its sibling `blockBasis` (`Concrete.lean:170`, the total-`hgp` A1 variant) is the same shape.
- **The make-or-break target** — the (C) bottom-block obligation is `submatrix_columnOp_toBlocks₂₂_eq_Gab`-style: the operated candidate bottom block, whose entries are `hingeRow (a-shifted endpoints) (F₀.blockBasisOn … j) (Pi.single col.1 (finScrewBasis col.2))` (the exact RHS of the landed `submatrix_columnOp_toBlocks₂₂_eq_mixedBottom`, `Concrete.lean:1741`), must LITERALLY EQUAL the IH framework's matrix rows (reading the IH framework's own basis). §(4.70) PROBE 2a showed this reduces to `F₁.blockBasisOn = F₂.blockBasisOn`, defeq-FALSE under the opaque basis.

### (4.71.2) THE PROBES — what compiled, what each settles (clause ii: the residual you cannot close is the verdict; reported, not forced).

The spike built **`Build completed successfully (2392 jobs)`** with ONLY: two cosmetic long-line docstring warnings + one INTENDED `sorry` on the negative control `control_no_hsupp`. Every POSITIVE probe is sorry-free.

- **PROBE 1 — the canonical re-keying is well-defined (sorry-free).** `canonBlock (s : ScrewSpace k) := (span ℝ {s}).dualAnnihilator`; `canonBlock_finrank (s) (hs : s ≠ 0) : finrank ℝ (canonBlock s) = screwDim k − 1` (the `finrank_hingeRowBlock` proof inlined, `s`-keyed, framework-free); `canonBlockBasis (s) (hs : s ≠ 0) : Module.Basis (Fin (screwDim k − 1)) ℝ (canonBlock s)` (= `finBasisOfFinrankEq ℝ (canonBlock s) (canonBlock_finrank s hs)`). **The canonical extensor-keyed basis EXISTS, is well-typed, and has the right finrank.** The structural-cardinality invariant (clause iii) holds: `canonBlockBasis s hs` is a basis of the `(screwDim k − 1)`-dim block, finrank preserved exactly.
- **PROBE 2a — the cross-framework basis-vector equality is PROVABLE (sorry-free).** `canonBlockBasis_congr {s₁ s₂} (hs₁) (hs₂) (hsupp : s₁ = s₂) (j) : (canonBlockBasis s₁ hs₁ j : Dual …) = (canonBlockBasis s₂ hs₂ j : Dual …)` closes by **`subst hsupp; rfl`** (after `subst`, the two `hs` proofs are proof-irrelevant ⟹ `rfl`). The framework-level form `probe2a` (extensors `F₁.supportExtensor e₁` / `F₂.supportExtensor e₂`, NOT free variables) follows by feeding `hsupp` directly to `canonBlockBasis_congr` — **no `subst` of a non-variable needed; the congruence lemma absorbs that.** This is EXACTLY the §(4.70.4) (D-canonical) claim, kernel-confirmed.
  - **REFINEMENT of the §(4.70.4) "becomes `rfl`" wording (honest correction).** The cross-framework equality is NOT bare `rfl` — the **NEGATIVE CONTROL** `control_no_hsupp` (the same statement with FREE `s₁ s₂` and NO `hsupp`) FAILS `rfl` at the kernel (verbatim: *"↑((canonBlockBasis s₁ hs₁) j) is not definitionally equal to ↑((canonBlockBasis s₂ hs₂) j)"*), proving the spike is NON-DEGENERATE: the two bases are genuinely distinct until `hsupp` is supplied. So the precise statement is "**provable via a congruence lemma consuming `hsupp`**", not "definitionally equal". That distinction is what makes PROBE Q2 (below) the real make-or-break: a propositional equality must still be shown to TRANSPORT through the matrix wrapper.
- **PROBE Q2 — THE MAKE-OR-BREAK: the equality transports to a literal `Matrix` equality (sorry-free).** `modelRow [DecidableEq α] (u v) (s) (hs) (j) (col : α × Fin (finrank ℝ (ScrewSpace k))) := hingeRow u v (canonBlockBasis s hs j : Dual …) (Pi.single col.1 (finScrewBasis k col.2))` — the EXACT entry shape of `submatrix_columnOp_toBlocks₂₂_eq_mixedBottom`'s RHS and of `rigidityMatrixEdge`. Then `probeQ2 [DecidableEq α] (F₁ F₂) … (hsupp) (m) (jof) : Matrix.of (fun i col => modelRow … (F₁.supportExtensor e₁) hs₁ (jof i) col) = Matrix.of (fun i col => modelRow … (F₂.supportExtensor e₂) hs₂ (jof i) col)` closes by `ext i col; simp only [Matrix.of_apply, modelRow]; rw [canonBlockBasis_congr hs₁ hs₂ hsupp (jof i)]`. **Kernel-verified the intermediate goal:** after `simp only [Matrix.of_apply, modelRow]` the goal is the bare entrywise `(hingeRow u v ↑(canonBlockBasis (F₁.supportExtensor e₁) hs₁ (jof i))) (Pi.single …) = (hingeRow u v ↑(canonBlockBasis (F₂.supportExtensor e₂) hs₂ (jof i))) (Pi.single …)` — `simp` does NOT close it on its own; the `rw [canonBlockBasis_congr …]` is what fires. **So the propositional basis equality DOES transport INSIDE the `hingeRow`/`Pi.single`/`Matrix.of` wrapper to a literal `Matrix`(-entry) equality — the §(4.70.4) feared "basis equality that holds only up to a rewrite that then CANNOT be transported across the `Matrix.of`/`submatrix` boundary" does NOT materialize.** The function-level form `probeQ2_fun` is even cleaner (`subst hsupp; rfl` on the whole `modelRow` family) — so any `Matrix.of` / `.submatrix` / `.reindex` built from these rows is equal by `congrArg`, and the `Matrix.rank` is preserved by `rank_reindex`/`rank_submatrix`, no span membership.
- **PROBE 4 — the re-keyed `blockBasisOn` is a literal DROP-IN (sorry-free).** `blockBasisOn_recanon F hgp {e} he := canonBlockBasis (F.supportExtensor e) (hgp e he) : Module.Basis (Fin (screwDim k − 1)) ℝ (F.hingeRowBlock e)` — **the EXACT same signature `(hgp) {e} (he)` and return type as the landed `blockBasisOn`** (the return type matches because `F.hingeRowBlock e` is defeq to `canonBlock (F.supportExtensor e)`, PROBE 1). And `blockBasisOn_recanon_congr` gives the framework-level cross-framework equality the cert leaf consumes, off the drop-in def. So the def swap is type-transparent at every callsite.

### (4.71.3) BLAST-RADIUS SCOPE (clause iii: traced to ground) — CONTAINED.

**Reader survey (grep, whole tree).**
- **`blockBasisOn` is read in CODE in exactly ONE file: `Concrete.lean`** (79 occurrences, mix of code + doc). The other three files that mention it — `Candidate.lean` (2), `ForkedArm.lean` (1), `Basic.lean` (5) — are **docstring/comment mentions only** (verified line-by-line: no `F.blockBasisOn` code application outside `Concrete.lean`). Its sibling `blockBasis` (the A1 total-`hgp` variant) is read in CODE only in `Concrete.lean` too (26 occurrences).
- **`hingeRowBlock` is read widely (18 files)** — BUT the (D-canonical) change does **NOT** touch `hingeRowBlock` (it is already extensor-keyed, PROBE 1). So all 18 `hingeRowBlock` readers are **UNAFFECTED**.
- **No proof depends on `blockBasisOn`/`blockBasis`'s internal `finBasisOfFinrankEq` construction.** Grep for `unfold blockBasis*` / `simp [blockBasis*]` / `rw [… blockBasis*]` / a direct `finBasisOfFinrankEq` pattern-match outside the two def sites: **ZERO hits.** Every consumer uses only the BASIS INTERFACE — `.linearIndependent_coe_subtype`, `.span_coe_eq`, `.repr`, `.sum_repr`, `.property`, and the coerced functional fed to `hingeRow`. All of these hold for ANY basis of `F.hingeRowBlock e`, so the re-keyed def is a behavior-preserving drop-in at every callsite.

**Consumer classification (the `Concrete.lean` code readers):**
- *(mechanical / unaffected)* — every existing `blockBasisOn`/`blockBasis` consumer: the `linearIndependent_blockBasisOn_screwDual` (`:528`), `exists_corner_blockBasisOn_linearIndependent` (3a/3b, `:566`), `rigidityMatrix`/`rigidityMatrixEdge`/`rigidityRowFun(Edge)` defs (`:168`–`:540`), the A2 rank bridges, `submatrix_columnOp_toBlocks₂₂_eq_mixedBottom` (`:1741`), `rank_columnOp_toBlocks₂₂_eq_finrank_span_mixedBottom` (`:1799`), the `Gab`-bridge family `hingeRow_blockBasisOn_mem_rigidityRows_of_supportExtensor_eq` (`:701`). They consume the basis interface ⟹ recompile unchanged after the def swap (no statement change, no proof change expected).
- *(genuinely-affected, the WORK)* — only the cert-leaf side: (a) the def swap itself (`blockBasisOn` + `blockBasis` → `canonBlockBasis`-backed, `Concrete.lean`), (b) the NEW cross-framework congruence lemma (`blockBasisOn_congr` / `blockBasis_congr`, ~2 lines each, PROBE 2a), (c) the NEW (C) cert leaf — the literal `Matrix` equality `submatrix_columnOp_toBlocks₂₂_eq_Gab` (the §(4.70)-blocked target, now provable via PROBE Q2's transport: rewrite the operated bottom block to read the IH framework's rows via `blockBasisOn_congr` under the `hsupp` from `caseIIICandidate_supportExtensor_of_ne` at `t=0`), then the `_zero₁₂` cert fed the literal-IH bottom instead of the `mixedBottom` reconstruction.
- *(unaffected — HARD CONSTRAINTS confirmed)* — **`d=3` zero-regression: the d=3 dispatch (`Realization.lean`) reads `blockBasisOn`/`blockBasis` ZERO times in code** (grep-confirmed), and the `_matrix`/M₃ engine consumes the same basis interface as everything else, so the def swap leaves it green. **C.0–C.6 contract / motive / IH: UNTOUCHED** — `blockBasisOn` is below the cert (`Concrete.lean`, the matrix layer); the C.3 `hIH` add (§(4.43), already adjudicated) is orthogonal. The cert card target is UNCHANGED: `card m₁ + card m₂ = D·(|V|−1) ≤ (D−1)|E|`, and the bottom `R(Gab)` still has finrank `D(|V|−2)` (the IH fact, unchanged by the basis re-keying).

**Commit estimate: ~4–7 commits.** (1) the def swap + `canonBlockBasis` machinery + the two `_congr` lemmas (1 commit, `Concrete.lean`; expect a green recompile of all interface consumers — if any callsite breaks it is a missing interface lemma, mechanical); (2) the literal-`Matrix` (C) bottom bridge `submatrix_columnOp_toBlocks₂₂_eq_Gab` (1–2 commits, `Concrete.lean`, the genuinely-new but now-kernel-feasible leaf); (3) the (C) cert leaf wiring (`case_III_rank_certification_*` fed the literal IH bottom) + the arm spine (1–2 commits, `Candidate.lean`/`ForkedArm.lean`); (4) the dispatch + CHAIN-5 (the §(4.43)/(4.71.4) item, 1 commit). This connects to the §(4.30)/(4.33) (C) "A1–A6" scoping: A1–A5c (the matrix model + column op + block-additivity backbones) are ALL LANDED and reused; the only NEW work is A6's bottom-block being the literal IH submatrix (the un-taken (C) core, now feasible).

### (4.71.4) THE ORDERED REFACTOR PLAN (the part to defer if it had not fit — it did; signatures kernel-anchored from the spike).

1. **D-CAN-1 — `Concrete.lean`: the canonical basis + def swap.** Add `canonBlock (s : ScrewSpace k) : Submodule ℝ (Dual ℝ (ScrewSpace k))`, `canonBlock_finrank (s) (hs : s ≠ 0)`, `canonBlockBasis (s) (hs : s ≠ 0) : Module.Basis (Fin (screwDim k − 1)) ℝ (canonBlock s)` (all kernel-built in the spike). Redefine `blockBasisOn F hgp he := canonBlockBasis (F.supportExtensor e) (hgp e he)` and `blockBasis F hgp e := canonBlockBasis (F.supportExtensor e) (hgp e)` (drop-in, PROBE 4). Add `blockBasisOn_congr` / `blockBasis_congr` (the cross-framework equality, PROBE 2a body `subst …; rfl` lifted through `canonBlockBasis_congr`). **Gate: full `lake build` green** — every interface consumer should recompile unchanged; investigate ANY break as a missing interface lemma (do not unfold the new def in a consumer).
2. **D-CAN-2 — `Concrete.lean`: the literal-`Matrix` (C) bottom bridge.** State `submatrix_columnOp_toBlocks₂₂_eq_Gab` (the §(4.70)-blocked, now-feasible target): the operated candidate bottom block EQUALS `Matrix.of` of the IH framework `Q`'s `a`-shifted rows, as a literal `Matrix` (no span membership). Proof: `submatrix_columnOp_toBlocks₂₂_eq_mixedBottom` (landed) to get the candidate-basis form, then `blockBasisOn_congr` (D-CAN-1) entrywise under `hsupp` (the candidate↔`Q` support-extensor agreement — from `caseIIICandidate_supportExtensor_of_ne` at `t=0` for the non-slot rows, the same `hsupp` the landed transport bridge `:701` already consumes). PROBE Q2 is the kernel proof-of-concept for the transport step.
3. **D-CAN-3 — `Candidate.lean`/`ForkedArm.lean`: the (C) cert leaf + arm.** Feed the `_zero₁₂` cert backbone (`Rank.lean:622`, landed) the literal IH bottom `[C D]` (via D-CAN-2) instead of the `mixedBottom` reconstruction; the bottom is then full-rank by `rank_reindex` of `R(Gab)` (the IH `hsplitGP` finrank fact), NOT a span-membership transport — so the §(4.29) gate `ρ₀ ⊥̸ C(vᵢ₊₁,n')` never forms (the wall dissolves, §(4.30)'s hope realized). Reuse the realization tail `case_III_realization_of_rank` UNCHANGED (its W6e input is `finrank (span F₀.rigidityRows) ≥ D(|V|−1)`, the cert's conclusion regardless of bottom shape — §(4.69.6)(2), VERIFIED-BENIGN, still holds).
4. **D-CAN-4 — the dispatch + CHAIN-5** (the §(4.43) item, unchanged by D-canonical): the `Fin cd.d` router (base/`d=3` → landed `chainData_split_realization`; interior `2 ≤ i` → the D-CAN-3 arm), the C.3 `hIH`-on-consume-shape one-field add, the `d=3` zero-regression adapter. Then ENTRY (23g) + ASSEMBLY (23h).

### (4.71.5) THREE DESIGN-PASS CLAUSES — verdicts.
- **(i) verified against LANDED source.** Every load-bearing object re-read at source this pass (not trusted from §(4.70) prose): `hingeRowBlock` (`Basic.lean:431`, extensor-keyed, `rfl`-confirmed `= canonBlock (supportExtensor e)`); `blockBasisOn` (`Concrete.lean:510`) + `blockBasis` (`:170`) + `finrank_hingeRowBlock` (`Basic.lean:1138`); `hingeRow` (`Basic.lean:490`, in `namespace BodyHingeFramework`); `submatrix_columnOp_toBlocks₂₂_eq_mixedBottom` (`:1741`, the entry shape `modelRow` mirrors); `rank_columnOp_toBlocks₂₂_eq_finrank_span_mixedBottom` (`:1799`); the transport bridge `:701`; `caseIIICandidate_supportExtensor_of_ne` (`Candidate.lean:983`). The reader survey is grep-over-tree (whole `Molecular/`). The spike `Build completed successfully (2392 jobs)`.
- **(ii) FLAG-DON'T-FORCE — applied as VERDICT-FEASIBLE, not forced.** The make-or-break (PROBE Q2: does the basis equality transport across the `Matrix.of`/`submatrix` boundary?) is answered YES at the kernel — the spike's `rw [canonBlockBasis_congr …]` fires inside the `hingeRow`/`Pi.single` wrapper, kernel-verified on the intermediate goal. So (D-canonical) is reported FEASIBLE, with an ordered plan whose only genuinely-new leaf (D-CAN-2, `submatrix_columnOp_toBlocks₂₂_eq_Gab`) is kernel-de-risked by PROBE Q2. The §(4.70.4) "becomes `rfl`" claim is HONESTLY REFINED to "provable via a `hsupp`-consuming congruence lemma" (the negative control proves it is not bare-`rfl`) — the refinement does not weaken the verdict (the congruence transports). NO decomposition is manufactured beyond what the kernel justifies: A1–A5c are landed-and-reused; D-CAN-1/3/4 are interface-preserving wiring; only D-CAN-2 is new, and it is the spike's proof-of-concept.
- **(iii) traced to GROUND.** Structural-cardinality invariants preserved: `canonBlockBasis s hs` is a basis of the `(screwDim k − 1)`-dim block (PROBE 1's `canonBlock_finrank`), finrank exactly preserved; the cert card target `card m₁ + card m₂ = D·(|V|−1) ≤ (D−1)|E|` UNCHANGED (the basis re-keying touches WHICH vectors, not HOW MANY); the bottom `R(Gab)` finrank `D(|V|−2)` UNCHANGED (the IH fact). `D = screwDim k = (k+2 choose 2)`; the blocked interior arm is `d ≥ 4`/`k ≥ 3`/`D ≥ 10`; `d=3`/`k=2`/`D=6` stays on the separate `_matrix`/M₃ engine, which reads the basis interface only ⟹ GREEN under the def swap (zero-regression hard constraint confirmed by the zero-`blockBasis*`-code-read in the d=3 dispatch).

---

## (4.72) THE D-CAN-2 `hsupp` SATISFIABILITY SPIKE — VERDICT: **`hsupp` is DISCHARGEABLE, GATE-FREE, for the real D-CAN-3 consumer.** Both bottom-row kinds (off-slot `Gv`-rows and the a-shifted reproduced `e_b`-fill row) discharge to the IH-`Q` rows via `caseIIICandidate_supportExtensor_of_ne` / `_reproduced` + the `ofNormals_*` accessors — NEITHER touches the override discriminator or the gate `ρ₀ ⊥̸ C(vᵢ₊₁,n')`. So the §(4.71) "assertion" that `hsupp` is available is now KERNEL-CONFIRMED for the real candidate↔IH-Q pair, and D-CAN-3 is a BUILD (not a wall). (opus, 2026-06-27, kernel-checked spike `SpikeHsupp.lean`, 7 probes A1/A2/B/C1/C2/C3/D, **`Build completed successfully (2780 jobs)`**, deleted before commit; tree clean, `d=3` fully green.)

> **Scope.** The FLOOR the task set: is D-CAN-2's deferred `hsupp` hypothesis (`∀ i : m₂, F.supportExtensor (re (Sum.inr i)).1.1 = F₂.supportExtensor (re₂ i).1.1`) DISCHARGEABLE, GATE-FREE, for the real D-CAN-3/4 consumer (candidate `F = caseIIICandidate G ends q …` vs IH `F₂ = ofNormals Gab Q.ends q`)? §(4.71) ASSERTED it ("from `caseIIICandidate_supportExtensor_of_ne` at `t=0` + the bridge `:701`") but did NOT compiler-verify it for the real pair — the classic deferred-hypothesis-satisfiability trap that the entire §(4.68)→(4.70) arc was. This pass closes that gap at the kernel before D-CAN-3 builds on it. The D-CAN-3 decomposition (the part to defer if the verdict went the other way) is delivered too — the verdict is GO, so it is a build plan.

### (4.72.1) THE MAKE-OR-BREAK STRUCTURE — what `hsupp` actually demands, and why it is gate-free.

The bottom `m₂` of the `_zero₁₂` cert is the operated `mixedBottom` block (`submatrix_columnOp_toBlocks₂₂_eq_mixedBottom`, `Concrete.lean:1741`). Re-confirmed at source (§(4.68)/(4.69.3), and re-read this pass): the `mixedBottom` has **two row kinds** — (1) the surviving `Gv = G − vᵢ` rows (off-slot, `e ∉ {e_a, e_b}`), and (2) the **a-shifted reproduced `e_b`-fill row** (the `hbot1` `Or.inr` "FIRST endpoint `= v`" branch, `:1772`–`1774`) that reconstructs the `e₀ = (a,b)` deficiency fill. It is NOT a literal `R(Gab)` matrix — it is `R(Gv)` PLUS the a-shifted `e_b`-fill (§(4.62)). D-CAN-2 (`submatrix_columnOp_toBlocks₂₂_eq_Gab`, `Concrete.lean:1896`) rewrites this `Matrix.of` block to read `F₂ = Q`'s `blockBasisOn` rows under a per-row selector `re₂` + `hj` (`Fin (D−1)` index preserved) + the `hsupp` per-row support-extensor agreement. The make-or-break: is `hsupp` provable for BOTH row kinds WITHOUT the gate? Yes:

- **Off-slot rows (`Gv`-rows).** `F.supportExtensor e = (ofNormals G ends q).supportExtensor e` by `caseIIICandidate_supportExtensor_of_ne` (`Candidate.lean:983`, a `Function.update_of_ne ×2`, `t`-independent — NO gate). With the dispatch's placement `q := Q.normal` and the same `q` defining `F₂ = ofNormals Gab Q.ends q`, this equals `F₂.supportExtensor e` when the recorded endpoints agree (`ends e = Q.ends e`), by pure `ofNormals_*` accessors. **PROBE A1/A2 — sorry-free.**
- **The reproduced `e_b`-fill row (the make-or-break — the ONE row NOT covered by `_of_ne`).** Its candidate extensor is the REPRODUCED OVERRIDE `panelSupportExtensor (n_u + 0•n') n_r`, which at `t=0` is `panelSupportExtensor n_u n_r` by `caseIIICandidate_supportExtensor_reproduced` (`:972`, a `Function.update_self` + `zero_smul`/`add_zero` — NO gate). With `n_u := q(a,·)`, `n_r := q(b,·)`, this LITERALLY equals the IH-`Q`'s `e₀ = (a,b)` row extensor `panelSupportExtensor (q(a,·)) (q(b,·))` (when `Q.ends e₀ = (a,b)`, by `ofNormals_*`). **PROBE C1/C2/C3 — sorry-free.** This is the row §(4.68.B)/(4.65) feared needed `ρ₀ ∈ span(opaque blockBasisOn(e_b))` (`hred`); under D-CAN-1's canonical basis the agreement is a literal extensor equality, discharged by the override accessor, NOT a span membership and NOT the gate.
- **Under the chain relabel (`shiftPerm i`).** The interior arm's candidate is on `G − vᵢ` with `qρ := q ∘ shiftPerm` and `endsσρ` the `.symm`-shifted selector. `ofNormals_supportExtensor_relabel_perm` (`Relabel/Basic.lean:64`) ALREADY proves the relabel coincidence GATE-FREE (`simp only [ofNormals accessors, Equiv.apply_symm_apply]`) — it is the same brick `chainData_bottom_relabel`'s genuine-row dispatch consumes. **PROBE B — sorry-free.**

**THE FULL INSTANCE FIRES (PROBE D, sorry-free).** A model two-row bottom (`m₂ := Bool`: off-slot `Gv`-row + reproduced `e_b`-row) with a constructed `re₂` (`false ↦ (e, ·)` same `Gab` edge; `true ↦ (e₀, ·)` the fresh IH edge — KT's (6.62) row correspondence), `hj` (`rfl`, j-index copied), and the GATE-FREE `hsupp` (off-slot via `_of_ne`, reproduced via `_reproduced`) — and `F.submatrix_columnOp_toBlocks₂₂_eq_Gab F₂ … re re₂ hbot2 hbot1 hj hsupp` FIRES, type-correct, kernel-clean. **No gate, no override-discriminator, no span membership anywhere in the `hsupp` discharge.**

### (4.72.2) THE GATE-FREE CONFIRMATION + THE PLACEMENT-CONSISTENCY CHECK (the task's "does it re-introduce the gate / conflict with other obligations?").

- **The gate is NOT re-introduced.** The §(4.49)–(4.52) arc localized the §(4.29) gate to the CORNER `hA` ONLY (the `corner_hA'_of_gate` / discriminator route; KT's 6.67 member-pick): "the bottom is the LANDED full-rank `mixedBottom` block ... a *RANK* fact `hD`, **never** a span membership" (§(4.69.5), `Candidate.lean:2418`–`2419`). `hsupp` is a fact about the BOTTOM rows' support extensors, discharged by the override ACCESSORS (`_of_ne`/`_reproduced`) — disjoint from the corner's gate `hρe₀`. So discharging `hsupp` does NOT re-introduce the gate; the gate's only legitimate use stays the corner `Mᵢ` row, exactly as the task required.
- **The placement choice `q := Q.normal` is the ESTABLISHED, conflict-free pattern.** The d=3 dispatch (`Realization.lean:303`–`304`) and the general-`d` `chainData_split_realization` (`:907`–`908`) BOTH set `q := fun p => Q.normal p.1 p.2` and re-express the IH as `ofNormals Gab Q.ends q = Q` (`rfl`). Every OTHER candidate obligation — `hLn`/`hgab` (the placement transversals), the discriminator's `hgate`/`hρe₀`, `hgp_seed`, `hne_Gv` — is DERIVED from `Q`'s own `IsGeneralPosition` (`hgp'`) and `AlgebraicIndependent` (`hQalg`), which the IH `HasGenericFullRankRealization` GUARANTEES. So `q := Q.normal` is precisely the placement that makes those obligations dischargeable; there is NO conflict — constraining `q := Q.normal` is what the dispatch ALREADY does, and `hsupp` is one more fact off the same choice. The interior arm `chainData_arm_realization_sep` (`Realization.lean:1291`, LANDED) routes through `case_III_arm_realization_matrix_sep` with `hLn`/`hgab`/`hne_Gv` all from `q := Q.normal` — confirming the placement consistency for the interior arm too.
- **Cardinalities to ground (clause iii).** `|V(Gab)| = |V(Gv)| = |V(G)| − 1` (splitOff removes `v`; removeVertex removes `v`), so the bottom `card m₂ = D·(|V(Gv)|−1) = D·(|V|−2)` MATCHES the IH-`Q` row count `R(Gab)` finrank `= D·(|V(Gab)|−1) − def(Gab) = D·(|V|−2) − 0` (`Gab` is def-0 minimal-`k`-dof by `splitOff_isMinimalKDof`). `re₂` is a concrete `Equiv`-free selector (KT 6.62 row map): surviving `Gv`-edges → same `Gab`-edge (`hle`, `Realization.lean:331`); the a-shifted `e_b`-row → the fresh `e₀ ∈ E(Gab)` (`he₀ab : Gab.IsLink e₀ a b`, `:328`). The `Fin (D−1)` j-index is copied (`hj`, `rfl`). All grounded.

### (4.72.3) WHERE `hsupp` IS DISCHARGED + THE D-CAN-3 DECOMPOSITION (buildable leaves, exact signatures).

`hsupp` is discharged **in the D-CAN-3 arm** (`Candidate.lean`/`ForkedArm.lean`), as part of constructing the cert's `hD`, NOT in the D-CAN-4 dispatch — because `re₂`/`hsupp`/`hj` are all framework-local (the candidate's overrides + the IH `Q`'s endpoints, both available at the arm where `Q` is unpacked). D-CAN-4 supplies only the `ChainData` geometry (`q := Q.normal`, the split tuple, the discriminator outputs) as it already does for `_matrix_sep`. The D-CAN-3 decomposition (note: D-CAN-2 ALREADY LANDED gives the literal-`Matrix` bottom equality; D-CAN-3 is the cert leaf + arm wiring around it):

- **D-CAN-3a — the `hD` leaf (the bottom-block full-rank via the literal IH bottom).** `hD : LinearIndependent ℝ D.row` where `D := ((F.rigidityMatrixEdge ends hgp * U).submatrix re en).toBlocks₂₂`. Proof: `rw [F.submatrix_columnOp_toBlocks₂₂_eq_Gab F₂ ends hgp hgp₂ hva re re₂ hbot2 hbot1 hj hsupp]` (D-CAN-2, LANDED) to make `D` literally `Matrix.of` of `F₂ = R(Gab)`'s `a`-shifted rows; then the row-LI is `R(Gab)`'s full rank — `F₂.rigidityMatrixEdge`'s rows are LI because `finrank (span F₂.rigidityRows) = D(|V|−2) = card m₂` (the IH `hsplitGP` fact, via the A2 bridge `rigidityMatrixEdge_rank_eq_finrank_span_rigidityRows` + `linearIndependent_iff_card_eq_finrank_span` / `rank_reindex`). The `re₂`/`hsupp`/`hj` constructed in-arm per §(4.72.1). **This REPLACES the landed `linearIndependent_toBlocks₂₂_row_mixedBottom_of_finrank_eq` (`Concrete.lean:1685`) `hD` route** — same `hD` target type, IH-matrix-full-rank proof instead of the `mixedBottom` `finrank_eq` reconstruction. Risk: LOW (D-CAN-2 lands the `Matrix` equality; the rest is the A2 rank bridge + a `LinearIndependent`-from-finrank step, both landed idioms).
- **D-CAN-3b — the arm spine.** A `case_III_arm_realization`-shaped closer (sibling of `chainData_arm_realization_sep`/`case_III_arm_realization_matrix`) that builds `re₂`/`hsupp`/`hj` from the unpacked IH `Q` + the candidate overrides, feeds D-CAN-3a's `hD`, the corner `hA` from `corner_hA'_of_gate` (UNCHANGED, the landed gate route — the corner is where the gate legitimately lives), `hblock` off `Matrix.fromBlocks_toBlocks`, fires `case_III_rank_certification_zero₁₂` (`Candidate.lean:2446`, LANDED) for `hrank`, then the SHARED tail `case_III_realization_of_rank` (`Arms.lean:63`, UNCHANGED — its W6e input is the cert's `finrank (span F₀.rigidityRows) ≥ D(|V|−1)` conclusion, bottom-shape-agnostic, §(4.69.6)(2) VERIFIED-BENIGN). Risk: LOW (pure cert→tail wiring; the carry-the-crux idiom, all bricks landed).

The §(4.43) C.3 `hIH`-one-field add is a D-CAN-4 obligation (the `hIH` is consumed to get the interior `hsplitGP` via D1 `interior_hsplitGP`, `Realization.lean:758`, LANDED) — unchanged by this verdict; the placement choice `q := Q.normal ∘ relabel` creates NO new D-CAN-4 obligation beyond what `_matrix_sep` already needs.

### (4.72.4) THREE DESIGN-PASS CLAUSES — verdicts.
- **(i) verified against LANDED source.** Re-read at source this pass (not trusted from §(4.71) prose): D-CAN-2 `submatrix_columnOp_toBlocks₂₂_eq_Gab` (`Concrete.lean:1896`, the `re₂`/`hj`/`hsupp` signature); `caseIIICandidate` (`Candidate.lean:940`) + `_supportExtensor_of_ne` (`:983`) + `_supportExtensor_reproduced` (`:972`) + `_supportExtensor_candidate` (`:960`); `ofNormals` (`PanelHinge.lean:253`) + `ofNormals_ends`/`_normal`/`toBodyHinge_supportExtensor` (`:95`/`:264`/`:268`, all `rfl`); `ofNormals_supportExtensor_relabel_perm` (`Relabel/Basic.lean:64`); the d=3 `hQeq` `q := Q.normal` (`Realization.lean:303`–`304`) + general-`d` `chainData_split_realization` (`:907`–`908`); the interior arm `chainData_arm_realization_sep` (`:1291`) → `case_III_arm_realization_matrix_sep` (`Candidate.lean:2355`); `case_III_realization_of_rank` (`Arms.lean:63`, takes `q` implicit, consumes only `hrank`); the `_zero₁₂` cert (`Candidate.lean:2446`); `case_III_rank_certification_matrix_sep`'s `hbotmem`/`hbotindep` route (`:2374`); `chainData_bottom_relabel` (`Relabel/Chain.lean:316`, the `hsupp` simp-only pattern `:379`–`381`). The spike `Build completed successfully (2780 jobs)`.
- **(ii) FLAG-DON'T-FORCE — applied as VERDICT-DISCHARGEABLE-GATE-FREE.** The make-or-break (the reproduced `e_b`-fill row, the ONE row not covered by `_of_ne`, the row §(4.65) feared needed `hred`) is the row I spiked HARDEST (PROBE C1/C2/C3 + the assembled PROBE D) — and it discharges by the override ACCESSOR `_reproduced`, GATE-FREE, kernel-confirmed. The §(4.71) assertion is UPHELD, now with the real candidate↔IH-Q instance compiled (not asserted). No residual could not be closed gate-free; the verdict is GO and the D-CAN-3 decomposition is delivered as a build plan (§(4.72.3)), kernel-anchored from the spike. No wall relocated.
- **(iii) traced to GROUND.** `card m₂ = D·(|V|−2)` matches `R(Gab)` finrank `D·(|V|−2)` (§(4.72.2)); `re₂` is a concrete row map (Gv-edge→same, e_b-fill→e₀); `hj` is `rfl`; the placement `q := Q.normal` is consistent with `hLn`/`hgab`/the gate/`hne_Gv` (all derived from `Q`'s GP + alg-independence the IH guarantees). `D = screwDim k = (k+2 choose 2)`; the blocked interior arm is `d ≥ 4`/`k ≥ 3`/`D ≥ 10`; `d=3`/`k=2`/`D=6` stays on the separate landed `_matrix`/M₃ engine, GREEN (zero-regression). `hsupp` lives below the C.0–C.6 contract / motive / IH (it is a `Concrete.lean`/arm matrix fact); the C.3 `hIH` add (§(4.43)) is orthogonal and unchanged.

## (4.73) THE `chainData_dispatch` COMPOSITION SPIKE — VERDICT: **9 of 13 carried obligations of `chainData_arm_realization_zero₁₂` compose SORRY-FREE from the landed D-CAN-4 feeders; the 4 residuals are `re`/`hre` (bookkeeping), `hB`/`L₀` and `hA` (the KT-6.66 operated-corner identity, genuinely-new), plus ONE load-bearing UNVERIFIED SEAM: the placement reconciliation of the spine's direct-`q` corner gate against the redundancy leaf's relabel-`q` perp.** (opus, 2026-06-27, kernel-checked spike `SpikeDispatch.lean`, fired the LANDED spine at a concrete `cd`/`i` binding, `Build completed successfully (2785 jobs)`, deleted before commit; tree clean.)

> **Scope.** The phase mandate ("compiler-check the FULL composition before declaring 'remaining = assembly'", §(4.46)/(4.54)) applied to the unbuilt `chainData_dispatch`: do the five landed D-CAN-4 feeders (rows 554–558) actually discharge the D-CAN-3b spine's carried obligations? The spike fired the spine with the dispatch's natural index/block choices (`m₁ := Fin (screwDim k)`, `A/B/C/D := M'.toBlocks` of the operated submatrix) and `apply`-ed each feeder to read the residual.

### (4.73.1) PER-OBLIGATION RESIDUAL MAP (kernel-checked).
- **CLOSE sorry-free (9):** `hgp` (`exact` the LANDED `caseIIICandidate_supportExtensor_ne_zero_of_genPos`, fed `hends`+`hgppair`); `hm₁` (`simp`); `hm₂` (`V(removeVertex)=V(Gab)`); `hM'eq` (`(fromBlocks_toBlocks M').symm` — the `toBlocks` block choice is kernel-correct); `hD` (modulo bundle: `rw [hM']; apply linearIndependent_toBlocks₂₂_row_Gab_of_finrank_eq` leaves EXACTLY the `F₂,hgp₂,re₂,hbot2,hbot1,hj,hsupp,hrank` bundle `bottom_selection_of_crossFramework_span_Gab` produces + `F₂`/`hgp₂` from the `hfr₂` producer — wiring constraint: `re`'s `Sum.inr` half must be DEFINITIONALLY the selector's `reInr`); `hends`/`hends_Gv`/`hne_Gv` (geometry from IH-`Q`'s `hQrec` + the two override hinges; `hne_Gv` is verbatim the `_sep:1436` inline proof); `hdef` (in context).
- **GAP (4):** `re`/`hre` (the corner⊕bottom `Sum.elim cornerRe reInr` selector + injectivity — pure dispatch assembly, no new math); `hB`/`L₀` (`matrix_eq_mul_of_dual_row_comb` needs the per-corner-row `hcomb : φ i = ∑ⱼ cGv i j • χ(μ i j)`, the KT-6.66 `cGv`-widening transported from the BASE split to the corner-row entries — unbuilt); `hA` (hardest — `corner_hA_zero₁₂_of_gate`'s `hAeq` precondition, the operated `A−L₀C = coordEquiv(Sum.elim blockBasisOn ρ₀) ∘ em₁`, is KT eq. (6.66)'s core matrix-entry identity, owed at the assembly per its own doc `Concrete.lean:749`/`:2624` — NO landed leaf produces it).

### (4.73.2) THE LOAD-BEARING SEAM — placement reconciliation — **RESOLVED: NO SEAM (the perp-producer is dead-arm; the corner consumes the direct-`q` NONZERO gate). The `hA` leaf is LANDED.** (opus, 2026-06-27 session #45, kernel-checked, two scratch composition files deleted; tree clean except the banked leaf.)
The diagnosis below was a MISATTRIBUTION. `corner_hA_zero₁₂_of_gate` (`Concrete.lean:757`) consumes `hρe₀ : ρ₀ (F.supportExtensor e_a) ≠ 0` — the **NONZERO** gate (`≠ 0`, KT (6.65)–(6.67) member-pick), NOT a perp (`= 0`). At the matched interior candidate `i` (`0 < i`) the candidate `F = caseIIICandidate … (q(vtx i.succ,·)) n' … 0` has `F.supportExtensor (cd.edge i) = panelSupportExtensor (q(vtx i.succ,·)) n'` (`caseIIICandidate_supportExtensor_candidate`, `e_c ≠ e_r` via `pred_edge_ne`), and `candidateVtx i = vtx i.succ` (`candidateVtx_succ_eq`); so the discriminator's DIRECT-`q` gate `ρ₀ (panelSupportExtensor (q(candidateVtx i,·)) n') ≠ 0` (`exists_shared_redundancy_and_matched_candidate`, `:1729`) IS, verbatim, `corner_hA_zero₁₂_of_gate`'s `hρe₀` — both against the same direct `q`, no `shiftPerm`. The perp-producer `interior_hρe₀_of_widening`/`_of_baseWidening` (`q∘shiftPerm` perp `= 0`) feeds the **dead-arm** `case_III_arm_corner_assembly` (`_sep`) route — the `_zero₁₂` chain (`case_III_arm_realization_rowOp` → `case_III_rank_certification_zero₁₂`) takes `hA`/`hD` and NEVER an `hρe₀`. So the spine's direct-`q` gate is CORRECT as stated; no `q`-choice change, no contract touch. Landed leaf: `chainData_arm_corner_hA_of_discriminator_gate` (`Realization.lean`, after the spine), sorry-free modulo the carried `hAeq` (KT 6.66, item (2) below). — *Superseded diagnosis (kept one line for the trail): the prose claimed `interior_hρe₀_of_baseWidening`'s relabel-`q` perp gated `hA` and the dispatch must set `q := (base seed) ∘ shiftPerm`; both false — the perp is never consumed in the `_zero₁₂` route.*

### (4.73.3) C.3 `hIH` add — CONFIRMED NEEDED. The interior `hsplitGP` (feeding `hfr₂`/`F₂` and the placement) is reachable only via D1 `interior_hsplitGP`, which consumes `hIH`/`hnoRigid`/`hV4`/`hG`; so the dispatch signature must carry the approved one-field `hIH` add (§(4.43)), touching the C.0 producer/consumer/ENTRY trio. Not performed in the spike (a contract change, flag-don't-force).

### (4.73.4) BUILD ORDER. (1) ✓ DONE — placement-reconciliation (§(4.73.2)): NO seam; the `hA` leaf `chainData_arm_corner_hA_of_discriminator_gate` is LANDED (modulo `hAeq`); (2) ✓ DONE — the `hAeq` leaf `submatrix_columnOp_toBlocks₁₁_sub_mul_toBlocks₂₁_eq_coordEquiv` (`Concrete.lean` A6, opus 2026-06-27, axiom-clean): the operated-corner matrix-entry identity `toBlocks₁₁ − L₀·toBlocks₂₁ = coordEquiv ∘ φ`, abstract over `L₀`/`φ` (the caller's `hφ` carries the KT-6.66 `φ i = blockBasisOn(corner) − ∑ L₀ • χ`), `φ`-shape matching `corner_hA_zero₁₂_of_gate`'s `hAeq` at `φ := Sum.elim blockBasisOn ρ₀ ∘ em₁`; (3) `hB`/`L₀` leaf — `corner_row_eq_cGv_comb_of_baseWidening` (the base-widening transport) feeding `matrix_eq_mul_of_dual_row_comb` (the SAME `L₀` as (2), §(4.64.A) shared-`?L₀`) — defines the concrete `L₀`; **(3b) — bundled with (3), GENUINELY-NEW, NOT dispatch plumbing:** the `hφ`-collapse for `φ := Sum.elim blockBasisOn ρ₀` (item-(2)'s abstracted-away part (b)): the operated `±r` row `blockBasisOn(±r) − ∑ L₀ • χ = ρ₀` via the KT-6.66 redundancy `hingeRow a b ρ₀ = ∑ cGv • hingeRow(…)` (the discriminator `hedgeGv` bundle), + the `e_a` panel rows' `L₀`-weights vanish. Rate the item-(3) dispatch by (3b)+the `cGv` transport, not the `B = L₀·D` factoring alone; building (3b) with (3) keeps the dispatch shell pure wiring. (4) `re`/`hre` builder (`Sum.elim cornerRe reInr` + injectivity, bookkeeping); (5) the dispatch shell (`Fin cd.d` router: base/`d=3` → `chainData_split_realization`, interior `2 ≤ i` → the spine) + CHAIN-5 + the C.3 `hIH` add.

## (4.74) THE `hcomb`/`hφ` PRODUCER SPIKE — VERDICT: **the D-canonical CORNER `hA` rests on `blockBasisOn(±r slot) = ρ₀`, which is FALSE against landed source; the §(4.73)/route-α `Sum.elim blockBasisOn ρ₀` corner `hAeq` is UNSATISFIABLE for the live pin-zero `Gab` bottom.** This is the §(4.65.B)/§(4.68.B) opaque-`blockBasisOn` CORNER obstruction — D-canonical fixed it for the BOTTOM (cross-framework basis *equality* `blockBasisOn_congr`) but NOT the corner (which needs a *specific* basis vector to *equal* `ρ₀`). (opus, 2026-06-27, kernel-checked spike `SpikeRpmR.lean`, 5 probes, deleted; tree clean, builds green.)

> **Scope.** The last genuinely-new geometry producer (the `hcomb`/`hφ` for the spine's `hB`/`hA` slots) was spiked before building. The spike kernel-read the residual of `hcomb`(±r) and `hφ`(±r) at the concrete interior binding.

### (4.74.1) THE KERNEL FACTS (coordinator-confirmed against source).
- `blockBasisOn = canonBlockBasis = Module.finBasisOfFinrankEq ℝ (canonBlock s) …` (`Concrete.lean:213`/`599`), an **opaque/arbitrary** basis of `canonBlock s = (span{s})ᗮ = {ρ : ρ s = 0}` (`Concrete.lean:186`). Keyed on the support extensor `s`, so cross-framework basis-vector EQUALITY is provable (`blockBasisOn_congr`, the bottom's `hD`) — but NO specific basis vector equals a specific functional. `ρ₀ ∈ hingeRowBlock(e_b) = canonBlock(supportExtensor e_b)` (the discriminator's `ρ₀(C(a,b))=0`) is the strongest landed fact, and is INSUFFICIENT to give `blockBasisOn(e_b,j₀) = ρ₀`.
- The D-canonical `Gab` bottom (`bottom_selection_of_crossFramework_span_Gab`, `Concrete.lean`) has BOTH endpoints `≠ v` (`hfirst₂`/`hsecond₂`), so `C = toBlocks₂₁ = 0` at the `v`-pin column (pin-zero). Hence `A − L₀C = A`: the `L₀` row-op is VACUOUS for the corner `hA`; `hA` reduces to bare `A.row` LI where `A`'s `±r` row reads the opaque `blockBasisOn(e_b,j₀)`. The `∑ L₀ • χ` correction in `hφ` is identically `0` (kernel-confirmed), leaving the bare false `ρ₀ = blockBasisOn(e_b,j₀)`.
- `hcomb`(±r) [the `hB` factoring, `hingeRow`-level] DOES compose sorry-free on its own via span-membership (`matrix_eq_mul_of_span_mem`; the W6b widening is not even needed). Only `hφ`(±r) [the `hA` bundle, Dual-level] is blocked.

### (4.74.2) CONSEQUENCE. The landed corner leaves `chainData_arm_corner_hA_of_discriminator_gate` (eeafe64), `submatrix_columnOp_toBlocks₁₁_sub_mul_toBlocks₂₁_eq_coordEquiv` (32808a3), and `toBlocks₁₁_sub_mul_toBlocks₂₁_row_linearIndependent_of_gate` (a1e5f9a) are CORRECT lemmas built on an UNSATISFIABLE hypothesis (`hφ`/`hAeq` in the `Sum.elim blockBasisOn ρ₀` shape) — the deferred-hypothesis-satisfiability trap, caught at the producer (DESIGN.md *Constructibility recon*). The engine `dual_comb_reindex_fiberwise` (e60135d) + the `hB`-block reads remain reusable.

### (4.74.3) OPEN (settled by the resume): is there a NON-`ρ₀` corner route under the pin-zero bottom — `A.row` LI via transverse blocks (`blockBasisOn(e_b,j₀) ∉ canonBlock(supportExtensor e_a)`, i.e. `blockBasisOn(e_b,j₀)(supportExtensor e_a) ≠ 0`) from general position — or is that ALSO blocked by the opaque `finBasisOfFinrankEq` (no control over the specific basis vector's value on `supp e_a`)? If blocked, the fix is a USER-ADJUDICATED cert re-shape (route α: a genuine-`ρ₀` augmented `±r` row → bare `corner_hA'_of_gate`, dropping the opaque-basis index; or a `ρ₀`-aligned `blockBasisOn` redefinition, foundational/worse) — the §(4.65.E)/§(4.68) STOP D-canonical was meant to avoid.

## (4.75) THE NON-`ρ₀` CORNER RE-ROUTE — VERDICT: **§(4.74.3)'s OPEN question RESOLVED: there IS a non-`ρ₀` corner route; NO cert re-shape / route-α STOP is needed.** Under the pin-zero `Gab` bottom (`C = toBlocks₂₁ = 0`), `hA` is bare `A.row` LI of the corner block-basis family `[blockBasisOn(e_a,·); blockBasisOn(e_b,j₀)]`, which needs only **block INCOMPARABILITY** `¬ hingeRowBlock e_b ≤ hingeRowBlock e_a` — NOT the false `blockBasisOn(±r) = ρ₀`. The opaque-`finBasisOfFinrankEq` dead-end is on the OPERATED (`C ≠ 0`) path ONLY. (opus, 2026-06-27, kernel-checked spike `SpikeHA2.lean`, 4 probes, deleted; BANKED `b39da26`, axiom-clean, gates green.)

### (4.75.1) WHY THE OPAQUE-BASIS DEAD-END DOESN'T BIND HERE. `A.row` LI needs SOME `e_b`-block basis vector to escape `canonBlock(supportExtensor e_a)` — an **∃ over the basis index**, satisfiable from incomparability (a block-level fact), NOT the **∀-control over a specific opaque vector** that `=ρ₀` (or the §(4.74.3) "specific `blockBasisOn(e_b,j₀)` value") demanded. (Coordinator note: the §(4.74.3) prose leaning toward a STOP was over-pessimistic — the compiler-checked decisive recon found the within-workflow re-route. Validates "check for a within-workflow resolution before stopping" + "compiler-check, don't prose-argue" in the defeq-fragile zone.) BANKED `ρ₀`-free (`Concrete.lean`): `hingeRowBlock_not_le_of_supportExtensor_not_mem_span` (incomparability from non-parallelism `C(e_a) ∉ span {C(e_b)}`, via dual-annihilator order-reversal + the finite-dim double-annihilator round-trip) + `exists_corner_blockBasisOn_linearIndependent_of_not_le` (the corner family LI from incomparability alone, choosing the escaping `j₀`).

### (4.75.2) CONSEQUENCE FOR THE LANDED LEAVES. The operated `hAeq` leaves (eeafe64 `chainData_arm_corner_hA_of_discriminator_gate`, 32808a3 `submatrix_columnOp_toBlocks₁₁_sub_mul_toBlocks₂₁_eq_coordEquiv`, a1e5f9a `toBlocks₁₁_sub_mul_toBlocks₂₁_row_linearIndependent_of_gate`) are the `C ≠ 0` operated path → OFF the pin-zero route; kept in tree (harmless; a phase-close cleanup candidate). The engine `dual_comb_reindex_fiberwise` + the `hB`-block reads stay reusable (`hcomb`/`hB` composes via span-membership, independent of the corner `hA`).

### (4.75.3) REMAINING — the incomparability SOURCE (the non-parallelism `C(e_a) ∉ span {C(e_b)}` of the two candidate corner extensors) + the `hA` wiring + the rest of the dispatch. Two routes to the source: **(a)** the GP non-parallelism via a panel-meet leaf `panelSupportExtensor (q a) n' ∉ span {panelSupportExtensor (q a) (q b)}` from a 3-normal LI `![q a, q b, n']` (cleaner, contract-free, but the 3-normal LI is not a discriminator output as-is); **(b)** `C(e_a) ∉ span {C(e_b)}` from the LANDED nonzero gate `ρ₀(C(e_a)) ≠ 0` + the perp `ρ₀(C(e_b)) = 0` (a one-liner: if `C(e_a) = c·C(e_b)` then `ρ₀(C(e_a)) = c·0 = 0`, contra) — but the direct-`q` interior perp `ρ₀(C(e_b)) = 0` is the §(4.73.2) seam (REAL for the perp gate, only the relabel-`q` `interior_hρe₀_of_widening` is landed). Both are genuinely-new but geometrically TRUE leaves; route (a) is the contract-free recommendation.

## (4.76) THE ROUTE-α CORNER-SOURCE BUILDOUT — STATUS: route (a) chosen (user-adjudicated session #45); the corner `hA` source's LA half is LANDED, the residual is ONE geometric side-condition. (opus, 2026-06-27, session #45; BANKED `767e120` + `66b1d36`, axiom-clean, gates green.)

### (4.76.1) LANDED. (i) the incomparability source leaf `panelSupportExtensor_not_mem_span_of_triLI` (`PanelLayer.lean`) + the spine-binding corner-LI chain `chainData_arm_corner_blockBasis_linearIndependent_of_triLI` (`Realization.lean`): `3-normal LI ![q a, n', q b] → C(e_a) ∉ span {C(e_b)} → incomparability → corner family LI → hA`, sorry-free on the spine's exact candidate binding (`C(e_a) = panelSupportExtensor (q a) n'` via `_supportExtensor_candidate`; `C(e_b) = panelSupportExtensor (q a) (q b)` at `t=0` via `_supportExtensor_reproduced`). (ii) the route-α LA core `exists_independent_perp_family_escape` (`Claim612.lean`, beside `exists_independent_perp_family`): the strengthened perp-family lemma — for `m ≤ k` kept points `p`, `n_u` perp-to-all + `≠ 0`, and `w` NOT perp-to-all (`∃ i, p i ⬝ᵥ w ≠ 0`), produces `n'` perp to `p`, `![n_u, n'] LI`, AND `n' ∉ span {n_u, w}` (the `W ⊓ ker L = span {n_u}` count collapses to 1-dim when `w ∉ ker L`). The engine the strengthened discriminator builds the corner transversal through (`n_u := q a`, `w := q b` ⟹ `n'` escapes `span {q a, q b}`).

### (4.76.2) THE RESIDUAL (route α). Route (b)'s perp was rejected (the §(4.73.2) seam, REAL: the landed perp crux gives the chain-edge panel `(i+1, i)`, the spine's direct-`q` reproduced panel is the short-circuit `(i+1, i-1)`). Route α = strengthen the discriminator pick: swap `exists_independent_perp_family` → `_escape` inside `exists_line_data_of_homogeneousIncidence_gen`'s `n'`-builder (fed `w := q b`) + thread the `n' ∉ span {q a, q b}` clause out through `exists_chainData_discriminator_pick` → `exists_shared_redundancy_and_matched_candidate` to the `htriLI` slot. **The one genuinely-new step:** supply the side-condition `q b ∉ ker (of p)` (`∃ i, p i ⬝ᵥ q b ≠ 0`) — the preceding chain panel normal is not orthogonal to the Claim-6.12 join's `k` kept points; KT general position, geometrically TRUE, but not a current GP guarantee (`q b` can be the omitted base body `v₁` at `i = 2`). Below the frozen C.0–C.6 contract; additive (the dispatch is unbuilt). Then the `hA` matrix wiring + the `chainData_dispatch` (re/hre + router) + CHAIN-5 + the C.3 `hIH` add.

## (4.77) THE ROUTE-α SIDE-CONDITION RECON — VERDICT: **FLAG-DON'T-FORCE STOP. The side-condition `∃ idx, p idx ⬝ᵥ q b ≠ 0` is NOT establishable for all matched joins — it is provably FALSE for a concrete family of configurations — so route α as currently scoped (thread `_escape` through the LANDED discriminator) CANNOT be completed. Two faithful escapes exist; both are user-adjudication decisions, neither is "thread `_escape` and build".** The threading half is fine — kernel-confirmed — but the geometric input it demands is sometimes a false proposition. Decision for the human. (opus, 2026-06-27 session #46, kernel-checked spike `SpikeRouteAlpha.lean`, 4 probes, deleted before commit; tree clean, `d=3` fully green.)

> **Scope.** The task's three recon questions, against LANDED source (the discriminator chain `exists_homogeneousIncidence_of_normals_gen` `Claim612.lean:555` → `exists_line_data_of_homogeneousIncidence_gen` `:747` → `exists_complementIso_ne_zero_of_homogeneousIncidence_gen` `:1547` → `exists_chainData_discriminator_pick` `Realization.lean:1774` → `exists_shared_redundancy_and_matched_candidate` `:1825`; the corner consumer `chainData_arm_corner_blockBasis_linearIndependent_of_triLI` `:1693`; the spine `chainData_arm_realization_zero₁₂` `:1481`; the cert `case_III_rank_certification_zero₁₂` `Candidate.lean:2599`): (1) is the side-condition establishable for all join cases incl. `i = 2`; (2) if so, pin the exact threaded route; (3) if it can fail, STOP for adjudication. Verdict: (3).

### (4.77.1) THE THREADING HALF IS SOUND (clause iii — objects match across the threading, kernel-confirmed). The `htriLI` slot the corner leaf consumes is, verbatim, `LinearIndependent ℝ ![q a, n', q b]` with `q a := q(vtx i.succ, ·)`, `q b := q(vtx (i−1).castSucc, ·)`, `n'` the discriminator transversal (`Realization.lean:1704`–1708). These ARE the same objects the spine binds (`hLn : ![q a, n'] LI` `:1491`; `hgab : ![q a, q b] LI` `:1492`–1494, both carried by the spine; the candidate-slot support `C(e_a) = panelSupportExtensor (q a) n'` and the reproduced-slot `C(e_b) = panelSupportExtensor (q a) (q b)` at `t = 0` — verified `:1722`–1732). And `_escape`'s output composes into the full `htriLI`: from `![n_u, n'] LI` + `n' ∉ span {n_u, w}` + `![n_u, w] LI` (the `hgab` the spine already carries, from `AlgebraicIndependent ℚ q`'s pairwise-LI shape), `![n_u, n', w] LI` follows (`LinearIndependent.finCons huw` onto the pair, reindexed `![1,0,2]`). **Kernel-confirmed sorry-free** (`spike_triLI_of_escape`). So IF the side-condition held, the build would go through. The gap is not threading; it is the side-condition's truth.

### (4.77.2) THE SIDE-CONDITION CAN BE FALSE (clause i — against LANDED source; clause ii — the residual you cannot close IS the verdict). The kept points are `p idx = pbar (emb idx)`, where `pbar : Fin (k+2) → Fin (k+2) → ℝ` (`exists_homogeneousIncidence_of_normals_gen`) realize the **off-one-panel incidence** against the discriminator's panel family `n = fun (j : Fin (k+1)) => q(cand j, ·)` with `cand = candidatePanel = candidateVtx ∘ Fin.cast` (the vertices `{v₀, v₂, v₃, …, v_d}`, **omitting `v₁`** — `candidateVtx` `Operations.lean:2783`), and `emb` enumerates the complement `{a,b}ᶜ` of the witness join `q = {a,b}`. The membership rule (`pbar_dotProduct_eq_zero_of_ne_succ` `Claim612.lean:701`): `pbar v ⬝ᵥ n j = 0 ⟺ v ≠ j.succ`. Hence for a kept-point family: **`∀ idx, p idx ⬝ᵥ n j = 0 ⟺ j.succ ∈ {a, b}`** (no kept index equals `j.succ`). So `∃ idx, p idx ⬝ᵥ n j ≠ 0 ⟺ j.succ ∉ {a, b}` — combinatorial, join-dependent. Two failure families, both real:
- **The two-panel collision (sharpest, definite).** When `0 ∉ {a, b}` (`exists_line_data_of_homogeneousIncidence_gen`'s two-panel branch, `Claim612.lean:783`–792), the discriminator sets `n' := n u_b` *directly* — the second real panel normal. If the corner's preceding panel `q b = q(v_{i−1}, ·)` IS that other panel `n u_b` (i.e. `v_{i−1}` is the candidate vertex `cand u_b`), then `n' = q b`, so `![q a, n', q b] = ![q a, q b, q b]` is degenerate — `htriLI` is **outright FALSE**, no side-condition can rescue it. (And `_escape`'s side-condition is exactly false here: `q b = n u_b` with `u_b.succ = b ∈ {a,b}`, so `p ⊥ q b`.)
- **The one-panel / general case.** When `q b = n j'` is any candidate panel with `j'.succ ∈ {a, b}` (the join line lies in panel `Π(q b)` too), ALL kept points are perp to `q b` by incidence, so `q b ∈ ker (of p)` and `_escape` dies. **Kernel-confirmed sorry-free** (the second spike probe: `j'.succ ∈ {a,b} → ∀ idx, pbar (emb idx) ⬝ᵥ n j' = 0`, via `pbar_dotProduct_eq_zero_of_ne_succ`). The matched candidate `i` and the witness join `{a,b}` are NOT jointly controlled — the discriminator returns `u` (matched to `i`) off a witness join `case_III_claim612_gen` produces with only `ρ(·) ≠ 0`; nothing links that join to `q b`'s panel index, so the failing configs are reachable.
- **The `i = 2` omitted-base case** the task flagged is the *softest* of the three: there `q b = q(v₁, ·)` is NOT in `n` (the incidence pattern says nothing about it), so the side-condition is *unconstrained* (could be true or false), not provably true. Even if it held at `i = 2`, the two failures above (at other `i`) sink the uniform route.

**So the answer to recon question (1) is NO**: the side-condition is not establishable for all matched joins; it is a sometimes-false proposition for the spine's actual `q b`. KT general position does NOT supply it, because the failure is not a measure-zero degeneracy escapable by genericity — it is the *combinatorial* event "the witness join line lies in the preceding panel too", which the discriminator's own construction can realize.

### (4.77.3) WHY THIS IS A REAL OBSTRUCTION, NOT A THREADING BUG (clause i — the `_escape` need is genuine). The corner-incomparability route needs `C(e_a) = q a ∨ n' ∉ span {C(e_b) = q a ∨ q b}`. This is NOT derivable from `![q a, n'] LI` + `![q a, q b] LI` alone: if `n' ∈ span {q a, q b}` (e.g. `n' = q a + q b`) then `q a ∨ n' = q a ∨ q b` (since `q a ∨ q a = 0`), so `C(e_a) = C(e_b)` — parallel, incomparability fails. The escape `n' ∉ span {q a, q b}` is therefore load-bearing, and its perp-family realization needs exactly `q b ∉ ker (of p)`. The two-panel collision shows `n' ∈ span {q a, q b}` (indeed `n' = q b`) genuinely occurs.

### (4.77.4) THE OPEN DECISION FOR THE USER — three faithful directions, none a unilateral pick. Cost estimates are rough (the recon settled feasibility, not a build).
- **(α′) Re-point the discriminator to escape the preceding panel `Π(q b)` at the matched candidate.** Strengthen `exists_chainData_discriminator_pick` so the returned `n'` of the matched panel `u` also escapes the chain-predecessor panel. **Obstruction: circularity / the two-panel branch.** The discriminator picks `(u, n')` BEFORE the match fixes `i` (hence `q b = q(v_{i−1})`); and in the two-panel branch `n'` is *forced* `= n u_b`, not free — there is no transversal freedom to steer. Feasible only by *re-architecting* the discriminator to be candidate-aware (the panel selector would need `v_{i−1}` as an input), which is a contract-level change to the CHAIN-2c family. ~Large, and the two-panel `n' = n u_b` collision may make it impossible without also changing the line-data builder. **Not recommended without deeper recon.**
- **(D / `ρ₀`-route, KT-faithful) Augment the corner row with `ρ₀` genuinely** — KT's `Mᵢ = [r(Lᵢ); ±r]` IS `[r(L_i); ρ₀]` (KT eq. (6.64), `katoh-tanigawa-2011` p.696–697: the `±r = ∑λ rⱼ(q(vᵢvᵢ₊₁))`, the SHARED redundancy). The LANDED `corner_hA'_of_gate` (`Concrete.lean:810`) already proves this corner full-rank from the discriminator's NONZERO gate `ρ₀(C(e_a)) ≠ 0` — no `n'`-escape, no side-condition. The blocker that sent the project off `ρ₀` (§(4.74): the *operated* `hAeq` needs `blockBasisOn(±r) = ρ₀`, false for the opaque `finBasisOfFinrankEq`) is a **cert-SHAPE** issue, not a geometry one: it arises because the pin-zero `Gab` bottom reads the `±r` slot as `blockBasisOn(e_b, j₀)` rather than `ρ₀`. The fix is a cert re-shape — carry a *genuine* `ρ₀` row in the corner (an extra `m₁`-row that is literally `ρ₀`, not an opaque block-basis vector), so `hA = corner_hA'_of_gate` fires directly off the discriminator gate the spine ALREADY produces (`exists_shared_redundancy_and_matched_candidate` returns `ρ₀(panelSupportExtensor (q(candidateVtx i)) n') ≠ 0` `:1879`). This is the §(4.74.3) "route-α STOP" option D-canonical was meant to avoid — but the avoidance (the incomparability re-route §(4.75)) is now refuted. **This is the most KT-faithful direction** (the corner IS KT's `Mᵢ`); cost is a cert-leaf re-shape (the `±r`-row augmentation + re-wiring `corner_hA_zero₁₂_of_gate`'s `hAeq` to the genuine-`ρ₀` row), ~3–6 commits, no new geometry. **Recommended for adjudication.**
- **(β) Replace the per-candidate discriminator with KT's actual disjunction-over-all-`Mᵢ` argument (eq. 6.65–6.67).** KT does NOT build a per-candidate `n'`; KT shows the span of `⋃ C(Lᵢ)` over all `d` candidates has dimension `D` (Lemma 2.1 over the `d+1` affinely-independent points `p₀,…,p_d`), so the nonzero `r` cannot annihilate all of it, hence ≥1 of `M₀,…,M_{d−1}` is full rank. The discriminator/`n'`/`htriLI`/incomparability device (the route the side-condition lives in) is **entirely project-specific** (design §(4.69.2)); it is what introduces the false side-condition. Routing the corner through KT's own dimension count removes `n'` and the side-condition altogether — but it changes WHICH candidate the cert certifies (an existential over candidates, not a fixed matched `i`), so the dispatch/spine shape changes (the router can no longer fix `i` from the discriminator). ~Large (re-opens the CHAIN-2c dispatch architecture), but maximally KT-faithful and dissolves the obstruction at its root. **Recommended if (D) re-shape proves too entangled with the opaque basis.**

### (4.77.5) THREE DESIGN-PASS CLAUSES — verdicts.
- **(i) verified against LANDED source.** Every load-bearing object re-read this pass at its `def`/`theorem` (not the §(4.76) prose): the discriminator chain (`Claim612.lean:407`/`466`/`555`/`747`/`1547`, `Realization.lean:1774`/`1825`), the membership rule `pbar_dotProduct_eq_zero_of_ne_succ` (`:701`), `candidateVtx`/`candidateVtx_succ_eq` (`Operations.lean:2783`/`2824`), the corner consumer `chainData_arm_corner_blockBasis_linearIndependent_of_triLI` (`Realization.lean:1693`, `htriLI` shape + the `q a`/`q b`/`n'` binding), the spine `chainData_arm_realization_zero₁₂` (`:1481`, carries `hLn`/`hgab`), the cert `case_III_rank_certification_zero₁₂` (`Candidate.lean:2599`, shape-agnostic in `A`), the corner leaves `corner_hA'_of_gate` (`Concrete.lean:810`) + `exists_corner_blockBasisOn_linearIndependent_of_not_le` (`:760`) + `linearIndependent_toBlocks₁₁_row_of_corner_gate` (`:2810`). KT eq. (6.60)–(6.67) re-read end-to-end (`katoh-tanigawa-2011-molecular-conjecture.pdf` p.696–698). The spike `lean_diagnostic_messages` reports zero errors; 4 probes sorry-free.
- **(ii) FLAG-DON'T-FORCE — applied as VERDICT-STOP.** The residual that cannot be closed (the side-condition is false in a concrete reachable family) IS the verdict; reported, not forced. No route unilaterally picked — three faithful directions handed over with their obstructions and rough costs. The `_escape` LA core stays a CORRECT, axiom-clean leaf (its `hw` precondition is just sometimes unsatisfiable for the spine's `q b` — the deferred-hypothesis-satisfiability trap again, now caught at the *consumer*-feasibility recon before any producer was built, per the §(4.62) compiler-check rule + DESIGN.md *Constructibility recon*); `panelSupportExtensor_not_mem_span_of_triLI` + `chainData_arm_corner_blockBasis_linearIndependent_of_triLI` also stay correct (they consume `htriLI` as a hypothesis; they do not assert it holds).
- **(iii) traced to GROUND.** The `htriLI`/`q a`/`q b`/`n'` denote the SAME geometric objects across the discriminator → spine threading (the spine binds `q b` as the reproduced-slot `t = 0` support `panelSupportExtensor (q a) (q b)`; confirmed `:1729`–1732 it IS the preceding-panel normal `q(v_{i−1})` the side-condition is about). Index/cardinality compatible: `cand : Fin (k+1) ↪ α` hits `d = k+1` vertices `{v₀,v₂,…,v_d}`; the witness `pbar : Fin (k+2)`; the kept family `p : Fin k` (the join's `k = d−1` complement points). The two-panel collision is a genuine structural coincidence (`n' = n u_b = q(v_{i−1})`), not a bookkeeping artifact.

## (4.78) ROUTE (D) FEASIBILITY SPIKE — VERDICT: **route (D) is FEASIBLE and gives a CLEAR path to CHAIN close, BUT NOT as a "cert-leaf re-shape" — it is the AUGMENTED matrix arm (`rigidityMatrixEdgeAug`, all cert/engine/arm landed) fired on the D-CANONICAL PIN-ZERO bottom, a combination §(4.67)/§(4.68) never tested (they had `C ≠ 0`).** Under D-canonical the bottom is the literal `R(Gab)` (full-rank, NO `e_b`-fill in the bottom ⟹ `C = toBlocks₂₁ = 0`), so the operated corner `A − L₀·C = A` is **bare** `A.row` LI, and the augmented `inr ()` `±r` row — oriented `hingeRow b v ρ₀` (head the OTHER chain neighbor `b`, **tail the pin `v`**) — reads `−ρ₀ (finScrewBasis c)` at the v-pin **through the column op** (NONZERO), so `A = coordEquiv ∘ [blockBasisOn(e_a); −ρ₀]` and `corner_hA'_of_gate` fires from the discriminator gate ALONE. No `n'`-escape, no side-condition, no override-gate re-entry. The genuinely-new work is a SMALL family of augmented-matrix bricks (siblings of the landed un-augmented ones) — flagged below, NOT pure wiring. (opus, 2026-06-27 session #46, kernel-checked spike `SpikeRouteD.lean`, 6 probes sorry-free, `Build completed successfully (2785 jobs)`, deleted before commit; tree clean, `d=3` fully green.)

> **Scope.** The task: a compiler-checked feasibility verdict on route (D) (§(4.77.4)(D)) — does carrying a GENUINE `ρ₀` corner row give a CLEAR buildable path to CHAIN close, against LANDED source (the cert `case_III_rank_certification_zero₁₂`/`_aug`, the spine `chainData_arm_realization_zero₁₂`, `corner_hA'_of_gate`, `linearIndependent_toBlocks₁₁_row_of_corner_gate`, the discriminator). The three recon questions answered (1) where a genuine-`ρ₀` corner row comes from under `C = 0`, (2) §(4.52)-vs-§(4.74) reconciliation, (3) no override-gate re-entry; (4) the path to close + sub-commit list.

### (4.78.1) THE HEADLINE — route (D) ≠ "cert re-shape"; it is the LANDED `_aug` ladder fired on the D-canonical bottom (clause i: every claim verified against LANDED source, not §(4.77) prose).
The §(4.77.4)(D) framing ("a cert-leaf re-shape — carry a *genuine* `ρ₀` row, ~3–6 commits, no new geometry") is **partly stale**: the cert that carries a genuine `ρ₀` corner row ALREADY EXISTS and is landed — `case_III_rank_certification_aug` (`Candidate.lean:2694`) over `rigidityMatrixEdgeAug ends hgp rRow` (`Concrete.lean:1045`), whose row index `(({e//e∈E}×Fin(D−1))) ⊕ Unit` carries the genuine functional `rRow : Dual ℝ (α → ScrewSpace k)` in the `inr ()` slot with `hr : rRow ∈ span F.rigidityRows`. Its engine `finrank_span_rigidityRows_ge_of_aug_submatrix_fromBlocks_zero₁₂` (`Concrete.lean:1258`) and its arm `case_III_arm_realization_aug` (`ForkedArm.lean:426`) are ALL landed (the αE1–αE4 "landed-but-dead" ladder). So route (D) does NOT re-shape the cert — it RE-POINTS the live spine from `case_III_arm_realization_rowOp` (`ForkedArm.lean:315`, `rigidityMatrixEdge`, no `⊕ Unit`) to the augmented arm, and fills the augmented arm's carried `(hM'eq, hB, hA, hD, hr)` against the D-canonical pin-zero bottom.

### (4.78.2) WHY §(4.67)/§(4.68) DID NOT KILL THIS — the `C = 0` reconciliation (recon Qs 1+2, kernel-checked).
§(4.67)/§(4.68.B) refuted the `_aug` arm at the operated `hA`, but **with `C ≠ 0`**: their bottom was the `mixedBottom` over `R(Gv)` (`Gv = G − v` is genuinely deficient — `def(Gv) ≥ def(G) = 0`, §(4.62) part 2 — so the count `card m₂` FORCES the v-incident a-shifted `e_b`-fill INTO the bottom, making `C = toBlocks₂₁ ≠ 0`), and the operated `inr` pin read `−ρ₀ − (L₀C)|_pin` then demanded `ρ₀ ∈ span(opaque blockBasisOn(e_b) pin reads)` (the refuted `hred`). **D-canonical changes the bottom.** Its bottom is the LITERAL `R(Gab)` (`Gab = G.splitOff v a b e₀`, the def-0 splitOff carrying the fresh `e₀ = (a,b)` edge), full-rank `D·(|V(Gab)|−1) = D·(|Gv|−1)` (the IH `hsplitGP` fact, D-CAN-3a's `hD` LANDED), so the count is met by the genuine IH matrix WITHOUT any `e_b`-fill — the `e_b` row leaves the bottom, every bottom-row endpoint is `≠ v`, and **`C = 0`** (the §(4.75) "pin-zero `Gab` bottom"). With `C = 0`: `A − L₀·C = A` (the `−L₀·C` correction is identically `0`, kernel-confirmed §(4.74.1)), so the §(4.68.B) "`(L₀C)|_pin` couples to opaque `e_b`-block" failure mode CANNOT arise — there is no `L₀C` term to demand `ρ₀ ∈ span`. **PROBE 5 (sorry-free):** for the corrected row `hingeRow b v ρ₀` (`b ≠ v`, `v ≠ a`), `hingeRow b v ρ₀ (columnOp hva (single v (finScrewBasis c))) = −ρ₀ (finScrewBasis c)` — the OPERATED `inr` corner read at the v-pin is `−ρ₀`, NONZERO (using only `b ≠ v`; `b ≠ a` is unused). So `A`'s `inr` row IS `coordEquiv(−ρ₀)`, the `corner_hA'_of_gate` row. The §(4.52) docstring claim (`Concrete.lean:803`–805: the operated `±r` row reads `ρ₀`) and §(4.74) ("opaque-basis blocks it") are reconciled: §(4.74) blocks the **un-augmented** `±r` slot (which reads `blockBasisOn(e_b,j₀)`, and `=ρ₀` is false for the opaque basis); §(4.52)/route (D) carries `ρ₀` as a GENUINE augmented `inr` row whose pin read IS `−ρ₀` by `reproducedSlot_pmR_acolumn_eq` (`Candidate.lean:2314`) — no opaque-basis identification needed. The §(4.67) "`±r` reads `0`" verdict was for the WRONG orientation `hingeRow a b ρ₀` (both `a,b ≠ v` ⟹ `ρ₀(S a − S b)` reads `0` at `single v`; PROBE 1a sorry-free); the corrected head-`v`-tail orientation reads `−ρ₀` (PROBE 5).

### (4.78.3) THE GENUINELY-NEW BRICKS (clause ii: FLAG-DON'T-FORCE — this is NOT pure wiring).
Route (D) is feasible, but four leaves have **no landed producer** and are siblings of the un-augmented bricks (each kernel-de-risked by a probe):
- **(D1) the augmented corner-apply** `rigidityMatrixEdgeAug_mul_columnOp_apply_corner_inr` — the `inr ()` row of `(augM * U)` at the v-pin column reads `−ρ₀ (finScrewBasis c)` (= `coordEquiv(−ρ₀)`); the `inl` e_a-panel rows read `blockBasisOn(e_a,·)` via the LANDED `rigidityMatrixEdge_mul_columnOp_apply_corner` (`Concrete.lean:1710`) applied to the `inl` sub-block. Kernel core = PROBE 5. ~1 commit.
- **(D2) the augmented C=0 collapse** `rigidityMatrixEdgeAug_mul_columnOp_submatrix_toBlocks₂₁_eq_zero` — the augmented sibling of the LANDED `rigidityMatrixEdge_mul_columnOp_submatrix_toBlocks₂₁_eq_zero` (`Concrete.lean:1774`), over the augmented row index with the bottom `m₂` mapping to pure-`Gab` `inl` rows (both endpoints `≠ v`). ~1 commit (mechanical clone; the `inr` slot is in `m₁`, not `m₂`, so it doesn't touch `C`).
- **(D3) the augmented `hAeq`/`hA` corner leaf** `corner_hA_aug_zero₁₂_of_gate` — under `C = 0`, `(A − L₀C).row = A.row` LI = `coordEquiv ∘ Sum.elim (blockBasisOn e_a) (−ρ₀)` LI, closed by `corner_hA'_of_gate` (PROBE 4, sorry-free) re-wrapped through `Matrix.linearIndependent_row_of_coordEquiv` (`Concrete.lean:148`) exactly as the un-augmented `linearIndependent_toBlocks₁₁_row_of_corner_gate` (`:2810`) does. Composes D1 + the C=0 collapse D2. ~1 commit.
- **(D4) the augmented `hM'eq`/`hblock`** — the `fromBlocks A B C D` read of `(augM * U).submatrix re en`, the augmented sibling of the spine's `hM'eq`; the `inl` sub-block via the LANDED `submatrix_columnOp_*` family (D-CAN-2's `submatrix_columnOp_toBlocks₂₂_eq_Gab` for the bottom `D`, the un-augmented corner-apply for the `inl` corner), the `inr` corner entry via D1. ~1 commit (bundled with D3 likely).

These are the `_aug` arm's `⚑`-flagged residual (`ForkedArm.lean:421`–423: "re-derive `hM'eq`/`hB`/`hblock` for the augmented matrix"). They are NEW LEMMAS, not assembly — but each is a near-verbatim clone of a landed un-augmented sibling + a one-line kernel fact (PROBE 5 / PROBE 4), zero new geometry, zero new MvPolynomial/LA theory. The `hB`/`L₀` slot: under `C = 0` the off-pin `B = L₀·D` factoring still needs an `L₀` (the corner's off-pin `inr` content `hingeRow b v ρ₀` at `body ≠ v` IS nonzero — PROBE 2 in §(4.67) showed the off-pin `B` block is nonzero), so the row op `Lrow` is STILL required to zero `B` (the `_zero₁₂` shape stays); BUT the `hA` no longer depends on it (`C = 0` ⟹ `A − L₀C = A` regardless of `L₀`). So `hB` is dischargeable via the LANDED `submatrix_columnOp_toBlocks₁₂_eq_mul_toBlocks₂₂` / span-membership machinery (the ON-path `hB` engine, §(4.74.1) "`hcomb`(±r) composes sorry-free via span-membership"), unchanged.

### (4.78.4) NO OVERRIDE-GATE RE-ENTRY (recon Q3, verified against LANDED source).
Route (D) consumes ONLY the discriminator's outputs the spine ALREADY produces (`exists_shared_redundancy_and_matched_candidate`, `Realization.lean:1825`): (a) the matched-candidate NONZERO gate `ρ₀ (panelSupportExtensor (q(candidateVtx i)) n') ≠ 0` (`:1879`) ⟹ `corner_hA'_of_gate`'s `hρe₀` (via `caseIIICandidate_supportExtensor_candidate` + `candidateVtx_succ_eq`); (b) the chain-pair PERP `ρ₀ (panelSupportExtensor (q a) (q b)) = 0` (`:1855`) ⟹ the genuine-row span membership `hr` via `hingeRow_mem_caseIIICandidate_rigidityRows_reproduced` (`Candidate.lean:2286`, consuming `hlink : G.IsLink e_b u w` + `hperp` at `t = 0`); (c) `ρ₀ ≠ 0` (`:1854`). NONE is the §(4.29) `caseIIICandidate`-override gate `ρ₀ ⊥̸ C(vᵢ₊₁, n')` that BLOCKED the §(4.68) αD arms — the bottom discharges GATE-FREE via the override ACCESSORS (D-CAN-2/§(4.72), LANDED), and the corner discharges from gates (a)+(b)+(c), all DIRECT-`q` discriminator outputs (no `shiftPerm`, the §(4.73.2) seam was a misdiagnosis, RESOLVED). The §(4.68.A) ROUTE-A `hS` wall is a DUAL-SPACE-chain-arm artifact — route (D) is the LITERAL-`Matrix` cert (D-canonical bottom = D-CAN-3a's `hD`), which never forms `hS`. So route (D) does NOT re-introduce the override gate. **VERIFIED.**

### (4.78.5) THE PATH TO CHAIN CLOSE — the exact remaining buildable sub-commit list (recon Q4, with rough sizes).
With the corner `hA` now via route (D), the rest of the `chainData_dispatch` composition is the §(4.73)/§(4.72.3) plan, re-pointed to the augmented arm. The 9/13 §(4.73) obligations that composed sorry-free (`hgp`/`hm₁`/`hm₂`/`hM'eq`-block-choice/`hD`/`hends`/`hends_Gv`/`hne_Gv`/`hdef`) are UNCHANGED (they don't touch the corner `±r` slot). Sub-commits:
1. **D1 + D2** (the augmented corner-apply `inr` read + the augmented C=0 collapse, `Concrete.lean`). ~1–2 commits. Kernel-de-risked (PROBE 5 / the landed un-augmented siblings).
2. **D3 + D4** (the augmented corner `hA` leaf + the augmented `hM'eq`/`hblock` read, `Concrete.lean`/`Candidate.lean`). ~1–2 commits. Composes D1/D2 + `corner_hA'_of_gate` (PROBE 4) + the bridge.
3. **the augmented-arm spine** `chainData_arm_realization_aug_zero₁₂` — clone `chainData_arm_realization_zero₁₂` (`Realization.lean:1481`) with `case_III_arm_realization_rowOp → case_III_arm_realization_aug` (LANDED), carrying the genuine `rRow := hingeRow b v ρ₀` + `hr` (gate (b)) + `hρe₀` (gate (a)). ~1 commit.
4. **`re`/`hre`** the corner⊕bottom `Sum.elim` selector with the corner half hitting `inl` e_a-panel + `inr ()`, the bottom half hitting the `reInr` Gab-selector (D-CAN-4 feeder `bottom_selection_of_crossFramework_span_Gab` LANDED) + injectivity. ~1 commit (bookkeeping).
5. **the `chainData_dispatch` router** (`Fin cd.d`: base/`d=3` → landed `chainData_split_realization`; interior `2 ≤ i` → the augmented spine of (3)) + **CHAIN-5** + the **C.3 `hIH`** one-field add (§(4.43), APPROVED; D1 `interior_hsplitGP` `Realization.lean:758` consumes it). ~1–2 commits. **Gate:** full `lake build` green + `lake lint` clean + axiom-clean.

**Total ~5–8 commits** to CHAIN close (23f), then ENTRY (23g) opens. The αE6 retirement of the now-LIVE `_aug` ladder is MOOT (route (D) uses it); the dead arms to retire shrink to `_matrix`/`_rowOp`/the dual-space chain arm.

### (4.78.6) THREE DESIGN-PASS CLAUSES — verdicts.
- **(i) verified against LANDED source.** Every load-bearing object re-read at its `def`/`theorem` this pass (not §(4.77) prose): the augmented cert `case_III_rank_certification_aug` (`Candidate.lean:2694`, the `(rRow, hr)` + `re : m₁⊕m₂ → ((…)⊕Unit)` signature), its engine `finrank_span_rigidityRows_ge_of_aug_submatrix_fromBlocks_zero₁₂` (`Concrete.lean:1258`) + `rigidityMatrixEdgeAug` (`:1045`) + `_rank_le_finrank_span` (`:1071`), the augmented arm `case_III_arm_realization_aug` (`ForkedArm.lean:426`, `hA : LI (A − L₀C).row`, the `⚑` residual `:421`–423); the LIVE spine `chainData_arm_realization_zero₁₂` (`Realization.lean:1481`, calls `_rowOp` `:1586`) + `case_III_arm_realization_rowOp` (`ForkedArm.lean:315`); `corner_hA'_of_gate` (`Concrete.lean:810`) + `corner_hA_zero₁₂_of_gate` (`:847`) + `linearIndependent_toBlocks₁₁_row_of_corner_gate` (`:2810`) + `rigidityMatrixEdge_mul_columnOp_apply_corner` (`:1710`) + `_submatrix_toBlocks₂₁_eq_zero` (`:1774`); `columnOp` (`Basic.lean:1274`, `S ↦ update S v (S v + S a)`) + `hingeRow`/`_apply`/`_swap` (`:490`/`:495`/`:547`) + `reproducedSlot_pmR_acolumn_eq` (`Candidate.lean:2314`); `hingeRow_mem_caseIIICandidate_rigidityRows_reproduced` (`:2286`); the discriminator (`Realization.lean:1825`, the `ρ₀`/perp/gate/`hr`-perp outputs); D-CAN-2/3a (`submatrix_columnOp_toBlocks₂₂_eq_Gab` `Concrete.lean:1896`-region, `linearIndependent_toBlocks₂₂_row_Gab_of_finrank_eq`). KT eq. (6.60)–(6.67) cross-checked. The spike `Build completed successfully (2785 jobs)`, 6 probes sorry-free.
- **(ii) FLAG-DON'T-FORCE — VERDICT-FEASIBLE, with the new-bricks flagged.** Route (D) is reported FEASIBLE (the make-or-break — the operated `inr` corner read `−ρ₀` under `C = 0` — is PROBE 5 kernel-confirmed; `corner_hA'_of_gate` fires PROBE 4). The four genuinely-new bricks (D1–D4, §(4.78.3)) are NAMED and flagged as new lemmas (siblings of landed un-augmented ones), NOT laundered as "wiring" (the §(4.73.4) item-(2)/(3) deferred-`hAeq` trap that §(4.74) sprang). NO motive/IH/C.0–C.6-contract change, NO `blockBasisOn`-def change, NO new geometry/LA/MvPolynomial theory. The §(4.77.4)(D) "cert re-shape, ~3–6 commits" estimate is REFINED to "re-point the live spine to the LANDED `_aug` ladder + 4 augmented-sibling bricks + the dispatch, ~5–8 commits". This SUPERSEDES the §(4.67)/§(4.68) `_aug`-blocked verdict **for the D-canonical (`C = 0`) bottom** — §(4.67)/§(4.68) are correct that `_aug` is blocked under the `mixedBottom` (`C ≠ 0`); they did not test the D-canonical bottom (which post-dates them, §(4.71)).
- **(iii) traced to GROUND.** Card UNCHANGED: corner `card m₁ = D = (D−1)` e_a-panel `inl` rows `+ 1` genuine `inr ()` `±r` row (NOT a `blockBasisOn(e_b,j₀)`); bottom `card m₂ = D·(|Gv|−1)` pure-`Gab` `inl` rows; total `D + D·(|Gv|−1) = D·|Gv| = D·(|V(G)|−1)` (PROBE 6, the cert `hm₁`/`hm₂`); the deficiency bound `≤ (D−1)·|E|` is the cert's `≤`-conclusion. The genuine `±r` functional `rRow = hingeRow b v ρ₀ : Dual ℝ (α → ScrewSpace k)` is the FULL-space lift of the per-block `ρ₀ : Dual ℝ (ScrewSpace k)` `corner_hA'_of_gate` consumes (the type seam IS bridged: the augmented `inr` row is the lift, read at the v-pin via `coordEquiv` back to `−ρ₀` on `ScrewSpace k`, PROBE 5 + PROBE 3). The gate object `ρ₀ (panelSupportExtensor (q(candidateVtx i)) n')` and the `ρ₀` of `rRow`/`hr` are the SAME `ρ₀` the discriminator binds (`Realization.lean:1825`, one existential `ρ₀` threaded to all of gate (a)/(b)/(c)) — confirmed against source. `D = screwDim k ≥ 3` at the interior arm; `d=3` stays on the separate `_matrix`/M₃ engine (zero-regression).

## (4.79) THE `chainData_dispatch` ROUTER — FULL-COMPOSITION COMPILER-CHECK + BITE-SIZED SUB-COMMIT DECOMPOSITION (the §(4.78.5) "sub-commit 5" decomposed; recon Q1–Q3, opus 2026-06-27 session #47, scratch spike `SpikeRouteDComposition.lean` compiled error-free modulo `sorry`, deleted before commit; tree clean).

> **Why this recon.** §(4.78.5) lumped "the `chainData_dispatch` router + CHAIN-5 + the C.3 `hIH` add" as ONE ~1–2-commit sub-commit. Two build dispatches then scope-shrank OFF the router (5a `rigidityMatrixEdgeAug_mul_columnOp_corner_hrow`, 5b `submatrix_columnOp_toBlocks₁₂_aug_eq`), each judging the full router "too large for one sitting" — the "2+ leaves feeding an unbuilt hard core" signal. This recon discharges the §(4.46)/(4.54) mandate (compiler-check the FULL composition before declaring "remaining = assembly") on the router itself, and decomposes the residual into confident-one-sitting sub-commits with EXACT signatures.

### (4.79.1) THE COMPOSITION FIRES — verdict (clause i: against LANDED source). The augmented interior arm composes.
The spike fired the LANDED augmented spine `chainData_arm_realization_aug_zero₁₂` (`Realization.lean:1625`) at the concrete interior `ChainData` binding (`v := cd.vtx iMatch.castSucc`, `0 < iMatch`), threading the landed feeders into its carried slots and `sorry`-feeding ONLY the genuinely-remaining gaps. **It compiled error-free (only `sorry` + style warnings, NO type errors).** Confirmed wirings (each type-checked against the landed `def`/`theorem`, not §(4.78) prose):
- **D1 the interior split-off realization fires.** `PanelHingeFramework.interior_hsplitGP cd iMatch hiM hD3 hV4 hSimple hG hnoRigid hIH` (`Realization.lean:758`) type-checks at the interior binding — confirming the C.3 `hIH` add is its sole new input (see §(4.79.4)).
- **the discriminator destructures.** `PanelHingeFramework.exists_shared_redundancy_and_matched_candidate cd hk1 hn v a b … h622lb hdef_Gab hsplitGP` (`Realization.lean:1974`) — the 18-component output `⟨q, ends, ρ₀, w, lamAB, rab, iMatch, n', hgpFull, hendsGv, hQalg, hρ₀ne, hρ₀e₀, hwLI, hwmem, hrab_blk, hρ₀_lam, hedgeGv, hLIcand, hgate⟩` destructures verbatim. It is fired at the BASE split `(v,a,b)`; the matched candidate `iMatch : Fin cd.d` is one of its outputs.
- **the gate bridges to the arm.** `rw [cd.candidateVtx_succ_eq hiM] at hLIcand hgate` (`Operations.lean:2824`, `candidateVtx i = vtx i.succ` for `0 < i`) rewrites the discriminator's gate `ρ₀(panelSupportExtensor (q(candidateVtx iMatch)) n') ≠ 0` into the arm's `ρ₀(panelSupportExtensor (q(aM)) n') ≠ 0` (`aM := vtx iMatch.succ`) — so `hLIcand` feeds the spine's `hLn` directly.
- **the `ends₁` override builds + feeds.** `ends₁ := Function.update (Function.update ends e_a (vM,aM)) e_b (vM,bM)`; `hends_ea₁`/`hends_eb₁` by `Function.update_self`/`_of_ne heab` (the model `chainData_split_realization:1277` pattern) feed the spine's `hends_ea`/`hends_eb`.
- **`hgab` from the discriminator's base GP.** `hgpFull aM bM (aM ≠ bM)` + `ofNormals_normal` gives `![q aM, q bM]` LI (the spine's `hgab`); `aM ≠ bM` via `cd.succ_ne_pred_castSucc hiM`.
- **`hgp` from the LANDED feeder.** `caseIIICandidate_supportExtensor_ne_zero_of_genPos G ends₁ q e_a e_b aM bM n' heab hLIcand hgab hends hgppair` (`Candidate.lean:1151`) type-checks (`hgppair` from `hgpFull` per distinct pair) — GATE-FREE.
- **`hM'eq` is `(fromBlocks_toBlocks M').symm`.** Pinning `A := M'.toBlocks₁₁` … `D := M'.toBlocks₂₂` (the §(4.64) Q1 read) discharges the spine's `hM'eq` by `rw [hM']; exact (Matrix.fromBlocks_toBlocks _).symm` — confirmed sorry-free.
- **`hr` composes off the reproduced-slot source.** `hingeRow_mem_caseIIICandidate_rigidityRows_reproduced G ends₁ q e_a e_b (q aM) n' (q bM) 0 hlink hperpR` (`Candidate.lean:2286`) type-checks with `hlink : G.IsLink e_b bM vM := hleb.symm` and the carried perp `hperpR` (a residual — see GAP G3 below); `rRow := hingeRow bM vM ρ₀` is the spine's genuine `inr` functional.

The spine's explicit geometry args (`cd iMatch hiM hV3 ends₁ hends_ea₁ hends_eb₁`) + `hLn := hLIcand` + `hgab` + `hgp` + `hends` + `hM'eq` + `hr` ALL unify; the residual is exactly the block-data slots. **This SUPERSEDES the §(4.78.5) "1–2 commits" estimate for sub-commit 5** — the router is decomposed below into 4 buildable sub-commits.

### (4.79.2) THE GENUINELY-REMAINING GAPS (clause ii: FLAG-DON'T-FORCE). The `sorry`d slots, each named + its landed-producer status.
The spike `sorry`d exactly these (none paper-able as "wiring"):
- **G1 — the matched-index router + `0 < iMatch`.** The dispatch case-splits on `(iMatch : ℕ)`: `iMatch = 0` → base/`d=3` floor via the LANDED `chainData_split_realization` (`Realization.lean:1164`); `0 < iMatch` → the augmented spine. The `0 < iMatch` interior-branch hypothesis is the case-split's `else` (mechanical). **No landed producer (it IS the router `Fin cd.d` match); buildable.**
- **G2 — the `re`/`hre`/`L₀` bundle.** `re : Fin (screwDim k) ⊕ Fin (D·(|Gv|−1)) → ((…×Fin(D−1)) ⊕ Unit)` (the corner⊕bottom selector), its injectivity, and the row-op weight `L₀`. Corner half = LANDED `reAug`/`reAug_injective` (`Concrete.lean:1427/1440`); bottom half = LANDED `bottom_selection_of_crossFramework_span_Gab` (`Concrete.lean:2880`, giving `reInr`/`hreInr`); `L₀` = the explicit fiberwise weight the **augmented `hB`/`L₀` factoring** consumes (NOT yet landed — see G4). **Partially landed; the assembly is buildable.**
- **G3 — the interior perp `hperpR : ρ₀(panelSupportExtensor (q aM) (q bM)) = 0`** at the MATCHED panel `(aM, bM) = (vtx iMatch.succ, vtx (iMatch−1))`. **NOT the base `hρ₀e₀`** (which is at the base split `(a,b)`; `iMatch ≠` base index in general). This is KT eq. (6.66)'s interior-redundancy carry — dischargeable from the discriminator's edge-grouped `Gv`-row widening `hedgeGv` (the `∃ nGv cGv … hingeRow a b ρ₀ = ∑ cGv • hingeRow …` output) via the interior `hρe₀` leaf (the planned `baseRedundancy_perp_interior_reproduced_panel` / `interior_hρe₀_of_widening`, `notes/Phase23f.md` references it). **No landed producer; the genuinely-new redundancy-carry leaf — FLAGGED, feasibility not yet compiler-confirmed (see G3 caveat in §(4.79.3)).**
- **G4 — `hB`/`hA`/`hD` (the block-LI/factoring reads).** `hA` = LANDED `corner_hA_aug_zero₁₂_of_gate` (`Concrete.lean:2088`), fed by the LANDED corner-`hrow` producer `rigidityMatrixEdgeAug_mul_columnOp_corner_hrow` (`:2152`) + the C=0 collapse (the un-augmented `rigidityMatrixEdge_mul_columnOp_submatrix_toBlocks₂₁_eq_zero` `:1839` on the `inl` sub-block — see §(4.79.3)(S3)). `hD` = LANDED `linearIndependent_toBlocks₂₂_row_Gab_of_finrank_eq` (`:2715`). `hB` = the **augmented `hB`/`L₀` factoring** (the augmented sibling of `submatrix_columnOp_toBlocks₁₂_eq_mul_toBlocks₂₂` `:3119`, off the LANDED `submatrix_columnOp_toBlocks₁₂_aug_eq` `:2043`) — **NOT yet landed; the one genuinely-new matrix brick.**
- **G5 — `hends`/`hends_Gv`/`hne_Gv` (the candidate-link recordings).** `hends : ∀ e ∈ E(G), G.IsLink e (ends₁ e).1 (ends₁ e).2` (from `hendsGv` for surviving `Gv`-edges + the two re-inserted-hinge records `hends_ea₁`/`hends_eb₁` + `hlea`/`hleb`); `hends_Gv`/`hne_Gv` (the surviving-`Gv` link + nonzero-support recordings, the model `chainData_split_realization:1289/1294` pattern off `hgpFull`). **No single landed producer; the per-edge classification, byte-near the model — buildable.**
- **G6 — `hm₁`/`hm₂` (the card facts).** `hm₁ : card (Fin (screwDim k)) = screwDim k` and `hm₂ : card (Fin (D·(|Gv|−1))) = D·(|Gv|−1)` are both `Fintype.card_fin` (`rfl`/`simp`). **Trivial; bundles with G2.**

### (4.79.3) STRUCTURAL INVARIANTS / CARDINALITIES — traced to ground (clause iii).
- **(S1) the `reAug`/`reInr` cards + `hdisj`.** Corner `m₁ = Fin (screwDim k)`: the `D−1` panel slots → `inl (e_a, j)`, the `±r` slot → `inr ()` (`cornerRowInjectionAug`, `Concrete.lean:1403`); bottom `m₂ = Fin (D·(|Gv|−1))` → `inl (reInr i)` (`reAug … (Sum.inr i) = Sum.inl (reInr i)` is `rfl`). The cross-disjointness `hdisj : ∀ i, (reInr i).1 ≠ e_a` holds because the bottom rows are surviving `Gv`-edges (endpoints `≠ v`) while `e_a` is incident to `v` — confirmed: `reInr` comes from `bottom_selection_of_crossFramework_span_Gab`'s `lift`, which lands on `Gab`-edges, all `≠` the re-inserted `e_a`. `reAug_injective` needs exactly `hreInr` (bottom injectivity, from the selector) + `hdisj`.
- **(S2) the `m₁`/`m₂` card facts.** `hm₁ = screwDim k` (`card_fin`), `hm₂ = screwDim k · (V(Gv).ncard − 1)` (`card_fin`) — match the spine's `hm₁`/`hm₂` slot types verbatim (spike pinned `m₁ := Fin (screwDim k)`, `m₂ := Fin (screwDim k * (V(G.removeVertex (cd.vtx iMatch.castSucc)).ncard - 1))` and the spine accepted them).
- **(S3) the corner edge `e_a`/`ends`-override facts.** The corner-`hrow` producer needs `hea1 : (ends₁ e_a).1 = v` + `hea2 : (ends₁ e_a).2 ≠ v` — both off `hends_ea₁ : ends₁ e_a = (vM, aM)` (`.1 = vM = v` ✓; `.2 = aM ≠ v` by `havM`). The D1 `_apply_corner_inr` needs `b ≠ v` = `hbvM` ✓. The C=0 collapse `hC : …toBlocks₂₁ = 0`: the bottom `m₂` rows route through `reAug … (Sum.inr i) = Sum.inl (reInr i)` to `inl` pure-`Gab` rows; the augmented matrix's `inl`-sub-block entry agrees with the un-augmented `rigidityMatrixEdge` by defeq (the `hentry` `mul_apply; rfl` bridge, the same one inside `rigidityMatrixEdgeAug_mul_columnOp_corner_hrow`), so the un-augmented `rigidityMatrixEdge_mul_columnOp_submatrix_toBlocks₂₁_eq_zero` (`:1839`) discharges `hC` after the `inl`-reindex — **a one-step bridge, FLAGGED as part of G4's `hA` wiring (not separately landed).**
- **(S4) the `ρ₀` is shared.** The corner `hA`'s gate `hρe₀` (negated to `(−ρ₀)(C(e_a)) ≠ 0` inside `corner_hA_aug_zero₁₂_of_gate`), the genuine `inr` row `rRow = hingeRow bM vM ρ₀`, and the perp `hperpR` ALL carry the SAME `ρ₀` the discriminator binds (`exists_shared_redundancy_and_matched_candidate`'s single existential `ρ₀`) — confirmed in the spike (one `ρ₀` threaded to `hLIcand`/`hgate`/`hρ₀e₀`/`rRow`/`hperpR`). **G3 caveat:** `hperpR` is at `(aM, bM)` (matched panel), whereas the discriminator's `hρ₀e₀` is at `(a, b)` (base panel) — they are the SAME `ρ₀` but DIFFERENT panels, so `hperpR` is genuinely-new content (G3), not a `simpa` of `hρ₀e₀`.

### (4.79.4) THE C.3 `hIH` ADD — blast radius traced to source (recon Q2).
The interior arm reaches `hsplitGP` ONLY via D1 `interior_hsplitGP` (`Realization.lean:758`), which consumes `hIH`/`hnoRigid`/`hV4`(`hV3`)/`hSimple`/`hG`/`hD3` — confirmed by the spike (it type-checks at the interior binding with exactly these). The C.3 consume-shape (`hcand`/`hdispatch`) does NOT currently carry `hIH`. The **one-bundle addition** (`hIH` + `hnoRigid` + `hV4`) touches the C.0 producer/consumer/d=3-adapter trio:
- **Consumer** `case_III_hsplit_producer_all_k` (`Arms.lean:853`, the `hcand` field) — widen `hcand`'s `∀`-prefix to also bind `hIH`/`hnoRigid`/`hV4`; the body (line ~890, the chain-arm branch) ALREADY has `hIH`/`hnoRigid`/`hV4'` in scope (it binds them at lines 837/839/887), so it just passes them into the `hcand` call.
- **Producer** `case_III_realization_all_k` (`Realization.lean:2075`, the `hdispatch` field) — widen `hdispatch`'s `∀`-prefix identically; the body re-forwards `hdispatch` unchanged (line 2113 in the d=3 wrapper).
- **d=3 adapter** `case_III_realization` (`Realization.lean:2113`) — the `hdispatch` callback fills the new `hIH`/`hnoRigid`/`hV4` args but the d=3 dispatch `case_III_candidate_dispatch` DROPS them (d=3 has no interior arm). Mechanical.
- **ENTRY `exists_chain_data_of_noRigid`** (`Reduction.lean:383`) — **NOT touched by the `hIH` add** (it produces the chain tuple; `hIH` is ambient in the consumer's body). It IS touched by the separate CHAIN-5 reshape (the `(v,a,b,c,…)`-8-tuple → `cd : G.ChainData n`), which §(4.78.5)/CHAIN-5 owns. **The `hIH` add and CHAIN-5 are independent reshapes of the same consume-shape — do them in ONE commit (the C.0 lockstep), not two passes.**

This is a one-bundle addition touching 3 decls in lockstep (NOT a motive/IH-strength change); the d=3 line stays green (the new args dropped). MATCHES §(4.43)/§(4.73.3).

### (4.79.5) THE BITE-SIZED SUB-COMMIT LIST — ordered, exact signatures, sizes (recon Q3). Replaces the §(4.78.5) "sub-commit 5".
Each is a confident-one-sitting deliverable; feasibility-flags noted.
1. **(5c) the augmented `hB`/`L₀` factoring** `submatrix_columnOp_toBlocks₁₂_aug_eq_mul_toBlocks₂₂` (`Concrete.lean`, the augmented sibling of `submatrix_columnOp_toBlocks₁₂_eq_mul_toBlocks₂₂` `:3119`). Signature: same shape as `:3119` but over `rigidityMatrixEdgeAug ends hgp rRow` and the augmented `re : … ⊕ Unit` index; reads the off-`v` `toBlocks₁₂` (LANDED `submatrix_columnOp_toBlocks₁₂_aug_eq` `:2043`) as `Matrix.of (∑ⱼ∈{μ·=i'} cGv) * toBlocks₂₂` via the LANDED engine `dual_comb_reindex_fiberwise` (`:2994`). The `inr ()` `±r` row's off-pin `B`-content is `rRow` precomposed with the column op (NOT a per-`ScrewSpace` `hingeRow`) — threaded through the `hrowB`/`hcomb` widening. **~1–2 commits.** COMPILER-CONFIRMED feasible (the un-augmented sibling + the LANDED `_aug_eq` B-read compose; the `_aug` row is the only new thread). The ONE genuinely-new matrix brick.
2. **(5d) the interior perp `hρe₀` leaf** `baseRedundancy_perp_interior_reproduced_panel` (or `chainData_interior_hρe₀_of_widening`) (`Realization.lean`/`Candidate.lean`). Signature: from the discriminator's base `ρ₀`/`hρ₀e₀`/`hedgeGv` (the edge-grouped `Gv`-row widening) at the matched candidate `iMatch`, produce `ρ₀(panelSupportExtensor (q(vtx iMatch.succ)) (q(vtx (iMatch−1)))) = 0` (the perp at the MATCHED panel). **~1–2 commits. FLAGGED — feasibility NOT yet compiler-confirmed** (the spike `sorry`d it; this is KT eq. (6.66)'s genuinely-new redundancy carry — recommend a dedicated kernel spike on `hedgeGv` → matched-panel-perp BEFORE building, per §(4.62) constructibility-recon). The ONE flagged-uncertain leaf.
3. **(5e) the `re`/`hre`/`L₀` + bottom assembly** (`Concrete.lean`/`Realization.lean`, the dispatch-body local). Bundles: build `reInr`/`hreInr`/`re₂`/`hbot2`/`hbot1`/`hj`/`hsupp`/`hrank` from `bottom_selection_of_crossFramework_span_Gab` (`:2880`, fed `F₂ = R(Gab)`/`lift`/`hlift_ends`/`hlift_supp` off the candidate `ends`-override accessors + `hfr₂` from `exists_ofNormals_finrank_span_rigidityRows_eq_of_hsplitGP` `:822`); set `re := reAug ⟨e_a,_⟩ reInr`, `hre := reAug_injective … hreInr hdisj`; fire D-CAN-3a's `hD := linearIndependent_toBlocks₂₂_row_Gab_of_finrank_eq`; set `L₀` = the explicit fiberwise weight from (5c). **~1–2 commits.** COMPILER-CONFIRMED feasible (all feeders LANDED; the spike confirmed the types unify).
4. **(5f) the `chainData_dispatch` router + C.3 `hIH` add + CHAIN-5** (`Realization.lean`, the capstone). Bundles: the `Fin cd.d` router (`rcases (iMatch : ℕ)`: `0` → `chainData_split_realization`; `0 < ·` → the augmented spine of §(4.79.1), threading 5c/5d/5e + `hA := corner_hA_aug_zero₁₂_of_gate` fed by the corner-`hrow` producer + the C=0 collapse bridge (S3) + `hgp`/`hends`/`hends_Gv`/`hne_Gv` (G5) + `hr` (5d's perp)); the C.3 `hIH` one-bundle add (§(4.79.4), the 3-decl lockstep — `case_III_hsplit_producer_all_k`/`case_III_realization_all_k`/`case_III_realization`); CHAIN-5 (the `(v,a,b,c,…)`-8-tuple → `cd : G.ChainData n` reshape + `d=3` zero-regression adapter). **~2–3 commits** (the router + the lockstep + CHAIN-5 may split). COMPILER-CONFIRMED the firing composes (§(4.79.1)); CHAIN-5's `d=3` adapter is the only fiddly sub-part (`case_III_candidate_dispatch` byte-reachable via the C.4 `vtx = ![b,v,a,c]` map). **Gate:** full `lake build` green + `lake lint` clean + axiom-clean.

**Total ~5–8 commits to CHAIN close** (5c, 5d, 5e, then 5f's 2–3). On (5f) landing the CHAIN layer closes and ENTRY (23g) opens. **Build order:** 5c + 5e first (compiler-confirmed, independent); 5d's kernel spike next (the one flagged-uncertain leaf — do it before 5f so 5f has all inputs); 5f last. Only 5d carries residual feasibility risk; everything else is compiler-confirmed by the §(4.79.1) full-composition spike.

### (4.79.6) THREE DESIGN-PASS CLAUSES — verdicts.
- **(i) verified against LANDED source.** Every load-bearing object fired at its landed signature in the spike (not §(4.78) prose): `chainData_arm_realization_aug_zero₁₂` (`Realization.lean:1625`), `interior_hsplitGP` (`:758`), `exists_shared_redundancy_and_matched_candidate` (`:1974`, the 18-tuple output), `candidateVtx_succ_eq` (`Operations.lean:2824`), `caseIIICandidate_supportExtensor_ne_zero_of_genPos` (`Candidate.lean:1151`), `hingeRow_mem_caseIIICandidate_rigidityRows_reproduced` (`:2286`), `corner_hA_aug_zero₁₂_of_gate` (`Concrete.lean:2088`), `rigidityMatrixEdgeAug_mul_columnOp_corner_hrow` (`:2152`), `submatrix_columnOp_toBlocks₁₂_aug_eq` (`:2043`), `bottom_selection_of_crossFramework_span_Gab` (`:2880`), `exists_ofNormals_finrank_span_rigidityRows_eq_of_hsplitGP` (`:822`), the C.3 trio `case_III_hsplit_producer_all_k` (`Arms.lean:853`)/`case_III_realization_all_k` (`Realization.lean:2061`)/`case_III_realization` (`:2100`). Spike compiled error-free modulo `sorry`.
- **(ii) FLAG-DON'T-FORCE.** Two leaves carry no landed producer + are genuinely-new: **G4/5c** the augmented `hB`/`L₀` factoring (COMPILER-CONFIRMED feasible — the un-augmented sibling composes) and **G3/5d** the interior perp `hρe₀` (FLAGGED — feasibility NOT compiler-confirmed; recommend a dedicated kernel spike on `hedgeGv → matched-panel-perp` BEFORE building 5d). All other slots are LANDED-feeder assemblies. NO motive/IH-strength change; the C.3 `hIH` add is a 3-decl lockstep one-bundle addition (§(4.79.4)). NO `blockBasisOn`-def change, NO new geometry/MvPolynomial theory.
- **(iii) traced to GROUND.** Cards/structural invariants confirmed compatible (§(4.79.3)): `reAug`/`reInr` cards + `hdisj` (bottom-`Gv`-edges `≠ e_a`), `hm₁ = screwDim k`/`hm₂ = D·(|Gv|−1)` (`card_fin`), the corner `e_a`/`ends`-override facts (`hea1`/`hea2`/`b ≠ v` off `hends_ea₁`/`hbvM`), the C=0 collapse via the `inl`-sub-block defeq bridge (S3), and the SHARED `ρ₀` across gate/`rRow`/perp (with the G3 caveat: matched-panel `(aM,bM)` ≠ base-panel `(a,b)`, so the perp is genuinely-new content).

## (4.80) THE G3/5d KERNEL SPIKE — VERDICT: **G3 is NOT closeable as planned. Route (D)'s `hr` re-hits the §(4.73.2)/§(4.76.2) seam — the discriminator's `hedgeGv` widening does NOT yield the DIRECT-`q` SHORT-CIRCUIT-panel perp; the LANDED redundancy-carry crux only delivers the DIRECT-`q` CHAIN-EDGE panel `(vtx(i+1), vtx i)`, never the short-circuit `(vtx(i+1), vtx(i−1))` that route (D)'s direct-`q` augmented candidate demands.** This is route (D)'s gap. FLAG-DON'T-FORCE STOP — the obstruction is a genuine panel-index mismatch (`vtx i` vs `vtx(i−1)` in the second panel normal), not wiring; the choice between the §(4.77.4) escapes is a user-adjudication question. (opus, 2026-06-27 session #48, kernel-checked spike `SpikeG3.lean`, 3 probes, `Build completed successfully (2785 jobs)` modulo `sorry`, deleted before commit; tree clean, `d=3` fully green.)

> **Why this recon.** §(4.79.5) flagged **G3/5d** (the interior perp `hperpR : ρ₀(panelSupportExtensor (q aM) (q bM)) = 0` at the matched panel `(aM,bM) = (vtx iMatch.succ, vtx(iMatch−1))`) as the ONE leaf whose feasibility was NOT compiler-confirmed, and mandated a dedicated kernel spike on `hedgeGv → matched-panel-perp` BEFORE building 5d. The coordinator's acceptance scrutiny noted this short-circuit panel `(i+1, i−1)` is precisely the panel the §(4.73.2)/§(4.76.2) SEAM declared genuinely NOT landed for the direct-`q` route — so the decisive question is whether the discriminator's `hedgeGv` (a possibly-newer output than the landed crux that prose examined) bridges it. It does not.

### (4.80.1) THE NEEDED PERP vs THE LANDED OUTPUT — verified against LANDED source (clause i).
- **What `hr` needs (route (D)'s augmented spine).** `chainData_arm_realization_aug_zero₁₂` (`Realization.lean:1625`) threads `hr : rRow ∈ span (caseIIICandidate G ends q (edge i) (edge (i−1)) (fun j => q(vtx i.succ,j)) n' (fun j => q(vtx(i−1).castSucc,j)) 0).rigidityRows` (`:1666`) on the **DIRECT-`q`** candidate (no `shiftPerm`). The §(4.79.1) spike feeds it via `hingeRow_mem_caseIIICandidate_rigidityRows_reproduced … (q aM) n' (q bM) 0 hlink hperpR` (`Candidate.lean:2286`), whose `hperp : ρ₀(panelSupportExtensor (n_u + t•n') n_r) = 0` at `t=0` reduces (kernel-confirmed `zero_smul; add_zero`) to **`ρ₀(panelSupportExtensor (q(vtx i.succ)) (q(vtx(i−1).castSucc))) = 0`** — the direct-`q` SHORT-CIRCUIT panel `(vtx(i+1), vtx(i−1))`.
- **What the LANDED crux delivers.** `baseRedundancy_perp_interior_reproduced_panel` (`ForkedArm.lean:640`) + the relabel bridge `reproduced_panel_eq_splice_panel` (`:547`) — composed in `interior_hρe₀_of_widening` (`:739`) / `interior_hρe₀_of_baseWidening` (`:785`), the lemmas that consume EXACTLY the discriminator's `hedgeGv` bundle — produce the perp at the relabelled panel `(qρ(vtx i.succ), qρ(vtx(i−1).castSucc))` with `qρ = q ∘ shiftPerm i.castSucc`, which `reproduced_panel_eq_splice_panel` collapses to the **direct-`q` CHAIN-EDGE panel `(vtx(i+1), vtx i)`** (`:555`, the `edge i` panel). Root cause: the framework-free redundancy carry `interior_group_acolumn_eq_neg_baseRedundancy` (`ChainColumn.lean:729`) pins the `edge i`-group column = `−ρ₀` **at the tail body `vtx i`** (`:744`); `edge i` links `vtx i — vtx(i+1)`, so via `edgeGroup_acolumn_mem_block` + `ofNormals_supportExtensor_eq_panel_of_ends` (`ForkedArm.lean:596`, with `hends_i : ends(edge i) = (vtx i.succ, vtx i.castSucc)`) the perp lands on the chain-edge panel. The carry NEVER reaches `(i+1, i−1)`: `vtx(i−1)` appears only as the TAIL of `edge(i−1)`, never as the head of `edge i`, and the short-circuit panel is the SPLICED edge (the bridge over the removed degree-2 body `v = vtx i`), not a `G`-link the carry is anchored to.

### (4.80.2) THE SPIKE — what compiled, the residuals read (clause ii).
Three probes (`SpikeG3.lean`, built on `…CaseIII.Realization`, **build green modulo `sorry`, NO type errors**):
- **PROBE 1a (SORRY-FREE).** `(fun j => q(vtx i.succ,j)) = (fun j => q(vtx⟨i+1⟩,j))` — the FIRST panel normals agree (`Fin.val_succ`). So the mismatch is isolated to the second normal.
- **PROBE 1b (negative control, UNPROVABLE).** Stating `(fun j => q(vtx(i−1).castSucc,j)) = (fun j => q(vtx⟨i⟩,j))` leaves the irreducible residual `⊢ (fun j ↦ q (cd.vtx ⟨↑i - 1, ⋯⟩.castSucc, j)) = fun j ↦ q (cd.vtx ⟨↑i, ⋯⟩, j)` — distinct chain vertices (`vtx` injective, `i−1 ≠ i` for `i ≥ 2`). Confirms the two panels are NOT the same object.
- **PROBE 2 (the PLANNED route, residual is the seam).** Fed the discriminator's `hedgeGv` bundle to the LANDED `interior_hρe₀_of_baseWidening`, then `reproduced_panel_eq_splice_panel`. The hypothesis `hlanded` resolves to **`ρ₀ (panelSupportExtensor (fun j ↦ q (cd.vtx ⟨↑i + 1, ⋯⟩, j)) (fun j ↦ q (cd.vtx ⟨↑i, ⋯⟩, j))) = 0`** (chain-edge panel) while the goal `G3_needed_panel` is **`ρ₀ (panelSupportExtensor (fun j ↦ q (cd.vtx i.succ, j)) (fun j ↦ q (cd.vtx ⟨↑i - 1, ⋯⟩.castSucc, j))) = 0`** (short-circuit panel). Differ exactly in the second normal `q(vtx i)` (have) vs `q(vtx(i−1))` (need); no rewrite closes it.
- **PROBE 3 (no free bridge from the full discriminator output).** Handed BOTH landed perps (`hρ₀e₀` at base panel `(vtx 0, vtx 2)`; `hchain` at chain-edge `(vtx(i+1), vtx i)`) + the short-circuit LI `hgab` + the gate `hgate`, the goal `ρ₀(panelSupportExtensor (q(vtx i.succ)) (q(vtx(i−1)))) = 0` is UNPROVABLE: `panelSupportExtensor = complementIso ∘ normalsJoin` (`PanelLayer.lean:232`) is NOT linear in its second argument, so the short-circuit extensor is no linear combination of the two landed-perp extensors — `ρ₀` annihilating those says nothing about it. `q(vtx(i−1))` appears as a panel-second-arg in NO available perp.

### (4.80.3) WHY ROUTE (D) CANNOT BORROW THE RELABEL-`q` CRUX (clause iii — traced to ground).
The LANDED crux DOES deliver the short-circuit-shaped perp `ρ₀(panelSupportExtensor (qρ a) (qρ b)) = 0` — but in the **relabel-`q` framework** `qρ = q ∘ shiftPerm`, where the DEAD-ARM `_sep` route `case_III_arm_corner_assembly` (`ForkedArm.lean:1022`) consumes it (`:1042` `hρe₀`, fed to `hingeRow_mem_caseIIICandidate_rigidityRows_reproduced` at `:1086`). Route (D) is the LIVE `_zero₁₂`/`_aug` cert built on the **DIRECT-`q`** candidate (`caseIIICandidate … (fun j => q(vtx i.succ,j)) n' (fun j => q(vtx(i−1).castSucc,j)) 0`, `Realization.lean:1658`/`:1667`), chosen because its corner `hA` fires from the discriminator's **direct-`q` NONZERO gate** `ρ₀(panelSupportExtensor (q(candidateVtx i)) n') ≠ 0` ALONE (the §(4.73.2)/§(4.78) finding; `candidateVtx i = vtx i.succ` direct-`q`). The two framings are MUTUALLY EXCLUSIVE: route (D)'s `hA` needs the direct-`q` candidate (gate fires there); its `hr` needs the direct-`q` short-circuit perp — which only the relabel-`q` crux produces, and only inside the relabel-`q` candidate. Adopting `qρ` for the candidate would un-fire the direct-`q` gate the corner `hA` rests on. So `hr` re-hits the seam route (b) hit (§(4.76.2)): "the landed perp crux gives the chain-edge panel `(i+1,i)`; the spine's direct-`q` reproduced panel is the short-circuit `(i+1,i−1)`" — confirmed REAL for route (D), kernel-checked, not prose.

### (4.80.4) THE OPEN DECISION FOR THE USER — flag-don't-force (NOT a unilateral pick).
The §(4.79.5) decomposition stands EXCEPT 5d; 5c/5e are still compiler-confirmed feasible. The escapes are the SAME §(4.77.4) family (the obstruction is the same direct-`q`-short-circuit-panel gap route α also hit, now reconfirmed for route (D)'s perp instead of route α's escape):
- **(β) KT's disjunction-over-all-`Mᵢ` dimension count (eqs. 6.65–6.67).** Removes the per-candidate `n'`/perp ENTIRELY — KT shows `span(⋃ C(Lᵢ))` over all `d` candidates has dimension `D`, so the nonzero `r` cannot annihilate all of it, hence ≥1 of `M₀…M_{d−1}` is full rank. This dissolves the short-circuit-panel obstruction at its root (no per-candidate reproduced perp to land), but changes WHICH candidate the cert certifies (an existential over candidates, not a fixed matched `i`), reshaping the dispatch/spine. ~Large (re-opens the CHAIN-2c dispatch architecture); maximally KT-faithful. **§(4.77.4)(β); recommended candidate.**
- **(γ) Re-derive `baseRedundancy_perp` at the short-circuit panel directly.** The redundancy carry is currently anchored to the chain edge `edge i` (tail `vtx i`); KT eq. (6.66)'s carry "across `vᵢ`" is to the SPLICED edge `(vtx(i+1), vtx(i−1))`, the bridge over the removed degree-2 body. Whether a framework-free value-read can reach the spliced (non-`G`-link) panel — as `baseRedundancy_perp_interior_reproduced_panel` reaches the `G`-link `edge i` — is NOT settled by this spike; it would be a NEW genuinely-new crux (the spliced edge is not a `G`-edge, so `interior_group_acolumn_eq_neg_baseRedundancy`'s `G.IsLink` anchor does not apply as-is). A dedicated recon on whether KT's (6.66) carry admits a spliced-panel value-read is the narrow-fix probe; feasibility UNKNOWN. **Surfaced, not recommended without that recon.**
- **(α′) Candidate-aware discriminator** — already rejected §(4.77.4)(α′) (circularity / two-panel collision); unchanged.

**Recommendation for adjudication:** (β) is the root-cause fix and maximally KT-faithful, at the cost of a CHAIN-2c dispatch reshape. (γ) is the narrow fix but its feasibility is genuinely open (needs its own recon). Route (D)'s other three sub-commits (5c/5e + the 5f router shell modulo `hr`) are landed-feasible and would be REUSED under either (the augmented `_aug` ladder, the corner `hA`/`hB`/`hD`, the bottom — none touches the `hr` perp). The decision is whether to invest in (β)'s architecture reshape or recon (γ)'s narrow fix first.

### (4.80.5) THREE DESIGN-PASS CLAUSES — verdicts.
- **(i) verified against LANDED source.** Every load-bearing object read at its `def`/`theorem` (not §(4.79) prose): the `hr` consumer `hingeRow_mem_caseIIICandidate_rigidityRows_reproduced` (`Candidate.lean:2286`, `hperp` at `t=0` = short-circuit panel); the augmented spine `chainData_arm_realization_aug_zero₁₂` (`Realization.lean:1625`, direct-`q` candidate bindings `:1658`/`:1667`); the LANDED crux `baseRedundancy_perp_interior_reproduced_panel` (`ForkedArm.lean:640`, conclusion at chain-edge panel `:657`) + `reproduced_panel_eq_splice_panel` (`:547`, relabel→chain-edge collapse `:555`) + `interior_hρe₀_of_baseWidening` (`:785`, consumes `hedgeGv`); the framework-free carry `interior_group_acolumn_eq_neg_baseRedundancy` (`ChainColumn.lean:729`, tail-body `vtx i` column `:744`); `panelSupportExtensor` (`PanelLayer.lean:232`, `complementIso ∘ normalsJoin`); the dead-arm `_sep` consumer `case_III_arm_corner_assembly` (`ForkedArm.lean:1022`/`:1042`); `candidateVtx`/`candidateVtx_succ_eq` (`Operations.lean:2783`/`2824`). Spike compiled error-free modulo `sorry`.
- **(ii) FLAG-DON'T-FORCE — applied as VERDICT-STOP.** The residual that cannot be closed (the short-circuit panel perp is not derivable from `hedgeGv`/the landed crux/the full discriminator output) IS the verdict; reported, not forced. No route unilaterally picked — the §(4.77.4)(β)/(γ)/(α′) directions handed over with their obstructions. The landed crux + relabel bridge + `_sep` consumer stay CORRECT, axiom-clean leaves (they live in the relabel-`q` `_sep` arm; they do not assert the direct-`q` short-circuit perp).
- **(iii) traced to GROUND.** The mismatch is a structural panel-index mismatch, not bookkeeping: `panelSupportExtensor` is a function of BOTH normals (nonlinear in each via `complementIso ∘ normalsJoin`), the two panels differ in the second normal (`vtx i` vs `vtx(i−1)`, distinct chain vertices), and the short-circuit panel is the SPLICED (non-`G`-link) edge the redundancy carry's `G.IsLink` anchor never reaches. `d=3` untouched (the `_matrix`/M₃ path; the spliced-panel coincidence is a single-swap there, `case_III_arm_realization_M3`'s `hqρ`). [**Caveat corrected by §(4.81):** the "(nonlinear in each)" phrasing is wrong — `panelSupportExtensor` IS bilinear/alternating (it is the wedge `normalsJoin` through the linear iso `complementIso`). The §(4.80) PROBE-3 "no free linear bridge" conclusion is right for the WRONG reason; §(4.81) re-grounds it on the missing *coplanarity*, not nonlinearity.]

## (4.81) THE (γ) NARROW-FIX KERNEL SPIKE — VERDICT: **(γ) is INFEASIBLE on the direct-`q` route.** The short-circuit-panel perp IS derivable framework-free from the LANDED chain-edge perp by a SORRY-FREE bilinearity step — but ONLY given the degree-2 coplanarity `q(vtx i) ∈ span {q(vtx(i+1)), q(vtx(i−1))}` (nonzero `vtx(i−1)`-coefficient), and that coplanarity is **provably FALSE** for the project's generic seed `q` (`AlgebraicIndependent ℚ q` ⟹ three distinct chain-body normals are linearly INDEPENDENT). So (γ) re-hits the SAME family of obstruction route α did (§(4.77)): a geometrically-FALSE-for-generic-`q` side-condition, not a missing-but-true crux. **No spliced-panel value-read circumvents it: KT eq. (6.66) does NOT carry the redundancy to the spliced panel at all — it carries to the CHAIN-EDGE panel (`v_i v_{i+1}`), exactly what the landed crux already delivers.** The short-circuit panel is a PROJECT artifact of the direct-`q` candidate's reproduced slot, not a KT (6.66) object. (opus, 2026-06-27 session #49, kernel-checked spike `SpikeGamma.lean`, 7 declarations — 4 bilinearity + PROBE B1/B2/C — `Build completed successfully (2784 jobs)` modulo the 1 intentional negative-control `sorry`, deleted before commit; tree clean, `d=3` fully green.)

> **Why this recon.** §(4.80.4) handed the user two routes — (β) KT's disjunction-over-all-`Mᵢ` (a large CHAIN-2c reshape) and (γ) a narrow spliced-panel-perp re-derivation (feasibility UNKNOWN). The user chose to recon (γ). The decisive question: can the project's framework-free machinery DERIVE the direct-`q` short-circuit-panel perp `ρ₀ (panelSupportExtensor (q(vtx(i+1))) (q(vtx(i−1)))) = 0` — by combining the LANDED chain-edge column reads with the `vtx i`-column cancellation — as a new value-read leaf analogous to `interior_group_acolumn_eq_neg_baseRedundancy` reaching the spliced (non-`G`-link) panel? **No** — but for a sharper reason than §(4.80) gave: the bridge IS a one-step bilinearity (NOT a value-read), and it needs a normal-space coplanarity the generic seed forbids.

### (4.81.1) KT eq. (6.66) RE-READ — the carry is to the CHAIN-EDGE panel, NOT the spliced panel (the task premise re-grounded; clause i, primary source).
KT 2011 p.696–698 (pdf p.50–52), eqs. (6.60)–(6.67) re-read end-to-end. Eq. (6.66) states, for `2 ≤ i ≤ d−1`:
`∑_{1≤j≤D−1} λ_{(v_i v_{i+1})_j} r_j(q(v_i v_{i+1})) = ± r` where `r = ∑_j λ_{(v_0 v_2)_j} r_j(q(v_0 v_2))` is the redundancy (= the project's `ρ₀`). **The panel KT carries `r` onto is `q(v_i v_{i+1})` — the CHAIN EDGE `(v_i, v_{i+1})`.** The spliced edge `v_0 v_2` appears ONLY at the base, inside `r` itself (the redundant row `(v_0 v_2)_{i*}`). The "carry across `v_i`" (KT's eq. (6.59) `p_i(v_{i−1}v_i) = q_1(v_i v_{i+1})` placement + the eq. (6.60)→(6.64) column op adding the `v_i`-column to the `v_{i+1}`-column) lands the redundancy on the chain edge `v_i v_{i+1}`, read off the BASE seed `q_1` — exactly `baseRedundancy_perp_interior_reproduced_panel`'s conclusion `ρ₀(panelSupportExtensor (q(vtx(i+1))) (q(vtx i))) = 0` (`ForkedArm.lean:657`). So the task brief's framing ("ρ₀ annihilating the spliced panel IS KT's (6.66) carry") is **not accurate against the primary source**: KT (6.66) annihilates the chain-edge panel; the spliced panel `(v_{i+1}, v_{i−1})` is not a KT (6.66) target. KT's disjunction (6.67) then reasons over `C(L_i)` with `L_i ⊂ Π_{i+1}` (the candidate body `v_{i+1}`), which is the (β) route — KT never needs a spliced-panel perp.

### (4.81.2) THE SPIKE — what compiled SORRY-FREE, what is the irreducible residual (clause ii).
`SpikeGamma.lean` (built on `…CaseIII.Relabel.ForkedArm`, build green modulo the 1 intentional `sorry`). Set `a = q(vtx(i+1))`, `m = q(vtx i)` (the removed degree-2 body), `b = q(vtx(i−1))`.
- **PROBE A (SORRY-FREE, 4 decls) — `panelSupportExtensor` IS bilinear/alternating.** `pse_add_right`/`pse_smul_right` (additive/homogeneous in the SECOND normal, derived from the LANDED `panelSupportExtensor_swap` + `_add_left`/`_smul_left`) + `pse_self` (`panelSupportExtensor n n = 0`, via `normalsJoin_self`). **This DISPROVES §(4.80) PROBE 3's stated reason** ("`panelSupportExtensor = complementIso ∘ normalsJoin` is NOT linear in its second argument"): it is the wedge `normalsJoin` (alternating bilinear) through the LINEAR iso `complementIso`, hence bilinear and alternating in both normals.
- **PROBE B1 (SORRY-FREE) — the coplanarity bridge.** `gamma_short_circuit_of_coplanar`: from `hcop : m = α'•a + β'•b`, `hβ : β' ≠ 0`, and the LANDED chain-edge perp `hchain : ρ₀(a∧m) = 0`, derive the short-circuit perp `ρ₀(a∧b) = 0` in ONE step: `a∧m = a∧(α'•a + β'•b) = α'(a∧a) + β'(a∧b) = β'(a∧b)` (PROBE A), so `0 = ρ₀(a∧m) = β'·ρ₀(a∧b)`, and `β' ≠ 0` ⟹ `ρ₀(a∧b) = 0`. The second chain-edge perp is not even needed.
- **PROBE B2 (the IRREDUCIBLE residual, the 1 `sorry`) — WITHOUT coplanarity, both chain-edge perps do NOT suffice.** `gamma_short_circuit_from_both_chain_perps`: from `ρ₀(a∧m) = 0` AND `ρ₀(b∧m) = 0` alone, `ρ₀(a∧b) = 0` is NOT derivable — `a∧b`, `a∧m`, `m∧b` are independent grade-2 wedges when `{a, m, b}` are independent, so `ρ₀` annihilating two says nothing about the third. This is the residual that confirms the coplanarity (a 3-body normal-space relation) is the genuinely-required input, not bookkeeping.
- **PROBE C (SORRY-FREE) — the full `hr` composes modulo the coplanarity.** `gamma_hr_of_coplanar`: feeds PROBE B1's short-circuit perp into the LANDED consumer `hingeRow_mem_caseIIICandidate_rigidityRows_reproduced` at `t = 0` (`zero_smul; add_zero` reducing the sheared support `panelSupportExtensor (a + 0•n') b` to `a∧b`), producing the exact `hr : hingeRow u w ρ₀ ∈ span (caseIIICandidate G ends q e_c e_r a n' b 0).rigidityRows` route (D)'s augmented spine demands. So the ENTIRE remaining `hr` gap is the single coplanarity hypothesis `hcop`/`hβ` — everything else (the bilinearity, the consumer wiring) is sorry-free.

### (4.81.3) WHY THE COPLANARITY IS UNAVAILABLE — traced to ground (clause iii).
The needed `hcop : q(vtx i) = α'•q(vtx(i+1)) + β'•q(vtx(i−1))` (with `β' ≠ 0`) says the removed degree-2 body's normal is COPLANAR with its two chain neighbours' normals. The project's seed `q` is **`AlgebraicIndependent ℚ q`** (the discriminator output `hQalg`, `Realization.lean:2001`; KT's *generic* framework `(G_1, q_1)`). For `k ≥ 1` (so the normal space `ℝ^{k+2}` has dim ≥ 3) three distinct generic chain-body normals (`vtx(i−1), vtx i, vtx(i+1)` distinct by `vtx_inj`) are linearly INDEPENDENT — the exact OPPOSITE of coplanarity. The only general-position fact the framework carries is `IsGeneralPosition` (`PanelHinge.lean:121`) = pairwise `LinearIndependent ![normal a, normal b]`, which strengthens, never weakens, toward independence. **So `hcop` is provably FALSE for reachable configurations** — the same shape of obstruction route α died on (§(4.77): its `_escape` side-condition `q b ∉ ker (of p)` was provably false for reachable matched joins). (γ) is therefore not a missing-but-true crux awaiting a value-read; it is a false side-condition.

Why no spliced-panel value-read rescues it (the task's "NEW leaf analogous to `interior_group_acolumn_eq_neg_baseRedundancy`"): the landed carry reaches the chain-edge panel because the chain-induction pins the `edge i`-group's screw COLUMN at the tail body `vtx i` to `−ρ₀` (`ChainColumn.lean:744`), and `edge i = (vtx i, vtx(i+1))` IS a `G`-link, so `edgeGroup_acolumn_mem_block` + `ofNormals_supportExtensor_eq_panel_of_ends` read it as the `(vtx(i+1), vtx i)` panel perp. The spliced edge `(vtx(i+1), vtx(i−1))` is NOT a `G`-link — there is no edge-group whose column the carry could pin, so the `G.IsLink`-anchored value-read has no spliced analogue. The relabel-`q` route reaches a short-circuit-SHAPED panel only because the body-rename `qρ = q ∘ shiftPerm` sends `qρ(vtx(i−1)) = q(vtx i)`, i.e. it collapses the reproduced panel back to the chain-edge panel `(q(vtx(i+1)), q(vtx i))` (`reproduced_panel_eq_splice_panel`, `:547`) — a body-RENAME, not a normal-space span relation. Route (D)'s direct-`q` candidate has no such rename, so its reproduced panel is the genuine short-circuit, and only the false coplanarity could bridge it.

### (4.81.4) THE DECISION (γ) FORCES — flag-don't-force; the recommendation stands at (β).
(γ) is INFEASIBLE: its single remaining gap is a side-condition provably false for the generic seed, with no value-read circumvention (the carry's `G.IsLink` anchor has no spliced analogue, and KT (6.66) never targets the spliced panel). Per the task's *flag-don't-force* clause, this does NOT auto-pivot to (β) — that is the user's call. For context only (NOT a decision):
- **(β) §(4.77.4)/§(4.80.4)** — KT's disjunction-over-all-`Mᵢ` (eqs. 6.65–6.67). Removes the per-candidate `n'`/perp ENTIRELY (no `hr` short-circuit perp to land), so it dissolves BOTH route α's `_escape` and route (D)'s coplanarity at the root — they are the same obstruction. Cost: a CHAIN-2c dispatch/spine reshape (the cert certifies an existential over the `d` candidates `M₀…M_{d−1}`, not a fixed matched `i`). This is now the only surfaced route whose feasibility is not refuted; maximally KT-faithful (it is literally KT's own argument). **Recommended for adjudication.**
- (γ) and (α′) are both refuted (γ here, α′ at §(4.77.4)).

The route-(D) sub-commits that DON'T touch `hr` stay landed-feasible and would be REUSED under (β): 5c the augmented `hB`/`L₀` factoring, 5e the `re`/`hre`/`L₀` + bottom assembly, and the 5f router shell modulo `hr` (§(4.79.5)/§(4.80.4)). The bilinearity lemmas PROBE A proved (second-normal `pse_add_right`/`pse_smul_right`/`pse_self`) are genuinely-useful and would land in `PanelLayer.lean` under any route that touches the panel meet algebra.

### (4.81.5) THREE DESIGN-PASS CLAUSES — verdicts.
- **(i) verified against LANDED source + primary source.** Every load-bearing object read at its `def`/`theorem`: the bilinearity bricks `panelSupportExtensor_swap`/`_add_left`/`_smul_left`/`normalsJoin_self` (`PanelLayer.lean:256`/`268`/`279`/`167`); `panelSupportExtensor` (`:232`, `complementIso ∘ normalsJoin`, `complementIso` a LINEAR `≃ₗ`); the `hr` consumer `hingeRow_mem_caseIIICandidate_rigidityRows_reproduced` (`Candidate.lean:2286`); the candidate def + reproduced-slot support `caseIIICandidate`/`_supportExtensor_reproduced` (`Candidate.lean:940`/`972`); the augmented arm `case_III_arm_realization_aug` (`ForkedArm.lean:426`, candidate bindings `(q a) n' (q b)` `:445`/`:459`) + the spine `chainData_arm_realization_aug_zero₁₂` (`Realization.lean:1625`, `a = vtx i.succ`/`b = vtx(i−1).castSucc` `:1658`/`:1667`); the landed carry `interior_group_acolumn_eq_neg_baseRedundancy` (`ChainColumn.lean:729`, tail-body `vtx i` column `:744`) + `baseRedundancy_perp_interior_reproduced_panel` (`ForkedArm.lean:640`, chain-edge conclusion `:657`) + `reproduced_panel_eq_splice_panel` (`:547`, body-rename collapse); `IsGeneralPosition` (`PanelHinge.lean:121`); the seed genericity `hQalg : AlgebraicIndependent ℚ q` (`Realization.lean:2001`). KT eqs. (6.60)–(6.67) re-read end-to-end at `katoh-tanigawa-2011-molecular-conjecture.pdf` pdf p.50–52 (paper p.696–698). Spike compiled error-free modulo the 1 intentional `sorry`.
- **(ii) FLAG-DON'T-FORCE — applied as VERDICT-STOP (γ INFEASIBLE).** The SORRY-FREE bilinearity bridge (PROBE B1) + the SORRY-FREE consumer wiring (PROBE C) prove the derivation reduces to ONE input; the negative-control `sorry` (PROBE B2) + the genericity contradiction prove that input (the coplanarity) is provably false. An honest "the coplanarity side-condition is irreducible and geometrically false for generic `q`" IS the verdict. (β) NOT picked unilaterally — surfaced as the only un-refuted route.
- **(iii) traced to GROUND.** Cardinalities/structural invariants confirmed: the three chain bodies `vtx(i−1), vtx i, vtx(i+1)` are distinct (`vtx_inj`/`vtx_ne`); the candidate's reproduced panel `(a, b) = (q(vtx(i+1)), q(vtx(i−1)))` is forced by the degree-2 split structure (`hends_ea`/`hends_eb` recording the two re-inserted hinges at `v = vtx i`, `ForkedArm.lean:433`/`Realization.lean:1631`); the bilinearity is REAL (PROBE A, the wedge through a linear iso), so the §(4.80.5)(iii) "nonlinear in each" caveat is corrected; the spliced panel is the non-`G`-link bridge with no edge-group column for the carry to pin. `d=3` untouched (the M₃ single-swap `qρ = q ∘ swap a v` makes `qρ(v) = q(a)`, collapsing the reproduced panel to the chain-edge panel — `case_III_arm_realization_M3`'s `hqρv`; the seam is a length-`d ≥ 4` phenomenon only).
