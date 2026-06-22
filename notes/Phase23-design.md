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
`shiftPerm_eq_prod_map_swap_shiftBodyList` is a separate bridge applied at the arm). `redundancy_panel_carry`
LANDED (the abstract eq.-(6.44) `±r` vector identity, a thin chain-step wrapper of `candidateRow_ac_eq_neg`,
`Claim612.lean`, KT eq. 6.44/6.66).

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
