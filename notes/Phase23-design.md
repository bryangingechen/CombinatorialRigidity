# Phase 23 — Case III general `d` (KT Lemma 6.13): general design recon

**Status:** live design recon (decision-support doc). This is the *general,
layer-level* sub-phase-division recon for Phase 23 — the first stage of a
two-stage recon (a later dispatch does the leaf-level recon of the FIRST
sub-phase before any build). It sketches the cut-points, their dependency
order, hard cores, and the reuse/replace/add map; it does **not** attempt
full leaf-level signatures for every sub-phase. Authoritative recon for
Phase 23; `notes/Phase23a.md` is the work log and points here.

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
producers off `Fin 4`** — that lift is added to CHAIN's deliverables (or a
dedicated sub-phase using CHAIN's duality), on top of the chain dispatch below.
Detail: `notes/Phase23a.md` *Hand-off* + Leaf-5 *Decisions* entry.

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
to state its conclusion `HasGenericFullRankRealization k n G`). The two
hard cores are largely independent of each other and could be two leaves
within CHAIN, or CHAIN could split into CHAIN (chain bookkeeping) + ENTRY′
(duality) on contact — flag this at CHAIN open (the detailed recon decides).

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
