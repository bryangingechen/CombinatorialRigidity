# Phase 22 — realization-layer design (decision-support doc)

**Status:** design pass, not a build plan. Produced 2026-06-04 after the
constructibility recon (FRICTION dead-end #5; `notes/Phase22.md` *Blockers*)
found the Case-I coupling has two real gaps **(G1)/(G2)** the type-level plan
was blind to. The user has paused per-commit Lean work to decide the **motive
question** — should `PanelHingeFramework.HasFullRankRealization` carry general
position (KT's "nonparallel") — before any more producer commits. This doc
states the decision inputs, maps the layer, and gives a recommendation with its
ripple cost. **The motive choice is the user's to make.** No Lean / `\leanok` /
blueprint edits accompany this doc.

Primary sources read for this pass: KT 2011 §5–§6.4 (`.refs/`, printed pp.
669–697); `Molecular/{AlgebraicInduction,Extensor,Deficiency,Induction}.lean`;
`blueprint/src/chapter/algebraic-induction.tex` Case I/II/III + `thm:theorem-55`;
`notes/Phase21b.md` *Finding A/B*; the cross-cutting `DESIGN.md` sections
(*Realization motive must be V(G)-relative*, *Constructibility recon …*,
*Phase Case-naming …*).

---

## 0. The crux, in one paragraph

KT Theorem 5.5 (printed p. 669) reads: *"there exists a **(nonparallel, if G is
simple)** panel-hinge realization `(G,p)` satisfying `rank R(G,p) =
D(|V|−1)−k`."* The induction is on `|V|`; **every inductive case invokes the IH
(KT's eq. (6.1)) in this same `∃ nonparallel realization` form** and builds a
new nonparallel realization from it. Three places consume the nonparallel-ness
of the *incoming* legs: (i) KT Claim 6.4's "each entry of the rigidity matrix of
a **nonparallel** realization is a polynomial in the panel coefficients"
(printed p. 674) — exactly the project's `panelRow`/B0 coordinatization, which
needs `supportExtensor e ≠ 0`, i.e. transversal hinges; (ii) Lemma 6.3/6.5's
boundary-panel intersection `Π_{G/E',p2}(u) ∩ Π_{G',p1}(v)` (eq. 6.6) is a
genuine `(d−2)`-flat **only when the two panels are transversal**; (iii) the
simple cases additionally require the two legs' panel coefficients to be
*jointly algebraically independent over ℚ* (printed pp. 673, 675), so they can
be placed on one shared generic point. The project's motive currently asks for a
**bare** rigid realization (`∃ Q, Q.graph = G ∧ Q rigid on V(G)`), with no
general-position promise. That mismatch **is** gap (G1); the joint-genericity in
(iii) **is** gap (G2). Both are intrinsic to KT's argument, not artefacts of the
Lean encoding.

---

## 1. Motive decision

### 1.1 What KT Theorem 5.5 actually guarantees

`Molecular/AlgebraicInduction.lean:2445`:
```
def HasFullRankRealization (k : ℕ) (G : Graph α β) : Prop :=
  ∃ Q : PanelHingeFramework k α β, Q.graph = G ∧
    Q.toBodyHinge.IsInfinitesimallyRigidOn V(G)
```
KT's conclusion is strictly stronger when `G` is simple: `∃ Q, Q.graph = G ∧
Q.IsGeneralPosition ∧ Q.toBodyHinge.IsInfinitesimallyRigidOn V(G)`, where
`IsGeneralPosition P := ∀ a b, a ≠ b → LinearIndependent ℝ ![P.normal a,
P.normal b]` (`AlgebraicInduction.lean:1762`). General position is a property of
the **normals `q` alone** (pairwise independence) — independent of the graph,
the endpoint selector, and `withGraph`. (`withGraph_normal` is `rfl`:
`(P.withGraph G').normal = P.normal`.) This is the single most important
structural fact for the whole decision: **a general-position seed `q₀` for the
parent is automatically general-position for every leg `withGraph GH/Gc`.**

KT's "if `G` is simple" caveat: general position can genuinely **fail** in the
non-simple base/Lemma-6.2 cases — two parallel edges, or the K₂-with-double-edge
base, want `ΠG,p1(a) = ΠG,p1(b)` (equal panels, printed pp. 670, 672). So a
motive that *unconditionally* demands general position is **too strong** — it is
false for the two-vertex double-edge base case. The honest strengthened motive
is general-position **conditioned on `G.Simple`** (or carried as a separate
conjunct only where the producers consume it). See §1.4.

### 1.2 What each producer NEEDS from / SUPPLIES to the motive

The table reads "for the recursion `theorem_55 = minimal_kdof_reduction hbase
hsplit hcontract`":

| Producer | NEEDS from IH | SUPPLIES (its conclusion) | Notes |
|---|---|---|---|
| **base** (`hbase`, `theorem_55_base`, `AlgebraicInduction.lean:831`) | nothing (leaf) | bare rigid on `{u,v}`; **already takes `hgen : LinearIndependent ![C(e₁),C(e₂)]`** as a hypothesis = general position of the *two hinges* | The base already *consumes* a general-position witness; it can *supply* `IsGeneralPosition` of `Q` for free when the two bodies' normals are independent. K₂-double-edge (parallel) is the one non-general-position leaf. |
| **Case II** (`hsplit`, **= KT Case III**, k=0, RED) | KT Lemma 6.8/6.10: a **nonparallel** realization of the smaller split `G_v^{ab}` | nonparallel realization of `G` | The eq. (6.12) degenerate placement explicitly sets `p1(vb)=q(ab)` — uses the incoming nonparallel `q` to reproduce the `e₀` row. Claim 6.4 (polynomial-in-normals) applied here needs the incoming leg nonparallel. |
| **Case I** (`hcontract`, KT §6.2, RED) | **nonparallel** realizations `(G',p1)`, `(G/E',p2)` of the two legs, **jointly generic** (algebraically independent panel coefficients, eq. 6.6) | nonparallel realization of `G` (Lemma 6.3/6.5); bare for non-simple (Lemma 6.2) | (G1) = "needs nonparallel legs"; (G2) = "needs them jointly generic on one seed". |
| **`theorem_55` statement** | — | — | the motive type only — flips with the producers |
| **device feed** (`exists_rankPolynomial_of_rigidOn`, `AlgebraicInduction.lean:3226`; `hasFullRankRealization_of_splice_ofNormals:3064`) | `hne : ∀ e, supportExtensor e ≠ 0` (transversal hinges) **and** `hgp : IsGeneralPosition` at the seed | the generic full-rank realization | This is where (G1)/(G2) bite in the *green* infra. Both the polynomial-producer and the splice already demand general position; the only thing missing is an IH that *delivers* it. |

The decisive observation: **the green producer infra already requires general
position** (`hne`/`hgp` are hypotheses of `exists_rankPolynomial_of_rigidOn` and
`hasFullRankRealization_of_splice_ofNormals`). The gap is purely that the IH
motive does not *carry* general position to discharge them. KT closes this by
making the IH itself nonparallel. The project currently does not.

### 1.3 What breaks / must change if the motive is strengthened

Enumerated green nodes touched (all in `AlgebraicInduction.lean` unless noted):

1. **`HasFullRankRealization` def (`:2445`)** — add the `IsGeneralPosition`
   conjunct (conditioned, see §1.4). One-line def edit; **no proof**, but every
   consumer/producer of the def re-types.
2. **`theorem_55` statement (`:2471`)** — purely transitive: it is
   `Graph.minimal_kdof_reduction hbase hsplit hcontract`, so its type follows
   the motive. The *body* is unchanged (one-line `exact`). The three IH
   hypotheses `hbase`/`hsplit`/`hcontract` re-type to the stronger motive.
3. **base case `theorem_55_base` / its `PanelHingeFramework` lift (`:2013–2028`)
   + `hbase` wiring** — must now *also conclude* `IsGeneralPosition`. The two-
   body case with independent normals supplies it directly from `hgen`; the
   **non-general-position parallel base** (K₂ double-edge) is the obstruction
   that forces the *conditioned* motive (§1.4). The base proof grows by the
   general-position conclusion (small, but real — it is where the "if simple"
   caveat has to be discharged).
4. **Case II accounting iff `lem:case-II` and Case I accounting iff `lem:case-I`
   (green, `:733`/the `isInfinitesimallyRigidOn_iff_pinnedMotionsOn_le` family)**
   — these are *rank-side* iffs about rigidity-on-`V(G)`; they do **not** mention
   the motive type, so they are **untouched**. (Confirmed: they take general
   position implicitly via the device hypotheses, not via the motive.)
5. **The device feed (`exists_rankPolynomial_of_rigidOn`,
   `hasFullRankRealization_of_splice_ofNormals`,
   `hasFullRankRealization_of_rigidOn_seed`,
   `exists_rigidOn_ofNormals_of_hasFullRankRealization`)** — these *already* take
   `hne`/`hgp` as explicit hypotheses, so the strengthened motive lets a producer
   *discharge* them rather than re-prove them. **They do not break; they get
   easier to feed.** `exists_rigidOn_ofNormals_of_hasFullRankRealization`
   (`:3192`) grows by one conjunct (carry the general-position witness out of the
   repackaged `Q`), still a ~5-line `rfl`/`subst` proof.
6. **`rigidityMatrix_prop11` (`:2525`), `lem:cycle-realization`** — consume the
   motive only through `theorem_55` as a *cited* `hgen`; the *statements* do not
   carry `HasFullRankRealization`, so they are untouched at the type level.

**Ripple cost: bounded and front-loaded.** The def edit + the `theorem_55`
re-type + the base-case general-position conclusion are a single small commit
(no new mathematics — general position of the base is read off `hgen`). The
*producers* (`hsplit`/`hcontract`) are red regardless; strengthening the motive
**reduces** their remaining obligation (they no longer have to manufacture
general position from a bare rigid IH — gap (G1) is dissolved at the source).
The one genuine new burden is handling the **non-general-position base** so the
motive stays *satisfiable* for the parallel K₂ leaf — see §1.4.

### 1.4 Recommendation

**Strengthen the motive — but condition the general-position conjunct on
`G.Simple`, matching KT's "(nonparallel, if `G` is simple)" exactly.** Concretely
the recommended shape is one of:

> (A) `HasFullRankRealization k G := ∃ Q, Q.graph = G ∧
>     Q.toBodyHinge.IsInfinitesimallyRigidOn V(G) ∧ (G.Simple → Q.IsGeneralPosition)`

or, if the `Simple` predicate proves awkward to thread through the reduction
(`minimal_kdof_reduction` does not currently track simplicity), the equivalent
**two-motive** split KT effectively uses: keep the bare `HasFullRankRealization`
for the non-simple/base legs, and add a *separate* `HasGenericFullRankRealization
k G` (general position unconditional) carried only through the simple-graph
cases, with a one-line `HasGenericFullRankRealization → HasFullRankRealization`
forgetful map.

Rationale for "strengthen", against the alternative (b) "keep the motive bare,
prove a perturbation lemma 'a bare rigid realization has a nearby transversal-
rigid sibling'":

- **(b) is circular / heavier.** The perturbation argument (rigidity is
  Zariski-open, so a generic nearby normal is still rigid) is *itself* the rank
  polynomial — you would need `exists_rankPolynomial_of_rigidOn`, which already
  needs `hne` (transversal). So (b) cannot bootstrap general position from a
  genuinely-degenerate rigid IH without first having general position. This is
  the (G1) circularity the recon flagged.
- **(A) matches the source.** KT's induction is *designed* so the IH is
  nonparallel; the project diverged by relativizing to a bare motive (a correct
  fix for the `V(G)`-relative trap, `DESIGN.md`, but it dropped the nonparallel
  conjunct that the relativization did not require it to drop). (A) re-adds only
  the dropped conjunct.
- **(A) dissolves (G1) at the source** and makes the splice feed direct: a
  general-position parent seed gives general-position legs (`withGraph_normal`
  is `rfl`), so `hgp`/`hne` are discharged for free.

**Caveat the user should weigh before committing to (A) vs the two-motive
split:** a `Graph.Simple` predicate *does* exist (the vendored
`Matroid/Graph/Simple.lean:183`, `class Simple … extends G.Loopless`), so (A) is
feasible — but `Graph.minimal_kdof_reduction` (`Induction.lean:3529`, Phase 20,
green) does **not** currently expose graph-simplicity to its case dispatch, and
the inductive subgraphs (`splitOff`, `rigidContract`) would need a simplicity-
preservation side-fact (KT Lemma 6.7(ii): `G_v^{ab}` is simple when `G` is
simple). KT spends Lemma 6.7 on exactly this. If threading `Simple` through the
reduction proves costly, the **two-motive split** localizes the general-position
bookkeeping to the simple cases and avoids re-opening Phase 20's reduction
principle. **I lean to the two-motive split** as the lower-ripple option: it
touches no Phase-20 node, the forgetful map is one line, and it mirrors KT's own
bifurcation (Lemma 6.2 bare vs. 6.3/6.5 nonparallel). The single-conjunct form
(A) is cleaner if and only if `Simple` threads cheaply through
`minimal_kdof_reduction` — that is a Lean-feasibility question worth a 1-commit
spike before the full producer build.

---

## 2. Shared-infra map (green vs. missing across the layer)

Built once, reused by all cases. **Green** unless marked.

| Brick | Lean name (`AlgebraicInduction.lean` unless noted) | Status | Reused by |
|---|---|---|---|
| Genericity device (Claim 6.4/6.9) | `exists_good_realization`, `_const`, `_ofParam` (`:2604`,`:3388`,`:2672`) | GREEN | Case I, Case II/III, Prop 1.1 |
| B0 row coordinatization (polynomial-in-normals) | `exists_good_realization_ofParam` (`:2672`) | GREEN | Case I, Case II/III |
| Device→motive closure (N7a) | `hasFullRankRealization_of_independent_panelRow` (`:2808`) | GREEN | all producers |
| N7b-0 (rigid-on-V ⟹ full-size independent panel-row subfamily) | `BodyHingeFramework.exists_independent_panelRow_subfamily_of_rigidOn` (`:2929`) | GREEN | Case I, Case II/III |
| N7b-1/2/3 (per-edge new-block rows; transport; pin-a-body column split) | `exists_independent_panelRow_subfamily_of_edge`, `…_transport`, `linearIndependent_sum_pinned_block` | GREEN | Case II/III (eq. 6.12) |
| Case-I splice glue (block-triangular gluing, genericity-free) | `BodyHingeFramework.isInfinitesimallyRigidOn_of_splice` (`lem:case-I-splice-seed`), `isInfinitesimallyRigidOn_union_of_inter` | GREEN | Case I |
| Splice producer (composes glue→N7b-0→device) | `hasFullRankRealization_of_splice` / `…_ofNormals` / `…_ofParam` (`:3016`,`:3064`,`:3110`) | GREEN | Case I |
| Single-leg seed→realization bridge | `hasFullRankRealization_of_rigidOn_seed` (`:3151`) | GREEN | Case I, Case II/III |
| IH repackage (motive ⟹ rigid `ofNormals` locus) | `exists_rigidOn_ofNormals_of_hasFullRankRealization` (`:3192`) | GREEN (re-types under §1.3.5) | Case I |
| Per-leg rank polynomial (rigid leg ⟹ nonzero Gram-det `MvPolynomial`) | `exists_rankPolynomial_of_rigidOn` (`:3226`) | GREEN — **but needs `hne` (G1)** | Case I |
| Rank-polynomial consumer (non-root ⟹ rigid at that point) | `isInfinitesimallyRigidOn_ofNormals_of_rankPolynomial_ne_zero` (`:3315`) | GREEN | Case I |
| Constructive rank-witnessing mirror | `exists_polynomial_ne_zero_of_linearIndependent_at` (`Mathlib/LinearAlgebra/Matrix/Rank.lean`) | GREEN | Case I |
| General-position witnesses (moment curve) | `momentCurve`, `withMomentNormals`, `ofParam`, `isGeneralPosition_ofParam` (`:1785`–`:1933`) | GREEN | all (seed) |
| transversal hinge ⟹ nonzero extensor | `supportExtensor_ne_zero_of_isGeneralPosition` (`:1773`) | GREEN | all |
| N4 graph↔matroid contraction-minimality | `Graph.rigidContract_isMinimalKDof` (`Induction.lean`) | GREEN | Case I (`hcontract` recursion) |
| Count bridges (`V(G)`-relative N1–N3) | `finrank_pinnedMotionsOn_vertexSet`, `exists_relative_full_count_ofParam`, `isInfinitesimallyRigidOn_vertexSet_of_finrank_le` | GREEN | all |
| **Lemma 2.1 (extensor independence)** | `omitTwoExtensor_linearIndependent` (`Extensor.lean:493`) | GREEN — **hyp `AffineIndependent ℝ p`** | Case III (the missing row) |
| **(G2) general-position factor** | — (Vandermonde-type `MvPolynomial` whose non-roots are exactly general-position assignments) | **MISSING** | Case I coupling |
| **`prop:rigidity-matrix-prop11` `hub`** | carried as hypothesis (`:2527`) | RED (multi-commit, Phase-19 partition count) | Prop 1.1 only |

**Reading:** the entire device + witness-transfer + splice + count + N4
substrate is GREEN. The *only two missing analytic bricks across the whole layer*
are **(G2)** the general-position `MvPolynomial` factor (Case I coupling) and the
**Case-III missing row** via Lemma 2.1 (Track B). (G1) is not a missing brick —
it is the motive decision of §1.

---

## 3. Per-case producer structure, node list, build order

Honesty gate applied: each node tagged **buildable** (math settled, arithmetic
closes from green inputs — decompose-then-build) or **research-shaped** (the
math is the hard part — math-first before any node is scheduled), per `DESIGN.md`
*Constructibility recon …*.

### Track A — Case I producer (`hcontract`), KT §6.2

KT splits Case I into three sub-cases by simplicity. The **constructibility
arithmetic closes for all three**: `rank = D(|V'|−1) [rigid block] + D(|V∖V'∪{v*}|−1)−k [contraction] = D(|V|−1)−k` (eqs. 6.3, 6.9), full rank at k=0. No
shortfall — this is the tractable track.

Nodes (composing the green infra of §2):

- **N6a — non-simple Case I (KT Lemma 6.2).** `buildable`. Equal-panel splice
  (`ΠG/E',p2(v*) = ΠG',p1(a) = ΠG',p1(b)`); a bare (non-general-position)
  realization suffices, so it consumes the *bare* motive and supplies the bare
  motive. Composes `hasFullRankRealization_of_splice` directly. Lowest-risk
  starting node; **does not need the motive strengthening.**
- **N6b — simple Case I, simple contraction (KT Lemma 6.3).** `buildable
  conditional on §1`. Needs the two legs nonparallel + jointly generic (eq. 6.6
  boundary-panel intersection). With motive (A)/two-motive: the legs arrive
  nonparallel; the shared generic seed is the (G2) factor. **Gated on (G2).**
- **N6c — simple Case I, no simple contraction (KT Lemma 6.5).** `buildable
  conditional on §1` (same shape as N6b; the contracted vertex's two boundary
  hinges give `+D` via Lemma 5.3 / the splice). **Gated on (G2).**
- **(G2) general-position factor.** `research-shaped (bounded).` A nonzero
  `MvPolynomial (α × Fin (k+2)) ℝ` whose non-roots are exactly
  `IsGeneralPosition` assignments. This is a *pairwise-independence* polynomial:
  for each body-pair `{a,b}`, general position is "the `2 × (k+2)` matrix
  `[q(a,·); q(b,·)]` has rank 2", i.e. *some* `2×2` minor `≠ 0`. A product over
  pairs of "sum of squared minors" or a single Vandermonde-on-a-generic-line
  witness works; the moment-curve assignment `ofParam` is the explicit non-root.
  **Recon check:** non-roots of a finite product of nonzero polynomials are
  Zariski-dense and the moment-curve point is a witnessed non-root, so the triple
  product `Q_H · Q_c · Q_gp` (two rank polynomials × the gp factor) has a shared
  non-root by `MvPolynomial.exists_eval_ne_zero` — arithmetic closes. Bounded:
  the math is standard, the Lean is a new mirror brick (~1–2 commits).
- **N6 — Case I composer (`lem:case-I-realization`).** `buildable` once
  N6a/N6b/N6c land. Dispatches on simplicity, feeds N4 (the contraction is a
  smaller minimal 0-dof-graph) + the IH legs + the (G2) seed into the splice
  producer, concludes `hcontract`.

**Build order (Track A):** §1 motive decision → N6a (non-simple, motive-
independent, de-risks the splice plumbing) → (G2) factor → N6b/N6c (need (G2) +
strengthened motive) → N6 composer.

### Track B — Case II/III producer (`hsplit`), KT §6.3 (Lemma 6.8) + §6.4.1

**This is KT Case III** at the project's k=0 scope (FRICTION dead-end #3; Finding
B; `DESIGN.md` *Phase Case-naming …*). Constructibility: eq. (6.12) degenerate
placement gives `+(D−1)` ⟹ `rank = D(|V|−1)−1`, **one row short** of the k=0 full
target. The missing row is the Case-III redundant-edge row.

- **eq. (6.12) degenerate placement** (`p1(vb)=q(ab)` reproduces the `e₀`
  row). `buildable` (feeds the green N7b-0/1/2/3 + pin-a-body split). Gives
  `+(D−1)`. **Needs the incoming split-leg nonparallel** (Claim 6.4) — so it too
  consumes the strengthened motive (or the two-motive's generic form).
- **Lemma 6.10 (`d=3`, 3 candidates)** — `research-shaped`. The single largest
  proof in KT (~12 pp.). Two sub-claims:
  - **Claim 6.11 (combinatorial↔linear):** `R(G_v^{ab},q)` has a redundant
    `ab`-row, via Lemma 4.3(ii) + IH. Wires `M(G̃_v^{ab})` to the row matroid of
    `R`. The hardest non-extensor step; `research-shaped`.
  - **Claim 6.12 (extensor-span genericity):** if all `D` candidates fail, a
    nonzero `r ∈ ℝᴰ` is ⟂ all extensors on `d+1` generic panels, which by
    **Lemma 2.1** (`omitTwoExtensor_linearIndependent`, green, hyp
    `AffineIndependent ℝ p`) span `ℝᴰ` — contradiction. The degree-2 condition
    forces all candidates to test the same `r` (eq. 6.44). The extensor half maps
    onto Phase-17's Lemma 2.1 directly; `research-shaped` only in the candidate-
    bookkeeping (consider an abstracted "candidate normal form" lemma to avoid
    repeating the row-ops three times).

**Build order (Track B):** strictly *after* Track A and the motive decision. The
eq. (6.12) placement is the buildable warm-up; Lemma 6.10 is the crux and is the
natural decompose-math-first target for a dedicated sub-session.

### Assembly (may defer to Phase 23)

- **`prop:rigidity-matrix-prop11` `hub` brick** — `research-shaped (multi-commit)`,
  Track-independent (Phase-19 partition count: construct `D(|P|−1)−(D−1)·d_G(P)`
  motions from a deficiency-attaining partition). Decompose math-first before
  scheduling.
- **`thm:theorem-55` / `lem:case-III` flip green** once the producers land
  (one-line, the recursion body is already assembled).

---

## 4. Risk / scope

**Genuinely research-shaped (the math is the hard part):**
- **Lemma 6.10 / Claim 6.11** (Track B) — the largest proof in KT; the
  combinatorial↔linear redundant-`ab`-row identity is the single highest-risk
  node in Phases 22–23. Claim 6.12's extensor half is de-risked (Lemma 2.1 green).
- **`hub` partition-count** — multi-commit but settled math (Phase-19 substrate).
- **(G2) general-position factor** — bounded research-shaped; standard math, new
  Lean mirror.

**Buildable once §1 is decided:** the entire Case-I track (N6a fully motive-
independent; N6b/N6c gated on (G2)+motive), the eq. (6.12) placement, and the
final `theorem_55` flip.

**Axiomatization / deferral candidates, if full formalization of a case proves
out of reach (in escalation order — do not reach for these before the math-first
decomposition is genuinely stuck):**
1. **Lemma 6.10 / Claim 6.11 as an explicit hypothesis on the Case-III node**,
   in the established Phase-21b "carry the analytic crux as `h…` and `\uses` the
   red node" idiom (exactly how Cases I/II carried the device pre-21b). This
   keeps `theorem_55` green-modulo-Lemma-6.10 and honest (the node stays red),
   and is the *recommended* fallback — it isolates the one genuinely-hard kernel
   without blocking the rest of the molecular program (Phases 24–26 depend on
   Thm 5.6, which needs Thm 5.5; a green-modulo capstone unblocks them).
2. **(G2) factor as a hypothesis** on the Case-I composer (same idiom), if the
   Vandermonde brick stalls — lower-risk than (1), since (G2) is bounded.
3. **`theorem_55` itself as `axiom`** — *last resort, not recommended.* It would
   make the whole molecular capstone (Cor 5.7) rest on an axiom; prefer the
   green-modulo decomposition (1)/(2), which keeps every discharged step honest
   and tracks the remaining obligation as a visible red node.

**Scope guard:** the motive decision (§1) is a *prerequisite* to any Case-I
simple-case build or any Track-B build — both consume nonparallel legs. The one
node that needs *nothing* from §1 is N6a (non-simple Case I). A sensible first
commit after the motive decision is N6a (proves out the splice plumbing on the
bare motive), then the (G2) factor, then the simple cases.

---

## 5. One-line recommendation

**Strengthen the motive to carry general position, conditioned on `G.Simple`
(matching KT's "nonparallel, if simple"); prefer the two-motive split if
threading `Simple` through `minimal_kdof_reduction` is costly — this dissolves
gap (G1) at the source, leaves the green producer infra needing only the bounded
(G2) general-position factor for Case I, and isolates the one genuinely
research-shaped kernel (Lemma 6.10 / Claim 6.11, Track B) as a green-modulo
deferral candidate.**
