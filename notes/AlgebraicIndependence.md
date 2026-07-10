# Algebraic independence — usage tracker + relaxation TODO

**Status (2026-07-09): active as the planning input of Phase 30 (RELAX)** —
the relaxation phase this note anticipated is open; work log
`notes/Phase30.md` (§2 below is its starting hypothesis, §3 its site
checklist).

**Purpose.** A standing, cross-cutting note that (1) records the **relaxation
question** — can the molecular-conjecture proof *avoid or weaken* its reliance on
algebraic independence of the inductive realization's coordinates — and (2) **tracks
every place** the program leans on that property, so a future relaxation phase can
revisit them systematically. This is a deferred-TODO ledger, not a phase log; append
to the usage table as later phases introduce new uses.

**Decision context (2026-06-06).** Phase 22d's KT-Claim-6.11 kernel (KT eq. (6.22) /
footnote 6) needs "*the inductively-fixed generic seed `q` attains the
IH/matroid-predicted rank* for nested subgraphs." The footnote-6 recon
(`notes/Phase22d.md` *Footnote-6 kernel recon*) found this is **genuinely-new
analytic content** — the project has zero `AlgebraicIndependent` machinery. The user
chose to **build the algebraic-independence route directly to fully green** (the
certain path; it is KT's actual argument), rather than gamble on the product-route
relaxation below. **So the relaxation is deferred, not on the critical path** — but
it is genuinely interesting and possibly substantially cheaper, hence this tracker.

## 1. What algebraic independence buys KT, and what we strictly need

KT's standing inductive choice (footnote 6, p. 685): at each inductive step the
realization `q` is taken with **panel coordinates algebraically independent over ℚ**.
An algebraically-independent point lies off the zero locus of *every* nonzero
rational polynomial, so `q` is automatically a non-root of *every* subgraph's rank
polynomial — hence one fixed generic `q` simultaneously attains the maximal rank for
*unboundedly many* subgraphs that arise later in the argument. This is the "generic
attains max, and this seed is generic" hammer behind eq. (6.22) and eq. (6.18).

What the proof *strictly needs* at any given use is weaker: that the **one** seed
in hand is a non-root of the **finitely many** rank polynomials that **particular**
argument touches.

## 2. The relaxation candidate — the "product-route" (avoid alg-independence at `d=3`)

**Insight (coordinator, 2026-06-06; VERIFIED 2026-07-10 — Phase 30 R1 verdict
GO-WITH-RESHAPINGS, with two premise corrections below).** Our formalization does not
need algebraic independence at the Claim-6.11 composition: it touches only **finitely
many** subgraphs (`G_v^{ab}` and `G_v = G_v^{ab} − ab`); each has a nonzero rank
polynomial; their **product** (times the general-position + LI polynomials the
candidate geometry needs) is nonzero (`MvPolynomial` over a field is a domain); the
**existing** device `MvPolynomial.exists_eval_ne_zero` yields a single `q` that is a
non-root of the product — hence of every factor.

**Premise corrections (R1, against the landed kernel):**
1. As landed, `q` is **not** free at the composition — both composition points
   (`chainData_split_w6b_gates`, `case_III_candidate_dispatch`) unpack `hsplitGP` and
   take `q` from the IH realization of `G_v^{ab}` (the original "22c takes the
   realization as a hypothesis parameter, so `q` can be chosen at composition" premise
   was structurally out of date). The freedom is **created** by a local reshape of
   that unpack, below the motive's existential — no IH-interface change beyond the
   conjunct deletion.
2. The producer/consumer pair originally named here (`exists_rankPolynomial_of_rigidOn`
   / `isInfinitesimallyRigidOn_ofNormals_of_rankPolynomial_ne_zero`) is the **def = 0**
   pair and does **not** compose with the *deficient* nested `G_v` (minimal `k'`-dof,
   `k' > 0` possible — no rigid seed exists for it). The correct producer is the
   **deficiency-aware** `exists_rankPolynomial_of_IH_linking` (Phase 22k L7a, already
   called inside `case_III_nested_rank_lower_all_k`), whose `N ≤ finrank` transfer is
   consumed directly for `G_v`; the def=0 consumer chain applies to `G_v^{ab}` only.

R1 confirms the route holds, so the Claim-6.11 kernel **dissolves** (pending R2 + the
motive-conjunct adjudication): no `AlgebraicIndependent` / transcendence machinery, no
`non-root-from-alg-independence` brick, no seed-genericity motive strengthening — just
"product of finitely many nonzero polynomials is nonzero" + the existing
producer/consumer, matching how Cases I/II already pick realizations via the device.
Compiler-witnessed route + composition-point pins: `notes/Phase30.md` (*R1 spike
route*, *R1 composition-point pins*).

**Residual risks — R1 status (2026-07-10):**
- **(a) RESOLVED — GO, no circularity.** Every `q`-condition at the composition is a
  non-root condition of one of four polynomials (`P_ab`, `P_v`, `Qgp`, the triple-LI
  det factor), all fixed before `q`. The Claim-6.12 geometry in the landed
  formalization imposes only *linear-independence* conditions (the Phase-23
  homogeneous route already removed the affine general-position conditions this risk
  worried about); the candidates are constructed downstream of any LI seed.
- **(b) RESOLVED — GO.** The nested IH hands over `G_v`'s rank polynomial in usable
  form via `exists_rankPolynomial_of_IH_linking` (premise correction 2); the Phase-30
  spike composed it with the device **sorry-free at general `k`**.
- **(c) RESOLVED — GO at general `d` (Phase 30 R2, 2026-07-10).** The interior/relabel
  machinery consumes **zero** `q`-conditions beyond the base bundle, so the product is
  the **same four base factors at every `d`** (no per-candidate factors; the
  discriminator's use reduces to one `(k+1)`-row LI factor, independent of the pick
  `i` and of `ρ₀`). Record: `notes/Phase30.md` *R2 record*.

**Status: Phase 30 owns the follow-through** — R1 and R2 both done (GO); the refactor
(incl. the motive fifth-conjunct deletion) awaits the user adjudication;
`notes/Phase30.md` is the live plan (scope + slice order there).

## 3. Usage tracker — where the program relies on algebraic independence

**Standing instruction (per the user, 2026-06-06): append a row whenever a new
algebraic-independence use is introduced into the molecular program.** "Relaxable?" =
does the §2 product-route (or another weakening) plausibly apply.

**Scan finding (2026-06-06).** A scan of the molecular Lean + blueprint for
algebraic-independence sites found: **the formalization has avoided algebraic
independence entirely so far** (grep: *zero* `AlgebraicIndependent`/transcendence
usage tree-wide). KT's inductive realization is "generic nonparallel" = algebraically
independent over ℚ, and KT leans on it pervasively — notably **Claim 6.4/6.9** (the
genericity device, Phases 21b/22a/22b), where KT justifies the rank-transport *via*
algebraic independence (see the `CaseI.lean:483`/`:1399` docstrings). **Yet the
project discharged the device and Claim 6.4 *without* it** — using the existence /
Zariski-genericity device (∃ a non-root of a nonzero polynomial) + general position
(`IsGeneralPosition`, pairwise-normal transversality). So those are *not* current
sites; they are the **precedent** that the existence formulation suffices. The
**Phase-22d kernel is the FIRST place the existence formulation falls short** —
footnote 6 needs "*this* given seed attains the rank", not "*∃* a good seed" — which
is exactly why algebraic independence becomes necessary there (absent the §2
relaxation). This track record makes the product-route relaxation a *continuation of
a proven strategy*, not a gamble.

| Where | What alg-independence is (would be) used for | Status | Relaxable? |
|---|---|---|---|
| Genericity device / **Claim 6.4/6.9** (Phases 21b, 22a, 22b) | KT transports rank across the collapse/generic step via alg-independence | **AVOIDED** — formalized via the existence/Zariski device + GP; green. *Not a site — the precedent.* | already avoided |
| **Phase 22d kernel** — KT Claim 6.11, eq. (6.22)/(6.18), footnote 6 (`lem:case-III-seed-rank-bridge`) | the inductively-fixed seed `q` attains the IH/matroid-predicted rank of nested subgraphs (`G_v^{ab}`, `G_v`) — so a redundant `ab`-row exists | **first forced site; being built** via the alg-independence route — leaf (i) `AlgebraicIndependent.aeval_ne_zero` ✓ landed (mirror); (ii) **SPLIT** into (ii-a) seed-genericity motive conjunct + (ii-b) a **rationality bridge**, both ✓ green. (ii-b): descent pair + consumed assembly + the `complementIso`-rational-entries leaf, wired into the device `Q`. (ii-a): `HasGenericFullRankRealization` carries the fifth conjunct `AlgebraicIndependent ℚ (fun p ↦ Q.normal p.1 p.2)`; producers build at `exists_injective_algebraicIndependent_real` (moment curve is NOT alg-indep) and discharge rational rank-poly non-roots via `eval_ne_zero_of_coeffs_subset_range_of_algebraicIndependent` (this forced the `_proj` rationality `dualMap_matrix_entry_eq`). (iii) the seed-rank bridge `isInfinitesimallyRigidOn_ofNormals_of_algebraicIndependent` ✓ green (rigid at one seed ⟹ rigid at every alg-indep-over-ℚ seed — the `0`-dof core); the eq. (6.22) `def>0` *upper* bound `finrank_infinitesimalMotions_le_of_rankPolynomial_algebraicIndependent` ✓ green (`dim Z ≤ D|α| − |s|` at any alg-indep seed from a rational rank polynomial). **Remaining: Gap 1** rank-attainment assembly (upper bound + `rigidityMatrix_prop11`'s `hub` lower bound ⟹ `RankHypothesis k'`) + the `D−1`-row pigeonhole | **§2 product-route: R1-VERIFIED GO-WITH-RESHAPINGS (Phase 30, 2026-07-10)** — compiler-witnessed sorry-free at general `k`; route + pins in `notes/Phase30.md` |
| **Phase 22e Claim 6.12 — N3a** (`lem:case-III-claim612-points-affineIndep`, KT eq. (6.45) point choice) | the four points with the `Π(a)/Π(b)/Π(c)` incidence pattern are **affinely independent** (KT p. 691) | **AVOIDED — existence route, like the pre-22d precedents** (re-scoped 2026-06-06, Phase-22e steering). KT *states* the affine independence via genericity (p. 691: *"Since `(Gᵥᵃᵇ, q)` is a **generic** nonparallel framework, we can take such four points … affinely independent"*; the general-`d` form p. 698 eq. (6.67) says the panel coefficients are alg-indep over ℚ, so any `j` hyperplanes meet in a `(d−j)`-dim flat). But our formalization does **not** need that: the residual `P ≠ 0` (the homogenization determinant, as a poly in the seed, is nonzero) is **logically equivalent** — via the converse of `MvPolynomial.exists_eval_ne_zero` plus the green det-poly bridge `exists_detPolynomial_of_pointPolynomial` — to *exhibiting one explicit seed `q*` where the four constructed points are affinely independent*. So it reduces to the **existence/Zariski route** (∃ a non-root of a nonzero polynomial), the same route the avoided row #104 precedents (Claim 6.4/6.9) used, **not** the seed-genericity hammer the Phase-22d kernel needs. The construction is explicit (numerically verified): `p₁` = triple-intersection of the 3 panels (Cramer/cross-product), `p₂ = p₁ + s·(nₐ×n_b)`, `p₃ = p₁ + s'·(n_b×n_c)`, `p₄ = p₁ + s''·(n_c×nₐ)` — affinely independent, all 6 lines in the panel union. Green bricks: existence `exists_ne_zero_dotProduct_eq_zero`, closure `exists_affineIndependent_of_det_polynomial_ne_zero`, det-poly bridge `exists_detPolynomial_of_pointPolynomial` (all `RigidityMatrix.lean`). **N3a `\uses{lem:genericity-device}` dropped** (demoted off the live route). (N3b, the point-join↔panel-meet duality, stays alg-independence-free — pure Grassmann–Cayley.) **Sole residual: build the explicit seed witness (N3a-1) + node flip (N3a-2).** | **AVOIDED** — existence route; no §2 product-route needed (it never was an alg-independence site once the residual is read as "one seed works") |
| **Phase 23** — KT Lemma 6.13, general `d` (the length-`d` chain) — **two distinct sites** | (a) the footnote-6 seed-rank transfer along the chain `v₀…v_d` (the general-`d` lift of `case_III_nested_rank_lower`, which *already* consumes `AlgebraicIndependent ℚ q` at `d=3`); (b) the eq. (6.67) **N3a points-in-general-position** step — KT p. 698: *"the set of the coefficients … is algebraically independent over the rational field. Therefore, for any `j` hyperplanes among them, their intersection forms a `(d−j)`-dimensional affine space."* | (a) **LANDED at general grade** (Phase 23a Leaf 4, `case_III_nested_rank_lower_all_k`; Phase 23 closed 2026-07-02 with it on the live A2/A5 spine). (b) **RESOLVED 2026-06-18 (`notes/Phase23-design.md` §(i)): NOT a site — existence/homogeneous route**, overturning the prior "leaning forced". | (a) the alg-independence machinery is **live** regardless (the `d=3` kernel already uses it; the 23a-lifted `case_III_nested_rank_lower_all_k` consumes `AlgebraicIndependent ℚ q`) — lifts to general grade in `CARRIER`(done)/`CHAIN`. **R1 correction (2026-07-10): this row undercounts the live consumers** — also the discriminator LI bridges (`linearIndependent_normals_of_algebraicIndependent{,_triple,_general}`, `exists_chainData_discriminator_pick`) and the motive fifth conjunct with its ~10 chooser producer sites + relabel transports; all product-routable (`notes/Phase30.md` *R1 composition-point pins*). **Relaxation status: product-route CONFIRMED at general `d` (R1 + R2, 2026-07-10)** — the touched family is the four base factors uniformly in `d` (the interior/relabel arms add zero `q`-conditions); refactor pending user adjudication (`notes/Phase30.md` *R2 record* + slice order). (b) **NOT a site (RESOLVED 2026-06-18, CHAIN-4 detailed-build recon).** The prior "leaning forced" followed KT's *affine* phrasing (the `(d−j)`-flat-in-union step *is* where KT invokes alg-independence). But the **landed d=3 formalization sidesteps it**: it works at the homogeneous-vector layer (§1.42 R1-affine), so the eq.-(6.67) `dim = D` is driven by `span_omitTwoExtensor_eq_top` (**already general-`k`**, only hyp `LinearIndependent ℝ pbar`, via Lemma 2.1) — **linear** independence of `d+1` **homogeneous** vectors, NOT affine independence / the `(d−j)`-flat fact. The row #106 cross-product construction (whose non-generalization motivated the "forced" lean) is **dead — zero live call sites** (the live d=3 dispatch consumes `exists_homogeneousIncidence_of_normals`, linear, only hyp `LinearIndependent ℝ n`). The per-join panel-membership generalizes purely combinatorially (join `{a,b}`⊂`Πᵢ` iff `i+1∈{a,b}`). So eq.-(6.67) lifts as a numeral generalization of green bricks with **no `AlgebraicIndependent` obligation** (CHAIN-4 leaves 4a–4d, design §(j)); one build-time residual (per-join membership must close from the orthogonality hyps, CHAIN-4b). §2 risk (c) (does the touched-subgraph family grow with `d`?) is now **only** site (a)'s relaxation question. |

(KT makes algebraic independence a single *global* inductive-seed choice, so the
forced sites are really one underlying need — "this seed attains the rank" —
surfacing at each point the *existence* device cannot reach; the table tracks those
surfacings the formalization must discharge, plus the avoided precedents.)

## 4. Status / how to use

- The alg-independence route is the **chosen path to green** (2026-06-06); this note
  does **not** block it.
- The Phase-22d kernel sub-phase built (i)+(ii)+(iii) directly, all green: leaf (i)
  (`AlgebraicIndependent.aeval_ne_zero`, mirror), (ii-b) (the rationality bridge), (ii-a) (the
  fifth `AlgebraicIndependent ℚ` motive conjunct + producers building at the transcendental seed
  `exists_injective_algebraicIndependent_real`), (iii) the seed-rank bridge
  `lem:case-III-seed-rank-bridge` (`isInfinitesimallyRigidOn_ofNormals_of_algebraicIndependent`), and
  the eq. (6.22) `def>0` upper bound `lem:case-III-seed-rank-upper`
  (`finrank_infinitesimalMotions_le_of_rankPolynomial_algebraicIndependent`).
  Next build = **Gap 1** — the eq. (6.22) `def>0` rank-attainment assembly (the landed upper bound +
  `rigidityMatrix_prop11`'s `hub` lower bound) + the `D−1`-row pigeonhole
  (`notes/Phase22d.md` *Hand-off* + *Lemma checklist*).
- The **relaxation phase** is **open as Phase 30 (RELAX)** (2026-07-09,
  `notes/Phase30.md`). **R1 + R2 both closed 2026-07-10: GO** (each
  compiler-witnessed; §2 risks (a)+(b)+(c) all resolved, two premises corrected
  above); next is the user's call on the motive fifth-conjunct deletion, then the
  refactor per Phase30.md's slice order.
- Keep §3 current: any new "this seed attains the rank" use is a new row.

Cross-refs: `notes/Phase22d.md` (*Footnote-6 kernel recon*, *Kernel-route decision*);
`notes/Phase22-realization-design.md` §1.30–§1.31; KT §6.4.1 (eq. (6.22), footnote 6),
§6.4.2 (Lemma 6.13).
