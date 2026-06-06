# Phase 22d — the D-candidate crux (KT Lemma 6.10 strata 2–3) (work log)

**Status:** in progress (opened 2026-06-05, **design-pass-first** — docs-only
opening recon, NO Lean node cut, NO `\leanok` flips). This sub-phase is the
**D-candidate crux** of Case III at `d=3`: KT §6.4.1, Lemma 6.10 strata 2–3
— Claim 6.11's redundant `(ab)i*`-row (eq. (6.23)) plus the
candidate-normal-form / Claim 6.12 extensor-span contradiction (eq. (6.44)).
It is the conjecture's hardest single argument and carries the **single
highest-risk node in Phases 22–23** (Claim 6.11, the combinatorial↔linear
conversion). The Lean node cut is deferred to the next session, after this
recon settles the load-bearing verdict (below) — the same design-pass-first
discipline as 22c, and the same defer-the-finer-cut discipline as 22a→22b,
22b→22c.

**Naming (user scoping decision, 2026-06-05).** 22d = **the D-candidate
crux** (this sub-phase). The `d=3` *assembly* (the `prop:rigidity-matrix-prop11`
`hub` brick + the `thm:theorem-55` flip + the `case_I_realization` →
`theorem_55_generic` Case-I wiring) is **deferred and UNLETTERED** — it gets a
letter only when its turn actually comes, because the number of crux
sub-phases before it is unknown (the crux may itself split, exactly as Case
III at `d=3` split into stratum 1 = 22c and strata 2–3 = 22d). See ROADMAP's
deferred planning note.

## Where 22c left off (the stratum-1 brick this crux completes)

Phase 22c landed **stratum 1** of Lemma 6.10 — the eq. (6.12) `+(D−1)`
block-triangular placement — green and axiom-clean as
`PanelHingeFramework.case_II_placement_eq612` (`CaseI.lean:2331`). From the IH
rigidity of the split-off `Gᵥ = G_v^{ab}` at a seed `q`, it builds the shared
seed `q₀ = update q v (n_a + t·n_b)` (`t ≠ 0`, `n_a = q(a,·)`, `n_b = q(b,·)`),
transports the IH rigidity to `q₀`, and composes the green Phase-21b N7b row
infra (N7b-1 → `hnewpin` → N7b-0 `_linking` → N7b-2 → N7b-3) into an
independent `panelRow` family of size `D(|V(G)|−1)−1`, all rigidity rows of
`ofNormals G ends q₀`. Output:

> `rank R(G,p₁) ≥ D(|V(G)|−1) − 1 = 6|V|−7` at `D = 6`, *plus* the `va`-hinge
> nondegeneracy (`supportExtensor e_a ≠ 0`, the `L ⊂ Π(a)` line, `t ≠ 0` —
> KT's actual eq. (6.12) candidate).

This is **one row short** of full rank `D(|V|−1)` — by KT's own statement
(p. 680, "does not complete the proof" for `k=0`). **22d's job is to supply
that missing `+1` row**, lifting the stratum-1 brick to full rank, discharging
`lem:case-II-realization` / `lem:case-III` / `theorem_55.hsplit` at `k=0`.

The producer already exposes the crux entry-point: its `e_a = va` link
hypothesis is carried as `_hG_ea` (named "crux-strata input"), so the crux's
second and third candidates `(G,p₂),(G,p₃)` — which place `v`'s *a*-hinge
degenerately — compose against the same signature with `a ↔ b` swapped.

## The load-bearing verdict — Claim 6.11: AXIOMATIZE-AS-HYPOTHESIS (carry `h…`, `\uses` the red node)

**This is the highest-risk decision in Phases 22–23 and the required output of
this opening recon (per the task and `CLAUDE.md`'s phase-open red-node gate).
The Lean node cut next session is built on it.**

### What Claim 6.11 actually is (read end-to-end against KT pp. 683–685)

Claim 6.11 (KT p. 684): *In `R(G_v^{ab}, q)`, there exists a redundant row
vector among those associated with `ab`* — i.e. one of the 5 (= `D−1`) rows of
the `ab`-block can be deleted without dropping `rank R(G_v^{ab},q) =
6(|V∖{v}|−1)` (eq. (6.23)). This redundant row, after fundamental row
operations (eqs. (6.24)–(6.28)), becomes the **`+1` row** that lifts the
stratum-1 `D(|V|−1)−1` to full `D(|V|−1)` (the top-left `6×6` block of
eq. (6.29) having full rank).

KT's proof of Claim 6.11 (pp. 684–685, the heart):

1. **KT Lemma 4.3(ii), matroid-base form.** Because `G_v^{ab}` is a minimal
   `0`-dof-graph, Lemma 4.3(ii) gives *a base `B'` of the combinatorial matroid
   `M(G̃_v^{ab})` (the `D`-fold graphic union) with `|B' ∩ ãb| < 5`*. Hence
   `G̃_v^{ab}` has a **redundant edge** `(ab)ᵢ` among the fiber `ãb` w.r.t.
   `M(G̃_v^{ab})` — removing it does not drop `rank M(G̃_v^{ab})`.
2. **The combinatorial → linear conversion (the genuinely new content).** KT
   then show *"this redundancy also appears in the linear matroid derived from
   `R(G_v^{ab},q)`"*. The bridge runs through a **further IH application**: let
   `G_v := G_v^{ab} − ab` (delete the short-circuit edge). Then `B' ∖ ãb` is
   independent in `M(G̃_v)` of cardinality `6(|V∖{v}|−1) − h` with `h = |B' ∩
   ãb| ≤ 4`, so `def(G̃_v) ≤ h ≤ 4` (eq. (2.4)); `G_v` is a minimal `k'`-dof-graph
   for some `k' ≤ 4` (minimality by Lemma 3.3). Apply the **induction
   hypothesis (6.1)** to `G_v` at the *restricted* realization `q|_{E_v}` (still
   generic-nonparallel because `q`'s coefficients are algebraically independent
   over ℚ and that property survives restriction): `rank R(G_v, q|_{E_v}) =
   6(|V∖{v}|−1) − k'` (eq. (6.22)). Since `R(G_v, q|_{E_v})` is exactly
   `R(G_v^{ab},q)` with the 5 `ab`-rows removed, and `rank R(G_v^{ab},q) =
   6(|V∖{v}|−1)`, adding back at most `4` of the `ab`-rows already spans the row
   space — so **at least one `ab`-row is redundant** (eq. (6.23)). □

### Why this is NOT buildable from the green Phase-19 `M(G̃)` machinery (the verdict's evidence)

The task asks: is Claim 6.11 buildable from `matroidMG_indep_iff` /
`thm:def-eq-corank`, or does it need the axiomatize-as-hypothesis fallback?
**Verdict: it needs the fallback.** Three independent gaps, each surfaced by
re-reading KT's proof against the actual green Lean:

- **Gap 1 — no `M(G̃)`↔row-dependence bridge exists.** The crux of Claim 6.11
  is the *conversion* of redundancy in the **combinatorial** matroid
  `M(G̃_v^{ab})` (the `D`-fold graphic union on edges, Phase 19) into
  redundancy in the **linear** matroid of the *rows of `R(G_v^{ab},q)`* at a
  *specific* realization `q`. A grep of `Molecular/` confirms **there is no
  such bridge in the project** — `matroidMG` and the rigidity-matrix row family
  (`panelRow` / `rigidityRows`) are never related; Phase 19 deliberately built
  `M(G̃)` as a *purely combinatorial* object (`matroidMG_indep_iff` routes
  through `mulTilde` sparsity, never touching `R`). Building that bridge IS the
  research content KT calls *"a key observation"* — it is not a corollary of the
  green machinery, it is a theorem the green machinery does not contain.

- **Gap 2 — KT Lemma 4.3(ii) is not formalized in matroid-base form.** Phase 20
  formalized KT 4.3 only in the **deficiency-count** form (`splitOff_deficiency_le`
  / `splitOff_deficiency_ge`, confining `def(G̃_v^{ab}) ∈ {def(G̃), def(G̃)−1}`).
  The matroid-base form Claim 6.11 needs — *a base `B'` of `M(G̃_v^{ab})` with
  `|B' ∩ ãb| < 5`* — was explicitly recorded as **off the Theorem-4.9 critical
  path and not built** (`SplitOffDeficiency.lean:195`: "why the matroid-base form
  of KT 4.3(ii) is off the Theorem-4.9 critical path"; `notes/Phase20.md`,
  `rem:kt-lemma-41`). So even the first input to Claim 6.11 would have to be
  freshly formalized.

- **Gap 3 — the conversion routes through a *fresh* IH application, not the
  green corank bridge.** KT's bridge (step 2 above) is not "read off `def =
  corank`": it applies the *geometric* induction hypothesis (6.1) — `rank R = D(|V|−1)
  − k'` — to a *different, further-reduced* graph `G_v = G_v^{ab} − ab` at a
  *restricted realization*, and uses the *algebraic-independence-survives-restriction*
  fact (KT footnote 6: one nonparallel realization at the rank ⟹ all generic ones
  attain it). This is the genericity device (Phase 21b) re-applied to a nested
  subgraph, wired to the matroid-base count — exactly the kind of interlocking,
  research-shaped step the "carry the analytic crux as a hypothesis" idiom exists
  for.

**Conclusion.** Claim 6.11 is the established **axiomatize-as-hypothesis**
case: the next session carries the redundant-row fact as an explicit `h…`
hypothesis on the candidate-completion node and `\uses`-links a red node
`lem:case-III-claim-6-11` (working label) that tracks the obligation, exactly
as Phase 21 carried Claim 6.4/6.9 as `hglue`/`hspan`/`hub`/`hgen` and `\uses`'d
`lem:genericity-device` before 21b discharged it, and as 22a carried `hclaim64`
before 22b discharged it. The honest shape:

> the candidate-completion producer is **green-modulo** `h_redundant_row`
> (Claim 6.11's eq. (6.23) redundant-`ab`-row fact), with the red node
> `lem:case-III-claim-6-11` tracking it; a *later* sub-phase discharges it
> (the matroid-base 4.3(ii) + the `M(G̃)`↔row-dependence bridge + the nested
> IH-at-restriction), exactly the 21→21b / 22a→22b discharge pattern.

This keeps the surrounding candidate-normal-form + Claim-6.12 assembly **fully
formal modulo the one analytic crux**, and is honest under the blueprint
honesty gate (the hypothesis is the *conclusion of a `\uses`'d node*, case (b)).
**Do NOT attempt to build Claim 6.11 from `matroidMG_indep_iff` next session** —
the recon above shows that route does not close.

## The other half — Claim 6.12 / eq. (6.44) — DE-RISKED (bottoms on the green Lemma 2.1)

Claim 6.12's extensor-span contradiction (KT p. 691, eqs. (6.44)–(6.45)) is the
*opposite* risk profile: it bottoms cleanly on the **green Phase-17 Lemma 2.1**
(`omitTwoExtensor_linearIndependent`). Read end-to-end against the source:

- If none of the three candidate top-left blocks `M1, M2, M3` has full rank,
  then a nonzero `r ∈ ℝ⁶` is orthogonal to the span of all `2`-extensors `C(L)`
  over lines `L ⊂ Π(a) ∪ Π(b) ∪ Π(c)` (eq. (6.45)).
- The **degree-2 forcing (eq. (6.44))**: because `a` has degree 2 in `G_v^{ab}`
  (only `ab, ac` incident), the `a`-block of the row-dependency forces `r =
  −Σⱼ λ_(ac)j rⱼ(q(ac))`; symmetry gives `r' = r`, `r'' = −r`. All three
  candidates test the **same** `r`.
- **The contradiction (the load-bearing use of Lemma 2.1).** Take four
  affinely-independent points `p₁ = Π(a)∩Π(b)∩Π(c)`, `p₂ ∈ Π(a)∩Π(b)∖Π(c)`,
  `p₃ ∈ Π(b)∩Π(c)∖Π(a)`, `p₄ ∈ Π(c)∩Π(a)∖Π(b)` (possible since `(G_v^{ab},q)` is
  generic-nonparallel). Every line `pᵢpⱼ` lies in `Π(a)∪Π(b)∪Π(c)`, so each
  `2`-extensor `pᵢ ∨ pⱼ` belongs to (6.45). By **Lemma 2.1**, the `(4 choose 2) =
  6` extensors `{pᵢ∨pⱼ}` are linearly independent, hence span ℝ⁶ — so `r ⟂` all
  of ℝ⁶ forces `r = 0`, contradiction. □

So at least one of `(G,p₁),(G,p₂),(G,p₃)` is full rank. (The final "convert to
nonparallel by slightly rotating `v`'s or `a`'s panel without dropping rank" is
KT Lemma 5.2, green from Phase 18 — `finrank_infinitesimalMotions_le_of_span_le`.)

**This half is buildable** once the candidate scaffold is in Lean; its only
deep input (Lemma 2.1) is green. The risk is concentrated entirely in Claim
6.11.

## Candidate normal form — ABSTRACT one per-candidate lemma, instantiate ×3 (settled in 22c's recon, §1.26 Q1)

The three candidates are symmetric: `p₂ = p₁` with `a ↔ b`; `p₃ = p₁ ∘ ρ` for
the iso `ρ : G_a^{vc} ≅ G_v^{ab}` (KT p. 686, `ρ(v)=a`, `ρ(u)=u` otherwise — `v,a`
both degree-2 adjacent). KT does the row-ops once ("the same analysis" for the
others). So the formalization states the **per-candidate row-op + the eq. (6.29)
block-triangular completion once**, parametrized by `(degenerate hinge, free
panel line L)`, and instantiates it three times via the `a↔b` swap and the `ρ`
relabel. The stratum-1 producer `case_II_placement_eq612` is already this
per-candidate shape (it takes the degenerate hinge `e_b`/`e_a` and the shear
`t`); 22d generalizes its output from `≥ D(|V|−1)−1` to `= D(|V|−1)` *under
Claim 6.11's redundant-row hypothesis* on a single candidate, then the
Claim-6.12 disjunction picks the full-rank one.

`d=3`-first (§1.26 Q2): YES — concrete `D=6` / 3-candidate case; general `d`
(Lemma 6.13, the length-`d` chain `v₀…v_d`, which re-instantiates the same
candidate normal form via isos `ρᵢ`, eqs. (6.46)–(6.64)) stays Phase 23, KT's
own §6.4.1-then-§6.4.2 cut.

## Lemma checklist

The Lean node cut is **deferred to the next session** (after this recon
settles, same as 22a→22b, 22b→22c). The opening recon's output is the verdict
above. Provisional node shape (to be cut leaf-most-first next session, NOT
committed yet):

- [ ] (next session) `lem:case-III-claim-6-11` — the redundant-`ab`-row fact
  (Claim 6.11, eq. (6.23)). **Carried as a hypothesis `h_redundant_row`** on the
  candidate-completion node, red, `\uses`'d; discharged in a *later* sub-phase
  (matroid-base 4.3(ii) + `M(G̃)`↔row-dependence bridge + nested IH-at-restriction).
- [ ] (next session) per-candidate completion: lift `case_II_placement_eq612`'s
  `≥ D(|V|−1)−1` to `= D(|V|−1)` on one candidate using `h_redundant_row` (the
  eq. (6.24)–(6.29) row-op + top-left-`6×6`-full-rank step). Candidate normal
  form, instantiated ×3.
- [ ] (next session) Claim 6.12 disjunction: `extensorSpan` contradiction via
  Lemma 2.1 (`omitTwoExtensor_linearIndependent`) + the eq. (6.44) degree-2
  forcing ⟹ one candidate is full rank. **Buildable** (Lemma 2.1 green).
- [ ] (next session) compose ⟹ `lem:case-III` / `lem:case-II-realization` /
  `theorem_55.hsplit` at `k=0`, **green-modulo `lem:case-III-claim-6-11`**.

## Blockers / open questions

- **Claim 6.11 build vs axiomatize — RESOLVED (this recon, the load-bearing
  verdict):** AXIOMATIZE-AS-HYPOTHESIS — carry `h_redundant_row`, `\uses` a red
  `lem:case-III-claim-6-11`. Three gaps (no `M(G̃)`↔row bridge; KT 4.3(ii) not in
  matroid-base form; the conversion is a fresh nested-IH-at-restriction, not the
  green corank bridge) make the build route not close. Discharge it in a later
  sub-phase (the 21→21b / 22a→22b pattern). Do NOT build it from
  `matroidMG_indep_iff` next session.
- **Claim 6.12 — DE-RISKED:** bottoms on the green Lemma 2.1
  (`omitTwoExtensor_linearIndependent`); buildable once the candidate scaffold
  is in Lean.
- **Candidate normal form — SETTLED (22c §1.26 Q1):** abstract one per-candidate
  lemma, instantiate ×3 (`a↔b` swap + `ρ` relabel).
- **Node cut deferred:** the leaf-most-first Lean node order is the next
  session's first task, after this verdict. Same discipline as 22c's stratum-1
  node-cut deferral.
- **Recurring Lean traps** (carry from 22a/22b/22c, FRICTION): heavy
  `IsInfinitesimallyRigidOn`/framework defeq across `ofNormals`/`withGraph`
  graph-swaps can `isDefEq`-timeout — make the two frameworks *syntactically*
  equal before a `convert`; pre-convert rigidity hypotheses; transfer across an
  `infinitesimalMotions` equality via a `mem_infinitesimalMotions` round-trip.

## Hand-off / next phase

**This commit is the design-pass-first opening recon** — docs only, no Lean, no
`\leanok`. Its load-bearing output is the **Claim 6.11 verdict
(axiomatize-as-hypothesis)** above, reached before any Lean node is cut, per the
user's standing direction for the crux ("very intricate; never dispatch a build
before the plan is clear").

**The next concrete commit cuts the FIRST LEAN NODE of 22d**, leaf-most-first:
build the **Claim 6.12 disjunction half first** (it is the de-risked, buildable
half — the extensor-span contradiction via the green Lemma 2.1 + the eq. (6.44)
degree-2 forcing), wiring the three candidates produced by instantiating
`case_II_placement_eq612` ×3, and carry the per-candidate completion's
redundant-row input (Claim 6.11) as the explicit hypothesis `h_redundant_row`
with the red node `lem:case-III-claim-6-11`. The candidate-completion node
(eq. (6.29) row-op lifting `≥ D(|V|−1)−1` to `= D(|V|−1)` under `h_redundant_row`)
is the second node. Compose ⟹ `lem:case-III` green-modulo `lem:case-III-claim-6-11`.

Re-recon the node order at that build's open (confirm the count
`(D−1)+1+D(|V|−2) = D(|V|−1)` closes and the candidate-normal-form ×3
instantiation type-aligns against `case_II_placement_eq612`'s signature — the
honesty gate's 2nd/3rd halves).

The **`d=3` assembly** (`prop:rigidity-matrix-prop11` `hub` + `thm:theorem-55`
flip + `case_I_realization` → `theorem_55_generic` Case-I wiring) stays the
**deferred, unlettered** planning note (it gets a letter when its turn comes;
the crux may split). General-`d` (Lemma 6.13) → Thm 5.5 → Thm 5.6 → Conjecture
1.2 stays Phase 23.

KT math: KT §6.4.1 (Lemma 6.10, Claims 6.11/6.12, eqs. (6.22)–(6.45)),
`notes/Phase21b.md` *Finding A/B*, `notes/Phase22-realization-design.md`
§1.26 (Q3/Q4) + §3 *Track B*, `notes/Phase22c.md` *Sub-phase scope cut*.
