# Phase 22d — Claim 6.11's first green-machinery prerequisite (the matroid-base 4.3(ii) leaf) (work log)

**Status:** in progress (opened 2026-06-05 design-pass-first; re-scoped
2026-06-05 per a fresh user direction; **Gap-2 leaf landed green 2026-06-06**;
**Gap-3 design recon 2026-06-06, docs-only**). This sub-phase builds the
**missing-green-machinery prerequisites of KT Claim 6.11**, bottom-up — not the
candidate scaffold and not an axiomatized Claim 6.11.

## Current state

**This commit is the design-pass-first recon of Gap 3 (the nested
IH-at-restriction), docs-only** — settling Gap-3's buildability + node cut before
any build, the way the Gap-2 re-scope recon preceded the Gap-2 build. **Verdict
(load-bearing): Gap 3 SPLITS.** Its combinatorial shell (`def(G̃_v) ≤ D−2` ⟹
`G_v` minimal `k'`-dof) is green; its analytic core — the eq. (6.22) rank of the
*specific restricted realization* `R(G_v, q|_{E_v})` — is the **irreducible
research-shaped kernel** (NOT buildable from green machinery the way Gap 2 turned
out to be), for a structural reason verified against the real signatures: the
project's IH motive is **existence-only** and KT's eq. (6.22) + footnote 6 need a
**rank-of-a-given-realization** statement the existence motive cannot deliver. The
leaf-most buildable Gap-3 piece — the combinatorial shell `splitOff_removeVertex_minimalKDof`
— is cut below; the kernel is isolated as a named carry-as-hypothesis red node. See
*Gap 3 recon (2026-06-06)* below.

The Gap-2 leaf **landed green + axiom-clean** (prior commit) as
`Graph.splitOff_exists_base_inter_fiber_lt` (`ForestSurgery.lean`), the
**matroid-base form of KT Lemma 4.3(ii) at `k = 0`** — the existence of a base
`B'` of `M(G̃_v^{ab})` with `|ãb ∩ B'| < D−1`, so `ãb ⊄ B'` (a redundant
`ãb`-copy exists). Blueprint node `lem:case-III-claim-6-11-base` is green;
`lem:case-III` / `lem:case-II-realization` stay red.

**The re-recon at build open refined the node cut** (the hand-off flagged this
exact check). KT 4.3(ii) is an **existence** statement ("there *is* a base with
`< D−1`"), not the "every base `B'`" universal the opening cut sketched —
matching the actual Claim-6.11 use ("the fiber `ãb` is not contained in *any*
base — a redundant copy exists"). Its `k=0` proof is KT's own route via **Lemma
4.1**'s surgery: the strengthened `forest_surgery_count` produces an
`M(G̃_v^{ab})`-independent `I'` with `|I'| = |base| − D` **and** `|ãb ∩ I'| < D−1`
(KT Lemma 4.1's *two* conclusions; the second was the genuinely-new half this
phase added), and at `k=0` `def(G̃_v^{ab}) = 0` makes `I'` a base. So the leaf
was a **two-brick** commit: (1) strengthen the green `forest_surgery_count` with
the `|ãb ∩ I'| < D−1` conjunct (the inserted `r i` are the only `e₀`-copies, one
per degree-2 forest, `h' ≤ D−2`); (2) the `k=0` base assembly. No separate
"parallel-copies sub-leaf" was needed (the open construction question resolved:
the bound falls out of the surgery's degree-count `2h' + (D−h') = h ≤ 2(D−1)`).

## The re-scope (user override of the opening recon, 2026-06-05)

The opening recon (commit 4e6a7bb, below under *Superseded opening verdict*)
concluded Claim 6.11 should be **axiomatized as a hypothesis** (`h_redundant_row`
+ a red node) and the Claim 6.12 scaffold built downstream onto eq. (6.12). The
user **overrode** that:

> "We just opened 22d so we can decide what to put here. If there's missing green
> machinery for Claim 6.11, shouldn't we queue one of those into 22d rather than
> pushing beyond onto 6.12?"

i.e. **do NOT defer Claim 6.11 and build onto 6.12; make 22d build the FIRST
missing-green-machinery prerequisite of Claim 6.11, attacking the hard node
bottom-up.** This recon re-scopes 22d to that leaf, verified against the *actual*
green Phase-19/20 Lean (not the opening recon's reading of it — which, the
re-recon found, **understated the green substrate**; see *The green substrate is
richer than the opening recon credited* below).

The Claim 6.11 discharge path's three gaps (opening recon) are, in dependency
order:
1. **Gap 2 — the matroid-base 4.3(ii) form** (a base `B'` of `M(G̃_v^{ab})`
   with `|B' ∩ ãb| < D−1`). Pure combinatorial `M(G̃)` matroid theory, no
   rigidity matrix. **All inputs green** (verified below) ⟹ **this is the leaf.**
2. **Gap 3 — the nested IH-at-restriction** (apply the geometric IH (6.1) to
   `G_v = G_v^{ab} − ab` at the restricted realization). **Consumes Gap 2's
   output** (`def(G̃_v) ≤ |B'∩ãb| ≤ 4` ⟹ `G_v` is minimal `k'`-dof, `k' ≤ 4`,
   the input to the IH). Not the leaf.
3. **Gap 1 — the `M(G̃)`↔row-dependence bridge** (combinatorial redundancy ⟹
   a redundant rigidity row at `q`). **Consumes Gap 2 AND Gap 3**. Not the leaf.

**22d = Gap 2, first buildable sub-brick** (the multi-stratum discipline 22c
used — Gap 2 is itself a small chunk; 22d cuts its leaf sub-brick, see *Node
cut*). The remaining Claim-6.11 pieces (Gap 3 nested IH, Gap 1 row bridge), the
Claim-6.12 disjunction, the candidate scaffold, and the candidate-completion
node become **named, deferred, unlettered further sub-phases** (the
assembly-naming precedent: a sub-letter is minted when its turn comes).

## The dependency decomposition of Claim 6.11 (verified against the green signatures)

Claim 6.11 (KT p. 684): *in `R(G_v^{ab}, q)` there is a redundant row among the
5 (= `D−1`) `ab`-rows* — eq. (6.23), the `+1` row that lifts 22c's stratum-1
`D(|V|−1)−1` brick to full `D(|V|−1)`. KT's proof (pp. 684–685):

1. **(Gap 2) matroid-base 4.3(ii).** `G_v^{ab}` minimal 0-dof ⟹ a base `B'` of
   `M(G̃_v^{ab})` has `|B' ∩ ãb| < D−1`, so the fiber `ãb` of the short-circuit
   edge `e₀=ab` is **not contained in any base** — a *redundant* `ãb`-copy
   exists in `M(G̃_v^{ab})`.
2. **(Gap 3) nested IH.** Set `G_v := G_v^{ab} − ab` (`= G − v = removeVertex v`).
   `B' ∖ ãb` is independent in `M(G̃_v)` of cardinality `D(|V∖{v}|−1) − h`,
   `h = |B' ∩ ãb| ≤ D−2`, so `def(G̃_v) ≤ h ≤ D−2`; `G_v` is minimal `k'`-dof,
   `k' = def(G̃_v) ≤ D−2` (minimality by Lemma 3.3, `subgraph_minimality`). Apply
   the **geometric IH (6.1)** to `G_v` at `q|_{E_v}` (still generic-nonparallel,
   KT footnote 6): `rank R(G_v, q|_{E_v}) = D(|V∖{v}|−1) − k'` (eq. (6.22)).
3. **(Gap 1) combinatorial↔linear conversion.** `R(G_v, q|_{E_v})` is
   `R(G_v^{ab}, q)` with the 5 `ab`-rows removed; `rank R(G_v^{ab},q) =
   D(|V∖{v}|−1)`; adding back `≤ D−2` of the `ab`-rows already spans the row
   space ⟹ at least one `ab`-row is redundant (eq. (6.23)). □

**Dependency order (verified):** Gap 2 → Gap 3 → Gap 1. Gap 2 is the only piece
whose inputs are *all* green (it is combinatorial-only); Gap 3 consumes Gap 2's
`h ≤ D−2` count to name `k'` and feeds the IH; Gap 1 consumes both. So the
leaf-most buildable piece is **Gap 2, the matroid-base 4.3(ii) form** — confirming
the task's strong prior, *and* (the re-recon's main finding) it is far more nearly
green than the opening recon credited.

## The green substrate is RICHER than the opening recon credited (the load-bearing finding)

The opening recon's Gap-2 claim — "KT 4.3(ii) is not in matroid-base form;
even the first input would have to be freshly formalized
(`SplitOffDeficiency.lean:195`)" — is **only half right**. The deficiency-count
form was indeed all Theorem 4.9 needed, BUT the green Phase-20 proof of
`splitOff_isMinimalKDof` (`ForestSurgery.lean:763`) **already builds the
matroid-base count for the `ãb` fiber** — it just discards it after using it for
minimality. Read its doc-comment (`ForestSurgery.lean:758–762`):

> *"any base `B'` of `M(G̃_v^{ab})` avoiding a fiber `ẽ` has `|B'| ≤ |E(G̃_v)|`
> (case `e = e₀`: `B' ⊆ E(G̃_v)`; case `e ≠ e₀`: `B'` splits into `B' ∩ ã̃b` of
> size `≤ D − 1` and `B' ∩ E(G̃_v) ⊆ E(G̃_v) ∖ ẽ` …). Via
> `isBase_ncard_add_deficiency_eq` … this forces `def(G̃_v) ≤ def(G̃_v^{ab}) = 0`."*

This is the **same** base-splits-across-`ãb` count Gap 2 needs. The green inputs,
all verified by signature:

- **`circuit_splitOff_meets_fiber`** (`ForestSurgery.lean:669`, KT (4.10), green):
  under no-proper-rigid, every circuit of `M(G̃_v^{ab})` meets `ãb`; equivalently
  `E(G̃_v) = E(G̃_v^{ab}) ∖ ãb` is **circuit-free**, i.e. an `M(G̃_v^{ab})`-base of
  its own ground set, descending to a base of `M(G̃_v)` by restriction.
- **`mulTilde_splitOff_deleteFiber_le`** (`ForestSurgery.lean:65`): `(G̃_v^{ab})
  ＼ ãb ≤ G̃` — surviving fibers are `v`-avoiding `G`-fibers.
- **`mulTilde_removeVertex_le_splitOff`** (`ForestSurgery.lean:91`): `(G_v)̃ ≤
  G̃_v^{ab}`, the Gap-3 nested-graph inclusion *already present at the
  combinatorial level*.
- **`matroidMG_restrict_mulTilde`** (`Deficiency.lean:212`): `M(G̃) ↾ E(H̃) =
  M(H̃)` — the base-transport engine.
- **`isBase_ncard_add_deficiency_eq`** (`Deficiency.lean:1005`, def=corank base
  form): `|B| + def(G̃) = D(|V|−1)`.
- **`splitOff_isMinimalKDof`** (`ForestSurgery.lean:763`): `G_v^{ab}` is minimal
  0-dof, so a base `B'` has `|B'| = D(|V∖{v}|−1)` and meets every fiber.
- **`removeVertex_deficiency_ge`** (`SplitOffDeficiency.lean:405`, KT 4.4):
  `def(G̃) ≤ def(G̃_v)` — the lower bound on `k'`.
- **The template** `isBase_vfiber_ncard_ge` (`ReducibleVertex.lean:60`): the
  *exact same proof shape* (rank count via `B ∖ fiber ⊆ E(restricted)` +
  def=corank) for the **parent** graph's `v`-fibers. Gap 2 is the split-off-graph,
  single-`e₀`-fiber analogue — `isBase_vfiber_ncard_ge` is a near-verbatim
  template.

**Net.** Gap 2 (the matroid-base 4.3(ii) form) is **buildable from green
infrastructure** — no axiom, no hypothesis-launder. The opening recon's
"axiomatize-as-hypothesis" verdict on Claim 6.11 was the right fallback *under
the old scope* (don't pause to build the whole bridge before the scaffold), but
the user's bottom-up direction is sound: the leaf prerequisite is reachable, and
building it first de-risks Gaps 3/1 by making the combinatorial substrate concrete.

## Node cut — the leaf-most-first first build of re-scoped 22d (the planning cut; LANDED)

**Landed as `splitOff_exists_base_inter_fiber_lt`** (not the working name
`splitOff_base_inter_fiber_lt`, and as the *existence* form — see *Current state*
for the build-open refinement). The planning cut below is retained as the recon
trail.

The leaf piece (Gap 2) is itself a small two/three-brick chunk; per the
multi-stratum discipline (22c), 22d cuts only its **first buildable sub-brick**,
the redundant-`ãb`-edge existence fact, leaf-most-first:

- [ ] **(next commit, the leaf) `splitOff_base_inter_fiber_lt`** (working name) —
  *the matroid-base 4.3(ii) form, upper-bound half.* For `G` minimal 0-dof with
  no proper rigid subgraph, `v` a reducible degree-2 vertex, `G_v^{ab} =
  splitOff v a b e₀`, and any base `B'` of `M(G̃_v^{ab})`:
  `(B' ∩ edgeFiber e₀ n).ncard < bodyHingeMult n` (`= D−1`), equivalently
  `(B' ∩ ãb).ncard ≤ D−2` — so `ãb ⊄ B'`, a redundant `e₀`-copy exists.
  **Inputs** (all green): `splitOff_isMinimalKDof` (`|B'| = D(|V∖{v}|−1)`,
  meets every fiber), the base-splits-across-`ãb` count
  (`|B'| = |B'∩ãb| + |B'∩E(G̃_v)|`, `Set.ncard_inter_add_ncard_diff_eq_ncard`
  as in `isBase_vfiber_ncard_ge:113`), `B'∩E(G̃_v)` independent in `M(G̃_v)`
  (`matroidMG_restrict_mulTilde` + `mulTilde_removeVertex_le_splitOff`),
  def=corank on `G_v` (`rank_add_deficiency_eq`), and KT 4.7
  (`def(G̃_v) > 0`, the proper-subgraph-not-rigid step that
  `splitOff_isMinimalKDof`'s proof already discharges internally — extract it).
  **Count** (to confirm at build open): `|B'∩ãb| = |B'| − |B'∩E(G̃_v)| ≥
  D(|V∖{v}|−1) − rank M(G̃_v) = def(G̃_v)`. The UPPER bound `< D−1` is the
  genuinely-new half: `B'∩ãb` is an independent set inside the `D−1` parallel
  `e₀`-copies on the single vertex pair `{a,b}`; the redundancy comes from the
  `def(G̃_v) ≥ def(G̃) > 0`-driven mismatch (a base cannot use all `D−1` copies
  without exceeding `rank M(G̃_v^{ab})`). **Likely one residual sub-brick:** a
  small "parallel-copies fiber on a single edge contribute a bounded amount to a
  union-matroid base" fact may be needed for the sharp `≤ D−2`; confirm at build
  open whether `splitOff_isMinimalKDof`'s internal count gives it directly or it
  needs its own leaf. **Target blueprint node:** new red `lem:case-III-claim-6-11-base`
  (working label), `\uses` the green Phase-20 nodes; `lem:case-III` /
  `lem:case-II-realization` stay red.

The honesty-gate 2nd half (count closes) is traced above; the 3rd half
(structural fidelity) holds because this brick *is* KT's own step-1 argument
(matroid base + def=corank), not a re-expression.

## Deferred, named, unlettered further sub-phases (the rest of Claim 6.11 + downstream)

These are parked until the leaf's shape is clear (a letter is minted when the
turn comes — the assembly-naming precedent; the crux may still split):

- **Gap 3 — the nested IH-at-restriction. SPLITS** (2026-06-06 recon, above):
  - *shell (next build, green):* `splitOff_removeVertex_minimalKDof` — `G_v`
    minimal `k'`-dof, `0 ≤ k' ≤ D−2` (`subgraph_minimality` etc., green).
  - *kernel (research-shaped, red):* the eq. (6.22) generic-rank transfer — the
    rank of the *specific* restricted realization `R(G_v, q|_{E_v})` at the
    inductively-fixed seed `q` (KT footnote 6). NOT green-buildable: the IH motive
    is existence-only; the device runs the opposite direction. Likely merges with
    Gap 1.
- **Gap 1 — the `M(G̃)`↔row-dependence bridge.** The genuinely-new analytic
  content: convert the leaf's combinatorial redundant `ãb`-copy + Gap 3's IH
  rank into a redundant *rigidity row* of `R(G_v^{ab},q)` (eq. (6.23)). Still no
  green `panelRow`↔`matroidMG` bridge exists (re-confirmed: no file mentions both).
  **Likely shares the Gap-3 kernel** — "the seed `q` attains the rank `M(G̃)`
  predicts" (recon item-3 sharpening).
- **The candidate-completion node + Claim 6.12 disjunction.** Once Gaps 2/3/1
  give the redundant `ab`-row, lift 22c's `case_II_placement_eq612`'s `≥
  D(|V|−1)−1` to `= D(|V|−1)` on one candidate (eq. (6.24)–(6.29) row-op), then
  the Claim-6.12 extensor-span contradiction via the **green** Lemma 2.1
  (`omitTwoExtensor_linearIndependent`) + the eq. (6.44) degree-2 forcing picks
  the full-rank candidate. Claim 6.12 stays **de-risked** (Lemma 2.1 green); the
  candidate normal form is **abstract-one / instantiate-×3** (settled, below).
- **The `d=3` assembly** (`prop:rigidity-matrix-prop11` `hub` + `thm:theorem-55`
  flip + the Case-I wiring) — unchanged, deferred + unlettered.
- **General `d`** (Lemma 6.13) → Thm 5.5 → Thm 5.6 → Conjecture 1.2 — Phase 23.

## Candidate normal form — ABSTRACT one per-candidate lemma, instantiate ×3 (settled in 22c's recon, §1.26 Q1)

Unchanged by the re-scope (it governs the *downstream* candidate-completion node,
now deferred). The three candidates are symmetric: `p₂ = p₁` with `a ↔ b`;
`p₃ = p₁ ∘ ρ` for the iso `ρ : G_a^{vc} ≅ G_v^{ab}`. State the per-candidate
row-op + eq. (6.29) completion **once**, instantiate ×3. `case_II_placement_eq612`
is already this per-candidate shape. `d=3`-first (§1.26 Q2): general `d`
(Lemma 6.13) stays Phase 23, KT's own §6.4.1-then-§6.4.2 cut.

## Gap 3 recon (2026-06-06) — the nested IH-at-restriction (design-pass-first, docs-only)

Settles the next piece flagged by the Gap-2 hand-off, verified against KT §6.4.1
(pp. 684–685, eq. (6.22) + footnote 6, `.refs/katoh-tanigawa-2011-…pdf` pdf
pp. 38–39) AND the actual green Lean signatures (lean-lsp / Read, not guesses).

### What Gap 3's job is (KT eq. (6.22))

From the Gap-2 leaf: a base `B'` of `M(G̃_v^{ab})` with `h := |ãb ∩ B'| < D−1`,
so `h ≤ D−2 = 4` and `|B'| = D(|V∖v|−1)` (`G_v^{ab}` is 0-dof). Set
`G_v := G_v^{ab} − ab = G − v` (`removeVertex v`). Then `B' ∖ ãb` is
`M(G̃_v)`-independent of cardinality `D(|V∖v|−1) − h`, so `def(G̃_v) ≤ h` (KT
(2.4)) ⟹ `G_v` is minimal `k'`-dof, `k' = def(G̃_v) ≤ h ≤ D−2`. KT's eq. (6.22)
then claims, **for the specific restricted realization** `q|_{E_v}` (where `q` is
the seed already chosen for `G_v^{ab}` in the inductive step):
`rank R(G_v, q|_{E_v}) = D(|V∖v|−1) − k'`. Its *only* downstream use (Gap 1): with
`rank R(G_v^{ab},q) = D(|V∖v|−1)` (full, eq. (6.18)), and `R(G_v, q|_{E_v}) =
R(G_v^{ab},q)` minus the `D−1` `ab`-rows, the corank `k' ≤ D−2` over the `D−1`
`ab`-rows forces (pigeonhole) **one `ab`-row redundant** (eqs. (6.23)–(6.24)). So
Gap 3's payload is exactly: **`corank R(G_v, q|_{E_v}) = k' ≤ D−2`** at the
incoming seed `q`.

### 1. The combinatorial glue — GREEN (confirmed, pin the lemmas)

The chain `leaf ⟹ def(G̃_v) ≤ D−2 ⟹ G_v minimal k'-dof` composes from green
Phase-19/20 lemmas, no new analytic content:

- **`def(G̃_v) ≤ h`** = the leaf's `h ≤ D−2` plus the `M(G̃_v)`-base count. The
  leaf already gives `B' ∖ ãb` independent in `M(G̃_v)` of size `|B'| − h`
  (`matroidMG_restrict_mulTilde` + `mulTilde_removeVertex_le_splitOff`, both green,
  `Deficiency.lean:212` / `ForestSurgery.lean:91`); `def = corank` via
  `rank_add_deficiency_eq` (`Deficiency.lean:994`) / `isBase_ncard_add_deficiency_eq`
  (`Deficiency.lean:1005`) converts the count to `def(G̃_v) ≤ h`.
- **lower bound `def(G̃) ≤ def(G̃_v)`** = `removeVertex_deficiency_ge` (KT 4.4,
  `SplitOffDeficiency.lean:405`, green) ⟹ `k' ≥ 0`; combined gives `0 ≤ k' ≤ D−2`.
- **`G_v` minimal `k'`-dof** = `subgraph_minimality` (KT Lemma 3.3,
  `Deficiency.lean:400`, green): `G_v ≤ G` minimal-`0`-dof + `G_v.IsKDof n k'` ⟹
  `G_v.IsMinimalKDof n k'`. The `G_v ≤ G` half is `removeVertex_le` (mathlib
  `Graph` order, green); the `IsKDof n k'` half is just the def-count above.

Small new sub-brick: a one-shot lemma `splitOff_removeVertex_minimalKDof` packaging
"`G_v` is minimal `k'`-dof with `0 ≤ k' ≤ D−2`" from the leaf's `B'`. Pure `M(G̃)`
matroid theory, mirrors `splitOff_exists_base_inter_fiber_lt`'s shape; buildable.
**This is the leaf-most buildable Gap-3 piece** (the node cut, below).

### 2. The device re-application — re-applies in PRINCIPLE, but to the WRONG output shape

The Phase-21b device's real interface (signatures verified):

- **`exists_good_realization_ofParam`** (`GenericityDevice.lean:177`): given a fixed
  `(G, ends)` recording links + a seed `q₀` at which the `s`-indexed `panelRow`
  family is independent, produces `∃ q, #s + dim Z(G,q) ≤ D|α|`. I.e.
  *one-point-independence ⟹ existence of a good point with that corank bound.*
- The IH motive **`HasFullRankRealization k G := ∃ Q, Q.graph = G ∧
  Q.toBodyHinge.IsInfinitesimallyRigidOn V(G)`** (`PanelHinge.lean:931`) — an
  **existence** of *some* full-rank framework, `V(G)`-relative (`DESIGN.md`
  *Realization motive must be V(G)-relative*). `theorem_55`'s `hsplit`/`hcontract`
  premises hand the IH for the smaller graph in exactly this existence shape.

The device **does** re-apply to the nested subgraph `G_v` mechanically:
`exists_good_realization_ofParam` is stated for an arbitrary fixed `(G, ends)`, so
`G := G_v`, `ends := ends|_{E_v}` is a valid instance, and the nested-graph
inclusion `mulTilde_removeVertex_le_splitOff` is green. **But it produces existence
of a good point, not the rank of a *given* point** — which is the wrong shape for
eq. (6.22) (see item 3). The `withGraph` primitive (`PanelHinge.lean:411`,
`ofNormals_withGraph` `:459`, the panel-data-preserving graph swap) is the project's
exact analogue of KT's `q|_{E_v}`: `(ofNormals G_v^{ab} ends q).withGraph G_v =
ofNormals G_v ends q` — *same `q`, smaller graph*. So the OBJECT `R(G_v, q|_{E_v})`
is expressible; what is missing is a theorem about its rank.

### 3. The research-shaped step — THE VERDICT: irreducible kernel, NOT green-buildable

**Verdict: the eq. (6.22) rank claim is the irreducible research-shaped kernel, NOT
buildable from green machinery the way Gap 2 was.** The reason is structural, not a
missing-lemma gap, and is verified against the real signatures:

> KT eq. (6.22) is a statement about the rank of **the specific realization**
> `(G_v, q|_{E_v})` for the **already-chosen** seed `q`. KT proves it via footnote 6:
> *"if one particular nonparallel realization achieves the rank `D(|V∖v|−1)−k'`,
> then all generic nonparallel realizations attain the same rank by definition"* —
> and `q` restricted to `E_v` inherits algebraic independence of its panel
> coefficients (KT: *"this property clearly remains in the realization restricted to
> `E_v`"*), so `(G_v, q|_{E_v})` is itself a generic nonparallel realization and the
> IH (6.1) applies to **it**.

The project's IH gives `HasFullRankRealization k G_v` = *∃ some full-rank framework
on `G_v`*. It does **not** give "the framework `ofNormals G_v ends q` (the
restriction of the already-fixed `q`) attains rank `D(|V∖v|−1)−k'`." Bridging the
two is exactly footnote 6, and the project's device runs the **opposite direction**:
device = *one-point-independence ⟹ existence of a good point* (`∃ q, …`); footnote 6
= *generic-attains-max ⟹ this generic point attains it* (`∀`-flavored, given-point).
There is no green lemma that says "a realization whose coefficients are algebraically
independent attains the existence-IH's maximal rank" — the project carries no
"algebraically-independent ⟹ generic ⟹ attains max" transfer (the device only
*produces* a good point, never certifies a *given* one is good). Confirmed: grep for
`generic.*attain` / `attains.*max` over `AlgebraicInduction/` returns nothing of this
shape; the only motive→`ofNormals` bridge, `exists_rigidOn_ofNormals_of_hasFullRankRealization`
(`GenericityDevice.lean:1078`), re-packages the *existence* witness `Q` as *some*
`ofNormals Q.ends q` — it does **not** let you pick `q`.

**Why this is genuinely the kernel and not a Gap-2-style understated substrate.** The
Gap-2 overturn worked because `splitOff_isMinimalKDof`'s green proof *already carried*
the `ãb`-base count — the content existed, was discarded. Here the content
(footnote 6's generic-rank-transfer for a *given* algebraically-independent seed) does
**not** exist anywhere green: it is the "restriction-survives-genericity + generic-
attains-max" device KT footnote 6 invokes, which the project never formalized (Phase
21b built the *existence* device deliberately, since the realization producers only
ever needed `∃ a good seed` — `notes/Phase21b.md` *What 21b delivered*). It is new
analytic content of the same family as Gap 1's `M(G̃)`↔row bridge.

**An important sharpening — Gap 3's payload may be reachable WITHOUT eq. (6.22)'s
exact form, but only together with Gap 1, and still needs the same kernel.** Gap 3's
sole downstream use is the corank bound `corank R(G_v, q|_{E_v}) ≤ D−2` feeding the
pigeonhole. One could imagine getting the redundant `ab`-row directly from the
*combinatorial* redundancy (Gap-2's `ãb ⊄ B'`) by a `M(G̃)`↔row-dependence bridge at
the seed `q` — but that bridge **is Gap 1**, the genuinely-new analytic content
(re-confirmed: no green `panelRow`↔`matroidMG` bridge exists, no file mentions both),
and it *also* needs the realization at the specific seed `q` to attain its
matroid-predicted rank — i.e. the same footnote-6 kernel. So Gaps 3+1 share one
research-shaped kernel: **"the rigidity matrix at the inductively-chosen seed `q`
attains the rank `M(G̃)` predicts"** (combinatorial corank = linear corank at `q`).
This is the single hard node; eq. (6.22) is its specialization to the `ab`-deleted
subgraph.

### 4. Split + node cut — the leaf-most-first Gap-3 first build

**Gap 3 splits** (multi-stratum, like 22c/Gap-2). Leaf-most-first:

- [ ] **(next build, the Gap-3 leaf) `Graph.splitOff_removeVertex_minimalKDof`** —
  *the combinatorial shell of Gap 3, pure `M(G̃)` matroid theory.* From the Gap-2
  leaf's base `B'` (`splitOff_exists_base_inter_fiber_lt`) and the green def-count
  chain (item 1): `G_v = G.removeVertex v` is a minimal `k'`-dof-graph with
  `0 ≤ k' ≤ D−2` (`k' = def(G̃_v)`). **Statement (to confirm shape at build open):**
  for `G` minimal 0-dof, no proper rigid subgraph, `v` reducible degree-2,
  `(G.removeVertex v).IsMinimalKDof n (G.removeVertex v).deficiency n ∧
  0 ≤ def(G̃_v) ∧ def(G̃_v) ≤ bodyHingeMult n − 1` (`= D−2`). **Green inputs (all
  verified by signature):** `splitOff_exists_base_inter_fiber_lt` (Gap-2 leaf),
  `subgraph_minimality` (`Deficiency.lean:400`), `removeVertex_le` (mathlib),
  `matroidMG_restrict_mulTilde` (`Deficiency.lean:212`),
  `mulTilde_removeVertex_le_splitOff` (`ForestSurgery.lean:91`),
  `rank_add_deficiency_eq` (`Deficiency.lean:994`), `removeVertex_deficiency_ge`
  (`SplitOffDeficiency.lean:405`). **Count** (honesty-gate 2nd half): `|B' ∖ ãb| =
  |B'| − h = D(|V∖v|−1) − h ≤ rank M(G̃_v) ≤ D(|V∖v|−1)` and `def(G̃_v) = D(|V∖v|−1)
  − rank M(G̃_v) ≤ h ≤ D−2` — closes from the named greens. **No rigidity matrix,
  buildable.** New green node `lem:case-III-gap3-minimalKDof` (working label),
  `\uses` Gap-2 leaf + the Phase-19/20 green nodes; `lem:case-III` /
  `lem:case-II-realization` stay red.

- **(deferred, the kernel) the eq. (6.22) generic-rank transfer.** Isolated as the
  named research-shaped red node — the carry-as-hypothesis treatment, exactly the
  Phase-21b "carry the analytic crux as `h…` and `\uses` a red node" idiom that
  Cases I/II used for the device pre-21b, and that the design notes' escalation
  ladder names as the recommended fallback for Lemma 6.10 / Claim 6.11
  (`notes/Phase22-realization-design.md` §4, escalation 1). Working name
  `h_seed_attains_matroid_rank` / red node `lem:case-III-gap3-rank` (or, once Gaps
  3+1 are seen to share the kernel, a single `lem:case-III-seed-rank-bridge`). The
  obligation it carries: `corank R(ofNormals G_v ends q) = def(G̃_v)` at the
  inductively-fixed seed `q` (the linear corank at `q` equals the combinatorial
  corank `M(G̃_v)` predicts). It does **not** get `\leanok` until discharged.

**Recommendation for the next build commit:** land the Gap-3 leaf
`splitOff_removeVertex_minimalKDof` (green, the combinatorial shell). The kernel
(eq. (6.22) generic-rank transfer) and Gap 1 (`M(G̃)`↔row bridge) are the two
research-shaped nodes; they likely **merge into one** "seed attains the
matroid-predicted rank" node (item 3 sharpening) and want their own dedicated
math-first sub-phase. Do NOT pre-commit their internal cut now (defer-the-finer-cut,
as 22a→22b, 22c→22d). The honesty-gate 3rd half (structural fidelity): the leaf IS
KT's own eq. (6.22) step-1 (the `def(G̃_v) ≤ h` count + `subgraph_minimality`), not a
re-expression; the kernel is KT's footnote 6, carried honest as a red obligation.

## Where 22c left off (the stratum-1 brick this crux completes)

Phase 22c landed **stratum 1** — the eq. (6.12) `+(D−1)` block-triangular
placement — green + axiom-clean as `PanelHingeFramework.case_II_placement_eq612`
(`CaseI.lean:2331`): `rank R(G,p₁) ≥ D(|V(G)|−1) − 1 = 6|V|−7` at `D = 6`, plus
the `va`-hinge nondegeneracy. **One row short** of full rank `D(|V|−1)`. 22d's
crux supplies the missing `+1` row — and the *bottom* of that crux (KT Claim 6.11)
is what 22d now attacks, leaf-first. The producer exposes the entry-point: its
`e_a = va` link hypothesis is carried as `_hG_ea` ("crux-strata input").

## Lemma checklist

- [x] `Graph.forest_surgery_count` — **strengthened** with the
  `|ãb ∩ ⋃ Fs'i| < D−1` conjunct (KT Lemma 4.1's second conclusion; the only
  `e₀`-copies of the reroute are the inserted `r i`, one per degree-2 forest,
  `h' ≤ D−2`). The one prior caller `forest_surgery_split` re-destructures.
- [x] `Graph.splitOff_exists_base_inter_fiber_lt` — the matroid-base 4.3(ii) leaf
  at `k=0` (Gap 2), green + axiom-clean. Existence of a base `B'` of
  `M(G̃_v^{ab})` with `|ãb ∩ B'| < D−1`, via the strengthened surgery + def=corank
  (an independent set of full rank is a base, `Indep.isBase_of_ncard`). New green
  node `lem:case-III-claim-6-11-base`; `lem:case-III` / `lem:case-II-realization`
  stay red.
- [ ] **(next build, the Gap-3 leaf) `Graph.splitOff_removeVertex_minimalKDof`** —
  the combinatorial shell of Gap 3 (cut by the 2026-06-06 recon above): `G_v =
  removeVertex v` is minimal `k'`-dof, `0 ≤ k' ≤ D−2`, from the Gap-2 leaf's base +
  the green def-count chain (`subgraph_minimality`, `removeVertex_deficiency_ge`,
  `rank_add_deficiency_eq`, `matroidMG_restrict_mulTilde`,
  `mulTilde_removeVertex_le_splitOff`). Pure `M(G̃)` matroid theory, **buildable**.
  New green node `lem:case-III-gap3-minimalKDof`; `lem:case-III` /
  `lem:case-II-realization` stay red.
- [ ] (deferred, **research-shaped kernel**) the eq. (6.22) generic-rank transfer —
  `corank R(ofNormals G_v ends q) = def(G̃_v)` at the inductively-fixed seed `q` (KT
  footnote 6: algebraically-independent seed ⟹ generic ⟹ attains the IH's maximal
  rank). NOT green-buildable: the IH motive is existence-only, the device runs the
  opposite direction (see recon item 3). Likely **merges with Gap 1** into one "seed
  attains matroid-predicted rank" node. Carry-as-hypothesis red node
  `lem:case-III-gap3-rank` / `lem:case-III-seed-rank-bridge`.
- [ ] (deferred) Gap 1 `M(G̃)`↔row bridge; the candidate-completion + Claim-6.12
  disjunction; the `d=3` assembly. Named, unlettered (below).

## Blockers / open questions

- **Gap-3 verdict (this recon): Gap 3 SPLITS** — green combinatorial shell
  (`splitOff_removeVertex_minimalKDof`, the leaf) + an **irreducible
  research-shaped kernel** (eq. (6.22) generic-rank transfer). Unlike Gap 2 (whose
  green substrate the opening recon understated), Gap 3's kernel content is
  genuinely absent from green: the IH is existence-only and the device runs the
  opposite direction from KT footnote 6. So the kernel is carried-as-hypothesis (a
  red node), not built — the recommended Phase-21b escalation idiom. See *Gap 3
  recon (2026-06-06)* items 2–3.
- **Open: do Gap 3's kernel and Gap 1 merge?** The recon's item-3 sharpening says
  the eq. (6.22) generic-rank transfer and the Gap-1 `M(G̃)`↔row bridge share one
  kernel ("the rigidity matrix at the fixed seed `q` attains the rank `M(G̃)`
  predicts"). Confirm when the kernel sub-phase opens whether to cut them as one
  node or two; do not pre-commit now.
- **(Gap-2, resolved):** the sharp upper bound `|B'∩ãb| ≤ D−2` came from the
  strengthened `forest_surgery_count`'s degree-count, not a separate sub-leaf — see
  *Current state*. The open construction question closed.
- **Claim 6.12 — DE-RISKED** (unchanged): bottoms on the green Lemma 2.1.
- **Recurring Lean traps** (carry from 22a/22b/22c, FRICTION): heavy
  `IsInfinitesimallyRigidOn`/framework defeq across `ofNormals`/`withGraph`
  graph-swaps can `isDefEq`-timeout — make the two frameworks *syntactically*
  equal before a `convert`; transfer rigidity across an `infinitesimalMotions`
  equality via a `mem_infinitesimalMotions` round-trip. (Less likely to bite the
  Gap-2 leaf, which is pure matroid theory, but relevant once Gap 1 lands.)

## Hand-off / next phase

**This commit is the design-pass-first recon of Gap 3 (docs-only)** — the check
the Gap-2 hand-off flagged. Verdict: **Gap 3 splits** into a green combinatorial
shell + an irreducible research-shaped kernel (full reasoning + signature
verification in *Gap 3 recon (2026-06-06)*). The shell is cut as the next build;
the kernel is carried-as-hypothesis. `lem:case-III` / `lem:case-II-realization`
stay red. No Lean, no build, no `\leanok`/`\lean{}` changes this commit.

**The next concrete commit builds the Gap-3 leaf
`Graph.splitOff_removeVertex_minimalKDof`** (in `ForestSurgery.lean` next to the
Gap-2 leaf): from the Gap-2 leaf's base `B'` + the green def-count chain
(`subgraph_minimality`, `removeVertex_deficiency_ge`, `rank_add_deficiency_eq`,
`matroidMG_restrict_mulTilde`, `mulTilde_removeVertex_le_splitOff`), prove
`G_v = removeVertex v` is minimal `k'`-dof with `0 ≤ k' ≤ D−2`. Pure `M(G̃)`
matroid theory, no rigidity matrix, **buildable** (count closes — recon item 4).
New green node `lem:case-III-gap3-minimalKDof`.

**After that, the research-shaped kernel** (eq. (6.22) generic-rank transfer) +
**Gap 1** (`M(G̃)`↔row bridge) are the two remaining research-shaped nodes; the
recon's item-3 sharpening argues they likely **merge into one** "the rigidity
matrix at the inductively-fixed seed `q` attains the rank `M(G̃)` predicts" node
(combinatorial corank = linear corank at `q`). They want their own dedicated
math-first sub-phase, carried-as-hypothesis (red) until discharged. Do NOT
pre-commit their internal cut now (defer-the-finer-cut, as 22a→22b, 22c→22d).

The remaining pieces (the candidate-completion + Claim-6.12 disjunction, the
`d=3` assembly, general-`d` Phase 23) stay the **named, deferred, unlettered**
further sub-phases above.

KT math: KT §6.4.1 (Lemma 6.10, Claims 6.11/6.12, eqs. (6.22)–(6.45));
KT §4 (Lemmas 4.3(ii)/4.4/4.7/4.8, the matroid-base substrate); `notes/Phase20.md`
(`splitOff_isMinimalKDof`, the `ãb`-base count); `notes/Phase21b.md` *Finding A/B*;
`notes/Phase22-realization-design.md` §1.26 (Q1–Q4) + §3 *Track B*;
`notes/Phase22c.md` *Sub-phase scope cut*.

---

## Superseded opening verdict (2026-06-05, commit 4e6a7bb) — retained for the audit trail

The opening recon concluded **AXIOMATIZE-AS-HYPOTHESIS** for Claim 6.11 (carry
`h_redundant_row`, `\uses` a red `lem:case-III-claim-6-11`, build the Claim-6.12
scaffold downstream, discharge in a later sub-phase — the 21→21b / 22a→22b
pattern). It identified the three gaps (no `M(G̃)`↔row bridge; KT 4.3(ii) not in
matroid-base form; the conversion is a fresh nested-IH-at-restriction) and judged
the *whole* Claim 6.11 not buildable before the scaffold.

**Superseded** by the user's bottom-up direction (above): rather than axiomatize
the whole claim and push onto 6.12, 22d builds the leaf-most missing prerequisite
(Gap 2, the matroid-base 4.3(ii) form), which the re-recon verified IS buildable
from green Phase-20 infra. The three-gaps decomposition stands; what changed is
that 22d now *attacks* the bottom gap rather than deferring the whole claim. The
opening recon's Gap-2 "not formalized in matroid-base form" was literally true of
the *standalone* lemma but understated that `splitOff_isMinimalKDof`'s proof
already builds the count.
