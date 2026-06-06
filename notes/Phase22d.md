# Phase 22d — Claim 6.11's first green-machinery prerequisite (the matroid-base 4.3(ii) leaf) (work log)

**Status:** in progress (opened 2026-06-05 design-pass-first; re-scoped
2026-06-05 per a fresh user direction; **Gap-2 leaf landed green 2026-06-06**;
**Gap-3 design recon 2026-06-06, docs-only**; **footnote-6 kernel recon
2026-06-06, docs-only** — the eq. (6.22)/(footnote-6) re-test against the *actual*
`HasGenericFullRankRealization` motive + the device's real `_ofNormals`/`_ofParam`
interface); **kernel-route decision 2026-06-06 (user): build the
algebraic-independence route directly to fully green; product-route shortcut
deferred to the standing tracker `notes/AlgebraicIndependence.md`**). This sub-phase
builds the **missing-green-machinery prerequisites of KT Claim 6.11**, bottom-up —
not the candidate scaffold and not an axiomatized Claim 6.11.

## Current state

**This commit is the design-pass-first "size the kernel" recon of KT eq. (6.22) /
footnote 6, docs-only** — a re-test, against the *actual* green signatures (the
22b-strengthened motive + the device's two-direction interface), of the hypothesis
that eq. (6.22) re-exposes from green 21b/22b machinery rather than being genuinely
new analytic content. **Verdict (load-bearing): the hypothesis is REFUTED on its
bottom line, but two of its three structural claims are CONFIRMED.** Confirmed: (a)
the matroid↔row link is *not* a separate matroid-isomorphism — it is the IH itself
(`rank R = D(|V|−1) − def`, the abstract `rigidityMatrix_prop11` bridge, which takes
the two rank bounds `hub`/`hgen` as *hypotheses*, green-modulo); (b) step ③
(redundancy from the rank count) is pure linear algebra given (6.18)+(6.22).
Refuted: eq. (6.22) does **NOT** re-expose, because the kernel it bottoms on —
KT footnote 6's *"this particular algebraically-independent seed `q` attains the
maximal/IH rank"* — is **genuinely absent from green machinery**, for a *sharpened*
structural reason this recon pins exactly (the prior Gap-3 recon stated it
loosely): the project has **no `AlgebraicIndependent`/transcendence machinery at
all**, the device engine runs *only* the existence direction
(`MvPolynomial.exists_eval_ne_zero` ⟹ *∃* a non-root), and `IsGeneralPosition` is
*only* degree-1 pairwise-normal transversality — none of these certifies a *given*
seed is a non-root of the rank polynomial `Q`. This **confirms and sharpens** the
prior Gap-3 verdict (irreducible kernel); it does not overturn it the way the Gap-2
recon overturned its opening verdict. The eq. (6.18) input is NOT separately in
hand either — 22c's `case_II_placement_eq612` *is* the `≥ D(|V|−1)−1` lower-bound
brick; the full `D(|V|−1)` (eq. (6.18)) is exactly the missing `+1` Claim 6.11
supplies. See *Footnote-6 kernel recon (2026-06-06)* below. The leaf-most buildable
Gap-3 piece — the combinatorial shell `splitOff_removeVertex_minimalKDof` — stays
the next build (unchanged from the Gap-3 recon); the kernel stays a named
carry-as-hypothesis red node.

**Earlier (Gap-3 recon, 2026-06-06): Gap 3 SPLITS.** Its combinatorial shell
(`def(G̃_v) ≤ D−2` ⟹ `G_v` minimal `k'`-dof) is green; its analytic core — the
eq. (6.22) rank of the *specific restricted realization* `R(G_v, q|_{E_v})` — is the
**irreducible research-shaped kernel** (NOT buildable from green machinery the way
Gap 2 turned out to be). The leaf-most buildable Gap-3 piece — the combinatorial
shell `splitOff_removeVertex_minimalKDof` — is cut below; the kernel is isolated as
a named carry-as-hypothesis red node. See *Gap 3 recon (2026-06-06)* below.

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

## Node cut for the Gap-2 leaf — LANDED (recon trail compressed)

The Gap-2 leaf landed green + axiom-clean as `Graph.splitOff_exists_base_inter_fiber_lt`
(the *existence* form; planning working name was `splitOff_base_inter_fiber_lt`). What
it delivers, the green inputs, and the build-open refinement (KT 4.3(ii) is an existence
statement proved via Lemma 4.1's surgery — no parallel-copies sub-leaf needed) are in
*Current state* + the *Lemma checklist*; the full planning-cut trail is in commit
13d2464.

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

### 2–3. The kernel — verdict SUPERSEDED by the *Footnote-6 kernel recon* below

Items 2–3 (the device-re-applies-but-wrong-shape analysis + the "eq. (6.22) is an
irreducible kernel, not green-buildable" verdict) are **superseded by the sharper
*Footnote-6 kernel recon (2026-06-06)*** below — it re-tested the same question against
the actual 22b-strengthened motive and named the exact missing brick. Net (full Q1–Q5
there): eq. (6.22)'s rank-at-a-given-seed is genuinely-new analytic content — the device
runs the *existence* direction (`∃` a good point), footnote 6 needs *this*
algebraically-independent seed to attain the rank; Gaps 3+1 share this one kernel ("the
rigidity matrix at the inductively-fixed seed attains the rank `M(G̃)` predicts"). The
device *consumer* `isInfinitesimallyRigidOn_ofNormals_of_rankPolynomial_ne_zero` does run
the given-point direction; what is missing is certifying the seed is a non-root of `Q`.

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

## Footnote-6 kernel recon (2026-06-06) — "size the kernel" against the ACTUAL green signatures (design-pass-first, docs-only)

A re-test of the prior Gap-3 verdict, prompted by the user's sharper hypothesis:
that eq. (6.22) re-exposes from green 21b/**22b** machinery (NOT a separate
matroid-iso), with the kernel collapsing to footnote 6 = "the Phase-21b genericity
device run in the direction we haven't exposed." Verified against the **actual**
current Lean signatures via lean-lsp/Read (the prior Gap-3 recon cited the *bare*
`HasFullRankRealization`; the user pointed at the 22b-strengthened
`HasGenericFullRankRealization`, so a re-read was warranted). Five sub-questions,
each settled against a cited signature.

### Q1 — the motive (existence vs. given-realization). REFUTES the re-expose hope.

`PanelHingeFramework.HasGenericFullRankRealization` (`PanelHinge.lean:968`):
```
∃ Q : PanelHingeFramework k α β,
  Q.graph = G ∧ Q.IsGeneralPosition ∧ Q.toBodyHinge.IsInfinitesimallyRigidOn V(G) ∧
  (the link-recording conjunct on Q.ends)
```
The 22b strengthening added **`Q.IsGeneralPosition`** + the **link-recording**
conjunct (route (i)) — but it is **still `∃ Q`, an EXISTENCE statement**. It gives
"*some* general-position rigid framework on `G`", **not** "the framework built from
the *given*, inductively-fixed seed `q` attains full rank." `IsGeneralPosition`
(`PanelHinge.lean:120`) is **only** `∀ a b, a ≠ b → LinearIndependent ![normal a,
normal b]` — degree-1 *pairwise-normal transversality*, the per-hinge non-degeneracy
the splice/row bricks consume. It does **not** control the high-degree
Gram-determinant rank polynomial `Q`. So even with the 22b strengthening, the motive
does not deliver footnote 6's payload. (The Gap-2 overturn worked because the green
proof already *carried* the discarded content; here the strengthening is the wrong
*kind* of content — pairwise transversality, not "this seed is a non-root of `Q`".)

### Q2 — the device engine (existence-of-a-good-point vs. this-point-attains-max). The precise gap, pinned.

The device has **two halves**, and the second half *is* a "given point attains the
max rank" lemma — but only relative to a polynomial manufactured from a rigid seed:
- **Producer** `exists_rankPolynomial_of_rigidOn{,_linking,_linking_set}`
  (`GenericityDevice.lean:1112/1201/1288`): from a **rigid seed `q₀`**, produces
  `∃ Q, eval q₀ Q ≠ 0 ∧ ∀ q, eval q Q ≠ 0 → (the s-subfamily is LI at q)`. The
  engine underneath is `exists_polynomial_ne_zero_of_linearIndependent_at`
  (`Rank.lean:474`) — `Q` is a *Gram-determinant minor* selected at `q₀`.
- **Consumer** `isInfinitesimallyRigidOn_ofNormals_of_rankPolynomial_ne_zero{,_linking,_linking_set}`
  (`GenericityDevice.lean:1378/1442/1517`): **GIVEN `eval q Q ≠ 0` for a given `q`**,
  concludes `(ofNormals G ends q)` rigid on `V(G)` (pure rank-nullity, **no GP at
  `q` needed** — `:1367`). This *is* "this specific point attains the maximal rank."

**So the engine CAN be re-pointed to a given point — but only if you can prove
`eval q Q ≠ 0` for the SPECIFIC `Q` the producer built from `q₀`.** That is the
entire gap. footnote 6 needs `eval q Q ≠ 0` to hold *because `q`'s coordinates are
algebraically independent over ℚ* (an alg.-indep. point lies off every nonzero
rational polynomial's zero locus). **The project has no such lemma — and no
`AlgebraicIndependent`/transcendence machinery at all** (confirmed: grep for
`AlgebraicIndependent`/`transcend`/`aeval_injective` over the whole tree returns
*nothing*; the only `nonzero-at-a-point` brick is `MvPolynomial.exists_eval_ne_zero`,
`Funext.lean:40`, which gives *∃ a* non-root, never certifies a *given* one). The
`ofParam`/`withMomentNormals` constructions (`PanelHinge.lean:182/225`,
`isGeneralPosition_ofParam`) give a *constructible* GP seed (moment curve, distinct
params ⟹ pairwise-independent normals) — but GP-ness, again, is not non-root-ness of
`Q`. **Precise gap:** the device exposes `(∃ Q, …) ∧ (∀ q non-root ⟹ rigid)`; footnote
6 needs `q-the-given-seed is a non-root of THAT Q`, which requires
`algebraically-independent ⟹ off the zero locus of any nonzero ℚ-polynomial` — a
genuinely-new analytic brick.

### Q3 — restriction-preserves-genericity. ELEMENTARY at the object level; vacuous for the kernel.

"Restrict `q` to `E_v` ⟹ still GP/expressible" is elementary: the object
`R(G_v, q|_{E_v})` is exactly `(ofNormals G_v^{ab} ends q).withGraph G_v`
(`PanelHinge.lean` `withGraph`, `withGraph_normal` is `rfl` — same normals, smaller
graph), and `IsGeneralPosition` reads only the normals, so it is inherited verbatim
(`withNormal`/`withGraph` keep normals; same fact 22c's `case_II_placement_eq612`
already uses, `CaseI.lean:2382`). **But this only preserves GP = pairwise
transversality, which Q2 showed is not the kernel.** The thing footnote 6 needs to
survive restriction is *algebraic independence of the coordinate family* — which the
project never records in the first place (Q2), so there is nothing to restrict. So
Q3 is "elementary but beside the point": the restriction is free; what it would need
to carry (alg. independence) is absent.

### Q4 — IH-application validity. VALID as a smaller instance; but routed through the WRONG branch + the existence shape.

`minimal_kdof_reduction` (`ForestSurgery.lean:992`) is **strong induction on
`V(G).ncard`** (`:1005`, `Nat.strong_induction_on`). `G_v = removeVertex v` drops
`|V|` by one, so it **is** a strictly-smaller instance the induction *could* cover.
Two caveats: (i) the eq. (6.22) subgraph arises in the **`hsplit` branch** (Case
III/II, no proper rigid subgraph), whose IH (`:1000`) is handed on
`G.splitOff v a b e₀` — *same* vertex count — not on the vertex-reduced
`G_v = G − v`; so the IH at `G_v` is a *nested, second* IH-invocation KT makes
inside the splitting-off case (KT's footnote-6 move), not the branch's own IH. (ii)
even granting the nested invocation, the IH delivers only
`HasFullRankRealization k G_v` = *∃ some* full-rank framework on `G_v` (Q1) — it does
**not** hand you the realization *at the restriction of the already-fixed `q`*. So
the IH is applicable to `G_v` as a smaller graph, but its output is the wrong shape
for eq. (6.22) (which is about *the* restricted `q`, not *a* fresh witness).

### Q5 — step ③ pure-LA + eq. (6.18) in hand. ③ CONFIRMED pure LA; (6.18) NOT separately in hand.

- **Step ③ (redundancy from the count) is pure linear algebra given (6.18)+(6.22)**:
  CONFIRMED. With `rank R(G_v^{ab},q) = D(|V|−1)` (6.18) and
  `rank R(G_v, q|_{E_v}) = D(|V|−1) − k'` (6.22), and `R(G_v, q|_{E_v}) =
  R(G_v^{ab},q)` minus the `D−1` `ab`-rows, the `k' ≤ D−2 < D−1` corank over `D−1`
  rows forces (pigeonhole) one `ab`-row redundant. No genericity, no matroid — the
  `isInfinitesimallyRigidOn_ofNormals_of_rankPolynomial_ne_zero` rank-nullity
  arithmetic (`GenericityDevice.lean:1411–1429`) is the template; this part is
  buildable *given the two rank inputs*.
- **eq. (6.18) (`rank R(G_v^{ab},q)` FULL) is NOT separately in hand.** 22c's
  `case_II_placement_eq612` (`CaseI.lean:2331`) takes the inductive `Gv`-realization
  as a *hypothesis* (`hrig`) and produces the `≥ D(|V|−1) − 1` lower bound — it is
  *one row short*. The full `D(|V|−1)` (= eq. (6.18)) is **exactly** the `+1` that
  Claim 6.11 supplies. So eq. (6.18) and the Claim-6.11 redundant row are the *same*
  missing content; step ③ cannot run until that `+1` lands, and that `+1` is what
  eq. (6.22)'s kernel is for. (The hypothesis's "(6.18) already in hand from 22c's
  seed `q`" is **incorrect** — 22c gives the `−1` brick, not full rank.)

### The matroid↔row link confirmation (the hypothesis's correct half)

The hypothesis that "the matroid only enters combinatorially (`k' ≤ 4`); the
rank↔M(G̃) link is the IH itself" is **CONFIRMED**: the only rank↔deficiency bridge
is `rigidityMatrix_prop11` (`PanelHinge.lean:1176`), which is *abstract* — it takes
the two rank bounds `hub` (`D + def ≤ dim Z`) and `hgen` (`dim Z ≤ D + def`) as
**explicit hypotheses** and concludes `RankHypothesis (def)`. Its own doc-comment
(`:1174`) says: *"the generic-rank argument (Claim 6.4) selects the point attaining
this max; that is the Phase-21b device."* So the matroidal half (`def = corank
M(G̃)`) is green (`rank_add_deficiency_eq`); the *analytic* "the seed attains the
matroid-predicted rank" lives in the device — which runs existence-only. No file
contains a `panelRow`↔`matroidMG` bridge lemma (re-confirmed: the files mentioning
both do so only in *prose*, never as a theorem statement).

### Net verdict (the deliverable)

**eq. (6.22), hence Claim 6.11's analytic kernel, is NOT buildable as a modest
re-exposure of green 21b/22b machinery.** It needs **genuinely-new analytic
content**, isolated exactly:

> **The new content = a `non-root-from-algebraic-independence` brick:** the
> inductively-fixed seed `q` (whose panel coordinates are algebraically independent
> over ℚ — KT's standing inductive choice, footnote 6) is a **non-root of the device's
> rank polynomial `Q`** (`eval q Q ≠ 0`), hence the device *consumer*
> `isInfinitesimallyRigidOn_ofNormals_of_rankPolynomial_ne_zero{_linking_set}`
> certifies `(ofNormals G_v ends q|_{E_v})` rigid at the *given* `q`. The two halves
> of this brick: **(i)** record/produce the seed `q` as algebraically independent
> over ℚ (NEW: no `AlgebraicIndependent` machinery exists), and **(ii)**
> `algebraically-independent point ⟹ off the zero locus of any nonzero rational
> polynomial` (NEW: a transcendence-degree / `MvPolynomial.eval`-injectivity fact —
> mathlib has `MvPolynomial` algebraic-independence API, so this half is *mirrorable*
> from upstream, but it is still net-new to this project).

This is the **same family** as the prior recon's diagnosis, but now *named to the
exact missing lemma*. It is **not** "the device run backwards" in the loose sense:
the device's *consumer half already runs the given-point direction* — what is
missing is the bridge that proves the inductive seed satisfies the consumer's
`eval q Q ≠ 0` hypothesis. The kernel does **not** get built here; it is carried as
the named research-shaped red node (Gap-3 kernel, likely merged with Gap 1 — *both*
need "the seed attains the matroid-predicted rank", and both bottom on the same
`non-root-from-alg-indep` brick). **The build queue is unchanged** by this recon:
the next build is still the Gap-3 *combinatorial shell* `splitOff_removeVertex_minimalKDof`.

### Leaf-most-first node cut for the kernel sub-phase (when it opens; do NOT pre-commit the finer internal cut)

When the kernel sub-phase opens, the leaf-most-first cut suggested by the above:
- **(leaf, mirrorable) `MvPolynomial.eval_ne_zero_of_algebraicIndependent`** (working
  name) — the upstream-flavored half (ii): an algebraically-independent
  coordinate-tuple over ℚ is a non-root of every nonzero `MvPolynomial _ ℚ` (cast to
  ℝ). Mirror under `Mathlib/Algebra/MvPolynomial/` if mathlib's
  `AlgebraicIndependent` API gives it cheaply; pure algebra, no rigidity.
- **(the seed) `…_seed_algebraicIndependent`** — record the inductive seed `q` as
  alg.-indep. over ℚ (KT footnote 6's standing choice). NEW; the honest place this
  enters the induction is a strengthened/threaded seed-genericity invariant — likely
  its own recon at open (it interacts with the existence-only motive: the motive may
  need a *third* form carrying "the witness is alg.-indep.", paralleling the 22b GP
  + link-recording strengthenings).
- **(the kernel) `lem:case-III-seed-rank-bridge`** — `corank R(ofNormals G_v ends
  q|_{E_v}) = def(G̃_v)` at the seed, composing the two leaves with the device
  consumer + `rigidityMatrix_prop11` + `rank_add_deficiency_eq`. Stays red /
  carry-as-hypothesis until the two leaves land.

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
  `corank R(ofNormals G_v ends q|_{E_v}) = def(G̃_v)` at the inductively-fixed seed
  `q` (KT footnote 6). NOT green-buildable (re-confirmed + **sharpened** by the
  footnote-6 kernel recon, 2026-06-06): the motive is existence-only even with the
  22b `IsGeneralPosition`+link-recording strengthening (`IsGeneralPosition` is only
  degree-1 pairwise transversality, not non-root-ness of the rank polynomial `Q`);
  the device *consumer* `isInfinitesimallyRigidOn_ofNormals_of_rankPolynomial_ne_zero`
  DOES run the given-point direction, but needs `eval q Q ≠ 0`, and **the project has
  no `AlgebraicIndependent` machinery** to certify the alg.-indep. seed is a non-root.
  The genuinely-new brick, named exactly: `MvPolynomial.eval_ne_zero_of_algebraicIndependent`
  (mirrorable upstream half) + the seed-alg-indep invariant. Likely **merges with
  Gap 1**. Red node `lem:case-III-gap3-rank` / `lem:case-III-seed-rank-bridge`,
  **to be BUILT DIRECTLY** (2026-06-06 decision — *Kernel-route decision*; not
  carried as a permanent hypothesis); the alg-independence *relaxation* candidate
  (product-route) is tracked in `notes/AlgebraicIndependence.md`. See *Footnote-6
  kernel recon (2026-06-06)*.
- [ ] (deferred) Gap 1 `M(G̃)`↔row bridge; the candidate-completion + Claim-6.12
  disjunction; the `d=3` assembly. Named, unlettered (below).

## Blockers / open questions

- **Gap-3 verdict (Gap-3 recon): Gap 3 SPLITS** — green combinatorial shell
  (`splitOff_removeVertex_minimalKDof`, the leaf) + an **irreducible
  research-shaped kernel** (eq. (6.22) generic-rank transfer). Unlike Gap 2 (whose
  green substrate the opening recon understated), Gap 3's kernel content is
  genuinely absent from green: the IH is existence-only and the device runs the
  opposite direction from KT footnote 6. So the kernel is carried-as-hypothesis (a
  red node), not built — the recommended Phase-21b escalation idiom. See *Gap 3
  recon (2026-06-06)* items 2–3.
- **Footnote-6 kernel verdict (footnote-6 kernel recon, 2026-06-06): eq. (6.22) is
  NOT a re-exposure of green machinery — CONFIRMS + SHARPENS the Gap-3 verdict.**
  The hypothesis that the 22b-strengthened `HasGenericFullRankRealization` motive +
  the device's `_ofNormals` consumer would re-expose eq. (6.22) is **refuted on the
  bottom line** (the motive is still `∃ Q`, existence; `IsGeneralPosition` is only
  pairwise transversality, not non-root-ness of `Q`) but **confirms two of its three
  structural claims**: the matroid↔row link is the IH (`rigidityMatrix_prop11`,
  green-modulo, takes the rank bounds as `hub`/`hgen` hypotheses), and step ③ is pure
  LA given (6.18)+(6.22). The genuinely-new content is now named exactly: a
  `non-root-from-algebraic-independence` brick (the project has **zero**
  `AlgebraicIndependent` machinery). eq. (6.18) is NOT separately in hand — 22c gives
  the `−1` brick, the full rank is the Claim-6.11 `+1`. See *Footnote-6 kernel recon
  (2026-06-06)* Q1–Q5 + Net verdict.
- **Open: do Gap 3's kernel and Gap 1 merge?** The recons' sharpenings say the
  eq. (6.22) generic-rank transfer and the Gap-1 `M(G̃)`↔row bridge share one kernel
  ("the rigidity matrix at the fixed seed `q` attains the rank `M(G̃)` predicts" —
  both bottoming on the `non-root-from-alg-indep` brick). Confirm when the kernel
  sub-phase opens whether to cut them as one node or two; do not pre-commit now.
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

## Kernel-route decision (2026-06-06, user)

The footnote-6 recon (above) named the kernel's content and the recon's own default
was **carry-as-hypothesis**. The user weighed three handlings and **decided: build
the algebraic-independence route DIRECTLY to fully green** — i.e. build the
`non-root-from-algebraic-independence` content ((i) the mirrorable
`MvPolynomial.eval_ne_zero_of_algebraicIndependent` half + (ii) the seed-alg-indep
invariant threaded through the induction), discharging the kernel so Claim 6.11 /
Case III close *for real* — rather than (a) carrying the kernel as a hypothesis to
bank a green-*modulo* milestone first, or (b) gambling on the unverified
product-route shortcut. **Rationale:** of the two paths to fully-green, the
alg-independence route is KT's actual, certain argument; the product-route shortcut
is faster-*if-it-works* but ~70% and could stall — so alg-independence is the fastest
*certain* path to green.

**The relaxation question is live and tracked.** The product-route shortcut — choose
the seed `q` at the Claim-6.11 composition as a non-root of the *finite product* of
the nested IH rank polynomials (+ GP polys), via the existing device producer,
avoiding algebraic independence entirely at `d=3` — is a genuine candidate for
*relaxing* the alg-independence requirement. It is captured in full (the argument,
the ~70% confidence, the residual risks, the general-`d` caveat) — together with a
usage tracker for **every** place the molecular program leans on algebraic
independence — in the standing note **`notes/AlgebraicIndependence.md`**, as a
deferred relaxation TODO for a later phase.

**Effect on the plan:** the immediate next build is UNCHANGED (the Gap-3 leaf
`splitOff_removeVertex_minimalKDof`). After it, the kernel sub-phase builds (i)+(ii)
*directly* (no carry-as-hypothesis intermediate); `lem:case-III` stays red until the
kernel + downstream scaffold land — red because *not-yet-built*, not because carried
as a permanent hypothesis.

## Hand-off / next phase

**This commit is the design-pass-first "size the kernel" recon of KT eq. (6.22) /
footnote 6 (docs-only).** Verdict: eq. (6.22) is **NOT** a modest re-exposure of
green 21b/22b machinery — it needs **genuinely-new analytic content**, now named to
the exact missing lemma: a `non-root-from-algebraic-independence` brick (the seed's
alg.-indep. panel coords ⟹ non-root of the device's rank polynomial `Q` ⟹ the
green device consumer `isInfinitesimallyRigidOn_ofNormals_of_rankPolynomial_ne_zero`
certifies the *given* seed rigid). The project has **zero** `AlgebraicIndependent`
machinery. This **confirms + sharpens** the prior Gap-3 verdict (does not overturn
it). Two of the user's three structural claims confirmed (matroid↔row link = the IH;
step ③ = pure LA); the bottom line refuted; eq. (6.18) is NOT separately in hand
(22c gives the `−1`, Claim 6.11 supplies the `+1`). Full Q1–Q5 reasoning +
signature citations in *Footnote-6 kernel recon (2026-06-06)*. `lem:case-III` /
`lem:case-II-realization` stay red. No Lean, no build, no `\leanok`/`\lean{}`
changes this commit.

**The next concrete commit is UNCHANGED — the Gap-3 leaf
`Graph.splitOff_removeVertex_minimalKDof`** (in `ForestSurgery.lean` next to the
Gap-2 leaf): from the Gap-2 leaf's base `B'` + the green def-count chain
(`subgraph_minimality`, `removeVertex_deficiency_ge`, `rank_add_deficiency_eq`,
`matroidMG_restrict_mulTilde`, `mulTilde_removeVertex_le_splitOff`), prove
`G_v = removeVertex v` is minimal `k'`-dof with `0 ≤ k' ≤ D−2`. Pure `M(G̃)`
matroid theory, no rigidity matrix, **buildable**. New green node
`lem:case-III-gap3-minimalKDof`. (This recon settles the *kernel's* shape; it does
not change the build queue — the combinatorial shell is still leaf-most.)

**After that, the research-shaped kernel** (eq. (6.22) generic-rank transfer) +
**Gap 1** (`M(G̃)`↔row bridge) are the two remaining research-shaped nodes; they
likely **merge into one** "the rigidity matrix at the inductively-fixed seed `q`
attains the rank `M(G̃)` predicts" node, **both bottoming on the
`non-root-from-algebraic-independence` brick** this recon named. Suggested
leaf-most-first cut for that sub-phase: (i) the mirrorable
`MvPolynomial.eval_ne_zero_of_algebraicIndependent` half, (ii) the seed-alg-indep
invariant (interacts with the existence-only motive — may need a *third* motive
form), (iii) the kernel `lem:case-III-seed-rank-bridge` composing them with the
device consumer + `rigidityMatrix_prop11`. **Per the 2026-06-06 decision (*Kernel-route
decision* above), this kernel is BUILT DIRECTLY** — a dedicated math-first sub-phase
builds (i)+(ii) to discharge it to green (NOT carried as a permanent hypothesis); the
product-route shortcut that might *relax* the alg-independence requirement is the
deferred TODO tracked in `notes/AlgebraicIndependence.md`. Do NOT pre-commit the
sub-phase's internal cut now (defer-the-finer-cut, as 22a→22b, 22c→22d).

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
