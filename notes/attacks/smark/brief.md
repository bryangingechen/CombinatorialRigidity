> **Brief — reviewed by the PI 2026-09-15; re-oriented at two `/review-attack` passes (after sessions 2 and 5, 2026-09-15/16): route R2 adopted (`state.md` *Statement*, workbook S14; review notes S15), and the PI decided both kernels take the induction hypothesis on smaller graphs.** Written by an agent from owning sections, driver code, the Lean statements and the KT paper; rewritten only at milestones (`/review-attack`). Its claims are the writer's readings of the sections cited in §8; an attack re-derives what it builds on. **§§2, 3 and 6 rewritten in full 2026-09-16 against the *landed* kernel restatement** (checklist item 5, `notes/Phase39-design.md` § *Kernel restatement (2026-09-16)*: both kernels now take the induction hypothesis ahead of their antecedent; `hK` concludes `HasGenericPencilRealization K 3 G` directly, no chart (`(d)`); `hbareSplit` takes and returns the new motive `HasDistinctPencilRealization`, and `PencilPair` gained it as a third, simple-conditioned conjunct (`(α)`), which deletes the former O8 obligation outright). **This rewrite is drafted by an agent, per the coordinator's task, and is PENDING PI REVIEW** — it is not itself a `/review-attack` pass and does not carry that pass's authority; session 6 waits on that review. §§1, 4, 5, 7, 8 are unchanged from the previous version and still carry their own *[review]*/*[review 2]*/*[formalization 2026-09-15]* marks; the retired *[review 2]* superseding-marks inside §§2, 3 (old Lemma, old antecedent misreading) have been folded into this rewrite rather than kept as strikethrough history — see git history for the blow-by-blow.

# The 2-cut composition step for the trigonal-planar molecular theorem

## 1. Objects

A *pencil configuration* of a finite simple graph `G` is `p : V → P³` (over an algebraically closed field `K`; *[formalization 2026-09-15]* no characteristic is used, §3), adjacent points distinct, each closed neighbourhood `N[v]` coplanar in a plane `π_v` (unique at a *hub*, `deg v ≥ 3`); hinge line `p_u p_v` per edge — the molecular framework with trigonal-planar atoms (dually, Katoh–Tanigawa's panel-hinge stratum with concurrent hinges). Rank `≤ target(G) := 6(|V|−1) − def₃(G)`, `def₃ = max_P [6(|P|−1) − 5d(P)]` over vertex partitions (Lean `deficiency G 3`). `G` *attains* if some configuration reaches the target; rank is lower semicontinuous, so one witness suffices and "generic point of a component" is the right quantifier.

A 2-separation `{u,v}` of 2-connected `G` has sides `H₁, H₂` (union `G`, meeting in `{u,v}`, edge-disjoint, each with an interior vertex). Per side: `f_i := def₃(H_i)`, `g_i := def₃(H_i/uv)` (partitions with `u,v` together), `δ_i := f_i − g_i ∈ [0,6]`. At a configuration: `M_i` the side's motion space; `a_i := dim M_i − 6 − f_i ≥ 0` its attainment loss; `ρ̄_i := {m(v) − m(u) : m ∈ M_i} ⊆ Λ²K⁴ ≅ K⁶`, the relative screws of `v` against `u` inside side `i`; `ρ_i := dim ρ̄_i`. Shared flag data `ϕ = (p_u, π_u, p_v, π_v)`, `p_u ∈ π_u`, `p_v ∈ π_v`; `Y°(H_i; ϕ)` is side `i`'s configuration variety at those flags.

## 2. The statement to prove

*[rewritten 2026-09-16, against the landed kernels]* The Lean composes only across the hub cut of a degree-2 chain, through `hK`/`hbareSplit` (`Escape.lean`, quoted in full in §3), each now carrying the induction hypothesis. Informally (`state.md` *Statement*; workbook S14):

`G = H′ ∪ ear_m` at the hub 2-cut `{w, v}` (`m ≥ 2`, the trichotomy's case (iii), §3.5 below); `G₋ := H′ ∪ ear_{m−1} = G.splitOff x a b e₀` for any interior chain vertex `x` (`Operations.lean:770`: delete `x`, join its neighbours). **If `H′` attains** (supplied by the induction hypothesis, since `|V(H′)| < |V(G)|`) **and `G₋` attains** (the kernels' own antecedent, at some configuration over `K̄`), **then `G` attains** — at the generic motive on `hK`'s (nondegenerate-feasible) arm, at the adjacent-distinct motive on `hbareSplit`'s (infeasible) arm. This needs `H′`'s configuration space irreducible (S13(iv), S14(vii)) so that the IH's single witness and the antecedent's single witness compose into a fact at the generic point — the residue, §6.

**Why the induction hypothesis is there (S14(v)).** Without it, the kernels' own antecedent alone allows a deficiency profile `δ′ + a′ ≤ 6 − m` on a side `H′` that has **not itself been shown to attain** (`a′ ≥ 1` means `H′` fails), while `G` attaining needs `a′ = 0` or `δ′ + a′ ≤ 5 − m`. In the gap cell `δ′ + a′ = 6 − m`, `a′ ≥ 1`: `G₋` attains (by the antecedent) and `G` fails at *every* configuration — so the bare implication, without the IH, is **false** there; proving it as first pinned would have required proving the pencil conjecture for `H′ = G − chain` *inside* the kernel. Pointwise witness: `specialcfg.py` family (i) on `K4−e` (`a′ = 1`): `H′ ∪ ear₁` attains, `H′ ∪ ear₂` does not (`splitoff.py --special`). The PI added the IH to both kernels 2026-09-16 on this finding (checklist item 5).

This replaces the brief's original two-general-sides Lemma (kept below only as retired history, §3.5): the Lean's own induction never composes across an arbitrary 2-separation, only the hub cut of a degree-2 chain.

Field: no characteristic; the informal argument runs over `K̄` and descends to `K`-points (O9, §6). *[formalization 2026-09-15]* The Lean statement is over any infinite field and stays so (PI, option C, checklist item 3); this route's genuine field item is exactly that descent, not a characteristic restriction.

## 3. Why it suffices

### 3.1 The consumer, quoted verbatim

`pencilPair_of_splitOff_of_habitat` (`Escape.lean`) carries both kernels as explicit hypotheses; this is their **current, landed** form (checklist item 5, 2026-09-16) — never the pinned blocks superseded by that restatement.

```lean
-- Escape.lean:360–366
(hK : ∀ (G : Graph α β) (v a b : α) (eₐ e_b e₀ : β),
  G.Simple →
  5 ≤ V(G).ncard →
  G.TwoEdgeConnected →
  (∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G 3) →
  G.degree v = 2 →
  eₐ ≠ e_b →
  G.IsLink eₐ v a →
  G.IsLink e_b v b →
  (¬ G.PencilHub a ∨ ¬ G.PencilHub b) →
  e₀ ∉ E(G) →
  (∀ G' : Graph α β, V(G').Nonempty → V(G').ncard < V(G).ncard → PencilPair K 3 G') →
  HasGenericPencilRealization K 3 (G.splitOff v a b e₀) →
  HasGenericPencilRealization K 3 G)
```

```lean
-- Escape.lean:367–374
(hbareSplit : ∀ (G : Graph α β) (v a b : α) (eₐ e_b e₀ : β),
  G.Simple →
  5 ≤ V(G).ncard →
  G.TwoEdgeConnected →
  (∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G 3) →
  G.degree v = 2 →
  eₐ ≠ e_b →
  G.IsLink eₐ v a →
  G.IsLink e_b v b →
  (¬ G.PencilHub a ∨ ¬ G.PencilHub b) →
  e₀ ∉ E(G) →
  ¬ PencilNondegFeasible K G →
  (∀ G' : Graph α β, V(G').Nonempty → V(G').ncard < V(G).ncard → PencilPair K 3 G') →
  HasDistinctPencilRealization K 3 (G.splitOff v a b e₀) →
  HasDistinctPencilRealization K 3 G)
```

Both are hypotheses of `pencilPair_of_splitOff_of_habitat`, whose own `hIH : ∀ G', V(G').Nonempty → V(G').ncard < V(G).ncard → PencilPair K 3 G'` is what feeds each kernel's second-to-last line.

### 3.2 Operators, glossed from their definition bodies (never from a docstring)

- **`Graph.splitOff G v a b e₀`** (`Induction/Operations.lean:770`): `vertexSet := V(G) \ {v}`; `IsLink e x y := (e ≠ e₀ ∧ G.IsLink e x y ∧ x ≠ v ∧ y ≠ v) ∨ (e = e₀ ∧ a ≠ v ∧ b ≠ v ∧ a ∈ V(G) ∧ b ∈ V(G) ∧ ((x=a∧y=b) ∨ (x=b∧y=a)))`. In prose: delete `v`, keep every old link avoiding `v`, and add one new edge `e₀` joining `a` and `b`. This construction *is* the brief's own `G₋ := H′ ∪ ear_{m−1}` (§1, §2) — the second disjunct is exactly the re-added edge that shortens the ear from length `m` to `m−1`. It is **not** "`G − v`" (no re-added edge) and **not** "a realization of `G − chain`" (the antecedent is `G₋`'s own realization, not `H′`'s). Both of those readings were this brief's two prior mis-paraphrases (logged 2026-09-16), both traceable to not reading this body.
- **`Graph.PencilHub G v`** (`Motive.lean:74`): `v ∈ V(G) ∧ 3 ≤ G.degree v`. Exactly "hub = degree ≥ 3" (§1).
- **`PencilNondegFeasible K G`** (`Motive.lean:134`): `∃ F normal point, IsNondegPencilRealization G F normal point`. `IsNondegPencilRealization` (`Motive.lean:111–116`) is four conjuncts — a pencil panel realization; adjacent concurrency points projectively distinct; closed-hub-neighbourhood normals linearly independent; closed-neighbourhood points linearly independent at every non-hub — with **no rank requirement**. So `PencilNondegFeasible` asserts only that *some* configuration meets every nondegeneracy constraint, not that it attains the target rank; `hbareSplit`'s domain is exactly its negation.
- **`HasDistinctPencilRealization K n G`** (`Statement.lean:129`): `∃ F normal point, HasPencilPanelRealization G F normal point ∧ (∀ e u v, G.IsLink e u v → LinearIndependent K ![point u, point v]) ∧ rank = target`. A panel realization at the target rank with adjacent concurrency points forced projectively distinct — nothing else from `IsNondegPencilRealization`'s four conjuncts. This is what `hbareSplit` now takes as its antecedent and returns as its conclusion (both changed from the bare motive `HasPencilRealization` in the 2026-09-16 restatement).
- **`HasGenericPencilRealization K n G`** (`Motive.lean:141`): `∃ F normal point, IsNondegPencilRealization G F normal point ∧ rank = target` — the full nondegeneracy stack plus the rank target. This is what `hK` now concludes directly, with no chart-form intermediate (`(d)` below).

### 3.3 The item-4 recon's answers (a)–(d) (`notes/Phase39-design.md` § *R2 recon*, § *Material for the S-mark brief's §3*)

1. **Rank bridge (a) — CONFIRMED identical, on the adjacent-distinct locus.** Lean `HasPencilRealization K 3 G` = some `Y(G)`-point attaining `6(|V|−1) − def₃(G)`: five rows per hinge (`hingeRowBlock`, the annihilator of the hinge screw), `screwDim 2 = 6 = bodyBarDim 3`, `deficiency 3 = def₃` via `6(|P|−1) − 5d(P)`, and the hinge is forced onto `p_u ∧ p_v` at distinct points — all compiled (spike A/C, same design-doc section). Over any infinite `K`; the `K̄`-to-`K` descent is O9 (§6).
2. **The bare motive's slack (b), settled (α).** The bare motive `HasPencilRealization` carries no distinctness conjunct; at coincident adjacent points sharing a panel, the hinge is free over the whole pencil, and every parallel class attains *only* that way (the landed base-arm witness; compiled cap `≤ 5` at distinct points). As pinned before item 5, `hbareSplit`'s antecedent would have certified a point of the Lean bare space, not of the attack's configuration variety `Y(G₋)`. **Settled by the user's (α) decision:** `PencilPair` gained the third conjunct `HasDistinctPencilRealization`, and `hbareSplit` now takes and returns it directly, so its antecedent *is* a `Y(G₋)`-point by construction. There is no coincident-stratum obligation left (§6 carries no O8).
3. **Feasibility on the side (c) — YES, by reconstruction, not restriction.** In the triangle-free habitat, `PencilNondegFeasible` is exactly `∀ w, |closedHubNbhd w| ≤ 3` (both directions landed: `⇒` `ncard_closedHubNbhd_le_three_of_isNondegPencilRealization`, `Motive.lean:437`; `⇐` `pencilNondegFeasible_of_ncard_closedHubNbhd_le_three_of_triangleFree`, `Steer.lean:1344`), and it — together with `G.Simple` — passes to every subgraph, hence to `H′ = G − chain` and to `G.splitOff …`, by *reconstructing* a fresh witness (`pencilNondegFeasible_of_le_of_triangleFree`, `Steer.lean:1386`), not by restricting the parent's. Restriction is gapped exactly at the chain ends, whose degree drops to `2` (`PencilNondegFeasible.mono`'s genuinely-gapped case, `Motive.lean:300`). So on `hK`'s arm the IH hands the route a nondegenerate `Y`-point for `H′`, meeting S14(vii)'s tower-nondegeneracy inputs.
4. **Weakening `hK`'s conclusion (d) — CONFIRMED "uses nothing else", adopted.** The old call site consumed nothing of `hK`'s chart-form conclusion beyond converting it to `HasGenericPencilRealization K 3 G`; `hK` now concludes the generic motive directly — strictly easier to prove, and already what the blueprint states (`pencil.tex:843–845`).

### 3.4 Hypotheses the route does not use

- **`eₐ ≠ e_b`** — label bookkeeping for `splitOff`'s well-formedness (distinct edge labels at `v`), not a fact any block inequality of the route needs.
- **`e₀ ∉ E(G)`** — likewise: freshness of the new edge label, needed only so `splitOff` is well-defined, not by the route's arithmetic.

Every other named hypothesis is consumed: `G.Simple` (rank bridge (a) and feasibility reconstruction (c)); `5 ≤ V(G).ncard`, `G.TwoEdgeConnected`, the no-proper-rigid-subgraph habitat, `G.degree v = 2` set up the trichotomy (§3.5) identifying `G = H′ ∪ ear_m`; `G.IsLink eₐ v a`/`G.IsLink e_b v b` identify `a, b` as `v`'s two neighbours; `(¬ PencilHub a ∨ ¬ PencilHub b)` forces the chain's existence (§3.5); the IH supplies `H′`'s attainment (S14(v), §2); the antecedent supplies `G₋`'s (S14(i)–(iii)); `¬ PencilNondegFeasible K G` (`hbareSplit` only) is the domain where O7 lives (§6).

### 3.5 Consumed shape

By the disjunct, `x` and a neighbour are adjacent degree-2 vertices, so `x` lies on a maximal degree-2 chain of `m ≥ 2` interior vertices whose ends are hubs — a **trichotomy** (blueprint `lem:pencil-degree-two-chain`): (i) `G` is a cycle (base case (b)); (ii) the chain closes at a **single** hub `w`, a cycle of length `m + 1 ≥ 7` through a cut vertex — owned by the cut-vertex case of the induction, not by these kernels; (iii) two distinct hubs `w ≠ v`: `G = H′ ∪ ear_m` at the hub 2-cut `{w, v}`, `H′ = G − chain` connected with side-degree `≥ 2` at both ends (`lem:pencil-chain-side-connected`), and every `w`–`v` path in `H′` has `≥ 6 − m` edges (`lem:pencil-chain-side-distance`), so `w ≁ v` only for `m ≤ 4`. The one-vertex ear between two hubs (workbook S9) is not consumed. The chain length stratifies the obligation (workbook S10): `m ≥ 4` needs nothing of `H′` beyond attainment and welded attainment at `(w, v)` (both now supplied by the IH plus the antecedent, S14(i)); `m = 3` needs only `ρ̄′ ∉ {Π_w, Π_v}` at `δ′ = 2` plus exception bookkeeping; `m = 2` is the core. This stratification is discharged from the antecedent at every `m` (S14(iii)) — no profile bound on `H′` is used anywhere.

"Every connected `G` attains" reduces to this by induction on `|V|`: (a) 3-connected ⇒ `def₂ = def₃ = 0` [proved] and the all-coplanar configuration has rank `6(|V|−1) − def₂` [Jackson–Jordán's pin-collinear theorem via duality; published, unformalized]; (b) paths, cycles [elementary; measured]; (c) `def₂ = def₃` [same witness]; (d) cut vertex: additive deficiency, `PGL₄` transitive on flags [proved]; (e) the composed step above. **Frame gap — closed under R2** (review 2, 2026-09-16): the Lean composes only across the hub cut of a degree-2 chain, where the split-off antecedent supplies welded attainment (S14(i)); no 3-block skeleton is consumed, so the frame-gap concern of the brief's original §3 (a "core clause" for a 3-block with `≥ 2` children) does not arise.

**Retired, kept for the record only:** the brief's original two-general-sides Lemma (`for i = 1,2` and every `ϕ`, some component with `ρ_i = δ_i + a_i` ⟹ `G` attains) — superseded by §2 above, since the Lean's own induction never composes across an arbitrary 2-separation; the 3-block/core-clause skeleton (not consumed by the Lean's induction); the classical/certificate route (Tay-style packing, retired under R2); (O4″)/O5/O6 and the census/SPQR program (retired as not consumed — `state.md` *Tried on this route*).

## 4. What is known

Proved (checked): both sides rigid *and attaining* ⇒ automatic; one side rigid and attaining ⇒ only welded attainment of the other side is needed; without "attaining" both fail (44 configurations with `ρ₂ ∈ {1,2}` on a rigid side). `ρ̄_i` lies in the span of any u–v path's hinge lines, so `ρ_i ≤ dist_i`; `δ_i ≤ dist_i`; `δ_xy = 0` when `x,y` share a cycle of length `≤ 6`. Generic flags form one `PGL₄`-orbit.

*[review]* Attack results, sessions 1–2 (workbook `notes/pencil/workbook/attack-smark.md`, proven-informally; S2, S6–S9 read at review): **S2–S3** the block inequalities with slack `max(0, ρ₁+ρ₂−6)`, plus avoidance of four isotropy exceptions (X1)–(X4), give `dim(A + gB) = min(6, ρ₁+ρ₂)` for generic `g` in the 5-dimensional flag stabiliser — the `⟸` of the corpus's 400/400 law; **S4** the block list alone is insufficient (Klein parity: two stars always meet); **S6** the side-degree-1 reduction, where welded attainment needs `L_{uw} ∉ ρ̄_{wv}(H − u)`; **S7** excess at a block `U` is the attainment loss of `H ∪ bars(U^⊥)`, and one exact witness certifies attainment, welded attainment and upper bounds on all sixteen `c(U)` for every component through it; **S8** hub-free sides have irreducible fibres, so the ear and theta profiles are theorems; **S9** the one-vertex-ear criterion in closed form (a theorem about a shape the consumer does not take, §3). *[review 2]* Sessions 3–5 (S12–S14): S13(ii) composition of `ρ̄` at the cut and S13(iv) irreducibility of the fibre for pairwise non-adjacent hubs, both now load-bearing for R2; S14 the theorem `ear_{m−1} ⟹ ear_m` from the antecedent. **S9 is revived:** at `m = 2` the antecedent graph is `H′ ∪ ear₁`, so S9's criterion states in closed form what the antecedent says about `H′`.

Ear side (a path, `m` interior vertices, side-degree 1 at both terminals): `ρ̄₂` is the span of its `m+1` lines; the maximum of `dim(ρ̄₁+ρ̄₂)` over the ear's moduli is claimed proved for `m ≥ 3` with an explicit loss (pencil-meets-subspace lemma plus sliding; read, unverified); loss `≤ max(0,Σδ−6)` when `ρ̄₁` meets each terminal pencil in `≤ 1` dimension plus one condition on their sum — true if side 1 is a path or has a short generic u–v path. Side-degree `≥ 2`: 16 necessary block inequalities hold at 1 281/1 281 draws on a 427-row side library; the residue is one rank condition (no terminal-pencil line Klein-orthogonal to `ρ̄_i`) at one profile; a saturation clause fails at side-degree 1.

Sweeps (an attaining draw is a theorem for its graph): connected `n ≤ 6`, max degree `≤ 4`, 2-cut, both `δ_i > 0`: 11 896/11 896; 1 588 sampled at `n = 7–9`; 5 824 graphs of hub load `≤ 3`; all 216 habitat members with `≤ 6` hubs; forced-coincident-flag peels (girth 3, `n = 11–13`): 392/392, 81/81. Kill-condition hunt: 486 forced peels at `Σδ ≥ 4` (`n₁ ≤ 12`, `n₂ ≤ 5`), none path-confined on both sides; confinement is claimed to force `δ_i ≤ 3`, leaving six cells: 6 444 peels, 0 forced.

## 5. What has failed

- Placing `v` into a given realization of `G − v` (the Lean antecedent's shape): an exact gadget where every placement fails; hence the bypass. *[review 2]* The conclusion is retracted: the antecedent's shape is the split-off graph, not `G − v`; pointwise placement fails at the special configurations of the `a′` gap (S14(v)), and read at the generic point the antecedent certifies `G` (S14(iii)–(iv)).
- Additive law `f₁+f₂−6`: goes negative.
- Rigid-side shortcuts without "attaining": false; the one-sided discharge built on them is void.
- General position from the gauge group: orbit 5/7 versus Grassmannian 9; but side moduli (4–26) dwarf both, so the pessimism was also wrong.
- Constructor misses read as shortfalls (56 ears: flattened free vertices).
- "Cross-cut forcing needs `(1,1)`" and "forcing impossible with both sides flexible": witnesses at `n = 12`, `11`; prior zeros vacuous.
- Irreducibility upgrades: unavailable at girth 3, i.e. at every forced-flag family.
- Dimension count for `Y° ⊄ Z(G)`: compatible at every graph with a hub.
- Forced-flat + `def₂ > def₃`: empty to `n = 6`; needs a triangle or `K_{2,3}`.

## 6. Live obligations

*[rewritten 2026-09-16]* Two obligations remain open, both bookkeeping of S14(iv)/(v) rather than a rigidity statement — **not** a rigidity fact in either case. **O8 is DELETED** by the (α) decision (§3.3): `hbareSplit`'s antecedent and conclusion are now typed `HasDistinctPencilRealization` (§3.2), so every witness it produces or consumes already has adjacent points projectively distinct — there is no coincident-stratum obligation to discharge, weakly or otherwise. Work **O7 first**, then O9.

**O7 — irreducibility of `Y(H′)`, or component matching.** The only structural residue, and only on `hbareSplit`'s arm (`hK`'s domain — hub graphs of max degree `≤ 2` — is already covered). *Consumed because:* `hbareSplit` fires exactly where `¬ PencilNondegFeasible K G` (`Escape.lean:371`), and by the exact criterion (c) that is where some vertex has `≥ 4` closed hub-neighbours — the case where `H′` can have a hub `z` with three hub-neighbours `z₁, z₂, z₃`, each continued to `w` or `v`. There the tower's 2-degenerate hub order (S13(iv)'s irreducibility input) need not exist, so promoting the IH's pointwise witness for `H′` and the antecedent's pointwise witness for `G₋` into a single generic-point argument (S14(iv)) is open. No driver population has sampled this arm: every census branch built so far has length `≥ 2` on all sides but not this exact three-hub-neighbour shape (item-4 recon, same finding).

*First move (this attack's next concrete step):* build an adjacent-hub side directly — a hub with three hub neighbours, each continued by a branch of length `≥ 2` to `w` or `v`, girth `≥ 7` — and sample it from several starts, *before* attempting either the tower extension (does the habitat's no-proper-rigid-subgraph condition force `H′`'s hub graph 2-degenerate?) or component matching (does the IH's witness-component for `H′` coincide with the one the antecedent certifies for `G₋`, or can S14(iii) be run on each component separately with both hypotheses?).

**O9 — descent** (write second). *Consumed because:* both kernels' field hypothesis is `[Infinite K]` (option C, checklist item 3), not `IsAlgClosed K` — the Lean statement is an `∃`-witness over the *given* field `K`, so the informal argument's `K̄`-generic-point reasoning must descend to an actual `K`-point before it discharges either conclusion. Write the descent paragraph in witness form (S7(vi), S11(v)): the attaining locus is dense open in a `K`-rational tower, and `K` infinite gives a `K`-point.

## 7. What a counterexample would look like

Universal statement: 2-connected, girth 3/4, a 2-separation with `u ≁ v`, the closure forcing `π_u = π_v` and a u–v path of *each* side into that plane, `δ₁+δ₂ ≥ 4`, each `δ_i ≤ 3`: then `dim(ρ̄₁+ρ̄₂) ≤ 3 < target` on the guarded locus. Needs hubs along long u–v geodesics; outside the habitat, so it kills the route only. Lean hypothesis: girth `≥ 7`, 2-edge-connected, no proper rigid subgraph, a degree-2 vertex, a closed hub neighbourhood with `≥ 4` hubs, every placement rank-deficient — no triangle-free cap mechanism is known. Lemma alone: a side whose `ρ̄_i` at generic flags always contains a line Klein-orthogonal to a terminal pencil.

## 8. Pointers

- Lean: `Escape.lean:467/555`; `Statement.lean:103`; `Motive.lean:73,133,160`; `Deficiency.lean:273,483`; *[review]* `Habitat.lean:94` (the `hsafe` disjunct in use), `ReducibleVertex.lean:1206` (`exists_adjacent_degree_two_pair_of_noRigid_of_deficiency_pos`); the blueprint node `thm:pencil-conditional-realization-pair` (`pencil.tex`) states the disjunct in prose.
- *[review 2]* The consumer, both sides of the implication: `Escape.lean` `pencilPair_of_splitOff_of_habitat` (the `hK`/`hbareSplit` statements and their sole call site, `hIH` in scope) and `pencil_conjecture_of_hcontract_hK_hbareSplit`; `Operations.lean:770` `splitOff`; `Motive.lean` `IsNondegPencilRealization` (the strata a bare witness may occupy). Workbook S12–S15; the Lean round's questions `notes/Phase39.md` checklist item 4.
- *[review]* Attack workbook `notes/pencil/workbook/attack-smark.md` S1–S10 (S10 = review notes: the S2 base-locus sentence, the §2 identities re-derived, the chain-length arithmetic); drivers and caps `notes/attacks/smark/drivers/README.md`.
- *[formalization 2026-09-15]* Blueprint nodes (red today; statements pinned and compiler-checked in `notes/Phase39-design.md` § *Lean-track design pass*): `def:girth`, `lem:pencil-short-cycle-spanning`, `lem:pencil-girth-of-hub`, `lem:pencil-closed-nbhd-girth-five`, `lem:pencil-degree-two-chain`, `lem:pencil-chain-side-connected`, `lem:pencil-chain-side-distance`; field: § *Field-hypothesis recon* (i′), `fmlnote:pencil-conditional-realization-pair-field`; workbook S11.
- §2: (BE-21)(ii), (BE-22) `BINDUC.md`; (BE-86)(i) `BGENUINE.md`; (BE-314)–(BE-315) `BSMARK.md`; (BE-25)(ii) `BTWOCUT.md`; `binduc.py rank2`, `bsmark.py cancel|rigid`.
- §3: (BE-14) `BATTAIN.md`; (BE-16)(iii), (BE-18) `BZAVOID.md`; (BE-20), (BE-23) `BINDUC.md`; (BE-25)(iii), (BE-28) `BTWOCUT.md`; (BE-120)(iv) in (BE-86)(ii); (BE-5) `K-bare-ext.md`.
- §4: (BE-30) `BIMAGE.md`; (BE-35)–(BE-38) `BEARCASE.md`; (BE-40) `BEARFULL.md`; (BE-326)–(BE-333) `BSIGFOUR.md`; (BE-299) `BGPLAW.md`; (BE-337) `BNEST.md`; (BE-104) `BSATUR.md`; (BE-95) `BUNIF.md`; (BE-29) `btwocut.py hunt`; `binduc.py hubplane`; `bgenuine.py bite`; `bsigfour.py widen`.
- §5: (BE-77)(ii)→(BE-324); (BE-79)–(BE-81) `BONEONE.md`; (BE-312) `BCOFLAG.md`; (BE-16)(iv); (BE-23)(ii); (BE-42) `BEARFULL.md`; (BE-334) `BNEST.md`.
