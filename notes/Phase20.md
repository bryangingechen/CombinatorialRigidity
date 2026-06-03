# Phase 20 — Combinatorial induction → Theorem 4.9 (work log)

**Status:** in progress.

This phase is stratum 4 of the molecular-conjecture program (KT §3
Lemmas 3.4/3.5 full forms, §4). The program-level plan, reuse map,
citations, and risk register live in `notes/MolecularConjecture.md`
*Phase 20*; read that first. This file carries Phase-20-local state,
the lemma checklist, decisions, and hand-off. The forward-mode
dep-graph / lemma index is the new blueprint chapter
`blueprint/src/chapter/molecular-induction.tex`
(`sec:molecular-induction`); its red nodes are the live to-do list.

> **PIVOT (2026-06-02).** Phase 20 changed route mid-stream. While
> formalizing the forest surgery (`lem:forest-surgery-split`, KT 4.1)
> we found KT's Lemma 4.1 is **over-quantified (formally disprovable)
> and its proof glosses an unjustified balanced-packing assumption**
> (see *Finding* below). We **route around it** via a deficiency-count
> argument on green infrastructure (see *Replan* below). The
> forest-surgery substrate already landed is now **off the Theorem-4.9
> critical path** and serves a deferred TODO. A fresh
> `/coordinate-phase 20` session should read *Finding* + *Replan* +
> *Hand-off* and start at **Replan commit A**.

## Finding: KT Lemma 4.1 / 5.1 is over-quantified, and its proof glosses a balanced-packing assumption (2026-06-02)

The molecular conjecture and KT's overall proof are **not** in question —
this finding is narrow and three-layered, and the value is in stating
*exactly* which layer is which. Sources verified directly: KT 2011
(*A proof of the molecular conjecture*, DCG **45**:647–700) **Lemma 4.1,
p.660**; the KT 2009 arXiv predecessor **Lemma 5.1, p.11** (essentially
verbatim, and makes the gloss *more* visible).

1. **Statement-as-quantified — false, formally disprovable.** Both
   versions read "*for any independent set `I` of `M(G̃)`* … there exists
   `I'` … with `|I'| = |I| − D`." For any independent `I` with `|I| < D`
   (e.g. `I = ∅`) this demands `|I'| = |I| − D < 0` — impossible. The
   intended quantifier is clearly over **bases**. We formalize the literal
   disproof (`I = ∅`, ℕ-cardinality: no `I'` with `|I'| + D = 0` since
   `D = bodyBarDim n ≥ 1`) as a one-line Lean `example`, framed as "the
   universal quantifier must be restricted."
2. **Proof of the intended (base) case — unjustified step.** "Convert each
   `Fᵢ` to `F'ᵢ` with `|F'ᵢ| = |Fᵢ| − 1` *for each i*" (2011), and the
   equation `2h' + (D − h') = h` (2009), silently assume the chosen
   `D`-forest packing is **balanced at `v`**: every forest uses ≥ 1 edge at
   `v` (no `dᵢ = 0`). Neither version justifies this. For a general
   independent `I` it can fail (pigeonhole when `h < D`), and when it does
   *both* conclusions break: cardinality becomes `|I'| = |I| − D + z`
   (`z` = #`v`-avoiding forests), and the slack clause `|ãb ∩ I'| < D − 1`
   can hit equality (take `h = 2(D−1)`, `z = 1` ⟹ `h' = D−1`). Whether the
   balanced packing is *achievable for a base* we leave **open** — KT omits
   a justification; we did not recover one. (Phrase as "KT omits / we did
   not recover", **not** "KT errs".)
3. **Intended content — true, established directly.** What the induction
   (KT 4.3) consumes is the deficiency inequality `def(G̃ᵥᵃᵇ) ≤ def(G̃)`.
   This is correct; we prove it by a partition-count comparison through the
   green `def = corank` bridge (`rank_add_deficiency_eq`), bypassing the
   forest surgery — see *Replan*.

## Replan (2026-06-02): route splitting-off via deficiency-counting

The viable route is a direct comparison of the deficiency max-formula,
entirely green infrastructure:

```
def(G̃) = max_P [ D(|P|−1) − (D−1)·d_G(P) ]   -- partitionDef / deficiency (Deficiency.lean)
rank M(G̃) + def(G̃) = D(|V|−1)                 -- rank_add_deficiency_eq (green)
```

**Correction (do not repeat the earlier misfire):** the route is **NOT
matroid contraction**. `Gᵥᵃᵇ ≅ G/va` does *not* give a clean
single-element matroid minor of `M(G̃)` — the count matroid's rank drops
by `D` per removed vertex, not 1. The route is the **partition-count
comparison**:

- `def(G̃ᵥᵃᵇ) ≤ def(G̃)` (KT 4.3(i)): take an optimal partition `P'` of
  `V−v`, extend by dropping `v` into `a`'s block. Then `|P| = |P'|`, and
  since `va` no longer crosses while `vb` crosses iff `ab` crosses `P'`,
  the crossing count is identical: `d_G(P) = d_{Gᵥᵃᵇ}(P')`, so
  `partitionDef_G(P) = partitionDef_{Gᵥᵃᵇ}(P')` and `def(G̃) ≥ def(G̃ᵥᵃᵇ)`.
  ~10 lines of partition arithmetic, no forests. **Confidence: high**
  (worked on paper). The `k`-vs-`(k−1)` refinement (4.3(ii)) and the
  removal `Gᵥ` case (4.4) are confirmed by the first implementation
  commit acting as a de-facto spike (commit B going green = route
  confirmed).

### Writeup principle (the headline — handle carefully)

The blueprint Remark and all prose MUST follow the three-layer framing of
*Finding*: (1) affirm KT's result + stature; (2) distinguish
*statement-as-quantified false* (formalized counterexample) /
*proof-of-base-case glosses balanced packing* (unjustified, open) /
*intended content true* (we prove it); (3) "KT omits / we did not recover",
never "KT errs". Cite KT 2011 Lemma 4.1 p.660 + KT 2009 Lemma 5.1 p.11.
This is genuinely interesting (formalization surfacing a refereed-proof gap
and a cleaner route) — explain it clearly in both the blueprint and the Lean.

### Commit sequence for the next /coordinate-phase session

- **A — Pivot commit (finding + node restate + counterexample).**
  *Blueprint:* new discussion subsection "On Katoh–Tanigawa Lemma 4.1"
  (three-layer); restate the dof-tracking dep-graph — add red nodes
  `lem:splitoff-deficiency` (`def(G̃ᵥᵃᵇ) ≤ def(G̃)` + refinement) and
  `lem:removal-deficiency` (KT 4.4); re-point `lem:dof-tracking`'s `\uses`
  to these; mark `lem:forest-surgery-split` / `-unsplit` **deferred / off
  critical path** (kept red, annotated → deficiency route + TODO).
  *Lean:* the `example` formally disproving the literal quantification
  (clearly commented as targeting the over-quantification). *Notes:* this
  Finding + Replan already record the rationale. Run `checkdecls` (new
  blueprint pointers + the `example`'s `\lean{}` if any).
- **B —** `lem:splitoff-deficiency` `≤` direction (`def(G̃ᵥᵃᵇ) ≤ def(G̃)`)
  via the partition extension above. The de-facto route-confirmation spike.
- **C —** the `k`-vs-`(k−1)` refinement (KT 4.3(ii)).
- **D —** `lem:removal-deficiency` (`Gᵥ`, KT 4.4). **REVISED (2026-06-03,
  *Finding 2*):** not a clean deficiency-count corollary — gated on the
  `h'=0` unsplit forest surgery (`lem:forest-surgery-unsplit`). D now means
  "formalize the `h'=0` lift, then the `≥ k` corollary."
- **E —** `lem:dof-tracking` (assemble KT 4.3–4.5; `\uses` the two new nodes).
- **F —** `lem:reducible-vertex` (KT 4.6).
- **G —** `lem:reduction-step` (KT 4.7–4.8).
- **H —** `thm:minimal-kdof-reduction` (Theorem 4.9) → phase close.

### TODO (parallel, non-blocking — Step 5)

Recover KT's surgery by **proving-or-refuting the balanced-packing lemma**:
"a base of `M(G̃)` admits a `D`-forest partition with every forest meeting
the degree-2 vertex `v`." If true, KT's proof is rescued (gap, not error)
and `lem:forest-surgery-split` completes from the substrate already landed
(framing / incidence / degree / both no-reroute directions / reroute count
cap — see *Current state*); if false, KT's surgery proof is genuinely broken
though the base-form lemma still holds via the deficiency route. Optionally
formalize a concrete `dᶠ(v)=0` witness as a sharper counterexample to the
*proof step* (distinct from the over-quantification disproof). The 6
substrate lemmas are **retained** for this track.

## Finding 2: KT Lemma 4.4's lower bound is not a deficiency-counting fact (2026-06-03)

The Replan's commit-D claim — that `lem:removal-deficiency` (KT 4.4,
`def(G̃ᵥ) ≥ k`) would fall to the same deficiency-counting route as the
splitting-off bound — is **wrong**. The obstruction is structural, and worth
recording because it sharpens the boundary of where the deficiency route
reaches. Verified against KT 2011 Lemma 4.4 (p.661) directly.

Via the green `def = corank` bridge (`rank_add_deficiency_eq`), with `Gᵥ`
dropping `D` from the ambient `D(|V|−1)`:
`def(G̃ᵥ) − k = (rank M(G̃) − rank M(G̃ᵥ)) − D`. So `def(G̃ᵥ) ≥ k` is
**equivalent** to `rank M(G̃) − rank M(G̃ᵥ) ≥ D`. But:
- `M(G̃ᵥ) = M(G̃) ↾ E(G̃ᵥ)` (green `matroidMG_restrict_mulTilde`, since
  `Gᵥ ≤ G`), and the deleted ground elements are exactly the two `v`-fibers
  `ẽₐ ∪ ẽ_b`, size `2(D−1)`. Restriction rank-monotonicity gives only the
  *reverse* bound `rank M(G̃) − rank M(G̃ᵥ) ≤ 2(D−1)` — an **upper** bound on
  `def(G̃ᵥ)`, not the lower bound we want.
- A single-partition comparison (the B/C engine): restrict an optimal
  partition of `V` to `V∖{v}`; `numParts` drops by ≤1 (costs `D`), `d` drops
  by ≤2 (helps, but in the wrong direction for a *lower* bound on
  `partitionDef`). Net: `def(G̃ᵥ) ≥ k − D`. Degree-2 does not rescue it —
  the `−D` is from the lost part, not the edges.

So the needed `≥ D` rank-increment is a forest-packing existence statement.
This is exactly what KT proves via Lemma 4.2(i) at `h'=0`: a base `B'` of
`M(G̃ᵥ)` = `D` forests on `V∖{v}` lifts to `D` forests on `V` by adding one
fresh `v`-edge per forest (`v` isolated ⟹ no added edge closes a cycle),
giving an independent set of `M(G̃)` of size `|B'| + D`. **This `h'=0`
extension does NOT use the balanced-packing assumption** the KT 4.1 *Finding*
flagged: that gloss is in the splitting-**off** direction (`-split`), not the
edge-**splitting** inverse (`-unsplit`). KT 4.4 is sound; it is gated on the
*unsplit* forest-packing lift, which is itself sound but unformalized.

**Consequence for the Replan commit sequence.** Commit D is no longer a quick
proof — it requires first formalizing `lem:forest-surgery-unsplit` (at least
its `h'=0` instance). The forest substrate already landed is mostly *into-G̃ᵥᵃᵇ*
acyclicity transport; the unsplit lift needs *into-G̃* transport (adding a
`va`/`vb` fiber to a forest on `V∖{v}` where `v` is fresh) plus a
`forest_packing_decomp`-driven count across all `D` forests. Blueprint:
`rem:kt-lemma-44` records this; `lem:removal-deficiency` `\uses`
`lem:forest-surgery-unsplit`; `lem:forest-surgery-unsplit` re-annotated as
*sound, not yet formalized* (distinct from `-split`'s balanced-packing block).

## Current state

Pivoted to the deficiency route (2026-06-02 — see *Finding* + *Replan*).
**Commits B + C landed:** `lem:splitoff-deficiency` is now two-sided and
green `\leanok` — `Graph.splitOff_deficiency_le` (`≤`, KT 4.3(i) upper) and
`Graph.splitOff_deficiency_ge` (`def(G̃) − 1 ≤ def(G̃ᵥᵃᵇ)`, the KT 4.3(i)
"`k`-dof or `(k−1)`-dof" lower bound). Both axiom-free, deficiency-count
route, no forests.

**Commit D BLOCKED (2026-06-03 — see *Finding 2* below).** The Replan
assumed `lem:removal-deficiency` (KT 4.4, `def(G̃ᵥ) ≥ k`) would yield to the
same deficiency-counting route as B/C. It does **not**: KT 4.4's lower bound
is provably *not* a deficiency-counting fact — it is equivalent to a
rank-increment lower bound `rank M(G̃) − rank M(G̃ᵥ) ≥ D` that is a
forest-packing *existence* statement, not derivable from rank-monotonicity
(gives only `≤ 2(D−1)`, wrong direction) or single-partition comparison
(gives only `≥ k − D`). It genuinely needs the `h'=0` case of the unsplit
forest surgery `lem:forest-surgery-unsplit` (KT 4.2(i)). That direction is
**sound** (no balanced-packing gloss — the gloss is only in `-split`) but is
not yet formalized; landing it is a multi-commit forest-packing-lift
development, not a clean corollary. **Next concrete task is now the unsplit
forest surgery `h'=0` lift, not a quick `≥ k` proof.** See *Finding 2* and
*Hand-off*.

**Green and `\leanok` in `Molecular/Induction.lean`** (all axiom-free): the
full inherited KT 3.4 + KT 3.5 chain — `lem:circuit-induces-rigid` (3.4),
and the 3.5 chain `lem:rigid-full-rank` → `lem:contract-rank-bridge` →
`lem:contract-deficiency-conservation` → `lem:contract-minimality-transport`
→ `lem:contraction-minimality` (all stated matroid-side, no graph↔matroid
`map`); the four graph operations `def:induced-span` / `def:graph-operations`
(`removeVertex` / `splitOff` / `edgeSplit`) / `def:rigid-contraction`; and
the forest-surgery framing `lem:forest-packing-decomp`. Per-lemma rationale
is in *Decisions* + the *Lemma checklist*; the full play-by-play is in git
history (commits `6b1176a`…`f7a7ebd`).

**Off the critical path (deferred surgery TODO — *Replan* Step 5):** the
forest-surgery substrate landed for `lem:forest-surgery-split` (none a
blueprint node; the node stays red) — incidence/cardinality
(`edgeFiber_ncard`, `edgeSet_splitOff`,
`edgeFiber_subset_edgeSet_mulTilde_splitOff`), degree-at-`v` (`fiberAtVertex`,
`mulTilde_inc`, `fiberAtVertex_inter_edgeSet[_ncard]`, `fiberDegree`,
`fiberDegree_{mono,le}`), both no-reroute acyclicity directions
(`mulTilde_splitOff_deleteFiber_le` +
`isAcyclicSet_mulTilde_of_splitOff_of_disjoint`;
`mulTilde_removeVertex_le_splitOff` +
`isAcyclicSet_mulTilde_splitOff_of_removeVertex`), and the reroute count cap
(`isCycleSet_pair_edgeFiber_splitOff`,
`fiber_inter_subsingleton_of_isAcyclicSet_splitOff`). These complete the
surgery only if the balanced-packing lemma is proven (*Finding* layer 2);
they are **not** needed for Theorem 4.9.

**Next:** *Replan* commit D (`lem:removal-deficiency`, KT 4.4: `def(G̃ᵥ) ≥ k`
for a degree-2 vertex of a minimal `k`-dof graph). Commits B + C (the two
directions of `lem:splitoff-deficiency`) **landed** axiom-free in
`Molecular/Induction.lean`:
- B (`≤`, `Graph.splitOff_deficiency_le`): `def(G̃ᵥᵃᵇ) ≤ def(G̃)` via the
  partition *extension* `f = update f' v (f' a)` (numParts equal; crossing
  injection `e_b ↦ e₀`).
- C (`≥`, `Graph.splitOff_deficiency_ge`): `def(G̃) − 1 ≤ def(G̃ᵥᵃᵇ)` via the
  partition *restriction* of an attained maximizer (`exists_eq_ciSup_of_finite`),
  case-split on whether `v`'s label is shared (numParts unchanged, crossing
  count non-increasing ⟹ `≥ def(G̃)`) or `v` isolated (numParts `−1`, crossing
  count `−1` via injection `e₀ ↦ e_b` missing the crossing `eₐ ∉ E(H)` ⟹
  `≥ def(G̃) − 1`).
Together they pin `def(G̃ᵥᵃᵇ) ∈ {def(G̃), def(G̃) − 1}`. The matroid-base form
of KT 4.3(ii) (which alternative holds) needs the deferred forest surgery and
is **not** on the Theorem-4.9 critical path (omitted; see *Replan*). See
*Hand-off*.

## Architectural choices made up front

- **New file `Molecular/Induction.lean`.** Per the one-`.lean` /
  one-`.tex` per molecular phase convention (post-Phase-18 cleanup
  split). Carrier: mathlib core `Graph α β`, matching Phases 13–19.
- **Graph operations as `Graph α β` constructions, reusing the matroid
  layer.** Splitting-off / edge-splitting / removal / rigid-contraction
  are graph-level ops; their *deficiency* behaviour routes through the
  matroid `M(G̃)` (Phase 19) and matroid restriction/contraction +
  fundamental circuits (mathlib `Matroid.restrict`, `Matroid.contract`,
  `Matroid.fundCircuit`) + the vendored union subsystem
  (`Matroid/Constructions/Union.lean`). `edgeMultiply` / `mulTilde`
  carry the `(D−1)·G` plumbing already.
- **Forest surgery (4.1/4.2) was the planned hard core — now deferred.**
  The framing question (explicit `D` forests vs. matroid-base) was settled
  by `lem:forest-packing-decomp` (matroid-base, forced by `matroidMG`'s
  union definition). But the surgery proper hit the KT 4.1 balanced-packing
  gloss (*Finding*); Theorem 4.9 instead routes through the
  deficiency-count argument (*Replan*), and the surgery is a non-blocking
  TODO.

## Lemma checklist

Forward-mode: the authoritative node list is `molecular-induction.tex`
(`sec:molecular-induction`). Tracked here for hand-off convenience;
flip to `[x]` as each lands `\leanok` in the chapter.

Inherited from Phase 19 (schedule early):
- [x] `lem:circuit-induces-rigid` — KT 3.4 full form: a circuit `X`
  induces a rigid `G[V(X)]` (tightness equality `|X−e| = D(|V(X)|−1)`).
  `Graph.circuit_induces_isTight`; lower bound is the direct circuit-minimality
  fact `Graph.circuit_ncard_gt` (NOT `thm:def-eq-corank`).
- [x] `lem:rigid-full-rank` — KT 3.5 rank core: a rigid subgraph `H`
  (`def(H̃) = 0`) attains full rank `rank M(H̃) = D(|V(H)| − 1)`.
  `Graph.rank_matroidMG_of_isKDof_zero`; 4-line corollary of `rank_add_deficiency_eq`.
- [x] `lem:contract-rank-bridge` — KT 3.5 contraction arithmetic:
  `rank(M(G̃)/E(H̃)) + rank M(H̃) = rank M(G̃)` (`Graph.contract_matroidMG_rank`),
  via the abstract adapter `Matroid.rank_contract_add_rank_restrict` + the vendored
  `contract_rank_cast_int_eq` + Phase 19's `matroidMG_restrict_mulTilde`.
- [x] `lem:contract-deficiency-conservation` — KT 3.5 deficiency-conservation half:
  `D(|V(G)| − |V(H)|) − rank(M(G̃)/E(H̃)) = def(G̃)` for rigid `H ≤ G`
  (`Graph.contract_matroidMG_deficiency_eq`); `zify` + `linarith` over `contract_matroidMG_rank`
  + rank core + `rank_add_deficiency_eq`. Matroid-side, no `map`.
- [x] `lem:contract-minimality-transport` — KT 3.5 minimality-transport half: every base
  of `M(G̃)/E(H̃)` meets every surviving edge-fiber (`Graph.contract_minimality_transport`).
  Base-lift via the abstract helper `Matroid.IsBase.union_isBasis_of_contract`, NOT
  fundamental-circuit swaps. Matroid-side, no `H ≤ G` needed.
- [x] `lem:contraction-minimality` — KT 3.5: contracting a proper rigid
  subgraph preserves minimal `k`-dof (Case I engine). `Graph.contraction_isMinimalKDof`,
  the 4-line conjunction of `contract_matroidMG_deficiency_eq` (corank `= k` via `hG.1`) +
  `contract_minimality_transport`. NO graph↔matroid `map` — matroid contraction `M(G̃)/E(H̃)`.

Graph operations:
- [x] `def:induced-span` — vertex-induced subgraph `G[V(X)]` from a fiber set
  `X` of `G̃` (`Graph.fiberSpan` / `Graph.inducedSpan`, via mathlib `Graph.induce`).
- [x] `def:graph-operations` — removal `G_v` (`Graph.removeVertex`), splitting-off
  `G_v^{ab}` (`Graph.splitOff`), edge-splitting `H_{ab}^v` (`Graph.edgeSplit`,
  inverse of splitting-off).
- [x] `def:rigid-contraction` — rigid-subgraph contraction `G/E(H)`
  (`Graph.rigidContract`, via `deleteEdges` + `map (collapseTo …)`).

Deficiency route to dof-tracking (Replan 2026-06-02 — **the critical path**):
- [x] `lem:splitoff-deficiency` — KT 4.3(i), both directions landed
  (commits B + C), green `\leanok`: `Graph.splitOff_deficiency_le`
  (`def(G̃ᵥᵃᵇ) ≤ def(G̃)`, partition *extension* `f = update f' v (f' a)`) and
  `Graph.splitOff_deficiency_ge` (`def(G̃) − 1 ≤ def(G̃ᵥᵃᵇ)`, partition
  *restriction* of an attained maximizer + case split on `v`-isolation). Pins
  `def(G̃ᵥᵃᵇ) ∈ {def(G̃), def(G̃) − 1}`. Degree-2 encoded as two edges `eₐ`/`e_b`
  (the *only* `v`-incident edges) + fresh `e₀ ∉ E(G)`. The matroid-base form of
  KT 4.3(ii) (which alternative) is **off the critical path** — it needs the
  deferred forest surgery (*Finding* layer 2); omitted, not needed by Thm 4.9.
- [x] (commit A) `ex:kt-41-overquantified` — the over-quantification disproof
  `example` (`I = ∅`, ℕ-cardinality: no `I'` with `|I'| + D = 0` for `D ≥ 1`),
  green `\leanok` in `Molecular/Induction.lean`. Blueprint Remark
  `rem:kt-lemma-41` carries the three-layer framing (*Finding*).
- [ ] `lem:removal-deficiency` — KT 4.4: `def(G̃ᵥ) ≥ k`. **BLOCKED on
  `lem:forest-surgery-unsplit` (`h'=0`)** — NOT a deficiency-counting fact
  (*Finding 2*). Replan commit D, but D now means "formalize the unsplit
  `h'=0` lift first".
- [ ] `lem:dof-tracking` — KT 4.3–4.5 assembly; `\uses` the two deficiency
  nodes above (NOT forest surgery). Replan commit E.
- [ ] `lem:reducible-vertex` — KT 4.6, existence of a reducible degree-2
  vertex (maximal-chain / degree-sequence count). Replan commit F.
- [ ] `lem:reduction-step` — KT 4.7–4.8, reduction preserves minimality
  (two circuit-swap arguments; the 4.8 capstone). Replan commit G.
- [ ] `thm:minimal-kdof-reduction` — KT Theorem 4.9 (capstone; phase
  close). Replan commit H.

Forest surgery (**DEFERRED — off critical path, TODO per Replan Step 5**):
- [x] `lem:forest-packing-decomp` — framing sub-node of KT 4.1/4.2:
  `I` independent in `M(G̃)` ⟺ covered by `D` cycle-matroid-independent fiber
  sets. `Graph.matroidMG_indep_iff_exists_forest_packing`. Green and still
  generally useful (and `def:matroid-MG`'s union form is the engine of the
  deficiency route too).
- [ ] `lem:forest-surgery-split` — KT 4.1, splitting-off direction.
  **DEFERRED**: blocked on the balanced-packing lemma KT glosses (*Finding*);
  *not* needed for Theorem 4.9 (deficiency route replaces it). Substrate
  landed (`edgeFiber_ncard`, `edgeSet_splitOff`,
  `edgeFiber_subset_edgeSet_mulTilde_splitOff`; degree substrate
  `fiberAtVertex` / `mulTilde_inc` / `fiberAtVertex_inter_edgeSet[_ncard]` /
  `fiberDegree` / `fiberDegree_{mono,le}`; both no-reroute acyclicity
  directions; reroute count cap `isCycleSet_pair_edgeFiber_splitOff` /
  `fiber_inter_subsingleton_of_isAcyclicSet_splitOff`). Completes from this
  substrate **iff** the balanced-packing lemma is proven (TODO).
- [ ] `lem:forest-surgery-unsplit` — KT 4.2, edge-splitting direction.
  **SOUND, not yet formalized (NOT deferred for the `-split` reason).** Its
  `h'=0` case carries no balanced-packing gloss and is now ON the critical
  path: `lem:removal-deficiency` (KT 4.4) needs it (*Finding 2*). The `h'=0`
  lift: `D` forests on `V∖{v}` (a base of `M(G̃ᵥ)`) extend to `D` forests on
  `V` by adding one fresh `v`-fiber each (`v` isolated ⟹ acyclic), giving an
  indep set of `M(G̃)` of size `+D`. Needs *into-G̃* acyclicity transport +
  a `forest_packing_decomp` count. The general `h'>0` case reroutes and
  shares `-split`'s subtleties — only `h'=0` is needed downstream.

(Off the Thm-4.9 critical path; schedule with Phase 21:) KT Lemma 3.2
(not 3-edge-connected), Lemma 3.6 (partition decomposition — needed
only by Case 6.1).

## Decisions made during this phase

- **Vertex-induced subgraph = mathlib `Graph.induce`, not a hand-rolled
  construction.** The phase-open blocker ("no existing analogue") was wrong:
  `Mathlib.Combinatorics.Graph.Delete` has `Graph.induce (X : Set α)` with the
  full API (`vertexSet_induce`, `induce_isLink`, `edgeSet_induce`, `induce_le`).
  `Graph.inducedSpan G n X := G.induce (G.fiberSpan n X)` is a thin wrapper;
  `fiberSpan` reuses Phase 16's `spanningVerts` on `mulTilde`. Reach for mathlib's
  `induce` before hand-rolling in the graph-operations nodes too.
- **KT 3.4 lower bound is the direct circuit-minimality fact, NOT
  `thm:def-eq-corank`.** A circuit `X` is a *minimal* dependent set, so every
  proper subset is independent ⟹ `(D,D)`-sparse (`matroidMG_indep_iff`); the
  dependent `X`'s sparsity failure is therefore at `X` itself, giving `|X| >
  D(|V(X)|−1)` (`circuit_ncard_gt`). This matches KT's "see [21]" (a count-matroid
  fact), not the JJ09 min–max. Blueprint `\uses` corrected to drop
  `thm:def-eq-corank`. (The def=corank reverse is still the engine for KT 3.5's
  rank-conservation, scheduled next.)

- **Graph operations: reuse mathlib where possible, structure-literal where not.**
  `removeVertex = deleteVerts {v}` and `rigidContract = (deleteEdges E(H)).map
  (collapseTo r V(H))` are thin compositions of mathlib `Graph` ops (mathlib's `map`
  realizes the vertex-collapse). `splitOff` / `edgeSplit` *add* edges/vertices, and
  mathlib's `Graph` has no union/join (`SemilatticeInf` only) or `addEdge`, so they
  are structure literals with explicit fresh edge labels (`e₀` for splitting-off;
  `e₁,e₂` for edge-splitting). `collapseTo r S` uses `open Classical in` for the
  membership `if`. Deficiency behaviour is deferred to the later surgery nodes.

- **KT 3.5 decomposed; rank core then contraction arithmetic.** The full
  `lem:contraction-minimality` is multi-commit. Earlier worry — a graph↔matroid `map`
  correspondence (`(G/E(H))̃` ↔ `M(G̃)/E(H̃)`) — turned out **unnecessary**: KT's proof
  reasons entirely on the matroid contraction `M(G̃)/E(H̃)`, so the deficiency/minimality
  statement is stated against the matroid, not the collapsed graph `rigidContract`. Two
  commits landed: (1) the **rank core** `lem:rigid-full-rank` (`rank M(H̃) = D(|V(H)|−1)`
  for rigid `H`, 4-line corollary of `rank_add_deficiency_eq`); (2) the **contraction
  arithmetic** `lem:contract-rank-bridge` (`rank(M(G̃)/E(H̃)) + rank M(H̃) = rank M(G̃)`).
  The latter is a 5-line composition of an abstract adapter
  `Matroid.rank_contract_add_rank_restrict` (`rank(M/C) + rank(M↾C) = rank M`, itself a
  4-line wrap of the vendored `contract_rank_cast_int_eq` + `restrict_rk_eq`) with Phase
  19's `matroidMG_restrict_mulTilde`. Remaining: deficiency conservation (assemble) +
  minimality transport (fundCircuit swaps).

- **KT 4.1 forest surgery hit an over-quantification + balanced-packing gloss
  (2026-06-02); routed around via deficiency-counting.** See *Finding* +
  *Replan* above. The substantive splitting-off content the induction needs is
  the deficiency inequality `def(G̃ᵥᵃᵇ) ≤ def(G̃)`, proved by a partition-count
  comparison through `rank_add_deficiency_eq` — not KT's explicit forest reroute.
  KT's surgery (and the balanced-packing lemma it glosses) is a non-blocking TODO.

- **Splitting-off `≤` (commit B): degree-2 encoded as two named edges, `≤` not `=`.**
  `splitOff_deficiency_le` takes the degree-2 hypothesis as two distinct edges
  `eₐ`/`e_b` (joining `v,a`/`v,b`) that are the *only* `v`-incident edges
  (`hdeg2 : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b`) + fresh `e₀ ∉ E(G)`. The
  partition-count step needs only `d_G(P) ≤ d_{Gᵥᵃᵇ}(P')` (a crossing-edge
  injection `e_b ↦ e₀`, identity elsewhere), not KT's claimed *equality* —
  the `≤` is what the `(D−1)·d` term in `partitionDef` consumes. The `va`-edge
  never crosses (both endpoints get label `f' a`); `vb` maps to `e₀`; all other
  crossing edges survive verbatim. Proof opens `rw [deficiency]; haveI :
  Nonempty α := ⟨a⟩; refine ciSup_le …` (FRICTION entry for the `Nonempty`/unfold).

### Promoted to FRICTION
- *`ciSup_le` on `deficiency = ⨆ f : α → α, …` needs `rw [deficiency]` + `haveI :
  Nonempty α` (from any vertex); the prior lemmas only bounded from below via
  `partitionDef_le_deficiency`* → FRICTION `[resolved] ciSup_le on deficiency …`.
- *No mathlib "base of `M ／ C` lifts to base of `M` via a basis of `C`" — route through
  `IsBasis'.contract_eq_contract_delete` + loops/spanning; `IsBasis'` carries no ground
  containment for its `X`* → FRICTION `[resolved] [matroid] no mathlib "base of M ／ C
  lifts …"`.
- *`IsCircuit.subset_ground` for `M(G̃)` gives a restrict-ground `⊆`, defeq-but-not-
  syntactic to `E(G̃)` — ascribe once* → FRICTION `[resolved] [matroid]
  IsCircuit.subset_ground for M(G̃) …`.
- *Contraction rank arithmetic is already in the vendored `Matroid/Minor/Rank.lean`
  (`contract_rank_cast_int_eq`); its `cast_int` RHS is ℤ-subtraction — keep atoms ℤ-cast
  + `omega`* → FRICTION `[resolved] [matroid] contraction rank arithmetic already lives
  in vendored Matroid.Minor.Rank …`.
- *Hand-rolled `Graph` with several fresh edge labels needs a distinctness guard in a
  clause, else `eq_or_eq_of_isLink_of_isLink` is unprovable* → FRICTION `[resolved] A
  hand-rolled Graph α β with several fresh edge labels …`.

## Blockers / open questions

- **[resolved] Forest-surgery framing.** Decided by `lem:forest-packing-decomp`:
  the matroid-base / `union_indep_iff` framing is *forced* by the existing
  `matroidMG` definition (`= (⋃_{i<D} cycleMatroid(G̃)) ↾ E(G̃)`), so the "D
  edge-disjoint forests" are the `union_indep_iff` decomposition and a "forest"
  is a `cycleMatroid`-independent fiber set. No hand-rolled acyclicity predicate.
- **[open, non-blocking] KT 4.1 balanced-packing (the *Finding*).** Is a base of
  `M(G̃)` always partitionable into `D` forests each meeting the degree-2 vertex
  `v`? KT's Lemma 4.1 proof assumes it without justification; we did not recover
  one. NOT on the Theorem-4.9 critical path (the deficiency route bypasses it);
  it gates only the deferred `-split` surgery TODO. Proving it rescues KT's
  proof (gap, not error); refuting it confirms the gap.
- **[blocking, on critical path — *Finding 2*] `h'=0` unsplit forest lift.** KT
  4.4 (`lem:removal-deficiency`) is on the Theorem-4.9 critical path and is NOT
  a deficiency-counting fact: it needs the `h'=0` case of
  `lem:forest-surgery-unsplit` (into-G̃ acyclicity transport + a
  `forest_packing_decomp` count). This direction is *sound* (no balanced-packing
  gloss) but unformalized. It is the genuine next chunk of work; see *Finding 2*
  + *Hand-off*. (Distinct from the non-blocking `-split` balanced-packing open
  question above.)

## Hand-off / next phase

**Read *Finding* + *Replan* first — Phase 20 pivoted (2026-06-02).** The
forest-surgery route (`lem:forest-surgery-split`, KT 4.1) is **off the
critical path**: KT's Lemma 4.1 is over-quantified (formally disprovable) and
its proof glosses a balanced-packing assumption we could not recover.
Theorem 4.9 is reached instead via the **deficiency-count route** (resting on
the green `def = corank` bridge `rank_add_deficiency_eq`).

Green and `\leanok` (axiom-free, `Molecular/Induction.lean`): the full
inherited KT 3.4 + KT 3.5 chain, the four graph operations, and the
forest-surgery framing `lem:forest-packing-decomp` (names in *Current
state*). The forest-surgery substrate is landed but serves the deferred
surgery TODO (*Replan* Step 5), not Theorem 4.9.

**Commits A–C landed.** A (the pivot): blueprint Remark `rem:kt-lemma-41`
(three-layer "On Katoh–Tanigawa Lemma 4.1") + green `example` node
`ex:kt-41-overquantified`; dep-graph nodes `lem:splitoff-deficiency` /
`lem:removal-deficiency` added with `lem:dof-tracking` re-pointed to them;
`lem:forest-surgery-split` / `-unsplit` annotated deferred; Lean `example`
disproving the `I = ∅` literal quantification. B + C (`lem:splitoff-deficiency`,
both directions, green `\leanok`, axiom-free): `Graph.splitOff_deficiency_le`
(`def(G̃ᵥᵃᵇ) ≤ def(G̃)`, partition extension `f = update f' v (f' a)` + `ciSup_le`)
and `Graph.splitOff_deficiency_ge` (`def(G̃) − 1 ≤ def(G̃ᵥᵃᵇ)`, restriction of an
attained maximizer + `v`-isolation case split). They pin
`def(G̃ᵥᵃᵇ) ∈ {def(G̃), def(G̃) − 1}` (KT 4.3(i)). **Scope note discovered at
commit C:** KT 4.3(ii) — the matroid-base characterization of *which*
alternative holds (`∃` base `B'` with `|ãb ∩ B'| < D − 1`) — is proved by KT
through Lemma 4.1/4.2 (the deferred forest surgery, *Finding* layer 2), so it is
**off the Theorem-4.9 critical path** and is omitted; the two-sided deficiency
bound is what `lem:dof-tracking` and Theorem 4.9 actually consume. Blueprint
`lem:splitoff-deficiency` restated to the two-sided form with this scope note.

**Commit D is BLOCKED as originally scoped (2026-06-03 — *Finding 2*).** KT
4.4 (`lem:removal-deficiency`, `def(G̃ᵥ) ≥ k`) is *not* a deficiency-counting
fact — it is equivalent to a rank-increment lower bound
`rank M(G̃) − rank M(G̃ᵥ) ≥ D` that needs the `h'=0` case of the *unsplit*
forest surgery (KT 4.2(i)), not rank-monotonicity (gives `≤ 2(D−1)`) or a
single partition (gives `≥ k − D`). This session's commit recorded the finding:
blueprint `rem:kt-lemma-44` + revised `lem:removal-deficiency` proof/`\uses` +
re-annotated `lem:forest-surgery-unsplit` (sound, not yet formalized) +
*Finding 2* above. **No Lean lemma landed** — there was no honest non-forest
proof to write.

**Next agent's concrete commit = formalize the `h'=0` unsplit forest-packing
lift** (`lem:forest-surgery-unsplit`, restricted to `h'=0`), which then makes
`lem:removal-deficiency` a short corollary via `rank_add_deficiency_eq`. The
lift: given `D` cycle-matroid-independent forests on `V∖{v}` covering a base
`B'` of `M(G̃ᵥ)` (use the green `matroidMG_indep_iff_exists_forest_packing` /
`forest_packing_decomp`), add one fresh `v`-fiber to each (`D−1` get a `va`
copy, one gets a `vb` copy) and show the result is acyclic in `G̃` (`v` is
isolated in each forest-on-`V∖{v}`, so any added `v`-edge cannot close a
cycle — the *into-G̃* analogue of the green
`isAcyclicSet_mulTilde_splitOff_of_removeVertex`, but targeting `G̃` not
`G̃ᵥᵃᵇ`) and edge-disjoint, giving an indep set of `M(G̃)` of size `|B'| + D`.
This is a multi-commit substrate development — assess after the first into-G̃
acyclicity-transport lemma lands. Only `h'=0` is needed; do NOT attempt the
general `h'>0` reroute (it shares `-split`'s open balanced-packing crux).
Then `lem:removal-deficiency`, then commits E–H per *Replan* (4.9 assembly).
Reuse shapes for the eventual corollary: `rank_add_deficiency_eq` for the
ambient/corank arithmetic; `matroidMG_restrict_mulTilde` for
`M(G̃ᵥ) = M(G̃) ↾ E(G̃ᵥ)`. Degree-2 stays encoded as two edges `eₐ`/`e_b`
(the only `v`-incident edges, `hdeg2`).
