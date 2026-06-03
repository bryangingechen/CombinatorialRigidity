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
> *Hand-off* and start at **Replan commit F** (`lem:reducible-vertex`).
> Commits A–E have landed (the deficiency-count route carries both the
> splitting-off bounds and the KT 4.4 removal bound, now assembled into
> the KT 4.3–4.5 dof-tracking packaging; the same-day *Finding 2* that
> claimed KT 4.4 needed the unsplit forest surgery was itself **refuted**
> — see *Finding 2 REFUTED*).

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
- **D —** `lem:removal-deficiency` (`Gᵥ`, KT 4.4: `def(G̃ᵥ) ≥ k`). **LANDED
  (2026-06-03)** by the deficiency-count route after all — see *Finding 2
  refuted* below. `Graph.removeVertex_deficiency_ge`, green `\leanok`,
  axiom-free. The 2026-06-03 *Finding 2* (which had re-scoped D onto the
  `h'=0` unsplit forest surgery) was itself wrong; the clean partition-count
  comparison goes through with a `2 ≤ bodyBarDim n` hypothesis.
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

## Finding 2 REFUTED: KT Lemma 4.4 *is* a deficiency-counting fact (2026-06-03, same day)

An earlier 2026-06-03 analysis ("Finding 2", commit d44789e) concluded that
`lem:removal-deficiency` (KT 4.4, `def(G̃ᵥ) ≥ k`) is **not** a
deficiency-counting fact and is gated on the `h'=0` unsplit forest surgery.
**That conclusion was wrong.** Commit D lands KT 4.4 by exactly the same
partition-count comparison as the splitting-off bounds B/C
(`Graph.removeVertex_deficiency_ge`, green `\leanok`, axiom-free), needing
only the strengthened hypothesis `2 ≤ bodyBarDim n`. (KT 2011 Lemma 4.4 is on
**p.662** — pdf page 16 of the DCG PDF opens "662 Discrete Comput Geom …" — not
p.661 as Finding 2 wrote.)

**The flaw in Finding 2.** Finding 2 considered restricting an optimal
partition `P` of `V` to `V∖{v}` and reasoned: `numParts` drops by ≤1 (costs
`D`), `d` drops by ≤2 (helps "in the wrong direction"), net `≥ k − D`. Two
errors: (1) the `−(D−1)·d` sign in `partitionDef` means a *larger* crossing-drop
*raises* the deficiency — dropping `d` is not "the wrong direction", it is the
*helpful* direction; (2) in the only case that loses a part (`v` isolated in its
block), `v`'s neighbours `a, b` are *forced* into blocks distinct from `v`'s, so
**both** `va` and `vb` cross — `c = 2` is forced, not merely `≤ 2`. The two cases:

- **shared** (`v`'s label carried by another vertex): `|P|` unchanged, crossing
  count non-increasing ⟹ `def_{Gᵥ}(P) = k + (D−1)·c ≥ k` (c = #v-edges crossing).
- **isolated**: `|P|` drops by exactly 1, `c = 2` forced ⟹ `def_{Gᵥ}(P) =
  k − D + 2(D−1) = k + (D−2) ≥ k`. The `+2(D−1)` crossing-drop pays for the
  `−D` part-loss precisely when `D ≥ 2`.

`removeVertex` is *structurally simpler* than `splitOff` (no fresh `e₀`/`ab`
edge to inject or track), so the crossing count strictly drops with no
replacement — the proof is shorter than `splitOff_deficiency_ge`. The
`2 ≤ bodyBarDim n` hypothesis (vs the bare `1 ≤` the splitting-off lemmas carry)
is trivial in the molecular regime (`n ≥ 2 ⟹ D = n(n+1)/2 ≥ 3`) but a genuine
signature difference, carried explicitly.

**Three-layer framing (unchanged for KT here).** KT 4.4 did *not* err: KT's
`h'=0` unsplit forest-surgery derivation is a sound alternative route (and the
`-unsplit` direction carries no balanced-packing gloss). We simply found a
deficiency-count route that avoids the forest surgery entirely — KT's route and
ours both establish the same true statement. `lem:forest-surgery-unsplit` is
therefore returned to deferred-TODO (off the Theorem-4.9 critical path), like
`-split`. The KT 4.1 *Finding* (over-quantification + `-split` balanced-packing
gloss) stands as before — only Finding 2's removal-bound claim is retracted.

## Current state

Pivoted to the deficiency route (2026-06-02 — see *Finding* + *Replan*).
**Commits B + C + D landed:** the splitting-off bounds `lem:splitoff-deficiency`
(two-sided, `Graph.splitOff_deficiency_{le,ge}`) and the removal bound
`lem:removal-deficiency` (`Graph.removeVertex_deficiency_ge`: `def(G̃) ≤
def(G̃ᵥ)`, KT 4.4 p.662) are all green `\leanok`, axiom-free, deficiency-count
route, no forests. All three are partition-count comparisons through the green
`def = corank` infrastructure.

**Commit D landed by deficiency counting after all (2026-06-03 — see *Finding 2
REFUTED*).** The 2026-06-03 "Finding 2" had claimed KT 4.4's lower bound was
*not* a deficiency-counting fact (gated on the `h'=0` unsplit forest surgery);
that was wrong. The clean partition-count comparison goes through with a
`2 ≤ bodyBarDim n` hypothesis: the isolated case forces both `v`-edges to cross
(`c=2`), and the `+2(D−1)` crossing-drop pays for the `−D` part-loss exactly
when `D ≥ 2`. `removeVertex` is structurally simpler than `splitOff` (no fresh
`e₀`/`ab` edge), so the proof is shorter than `splitOff_deficiency_ge`.

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

**Commit F′ landed (`no_rigid_edge_count`, KT 4.5(i) edge bound; `lem:no-rigid-edge-count`
GREEN).** The KT 4.5(i) edge bound `(D−1)|E| < D(|V|−1)+(D−1)` for a minimal 0-dof-graph
with no proper rigid subgraph — equivalently `corank M(G̃) ≤ D−2` — is fully landed as
`Graph.no_rigid_edge_count` (green `\leanok`, axiom-free). The fundamental-circuit-swap
argument (KT eq. 4.3) goes through: the prior `X∩ẽ≠∅` "blocker" was an un-attempted clean
restatement, NOT a real obstruction — it is a direct base-meets-fiber contradiction off
`IsMinimalKDof`'s clause (if `X∩ẽ=∅`, `X−ej` is a full-rank base avoiding `ẽ`), no forest
reasoning, no `rank M(G̃)↾(E(G̃)∖ẽ)` detour. Supports `mulTilde_edgeSet_ncard` (`|E(G̃)| =
(D−1)|E|`) and `fundCircuit_inducedSpan_vertexSet_eq` (spanning step) were landed earlier.
Needs `2 ≤ bodyBarDim n` (`D ≥ 2`, trivial in the molecular regime).

**Citation reconciliation (verified against `.refs/` PDF).** KT 2011 Lemma 4.4 begins on
**printed p.662** (the running header of pdf page 16 reads "662 Discrete Comput Geom …"),
confirming the *Finding 2 REFUTED* / commit-D record. An independent scrutiny pass had
placed it on p.661; that is **wrong** — corrected here. KT 2011 Lemma 4.5 is on **printed
p.663** (verified, pdf page 17), and its proof runs onto p.664.

**Commit F′-spanning landed (`fundCircuit_inducedSpan_vertexSet_eq`, KT 4.5(i) spanning
step).** The "no-proper-rigid ⟹ `V(X)=V`" reduction half of F′ is now green, axiom-free
(`Molecular/Induction.lean`): for a base `B` of `M(G̃)` and a redundant fiber `p ∈ E(G̃)∖B`,
the fundamental circuit `X = fundCircuit p B` (`IsBase.fundCircuit_isCircuit`) induces a
rigid `G[V(X)]` (green `circuit_induces_isRigidSubgraph`); under the no-proper-rigid
hypothesis it cannot be a *proper* rigid subgraph, so `V(X) = V(G)`. This isolates the
clean matroid-API half of F′ from the remaining base-exchange count + the `X∩ẽ≠∅` blocker
(unchanged — see *Hand-off*). It is also reused by commit G (KT 4.7–4.8). Referenced in the
`lem:no-rigid-edge-count` proof prose (node stays red; the corank core is still open).

**Commit F landed (`circuit_induces_isRigidSubgraph`, KT 3.4 rigid-subgraph form).**
While scoping the planned commit F (`lem:reducible-vertex`, KT 4.6) it became clear
KT 4.6 is multi-commit and rests on a prerequisite KT 3.4 never delivered in Lean:
`circuit_induces_isTight` proved the tightness *equality* but never packaged the
`G[V(X)]` rigid-subgraph conclusion the node claims. Commit F lands that packaging —
`Graph.circuit_induces_isRigidSubgraph : (G.inducedSpan n X).IsRigidSubgraph G n` —
which KT 4.5(i)/4.8 (and hence KT 4.6) invoke directly. See the `lem:circuit-induces-rigid`
checklist entry. Next is the KT 4.6 chain proper (see its refined checklist entry +
*Hand-off*).

**Local-dof bookkeeping (commits B–E)** is complete and assembled
on the Lean side (axiom-free, `Molecular/Induction.lean`):
- B (`≤`, `Graph.splitOff_deficiency_le`): `def(G̃ᵥᵃᵇ) ≤ def(G̃)` via the
  partition *extension* `f = update f' v (f' a)` (numParts equal; crossing
  injection `e_b ↦ e₀`).
- C (`≥`, `Graph.splitOff_deficiency_ge`): `def(G̃) − 1 ≤ def(G̃ᵥᵃᵇ)` via the
  partition *restriction* of an attained maximizer (`exists_eq_ciSup_of_finite`),
  case-split on `v`-isolation.
- D (`Graph.removeVertex_deficiency_ge`): `def(G̃) ≤ def(G̃ᵥ)` via the *same*
  maximizer-restriction route, simpler (no `e₀`), `2 ≤ bodyBarDim n`.
- E (`Graph.dof_tracking`): the KT 4.3–4.5 packaging — a 3-way conjunction over
  B + C + D under `2 ≤ bodyBarDim n`. B + C pin `def(G̃ᵥᵃᵇ) ∈ {def(G̃),
  def(G̃) − 1}`; D adds `def(G̃ᵥ) ≥ def(G̃)`.
The matroid-base forms of KT 4.3(ii) / 4.4's "moreover" clause need the deferred
forest surgery and are **not** on the Theorem-4.9 critical path (omitted; see
*Replan*). See *Hand-off*.

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
  induces a rigid `G[V(X)]`. Two Lean decls: the tightness equality
  `|X−e| = D(|V(X)|−1)` (`Graph.circuit_induces_isTight`; lower bound the direct
  circuit-minimality fact `Graph.circuit_ncard_gt`, NOT `thm:def-eq-corank`), and
  the **rigid-subgraph packaging** `Graph.circuit_induces_isRigidSubgraph`
  (commit F): `(G.inducedSpan n X).IsRigidSubgraph G n`, i.e. `G[V(X)] ≤ G ∧
  def(G[V(X)]̃) = 0`. The packaging pins `rank M(G[V(X)]̃) = D(|V(X)|−1)` from both
  sides (`rank_matroidMG_le` ∧ the independent `X−e` of tight size, independent in
  `M(G[V(X)]̃) = M(G̃) ↾ E(G[V(X)]̃)` via `matroidMG_restrict_mulTilde` since `X ⊆
  E(G[V(X)]̃)` — new support lemma `subset_edgeSet_mulTilde_inducedSpan`), then
  `rank_add_deficiency_eq` forces `def = 0`. This is the "Lemma 3.4 implies G[V(X)]
  is a (proper) rigid subgraph" form KT 4.5(i)/4.8 invoke.
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
- [x] `lem:removal-deficiency` — KT 4.4 (p.662): `def(G̃) ≤ def(G̃ᵥ)`, so
  `def(G̃ᵥ) ≥ k`. **LANDED** by the deficiency-count route (commit D),
  `Graph.removeVertex_deficiency_ge`, green `\leanok`, axiom-free, needs
  `2 ≤ bodyBarDim n`. *Finding 2* (which claimed it was blocked on the unsplit
  forest surgery) is **refuted** — see *Finding 2 REFUTED*.
- [x] `lem:dof-tracking` — KT 4.3–4.5 assembly; `\uses` `lem:splitoff-deficiency`
  + `lem:removal-deficiency` (NOT forest surgery). **LANDED** (commit E),
  `Graph.dof_tracking`, green `\leanok`, axiom-free. Packaging lemma: a 3-way
  conjunction over the green bounds (`splitOff_deficiency_{le,ge}` +
  `removeVertex_deficiency_ge`) under `2 ≤ bodyBarDim n` (deriving `1 ≤` for the
  splitting-off pair via `le_trans`). For a `k`-dof-graph `G`:
  `k − 1 ≤ def(G̃ᵥᵃᵇ) ≤ k` and `def(G̃ᵥ) ≥ k`. The "which alternative" refinement
  (forest-surgery fundamental-circuit count) is off the Thm-4.9 critical path,
  omitted.
- [x] `lem:no-rigid-edge-count` — KT 4.5(i) edge-count bound `(D−1)|E| <
  D(|V|−1)+(D−1)` for a minimal 0-dof-graph with no proper rigid subgraph.
  **LANDED (F′ swap core)** — `Graph.no_rigid_edge_count`, green `\leanok`,
  axiom-free. Equivalent matroidal form: `corank M(G̃) ≤ D−2`. The full KT eq. 4.3
  fundamental-circuit swap: `h* = minₐ |ẽ ∩ B|` over bases (finite-min via
  `Set.exists_min_image` on `{B | IsBase B}`, finite as `⊆ 𝒫(E(G̃))`); `h* ≥ 1`
  from `IsMinimalKDof`'s base-meets-fiber clause. The `X∩ẽ≠∅` step (the prior
  blocker) is a **direct base-meets-fiber contradiction**, NOT forest reasoning:
  if `X∩ẽ=∅`, then `X−ej` is independent of full size `D(|V|−1)=|B*|` (`(D,D)`-tight
  on `V(X)=V` via `circuit_induces_isTight`), hence a *base* (certified via
  `exists_isBase_superset` + `eq_of_subset_of_ncard_le` since all bases share card)
  avoiding `ẽ` — contra `hG.2`. The exchange `B = insert f B* ∖ {ej}`
  (`IsBase.exchange_isBase_of_indep`, independence from `Indep.mem_fundCircuit_iff`)
  drops `|B∩ẽ| = h*−1`. Support: `Graph.mulTilde_edgeSet_ncard` (`|E(G̃)|=(D−1)|E|`),
  the spanning step `Graph.fundCircuit_inducedSpan_vertexSet_eq`, and
  `Graph.circuit_induces_isRigidSubgraph`. Needs `2 ≤ bodyBarDim n` (`D ≥ 2`).
- [ ] `lem:reducible-vertex` — KT 4.6, existence of a degree-2 vertex in a
  2-edge-connected minimal 0-dof-graph with no proper rigid subgraph. **Scope
  refined at commit F** (which landed the *prerequisite* `circuit_induces_isRigidSubgraph`
  instead): Thm 4.9 consumes only "∃ degree-2 vertex" (the chain/cycle refinement
  is for the §5–6 *algebraic* induction, off the Thm-4.9 critical path). The "∃
  degree-2 vertex" core needs (a) the **KT 4.5(i)** edge bound `lem:no-rigid-edge-count`
  above; and (b) the average-degree arithmetic `d_avg = 2|E|/|V| < 2D/(D−1) ≤ 3`,
  which needs a **multigraph degree notion on `Graph α β`** (the project has none —
  degree-2 is encoded ad hoc as `hdeg2 : ∀ e x, IsLink e v x → e = eₐ ∨ e = e_b`).
  Likely 2 commits: F′ = KT 4.5(i) edge bound (corank core); F″ = degree theory +
  ∃-degree-2.
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
  **DEFERRED / off critical path** (returned here after *Finding 2 REFUTED*).
  This direction is **sound** (no balanced-packing gloss, unlike `-split`) but
  is **not** needed by Theorem 4.9: the removal bound it was thought to gate
  (`lem:removal-deficiency`, KT 4.4) lands by the deficiency-count route
  instead (commit D). The `h'=0` lift (`D` forests on `V∖{v}` extend to `V` by
  adding one fresh `v`-fiber each, `v` isolated ⟹ acyclic) is KT's route to
  KT 4.4; we no longer need to formalize it.

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
- **[resolved] KT 4.5(i) swap core (`X∩ẽ≠∅`).** LANDED (`Graph.no_rigid_edge_count`).
  The prior "could not crisply formalize" was an un-attempted clean restatement: the
  `X∩ẽ≠∅` step is **not** intrinsically forest reasoning. If `X∩ẽ=∅`, the independent
  `X−ej` is full-rank (`(D,D)`-tight on `V(X)=V` ⟹ `|X−ej|=D(|V|−1)=|B*|`), hence a
  *base* avoiding `ẽ` — a direct base-meets-fiber contradiction with
  `IsMinimalKDof`'s clause (`hG.2`). No `rank M(G̃)↾(E(G̃)∖ẽ)` detour needed. Certify
  base-hood by `exists_isBase_superset` + `Set.eq_of_subset_of_ncard_le` (all bases
  share cardinality). Reused green machinery: `circuit_induces_isTight`,
  `fundCircuit_inducedSpan_vertexSet_eq`. Needs `2 ≤ bodyBarDim n`.
- **[resolved — *Finding 2 REFUTED*] KT 4.4 removal bound.** Earlier thought to
  need the `h'=0` unsplit forest lift; in fact lands by the deficiency-count
  route (`Graph.removeVertex_deficiency_ge`, commit D) with `2 ≤ bodyBarDim n`.
  The unsplit forest surgery (`lem:forest-surgery-unsplit`) is back to deferred /
  off the critical path. See *Finding 2 REFUTED*.

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

**Commit D landed (2026-06-03), refuting the same-day *Finding 2*.** KT 4.4
(`lem:removal-deficiency`, `def(G̃) ≤ def(G̃ᵥ)`, p.662) lands by the
deficiency-count route after all — `Graph.removeVertex_deficiency_ge`, green
`\leanok`, axiom-free — needing the strengthened `2 ≤ bodyBarDim n`. Finding 2
had wrongly concluded the bound was *not* a deficiency-counting fact; the flaw
was (i) treating the crossing-drop as "the wrong direction" when the
`−(D−1)·d` sign in `partitionDef` makes it *helpful*, and (ii) missing that the
isolated case *forces* both `v`-edges to cross (`c=2`). This session's commit:
the Lean lemma + blueprint flip of `lem:removal-deficiency` to green (deficiency
route) + rewrite of `rem:kt-lemma-44` (now "KT 4.4 *is* a deficiency-counting
fact") + return of `lem:forest-surgery-unsplit` to deferred-TODO + *Finding 2
REFUTED* above. KT did not err: KT's `h'=0` unsplit forest-surgery route is a
sound alternative; we simply found a shorter deficiency count.

**Commit E landed.** `lem:dof-tracking` (KT 4.3–4.5 assembly, `Graph.dof_tracking`,
green `\leanok`, axiom-free): a 3-way conjunction over the three green bounds
(`splitOff_deficiency_{le,ge}` + `removeVertex_deficiency_ge`) under
`2 ≤ bodyBarDim n` — `k − 1 ≤ def(G̃ᵥᵃᵇ) ≤ k` and `def(G̃ᵥ) ≥ k` for a
`k`-dof-graph `G`. No new infrastructure (the `1 ≤ bodyBarDim n` the
splitting-off pair wants is derived from `2 ≤` by `le_trans`). Blueprint
`lem:dof-tracking` flipped green with the two-sided statement; the "which
alternative" forest-surgery refinement noted off-critical-path.

**Commit F landed (`circuit_induces_isRigidSubgraph`, KT 3.4 rigid-subgraph form,
the prerequisite for KT 4.6).** Green `\leanok`, axiom-free, `Molecular/Induction.lean`.
Scoping the originally-planned commit F (`lem:reducible-vertex`, KT 4.6) showed it is
2+ commits and rests on a KT 3.4 conclusion never delivered in Lean: the node
`lem:circuit-induces-rigid` *claimed* "G[V(X)] is rigid" but only pinned the tightness
equality. Commit F lands the rigid-subgraph packaging (`(G.inducedSpan n X).IsRigidSubgraph
G n`), pinning `rank M(G[V(X)]̃) = D(|V(X)|−1)` from both sides (`rank_matroidMG_le`
∧ independent `X−e` of tight size via `matroidMG_restrict_mulTilde` +
`subset_edgeSet_mulTilde_inducedSpan`) then `rank_add_deficiency_eq`. Blueprint
`lem:circuit-induces-rigid` `\lean{}` now pins both decls; proof prose + `\uses` updated.

**Commit F′ landed (`no_rigid_edge_count`, KT 4.5(i) edge bound — `lem:no-rigid-edge-count`
GREEN, axiom-free).** The fundamental-circuit swap (KT eq. 4.3) fully formalized: `h* = minₐ
|ẽ∩B|` over bases (finite-min via `Set.exists_min_image` on the finite `{B | IsBase B}`),
`h* ≥ 1` from `hG.2`; `Ẽ∖ẽ ⊆ B*` by the exchange `B = insert f B* ∖ {ej}`
(`IsBase.exchange_isBase_of_indep`, independence via `Indep.mem_fundCircuit_iff`). The prior
`X∩ẽ≠∅` "blocker" dissolved on a clean restatement: it is a **direct base-meets-fiber
contradiction** (if `X∩ẽ=∅`, `X−ej` is independent of full size `D(|V|−1)=|B*|`, hence a
base avoiding `ẽ` — contra `hG.2`), NOT forest reasoning and NOT needing
`rank M(G̃)↾(E(G̃)∖ẽ)`. Base-hood certified via `exists_isBase_superset` +
`Set.eq_of_subset_of_ncard_le`. Final count `|E(G̃)| = |B*| + (|ẽ|−h*) ≤ D(|V|−1)+(D−2)` via
`mulTilde_edgeSet_ncard` + `edgeFiber_ncard`. Needs `2 ≤ bodyBarDim n`.

**Next agent's concrete commit = F″, the second half of `lem:reducible-vertex` (KT 4.6).**
Thm 4.9 consumes only "∃ degree-2 vertex" — the chain/cycle refinement (length-`d`
chain, cycle-of-`≤d`-vertices) is for the §5–6 *algebraic* induction, **off the
Thm-4.9 critical path** (confirmed: KT 4.9's proof says only "G has a vertex of
degree two by Lemma 4.6"). With F′ (the edge bound) now green, the remaining piece is:
- **F″ — multigraph degree theory + ∃-degree-2.** `d_avg = 2|E|/|V| < 2D/(D−1) ≤ 3`
  (using `D ≥ 3`) forces a degree-2 vertex. **The project has no `Graph α β` degree
  function** — degree-2 is encoded ad hoc as `hdeg2 : ∀ e x, IsLink e v x → e = eₐ ∨
  e = e_b`. F″ must build a degree notion (`∑ degree = 2|E|` handshake on the
  multigraph) and the ∃-low-degree pigeonhole; this is genuinely new infrastructure,
  not parked KT Lemma 3.2 (which is the 3-edge-conn refinement, still off-path).
Then commits G (`lem:reduction-step`, KT 4.7–4.8 — circuit-swap minimality transport,
`\uses` `circuit_induces_isRigidSubgraph` for the `X∩ãb=∅ ⟹ proper rigid` step),
H (`thm:minimal-kdof-reduction`, Theorem 4.9 capstone → phase close) per *Replan*.
Degree-2 stays encoded as two edges `eₐ`/`e_b` where the bookkeeping lemmas need it.
