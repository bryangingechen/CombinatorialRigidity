# Phase 20 — Combinatorial induction → Theorem 4.9 (work log)

**Status:** ✓ complete. Capstone `thm:minimal-kdof-reduction` (KT Theorem 4.9,
`Graph.minimal_kdof_reduction`) green, axiom-free; commit H landed 2026-06-03.
Forest-surgery core (KT 4.1, splitting-off direction) is off the critical path but **now
fully formalized** (2026-06-03 addendum, corrected): `lem:forest-surgery-count`
(`Graph.forest_surgery_count`) and `lem:forest-surgery-split` (`Graph.forest_surgery_split`,
`def(G̃ᵥᵃᵇ) ≤ def(G̃)`) are both green `\leanok`, axiom-free — the corrected non-vacuous
construction that replaces and deletes the superseded `c3df62f` over-claim. KT 4.2 (edge-splitting
inverse `lem:forest-surgery-unsplit`) stays deferred (sound, not needed by Thm 4.9). The remaining
addendum item is the narrative-bridge shim (Task #2), explicitly NOT in this commit.
The KT 4.1 balanced-packing gloss is **fully discharged (2026-06-03): a GAP, not an error** —
its counting half (`isBase_vfiber_ncard_ge`), redistribution half
(`acyclicSet_insert_vfiber_of_not_inc`), rebalancing move (`exists_packing_move_of_not_inc`),
and the descent's **outer loop** (`exists_balanced_forest_packing`: a base admits a balanced
`D`-forest packing) are all green, and both reroute acyclicity steps are green — step 1
(`isAcyclicSet_splitOff_of_diff_fiberAtVertex`, the `v`-free part) and step 2
(`isAcyclicSet_splitOff_reroute`, the genuinely-hard `dᶠ(v)=2` cycle-lift). See **## CORRECTION**
below for the now-resolved over-claim history.

## CORRECTION (2026-06-03): the `forest_surgery_split` over-claim, and its repair

**RESOLVED (2026-06-03 addendum).** The corrected surgery is now formalized: `forest_surgery_count`
(the `|⋃ F'ᵢ| + D = |I|` bookkeeping, stated additively to avoid ℕ-subtraction) + `forest_surgery_split`
(`def(G̃ᵥᵃᵇ) ≤ def(G̃)`) are both green, axiom-free, and the vacuous `c3df62f` declaration is deleted.
The history below records the over-claim that this repair corrects.

Commit `c3df62f` flipped `lem:forest-surgery-split` green via `Graph.forest_surgery_split`.

Commit `c3df62f` flipped `lem:forest-surgery-split` green via `Graph.forest_surgery_split`.
**This was an over-claim; the `\leanok` is reverted to red.** Two independent defects, the
first decisive:

1. **The hypotheses are jointly unsatisfiable ⟹ the theorem is vacuous.** `hr_inj` asks for an
   injection `Fin (bodyBarDim n) ↪ {e₀} × Fin (bodyHingeMult n)`, but `bodyHingeMult n =
   bodyBarDim n − 1` (`BodyHinge.lean:147`), so the codomain (`D−1` elements) is strictly
   smaller than the domain (`D`). No such `r` exists; the theorem proves nothing.
2. **It assumes away the `dᶠ(v)=1` forests.** `hreroute` forces every `v`-meeting forest to have
   `v`-degree exactly 2 (a fiber to *both* `a` and `b`). But each `v`-edge has only `D−1`
   fiber-copies in `G̃` (since `G̃ = (D−1)·G`) while there are `D` forests, so at most `D−1`
   forests can be `dᶠ=2`; a balanced packing forces ≥ 1 forest of `dᶠ=1`. KT's own accounting
   `2h′+(D−h′)=h` includes these `D−h′` degree-1 forests.

**The corrected surgery (worked out 2026-06-03; no source supplies it — we reconstruct it).**
A balanced packing's forests are each `dᶠ(v) ∈ {1,2}`. Reroute: a `dᶠ=2` forest swaps its
`a–v–b` path for one `ã̃b`-copy (cycle-lift, `isAcyclicSet_splitOff_reroute`, green); a `dᶠ=1`
forest **drops its lone `v`-fiber and adds no `ã̃b`-copy** (verbatim transport of the `v`-free
part, `isAcyclicSet_splitOff_of_diff_fiberAtVertex`, green). Because the packing is balanced,
**every** forest shrinks by exactly one, so `|I′| = |I| − D`; then `rank M(G̃ᵥᵃᵇ) ≥ rank M(G̃) −
D` and the def\,=\,corank identity (one fewer vertex) gives `def(G̃ᵥᵃᵇ) ≤ def(G̃)`. This is now
**all green**: `lem:reroute-vfree-transport`, `lem:reroute-cycle-lift`, `lem:forest-surgery-count`
(the `|⋃F'ᵢ|+D=|I|` bookkeeping), and `lem:forest-surgery-split` (the def-bound assembly).
`rem:kt-lemma-41` layer (2) records this two-part repair as formalized.

**Formalization notes (2026-06-03 addendum).** The `dᶠ(v)≤2` cap reuses a new plain-`G̃` 2-cycle
lemma `isCycleSet_pair_edgeFiber_mulTilde` + per-edge subsingleton
`fiber_inter_subsingleton_of_isAcyclicSet_mulTilde` (analogues of the `splitOff` versions, applied
to `eₐ` and `e_b` separately). The fresh `ã̃b`-copies are chosen as `r i = (e₀, (paOf i).2)` where
`paOf i` is the unique `eₐ`-copy of a `dᶠ=2` forest — distinct second coordinates across disjoint
forests give injectivity for free (no global pigeonhole). `exists_balanced_forest_packing` was
strengthened to also export pairwise-disjointness of the packing (threaded through its descent
induction already; only the `suffices`/conclusion shapes needed the extra conjunct), which
`forest_surgery_count` consumes for the additive count.

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

**Progress (2026-06-03): the COUNTING HALF of the balanced packing is proven.**
`Graph.isBase_vfiber_ncard_ge` (green `\leanok`, axiom-free, `Molecular/Induction.lean`;
blueprint node `lem:base-vfiber-count`): every base `B` of `M(G̃)` contains
**at least `D`** of the `2(D−1)` fibers at the degree-2 vertex `v`
(`D ≤ |B ∩ (ẽₐ ∪ ẽ_b)|`, needs `2 ≤ bodyBarDim n`). A rank count on green
infrastructure, **not** a forest reroute: `B ∖ vfibers ⊆ E(G̃ᵥ)` is independent
in `M(G̃ᵥ) = M(G̃)↾E(G̃ᵥ)` (`matroidMG_restrict_mulTilde`), so
`|B∖vfib| ≤ rank M(G̃ᵥ)`; the def\,=\,corank bridge turns
`|B∩vfib| = |B| − |B∖vfib|` into `≥ D + (def(G̃ᵥ) − def(G̃)) ≥ D` via the green
`removeVertex_deficiency_ge` (KT 4.4). **Significance:** this discharges the
pure-cardinality content KT's Lemma 4.1 base-case proof glosses — the
pigeonhole obstruction "`h < D`" of *Finding* layer 2 **cannot arise**, since
a base always has ≥ D `v`-fibers available.

**VERDICT (2026-06-03): the REDISTRIBUTION question is resolved POSITIVELY for all `D` —
KT Lemma 4.1's gloss is a GAP, not an error.** The redistribution residue ("given ≥ D
`v`-fibers, each forest holding ≤ 1 `va`-copy and ≤ 1 `vb`-copy, can the `D` forests be
rechosen so each meets `v`?") was thought open for `D ≥ 3`. It is **not** open: the
mechanism turns on `v` having **degree 2**, so a forest avoiding `v` has `v` *isolated*,
and a free `v`-fiber `x : v—w` (`w ≠ v`) is then a **pendant** edge of that forest — its
`v`-endpoint has degree 1 — hence a bridge, and adding a bridge to a forest keeps it a
forest. So any `v`-avoiding forest absorbs any free `v`-fiber, and a finite descent (move
a `v`-fiber from a forest holding two into a `v`-avoiding one; the pigeonhole donor always
exists since ≥ D fibers sit in < D non-empty forests) makes every forest meet `v`. There
is **no `D ≥ 3` counterexample**; the earlier "`D = 2` balanced, `D ≥ 3` open" framing was
too pessimistic — degree-2 makes all `D` uniform. The load-bearing kernel is formalized:
`Graph.acyclicSet_insert_vfiber_of_not_inc` (green `\leanok`, axiom-free; blueprint node
`lem:acyclic-insert-vfiber`): a `cycleMatroid`-independent fiber set avoiding `v` stays
independent after inserting a non-loop `v`-fiber. Proof via `cycleMatroid_indep` →
`IsAcyclicSet` → `IsForest.of_deleteEdges_singleton` with `x` a bridge
(`IsLink.isBridge_iff_not_connBetween` + `v` isolated in the deletion via
`Isolated.connBetween_iff_eq`). The descent's **load-bearing assembly step is now formalized
too** (2026-06-03): `Graph.exists_packing_move_of_not_inc` (green `\leanok`, axiom-free;
blueprint node `lem:packing-move`) — *one rebalancing move*. Given a forest packing
`Fs : Fin D → Set _` covering `I`, a `v`-avoiding forest `Fs j`, and a `v`-fiber `x ∈ I`,
the re-choice `Fs' j = insert x (Fs j)`, `Fs' i = Fs i ∖ {x}` (`i ≠ j`) is again a packing
covering `I` (recipient acyclic via the kernel, donors acyclic as subsets, union unchanged
since `x ∈ I` is re-added at `j`), and `Fs' j` now meets `v`. **The descent's outer loop is now
formalized too (2026-06-03):** `Graph.exists_balanced_forest_packing` (green `\leanok`, axiom-free;
blueprint node `lem:balanced-forest-packing`) — a base `B` of `M(G̃)` admits a `D`-forest packing with
**every** forest meeting `v`. Runs on a *disjointified* packing (mathlib `disjointed` over `Fin D`,
`iUnion_disjointed` + `disjoint_disjointed`); disjointness is the device handling the hand-off's
disjointness caveat — when a `v`-fiber moves into `Fs j` it leaves every other forest, and
disjointness means exactly one donor held it. Strong induction on the count of `v`-avoiding forests
(via a `≤ m` bound); the pigeonhole (`≥ D` `v`-fibers partitioned among `≤ D−1` non-`j` forests ⟹ some
forest holds `≥ 2`) keeps the move strictly safe (donor keeps a `v`-fiber). **The only remaining piece
toward `lem:forest-surgery-split` itself is the final wiring** — rerouting the balanced packing of `G̃`
across `v` to produce the `G̃ᵥᵃᵇ` packing (reroute-acyclicity substrate already landed). Off the
Theorem-4.9 critical path. **[Update — RESOLVED: the corrected count + assembly
(`lem:forest-surgery-count` → `lem:forest-surgery-split`) are now both green, axiom-free, and the
vacuous `c3df62f` declaration is deleted. See the ## CORRECTION header.]**

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

**Commit G step 2 landed (splitting-off minimality transport, KT 4.8(i), 2026-06-03):**
`Graph.splitOff_isMinimalKDof` (green `\leanok`, axiom-free) — for a minimal `0`-dof-graph `G`
with no proper rigid subgraph and a degree-2 vertex `v` (`e₀` fresh), `G_v^{ab}` is minimal
`0`-dof. The `lem:reduction-step` splitting-off branch is now done (contraction branch was
already `contraction_isMinimalKDof`); the blueprint node carries both `\lean{}` pins, staying
red until `thm:minimal-kdof-reduction` (commit H) ties measure + branches together.
**The Finding ("base correspondence must be built by hand, no matroid minor") was right that
there is no minor, but KT's iterated fundamental-circuit swap is BYPASSED entirely by a rank
count** — see the `lem:reduction-step` checklist entry + FRICTION (`[matroid] Transporting
circuits between M(G̃) and M(H̃)…`). Support lemma `Graph.circuit_splitOff_meets_fiber` (KT's
claim (4.10), = `E(G̃_v)` circuit-free in `M(G̃_v^{ab})`); ground-set bridge
`edgeSet_mulTilde_splitOff_diff_fiber` (`E(G̃_v^{ab})∖ã̃b = E(G̃_v)`, landed commit G step 2a).
Needs `2 ≤ bodyBarDim n`. The KT 4.8(ii) `k>0` branch is off the Theorem-4.9 critical path.

**Commit G step 1 landed (`lem:reduction-measure`, 2026-06-03):** both reduction operations
strictly shrink `|V|` (`Graph.splitOff_vertexSet_ncard_lt`,
`Graph.rigidContract_vertexSet_ncard_lt`; the latter needs `2 ≤ |V(H)|`), green `\leanok`,
axiom-free — the well-founded measure for Theorem 4.9's `|V|`-induction. Residual of commit G
is the `lem:reduction-step` splitting-off minimality transport (no matroid-minor shortcut; see
*Hand-off*); the contraction branch is already `contraction_isMinimalKDof`.

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

**Off the critical path (forest surgery, now fully formalized — *Replan* Step 5):** the
forest-surgery substrate landed for `lem:forest-surgery-split` (which is now GREEN,
2026-06-03 addendum, along with `lem:forest-surgery-count`) — incidence/cardinality
(`edgeFiber_ncard`, `edgeSet_splitOff`,
`edgeFiber_subset_edgeSet_mulTilde_splitOff`), degree-at-`v` (`fiberAtVertex`,
`mulTilde_inc`, `fiberAtVertex_inter_edgeSet[_ncard]`, `fiberDegree`,
`fiberDegree_{mono,le}`), both no-reroute acyclicity directions
(`mulTilde_splitOff_deleteFiber_le` +
`isAcyclicSet_mulTilde_of_splitOff_of_disjoint`;
`mulTilde_removeVertex_le_splitOff` +
`isAcyclicSet_mulTilde_splitOff_of_removeVertex`), and the reroute count cap
(`isCycleSet_pair_edgeFiber_splitOff`,
`fiber_inter_subsingleton_of_isAcyclicSet_splitOff`). The balanced-packing assembly is now
**fully landed**: counting half `isBase_vfiber_ncard_ge`, redistribution kernel
`acyclicSet_insert_vfiber_of_not_inc`, the descent's rebalancing move
`exists_packing_move_of_not_inc` (`lem:packing-move`), and the descent's **outer loop**
`exists_balanced_forest_packing` (`lem:balanced-forest-packing`: a base admits a `D`-forest
packing meeting `v` everywhere) are all green `\leanok` blueprint nodes. **Both reroute wiring
steps now landed**: step 1 `isAcyclicSet_splitOff_of_diff_fiberAtVertex` (the `v`-free part of a
`G̃`-forest transports verbatim into `G̃ᵥᵃᵇ`); step 2 `isAcyclicSet_splitOff_reroute`
(2026-06-03, green, axiom-free) — the `dᶠ(v)=2` forest's `ã̃b`-swap cycle-lift, the genuinely-hard
step. A `G̃ᵥᵃᵇ`-cycle through the inserted short-circuit copy `r` is rotated so `r` is first,
then `r` (joining `a,b`) is substituted by the `v`-traversing 2-path `a—pa—v—pb—b` of `G̃`, giving
a closed `G̃`-trail inside `F` that contains a `G̃`-cycle (`IsTour.exists_isCyclicWalk`),
contradicting `F`'s acyclicity. **The per-`D`-forest assembly is now done (2026-06-03 addendum):**
`lem:forest-surgery-count` (`Graph.forest_surgery_count`, the `|⋃F'ᵢ|+D=|I|` count, handling `dᶠ=1`
forests by dropping their `v`-fiber with no copy) and `lem:forest-surgery-split`
(`Graph.forest_surgery_split`, the `def(G̃ᵥᵃᵇ) ≤ def(G̃)` read-off) are both green, axiom-free; the
vacuous `c3df62f` declaration is deleted. The two acyclicity steps above (step 1, step 2)
are reused by the corrected surgery. None of this is needed for Theorem 4.9. (The step-1/step-2/cap
substrate lemmas are not blueprint nodes; the two reroute steps are now promoted to nodes
`lem:reroute-vfree-transport` / `lem:reroute-cycle-lift`.)

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

**Commit F″-core landed (`exists_degree_le_two`, KT 4.6 average-degree core; `lem:low-degree-vertex`
GREEN, axiom-free).** ∃ a degree-`≤ 2` vertex in a minimal 0-dof-graph with no proper rigid
subgraph (`3 ≤ bodyBarDim n`): the average-degree count `2|E| < 3|V|` + the handshake
`∑ deg = 2|E|` + a Finset pigeonhole. **Finding:** the multigraph degree + handshake already
exist in the **vendored `apnelson1/Matroid`** package (transitively imported); no new degree
infrastructure was built. See *Hand-off* + FRICTION. Needs `3 ≤ bodyBarDim n` (stronger than
the `2 ≤` elsewhere — the pigeonhole needs `2D ≤ 3(D−1)`).

**Commit F‴ landed (`exists_degree_eq_two`, KT 4.6 degree-`=`-2 upgrade; `lem:reducible-vertex`
GREEN, axiom-free).** ∃ a vertex of multigraph degree *exactly* 2 (`3 ≤ bodyBarDim n`, `|V| ≥ 2`):
the F″ core gives `≤ 2`; two-edge-connectivity (`two_le_crossingEdges_of_isKDof_zero`, KT 3.1)
rules out `≤ 1`. The cut↔degree bridge (the predicted only-new-piece, clean): the crossing edges
of the single-vertex cut `{v}` are exactly the *nonloop* edges at `v` (an edge crosses iff exactly
one endpoint is `v`), so `degree v ≥ d_G({v}) ≥ 2` via vendored `Graph.degree_eq_ncard_add_ncard`
(`degree = 2·loops + nonloops`). Support: `crossingEdges_cutLabeling_singleton_{subset,ncard_le}`.

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
- [x] `lem:low-degree-vertex` — KT 4.6 **F″ core**, `Graph.exists_degree_le_two`
  (green `\leanok`, axiom-free): a minimal 0-dof-graph with no proper rigid subgraph and
  `3 ≤ bodyBarDim n` has a vertex of multigraph degree `≤ 2`. The average-degree count
  `2|E| < 3|V|` (from `no_rigid_edge_count` ×2, cancelling `3(D−1)|V|` with `D ≥ 3`,
  `|V| ≥ 1`) + the handshake `∑ deg = 2|E|` + a Finset pigeonhole
  (`Finset.exists_lt_of_sum_lt`). **Key finding:** the multigraph degree + handshake
  already exist in the **vendored `apnelson1/Matroid`** package
  (`Graph.degree`/`eDegree`/`incFun`/`handshake_degree_subtype`,
  `.lake/packages/Matroid/Matroid/Graph/Degree/Basic.lean`), transitively imported — the
  hand-off's "project has no degree function" was stale. No new degree infrastructure was
  built; see FRICTION `[resolved] [matroid] The vendored … package already supplies a full
  multigraph Graph.degree …`. Needs `3 ≤ bodyBarDim n` (`d ≥ 2`; stronger than the `2 ≤`
  elsewhere — the pigeonhole needs `2D ≤ 3(D−1)`).
- [x] `lem:reducible-vertex` — KT 4.6, existence of a degree-`exactly`-2 vertex in a
  minimal 0-dof-graph with no proper rigid subgraph, `|V| ≥ 2`, `3 ≤ bodyBarDim n`.
  **LANDED** (`Graph.exists_degree_eq_two`, green `\leanok`, axiom-free). Scope: Thm 4.9
  consumes only "∃ degree-2 vertex" (the chain/cycle refinement is §5–6 *algebraic*, off
  the Thm-4.9 critical path; reducibility-preserves-minimality is `lem:reduction-step`,
  commit G). The `≤ 2` → `= 2` upgrade is the F″ core (`exists_degree_le_two`, ∃-degree-≤-2)
  plus two-edge-connectivity (`two_le_crossingEdges_of_isKDof_zero`, KT 3.1, green) ruling
  out degree `≤ 1`. **Cut↔degree bridge** (the only new piece, as predicted): the crossing
  edges of the single-vertex cut `{v}` are exactly the *nonloop* edges at `v` (an edge
  crosses iff exactly one endpoint is `v`), so `degree v ≥ d_G({v}) ≥ 2` via the vendored
  `Graph.degree_eq_ncard_add_ncard` (`degree = 2·loops + nonloops`). Two support lemmas:
  `crossingEdges_cutLabeling_singleton_subset` (⊆ nonloops) +
  `crossingEdges_cutLabeling_singleton_ncard_le` (count ≤ degree). FRICTION: a lemma whose
  statement mentions `cutLabeling V'` needs `[∀ x, Decidable (x ∈ V')]` in the binder list.
  (Degree-2 stays encoded ad hoc as `eₐ`/`e_b` in the splitting-off bookkeeping; this node
  is the *existence* of such a vertex.)
- [x] `lem:reduction-measure` — KT Thm 4.9 well-founded measure (commit G, step 1).
  **LANDED**, green `\leanok`, axiom-free: both reductions strictly shrink `|V|`.
  `Graph.splitOff_vertexSet_ncard_lt` (`|V(G_v^{ab})| < |V(G)|` from `V = V(G)∖{v}`,
  one-liner via `Set.ncard_diff_singleton_lt_of_mem`) and
  `Graph.rigidContract_vertexSet_ncard_lt` (`|V(G/E(H))| < |V(G)|` *needs `2 ≤ |V(H)|`* —
  collapsing a single-vertex `H` is a vertex no-op; the `collapseTo` image lands in
  `(V(G)∖V(H)) ∪ {r}`). Consumed by `thm:minimal-kdof-reduction`'s induction on `|V|`.
- [x] `lem:reduction-step` — KT 4.7–4.8, reduction preserves minimality. Replan commit G.
  **Node green** (both `\lean{}` pins): splitting-off branch `Graph.splitOff_isMinimalKDof`,
  contraction branch `Graph.contraction_isMinimalKDof`. Flipped `\leanok` at commit H, when
  `thm:minimal-kdof-reduction` tied measure + branches together.
  **Splitting-off branch LANDED (2026-06-03), `k=0`:** `Graph.splitOff_isMinimalKDof` (green
  `\leanok`, axiom-free) — `G` minimal `0`-dof + no proper rigid + `v` degree-2 + `e₀` fresh ⟹
  `G_v^{ab}` minimal `0`-dof. Contraction branch is already `contraction_isMinimalKDof`. Node
  carries both `\lean{}` pins; stays **red** until `thm:minimal-kdof-reduction` (commit H)
  assembles the measure + both branches into the Theorem-4.9 step.
  **Key finding — the iterated swap is BYPASSED by a rank count.** KT 4.8(i) proves minimality
  via an iterated fundamental-circuit swap (relocate each `ã̃b` copy onto an `ẽ` copy, induction
  on `|B₁∩ã̃b|`). That induction is unnecessary: KT's claim (4.10) — every circuit of
  `M(G̃_v^{ab})` meets `ã̃b` — is exactly "`E(G̃_v)` is independent (circuit-free) in
  `M(G̃_v^{ab})`", landed as `Graph.circuit_splitOff_meets_fiber` (a circuit avoiding `ã̃b` is a
  circuit of `M(G̃)` avoiding `v`, inducing a proper rigid subgraph via
  `circuit_induces_isRigidSubgraph`). So `E(G̃_v)` is a *base* of `M(G̃_v)`; with KT 4.7
  (`def(G̃_v)>0`: `G_v ≤ G` proper ⟹ not rigid) a single cardinality split of any fiber-avoiding
  base `B'` across `ã̃b ⊔ E(G̃_v)` gives `|B'| ≤ |E(G̃_v)|`, forcing `def(G̃_v) ≤ 0` through
  `isBase_ncard_add_deficiency_eq` — contradiction. No matroid minor, no swap induction, no
  forest reasoning; needs `2 ≤ bodyBarDim n`. Circuit-transport idiom + swap-bypass lesson in
  FRICTION (`[matroid] Transporting circuits between M(G̃) and M(H̃)…`). The ground-set bridge
  `edgeSet_mulTilde_splitOff_diff_fiber` (`E(G̃_v^{ab})∖ã̃b = E(G̃_v)`) is the substrate it runs on.
  **`k>0` branch (KT 4.8(ii), `G_v^{ab}` minimal `(k−1)`-dof)** is *not* needed by Theorem 4.9
  (minimally body-hinge rigid = minimal `0`-dof) — off the critical path, omitted.
- [x] `thm:minimal-kdof-reduction` — KT Theorem 4.9 (capstone; phase close, commit H,
  2026-06-03). **LANDED** `Graph.minimal_kdof_reduction`, green `\leanok`, axiom-free.
  Stated as the well-founded **induction principle** the reduction dichotomy + the `|V|`
  measure (`lem:reduction-measure`) drive: a motive `P` closed under the two-vertex base case
  (`hbase`), under splitting off a reducible degree-2 vertex (`hsplit`), and under contracting
  a proper rigid subgraph *given the strong IH on every smaller minimal `0`-dof-graph*
  (`hcontract`) holds of every minimal `0`-dof-graph with `2 ≤ |V|`. Proof: strong induction on
  `|V|` (`induction hN : V(G).ncard using Nat.strong_induction_on generalizing G`, idiom lifted
  to TACTICS-GOLF §11); base `|V|=2`; for `|V|≥3`, dichotomy on `∃` proper rigid subgraph —
  Case I hands `hcontract` the existence + IH, Case II (`exists_degree_eq_two`) splits off via
  `splitOff_isMinimalKDof` and recurses on the smaller `splitOff` (`splitOff_vertexSet_ncard_lt`).
  **Two scope decisions** (both honest, both in the doc-comment): (i) the **contraction branch is
  handed the IH rather than recursing internally** — bridging matroid-side `contraction_isMinimalKDof`
  to a graph-level `(rigidContract).IsMinimalKDof` is the graph↔matroid map Phase 20 deliberately
  did not build, and a single-vertex subgraph is vacuously rigid so the predicate alone doesn't
  force the measure to drop; the splitting-off branch, fully graph-level, recurses internally.
  (ii) An explicit **freshness premise** `hfresh : ∀ G', ∃ e₀ ∉ E(G')` supplies the fresh
  short-circuit edge each `splitOff` injects (`[Finite β]` would otherwise exhaust `β`). New
  support: `exists_splitOff_data_of_degree_eq_two` (the degree↔edges bridge — `degree v = 2` ⟹
  two distinct *nonloop* edges at `v`, the single-loop case ruled out by `0`-dof
  two-edge-connectivity, far endpoints `a,b` and the `hdeg2` closure). Needs `3 ≤ bodyBarDim n`.

Forest surgery (**DEFERRED — off critical path, TODO per Replan Step 5**):
- [x] `lem:forest-packing-decomp` — framing sub-node of KT 4.1/4.2:
  `I` independent in `M(G̃)` ⟺ covered by `D` cycle-matroid-independent fiber
  sets. `Graph.matroidMG_indep_iff_exists_forest_packing`. Green and still
  generally useful (and `def:matroid-MG`'s union form is the engine of the
  deficiency route too).
- [x] `lem:forest-surgery-count` — KT 4.1 surgery count (2026-06-03 addendum, GREEN).
  `Graph.forest_surgery_count` (green `\leanok`, axiom-free): a *balanced* edge-disjoint forest
  packing of a base `I` reroutes into a `D`-forest packing of `G̃ᵥᵃᵇ`, `M(G̃ᵥᵃᵇ)`-independent, with
  `|⋃F'ᵢ| + D = |I|` (stated additively to avoid ℕ-subtraction). Every forest has `dᶠ(v) ∈ {1,2}`
  (≥1 balance, ≤2 via new plain-`G̃` per-edge subsingleton `fiber_inter_subsingleton_of_isAcyclicSet_mulTilde`
  on `eₐ`/`e_b` separately), so each shrinks by exactly one. The `dᶠ=2` reroute uses
  `isAcyclicSet_splitOff_reroute`; the `dᶠ=1` (and `v`-free core) uses
  `isAcyclicSet_splitOff_of_diff_fiberAtVertex`. Fresh copies `r i = (e₀, (paOf i).2)` (the unique
  `eₐ`-copy's index) are distinct across disjoint `dᶠ=2` forests — no global pigeonhole.
- [x] `lem:forest-surgery-split` — KT 4.1, splitting-off direction (2026-06-03 addendum, GREEN).
  `Graph.forest_surgery_split` (green `\leanok`, axiom-free): `def(G̃ᵥᵃᵇ) ≤ def(G̃)`. The corrected
  non-vacuous construction replacing/deleting the over-claimed `c3df62f` (which was vacuous —
  `hr_inj : Fin D ↪ {e₀}×Fin(D−1)` unsatisfiable — and assumed away `dᶠ(v)=1` forests). Take a base
  `B` of `M(G̃)` (`Matroid.exists_isBase`), its balanced packing
  (`exists_balanced_forest_packing`, now also exporting pairwise-disjointness), reroute
  (`forest_surgery_count`): `rank M(G̃ᵥᵃᵇ) ≥ |B|−D`, and the def\,=\,corank identity (one fewer
  vertex, `rank_add_deficiency_eq` + `isBase_ncard_add_deficiency_eq`) gives the bound by `linarith`.
  Same conclusion as the green `splitOff_deficiency_le` (deficiency route). Off the Theorem-4.9
  critical path. Substrate (still retained)
  landed (`edgeFiber_ncard`, `edgeSet_splitOff`,
  `edgeFiber_subset_edgeSet_mulTilde_splitOff`; degree substrate
  `fiberAtVertex` / `mulTilde_inc` / `fiberAtVertex_inter_edgeSet[_ncard]` /
  `fiberDegree` / `fiberDegree_{mono,le}`; both no-reroute acyclicity
  directions; reroute count cap `isCycleSet_pair_edgeFiber_splitOff` /
  `fiber_inter_subsingleton_of_isAcyclicSet_splitOff`). **Balanced-packing assumption
  now fully settled (2026-06-03) — KT 4.1's gloss is a GAP, not an error.** Counting half:
  `lem:base-vfiber-count` / `Graph.isBase_vfiber_ncard_ge` (a base meets ≥ D of `v`'s
  fibers, no pigeonhole obstruction). Redistribution half: `lem:acyclic-insert-vfiber` /
  `Graph.acyclicSet_insert_vfiber_of_not_inc` (a `v`-avoiding forest absorbs a free
  `v`-fiber as a pendant — `v` deg 2 ⟹ `v` isolated ⟹ the fiber is a bridge). The descent's
  load-bearing **rebalancing move** is also green: `lem:packing-move` /
  `Graph.exists_packing_move_of_not_inc` (one move preserves the cover + independence and
  lands `x ∈ Fs' j`). The descent's **outer loop** is now green too: `lem:balanced-forest-packing` /
  `Graph.exists_balanced_forest_packing` (a base admits a `D`-forest packing with every forest
  meeting `v`). All four green `\leanok`, axiom-free — the balanced-packing assumption is **fully
  discharged**. **Both reroute wiring steps now landed (2026-06-03):** step 1
  `Graph.isAcyclicSet_splitOff_of_diff_fiberAtVertex` (green, axiom-free) — the `v`-free part
  `F ∖ fiberAtVertex v` of a `G̃`-forest transports verbatim into `G̃ᵥᵃᵇ` (the fibers KT's surgery
  keeps untouched), via `IsAcyclicSet.anti_inter` along `(G_v)̃ ≤ G̃` then
  `isAcyclicSet_mulTilde_splitOff_of_removeVertex`; step 2 `Graph.isAcyclicSet_splitOff_reroute`
  (green, axiom-free) — the genuinely-hard `dᶠ(v)=2` cycle-lift. The `dᶠ(v)=2` forest swaps its two
  `v`-edges `pa,pb` for one short-circuit copy `r`; the result stays acyclic because a `G̃ᵥᵃᵇ`-cycle
  through `r` rotates so `r` is first (`WList.exists_rotate_firstEdge_eq`), substitutes `r` (joining
  `a,b`) by the `v`-traversing 2-path `a—pa—v—pb—b` of `G̃` (the surviving `w'` lifts to `G̃` via
  `mulTilde_splitOff_deleteFiber_le`), giving a closed `G̃`-trail inside `F` that contains a
  `G̃`-cycle (`IsTour.exists_isCyclicWalk` + `IsSublist.edge_subset`) — contradiction. The
  per-`D`-forest **bookkeeping assembly** that stitches these two maps over all forests into a
  `G̃ᵥᵃᵇ` packing and reads off the deficiency relation is `Graph.forest_surgery_split`
  (the node, now green; see the `lem:forest-surgery-split` checklist entry above). Off the
  Thm-4.9 critical path. FRICTION (`[matroid] Cycle-lift by edge-substitution…`)
  / TACTICS-QUIRKS § 29. See the *TODO* Progress *VERDICT* note + *Hand-off*.
- [x] `lem:balanced-forest-packing` — the repacking descent's **outer loop**
  (`Graph.exists_balanced_forest_packing`, green `\leanok`, axiom-free): a base `B` of `M(G̃)` admits
  a `D`-forest packing with every forest meeting the degree-2 vertex `v`. Disjointify the
  `matroidMG_indep_iff_exists_forest_packing` cover (mathlib `disjointed` over `Fin D`), then strong
  induction on the `v`-avoiding-forest count: pigeonhole (`isBase_vfiber_ncard_ge` gives `≥ D` `v`-fibers
  partitioned among `≤ D−1` non-`j` forests ⟹ a donor with `≥ 2`) + the move (`exists_packing_move_of_not_inc`)
  + disjointness (the move leaves exactly one donor) keep the count strictly decreasing. Closes the
  balanced-packing assumption KT 4.1 glosses (GAP, not error). FRICTION: `Set.ncard_iUnion_of_finite`
  returns `∑ᶠ`, bridge via `finsum_eq_sum_of_fintype`.
- [x] `lem:base-vfiber-count` — counting half of the balanced-packing assumption
  (`Graph.isBase_vfiber_ncard_ge`, green `\leanok`, axiom-free): every base of
  `M(G̃)` contains ≥ D = `bodyBarDim n` of the `2(D−1)` fibers at a degree-2
  vertex `v` (`2 ≤ bodyBarDim n`). Rank count on green infrastructure
  (`matroidMG_restrict_mulTilde` + `isBase_ncard_add_deficiency_eq` /
  `rank_add_deficiency_eq` + `removeVertex_deficiency_ge`), not a forest reroute.
  Reduces `lem:forest-surgery-split`'s gating assumption to pure redistribution.
- [x] `lem:acyclic-insert-vfiber` — redistribution half of the balanced-packing
  assumption (`Graph.acyclicSet_insert_vfiber_of_not_inc`, green `\leanok`, axiom-free):
  a `cycleMatroid`-independent fiber set `F` avoiding `v` stays independent after inserting
  a non-loop `v`-fiber `x : v—w` (`w ≠ v`). Because `v` has degree 2, a `v`-avoiding forest
  has `v` isolated, so `x` is a *pendant* (bridge) of `F ∪ {x}` and acyclicity is preserved.
  Resolves the redistribution residue POSITIVELY for all `D` (no `D ≥ 3` counterexample) ⟹
  KT 4.1's gloss is a GAP, not an error. Proof: `cycleMatroid_indep` → `isAcyclicSet_iff`
  → `IsForest.of_deleteEdges_singleton` (vendored `Matroid` pkg) with `x` a bridge via
  `IsLink.isBridge_iff_not_connBetween` + `Isolated.connBetween_iff_eq`.
- [x] `lem:packing-move` — the descent's load-bearing rebalancing step
  (`Graph.exists_packing_move_of_not_inc`, green `\leanok`, axiom-free): for a forest packing
  `Fs : Fin D → Set _` covering `I`, a `v`-avoiding forest `Fs j`, and a `v`-fiber `x ∈ I`,
  the re-choice `Fs' j = insert x (Fs j)`, `Fs' i = Fs i ∖ {x}` (`i ≠ j`) is again a packing
  covering `I` with `x ∈ Fs' j`. Recipient acyclic via `acyclicSet_insert_vfiber_of_not_inc`,
  donors via `Indep.subset diff_subset`, union unchanged (`x ∈ I` re-added at `j`). The single
  step the descent's outer loop iterates. FRICTION/TACTICS-QUIRKS § 28 (`↓reduceIte` vs
  `if_pos rfl` on the beta-redex'd `(fun i ↦ if i = j then …) j` goal).
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
- **[resolved, non-blocking] KT 4.1 balanced-packing (the *Finding*).** Is a base of
  `M(G̃)` always partitionable into `D` forests each meeting the degree-2 vertex `v`?
  **YES — proven in both halves (2026-06-03), so KT's Lemma 4.1 gloss is a GAP, not an
  error.** Counting half `isBase_vfiber_ncard_ge` (a base meets ≥ D fibers, no pigeonhole),
  redistribution half `acyclicSet_insert_vfiber_of_not_inc` (a `v`-avoiding forest absorbs
  a free `v`-fiber as a pendant — `v` deg 2 makes `v` isolated). No `D ≥ 3` counterexample.
  The descent's load-bearing rebalancing move is also green (`exists_packing_move_of_not_inc`,
  `lem:packing-move`). Only the descent's *outer loop* (pigeonhole + WF measure) remains; off
  the Theorem-4.9 critical path. See *TODO* Progress *VERDICT*.
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

**Commit F″-core landed (`exists_degree_le_two`, KT 4.6 average-degree core; `lem:low-degree-vertex`
GREEN, axiom-free).** ∃ a vertex of multigraph degree `≤ 2` in a minimal 0-dof-graph with no
proper rigid subgraph (`3 ≤ bodyBarDim n`): `2|E| < 3|V|` (from `no_rigid_edge_count` ×2,
cancelling `3(D−1)|V|` with `D ≥ 3`) + the handshake `∑ deg = 2|E|` + Finset pigeonhole
(`Finset.exists_lt_of_sum_lt`). **Finding (corrected the hand-off):** the multigraph degree
and handshake are **already in the vendored `apnelson1/Matroid`** package
(`Graph.degree`/`eDegree`/`incFun`/`handshake_degree_subtype`,
`.lake/packages/Matroid/Matroid/Graph/Degree/Basic.lean`), transitively imported — the prior
"the project has no `Graph α β` degree function" was stale. No new degree infrastructure was
needed; F″ reduced to the pigeonhole on top. FRICTION entry filed (grep `.lake/packages/Matroid`
before building any `Graph α β` graph-theory notion).

**Commit F‴ landed (`exists_degree_eq_two`, KT 4.6 degree-`=`-2 upgrade; `lem:reducible-vertex`
GREEN, axiom-free).** ∃ a vertex of multigraph degree *exactly* 2 in a minimal 0-dof-graph with
no proper rigid subgraph (`3 ≤ bodyBarDim n`, `|V| ≥ 2`). The `≤ 2` half is the F″ core
(`exists_degree_le_two`); the `= 2` upgrade is two-edge-connectivity
(`two_le_crossingEdges_of_isKDof_zero`, KT 3.1, green) ruling out degree `≤ 1`. The **cut↔degree
bridge** (the predicted only-new-piece) turned out clean: the crossing edges of the single-vertex
cut `{v}` are exactly the *nonloop* edges at `v` (an edge crosses `{v}` iff exactly one endpoint
is `v`), and the vendored `Graph.degree_eq_ncard_add_ncard` (`degree = 2·loops + nonloops`) gives
`degree v ≥ d_G({v}) ≥ 2`. Two support lemmas (`crossingEdges_cutLabeling_singleton_subset` /
`_ncard_le`). FRICTION filed (`cutLabeling V'`-in-statement needs `[∀ x, Decidable (x ∈ V')]`).

**Commit G step 1 landed (`lem:reduction-measure`, KT Thm 4.9 well-founded measure).** Green
`\leanok`, axiom-free, `Molecular/Induction.lean`: both reductions strictly shrink `|V|`
(`Graph.splitOff_vertexSet_ncard_lt` clean one-liner; `Graph.rigidContract_vertexSet_ncard_lt`
*needs `2 ≤ |V(H)|`*, the genuine requirement — collapsing a single-vertex `H` is a vertex
no-op). This is the induction measure `thm:minimal-kdof-reduction` consumes. **Finding (records
on the residual):** there is **no clean matroid minor** relating `M(G̃_v^{ab})` to `M(G̃)` — the
splitting-off injects a fresh `e₀`-fiber and drops the `v`-incident `eₐ`/`e_b` fibers, so it is
neither a deletion nor a contraction of `M(G̃)`; KT 4.7–4.8's base correspondence must be built
by hand (unlike the contraction branch, which IS a matroid contraction and is already
`contraction_isMinimalKDof`).

**Commit G step 2 landed (2026-06-03): splitting-off minimality transport, KT 4.8(i).**
`Graph.splitOff_isMinimalKDof` (green `\leanok`, axiom-free, `Molecular/Induction.lean`) — a
minimal `0`-dof-graph with no proper rigid subgraph stays minimal `0`-dof after splitting off a
degree-2 vertex. **KT's iterated fundamental-circuit swap was bypassed by a rank count** (the
genuine win this session): claim (4.10) = "`E(G̃_v)` is circuit-free in `M(G̃_v^{ab})`"
(`Graph.circuit_splitOff_meets_fiber`) makes `E(G̃_v)` a base of `M(G̃_v)`, and a single
cardinality split of any fiber-avoiding base across `ã̃b ⊔ E(G̃_v)` contradicts KT 4.7
(`def(G̃_v)>0`) through `isBase_ncard_add_deficiency_eq`. No matroid minor (the Finding's
"by hand" was right), no swap induction, no forest reasoning. Both `lem:reduction-step` branches
are now landed (contraction = `contraction_isMinimalKDof`); the node carries both `\lean{}` pins
and stays red until commit H. The `k>0` branch (KT 4.8(ii)) is off the Theorem-4.9 critical path.

**Commit H landed (2026-06-03) → Phase 20 complete.** `thm:minimal-kdof-reduction` (KT Theorem
4.9, `Graph.minimal_kdof_reduction`) is green, axiom-free, stated as the well-founded induction
principle the dichotomy + `|V|` measure drive (see its checklist entry for the full shape, the
two scope decisions, and the `exists_splitOff_data_of_degree_eq_two` degree↔edges bridge). The
`induction-on-a-derived-measure` idiom was lifted to TACTICS-GOLF §11. Blueprint
`thm:minimal-kdof-reduction` and `lem:reduction-step` both flipped green; status surfaces
(README, `home_page/index.md`, `intro.tex`) synced to Phase 20 ✓.

**Next phase = Phase 21 (algebraic induction, KT §5–6).** Theorem 4.9 is the *combinatorial*
skeleton; Phase 21 realizes it at the rigidity-matrix rank (the algebraic-induction base +
Cases I & II) — see `notes/MolecularConjecture.md` *Phase 21* and `ROADMAP.md` §21 (planning).
The first concrete Phase-21 commit creates `notes/Phase21.md` + opens the Phase-21 blueprint
chapter (forward-mode). **Two Phase-20 carry-forwards**, both off the Theorem-4.9 critical path,
to schedule as Phase 21 needs them:

1. **Graph↔matroid contraction bridge.** `minimal_kdof_reduction`'s contraction branch is handed
   the IH rather than recursing internally, because `(G.rigidContract H r).IsMinimalKDof` is not
   yet derived from matroid-side `contraction_isMinimalKDof` (no `(G/E(H))̃ ↔ M(G̃)/E(H̃)` map —
   deliberately deferred). If the algebraic induction wants a fully graph-level recursion, this
   bridge is the missing piece; otherwise the IH-handed form suffices and the bridge stays unbuilt.
2. **Forest surgery (KT 4.1/4.2) + the balanced-packing lemma** (*Replan* Step 5 / *Finding*
   layer 2). Off-critical-path TODO; substrate landed (`lem:forest-surgery-{split,unsplit}` stay
   red). **The balanced-packing lemma is now fully RESOLVED (2026-06-03): KT's Lemma 4.1 has a
   GAP, not an error.** Counting half `Graph.isBase_vfiber_ncard_ge` (`lem:base-vfiber-count`,
   every base meets ≥ D fibers — no pigeonhole obstruction) and redistribution half
   `Graph.acyclicSet_insert_vfiber_of_not_inc` (`lem:acyclic-insert-vfiber`, a `v`-avoiding
   forest absorbs a free `v`-fiber as a pendant since `v` deg 2 ⟹ `v` isolated) are both green
   `\leanok`, axiom-free. No `D ≥ 3` counterexample. The descent's load-bearing **rebalancing
   move** is green (`Graph.exists_packing_move_of_not_inc`, `lem:packing-move`), and the descent's
   **outer loop is now green too (2026-06-03)**: `Graph.exists_balanced_forest_packing`
   (`lem:balanced-forest-packing`) — a base admits a `D`-forest packing with every forest meeting
   `v`. The disjointness caveat the prior hand-off named is resolved by *disjointifying* the packing
   first (mathlib `disjointed` over `Fin D`): the move then leaves exactly one donor, and the
   pigeonhole (`≥ D` `v`-fibers among `≤ D−1` non-`j` forests ⟹ a donor with `≥ 2`) keeps the
   `v`-avoiding count strictly decreasing under strong induction. **So the balanced-packing
   assumption is now fully DISCHARGED.** The remaining piece toward `lem:forest-surgery-split`
   itself is the final **reroute wiring**: take the balanced packing of `G̃` and reroute it across `v`
   to the `G̃ᵥᵃᵇ` packing. **Both reroute wiring steps now LANDED (2026-06-03):** step 1
   `Graph.isAcyclicSet_splitOff_of_diff_fiberAtVertex` (green, axiom-free) — the `v`-free part of
   each balanced forest (the fibers the surgery keeps untouched) transports verbatim into `G̃ᵥᵃᵇ`,
   assembling the landed `IsAcyclicSet.anti_inter` + `isAcyclicSet_mulTilde_splitOff_of_removeVertex`;
   step 2 `Graph.isAcyclicSet_splitOff_reroute` (green, axiom-free) — the genuinely-hard cycle-lift.
   The `dᶠ(v)=2` forest swaps its two `v`-edges `pa,pb` for one short-circuit copy `r`; a
   `G̃ᵥᵃᵇ`-cycle through `r` rotates so `r` is first (`WList.exists_rotate_firstEdge_eq`), substitutes
   `r` (joining `a,b`) by the `v`-traversing 2-path `a—pa—v—pb—b` of `G̃` (the surviving `w'` lifts to
   `G̃` via `mulTilde_splitOff_deleteFiber_le`), and the resulting closed `G̃`-trail inside `F`
   contains a `G̃`-cycle (`IsTour.exists_isCyclicWalk` + `IsSublist.edge_subset`) — contradicting `F`
   acyclic. FRICTION (`[matroid] Cycle-lift by edge-substitution…`) / TACTICS-QUIRKS § 29.
   **RESOLVED (2026-06-03 addendum): `lem:forest-surgery-count` and `lem:forest-surgery-split` are
   both GREEN, axiom-free; the vacuous `c3df62f` declaration is deleted.** `Graph.forest_surgery_count`
   (the `|⋃F'ᵢ|+D=|I|` count, stated additively; `dᶠ=2` forests swap via the green
   `lem:reroute-cycle-lift`, `dᶠ=1` forests drop their `v`-fiber via the green
   `lem:reroute-vfree-transport`, balance ⟹ each shrinks by one) → `Graph.forest_surgery_split`
   (reads off `def(G̃ᵥᵃᵇ) ≤ def(G̃)` via def\,=\,corank on a base, `linarith`). **Next addendum
   commit = *User-directed addendum item #1* below** (the narrative-bridge
   `@[deprecated … (since := "narrative-bridge")]` shim deriving the KT-4.3 deficiency content
   *from* `forest_surgery_split`). Off the Theorem-4.9 critical path (the deficiency route already
   delivered Thm 4.9). See ## CORRECTION + the *TODO* Progress *VERDICT*.

### User-directed addendum items (2026-06-03 coordination)

Two items raised by the user while coordinating this forest-surgery addendum; recorded
here so they survive across dispatches:

1. **Narrative-bridge shim: forest surgery ⟹ alternative route to Theorem 4.9** — *this
   track, the next commit AFTER `lem:forest-surgery-split` goes green.* The forest-surgery
   route gives an alternative (and strictly stronger — it also reaches KT 4.3(ii)) route to
   the KT-4.3 splitting-off deficiency content that `lem:dof-tracking` / Theorem 4.9 consume.
   Record it in Lean as a lemma deriving that deficiency content **from** `forest_surgery_split`,
   marked `@[deprecated <deficiency-count `splitOff_deficiency_*`> (since := "narrative-bridge")]`
   with a doc-comment explaining the intent, plus a narrative-bridge corollary node in the
   blueprint (`\lean` + `\leanok`). Pattern + rationale: `blueprint/CLAUDE.md` *Narrative-bridge
   corollaries (the `@[deprecated]` shim pattern)*; this is API surface with no caller, exactly
   the shim's use-case. This commit closes the addendum.
2. **`ex:kt-41-overquantified` `example` → named lemma — NEXT CLEANUP PASS, not this addendum.**
   The KT-4.1 over-quantification disproof is currently an anonymous Lean `example`, so the
   blueprint node `ex:kt-41-overquantified` is an orphan (no identifier to carry a `\lean{}`
   pointer; see its `% Formalized as an unnamed Lean example` comment). Promote it to a named
   lemma so the node can link. The user will open the cleanup pass once this addendum finishes;
   this item is its seed.
