# Fresh-edge supply (`hfresh`) repair — design recon

**Status:** VERDICT SETTLED (2026-07-02, design pass) — the repair route is
pinned below (*Verdict*), with leaves F1–F3 as the to-do list. Blocks R1 of
the post-Phase-23 cleanup round (`notes/Phase23-cleanup.md`) until F1–F2
land. Canonical home for this arc per `notes/CLAUDE.md` (*Live design
recon*); compress to a verdict + pointer once the repair lands.

## The finding (coordinator, 2026-07-02; kernel-checked)

The hypothesis threaded through the Theorem-5.5 spine and
`molecular_conjecture`
(`CombinatorialRigidity/Molecular/AlgebraicInduction/Theorem55.lean` 2522ff)

```lean
hfresh : ∀ G' : Graph α β, ∃ e₀ : β, e₀ ∉ E(G')
```

is **unsatisfiable for every nonempty `α` and every `β`** (finite or
infinite): the all-loops-at-one-vertex graph is a legal `Graph α β` with
`edgeSet = Set.univ`. Kernel-checked against the project's mathlib
(compiles as a standalone snippet):

```lean
import Mathlib.Combinatorics.Graph.Basic

open Graph in
example {α β : Type} [Nonempty α] : ¬ (∀ G' : Graph α β, ∃ e₀ : β, e₀ ∉ E(G')) := by
  intro h
  obtain ⟨a⟩ := ‹Nonempty α›
  obtain ⟨e₀, he₀⟩ := h
    { vertexSet := {a}
      IsLink := fun _ x y => x = a ∧ y = a
      edgeSet := Set.univ
      isLink_symm := by intro e _ x y hxy; exact ⟨hxy.2, hxy.1⟩
      eq_or_eq_of_isLink_of_isLink := by
        intro e x y v w hxy hvw; left; rw [hxy.1, hvw.1]
      edge_mem_iff_exists_isLink := by
        intro e; simp only [Set.mem_univ, true_iff]; exact ⟨a, a, rfl, rfl⟩
      left_mem_of_isLink := by intro e x y hxy; exact hxy.1 }
  exact he₀ (Set.mem_univ e₀)
```

Consequences:

- **`molecular_conjecture` is vacuously true**: it assumes `[Nonempty α]`
  and `hfresh`, an inconsistent set. It can never be instantiated.
- The whole `hfresh`-carrying family is effectively vacuous the same way
  (their `2 ≤ V(G).ncard` hypotheses force `α` nonempty). Carriers (grep
  `hfresh`, 2026-07-02): `AlgebraicInduction/Theorem55.lean` (the spine +
  Thm 5.6 forms + `molecular_conjecture`), `AlgebraicInduction/CaseII.lean`,
  `AlgebraicInduction/CaseIII/{Arms,Realization}.lean`,
  `Induction/ForestSurgery/{ChainExtraction,Reduction}.lean`. (The
  `PebbleGame/Algorithm.lean` hit is an unrelated same-named local, as are
  `Induction/Operations.lean`'s `hfresh_*` locals.)
- **The mathematics is not affected**: no proof exploits the falsity. This
  is a statement-packaging error in how the fresh-label supply was
  quantified. The recon's consumption census (below) verified against the
  landed tree that `hfresh` is *applied* at exactly three sites, each at a
  graph carrying an `IsMinimalKDof` hypothesis in scope. (An earlier draft
  of this section claimed applications "at helper graphs carrying
  `E(G) ∪ {e₀}`" per `notes/Phase22-realization-design.md` §1.49(3); that
  was stale design-route prose — the M-arm route it described was dissolved
  in §1.50 and no such application site landed.)
- The cleanup round's S1 audit item proposed deriving `hfresh` from
  `[Infinite β]` — impossible twice over: the family carries `[Finite β]`
  (load-bearing; see the dependency map below), and the unconditioned
  `hfresh` is false even for infinite `β`. S1's instinct (the binder is
  wrong) was right; its remedy is dissolved. S1 closes when F1–F2 land.
- A Phase-22a design decision **cited the false hypothesis**
  (`notes/Phase22a.md` ~440): re-examined below (*The Phase-22a seam*) —
  nothing landed depends on it in a way the repair changes.

## Verdict (2026-07-02 design pass; spikes compile-checked)

**Route: condition the supply on minimality — two tiers, `[Finite β]`
untouched.** Every application site instantiates `hfresh` at a graph known
to be a minimal `c`-dof-graph, so the honest binder quantifies over exactly
those. The reshaped hypothesis is *satisfiable* (for `β` with headroom
`D·(|α|−1) < |β|`, because minimality bounds the edge count — spiked below),
*derivable* where the old one was assumed, and *sufficient* at every
consumption site. No motive, IH, or framework-layer change; no new
mathematics beyond one ~15-line counting lemma. Routes 1 and 2 of the
original list are adjudicated at the end of this section.

### Consumption census (verified against the landed tree, 2026-07-02)

`hfresh` is **applied** (i.e. `obtain ⟨e₀, he₀⟩ := hfresh G`) at exactly
three sites, each at the decl's own ambient graph with minimality in scope:

| Site | Graph's hypotheses at the application point |
|---|---|
| `Reduction.lean:659` (`minimal_kdof_reduction`, inside the strong induction) | `hG : G.IsMinimalKDof n 0`, `3 ≤ V(G).ncard`, no proper rigid subgraph |
| `CaseII.lean:350` (`case_II_realization_all_k`) | `hG : G.IsMinimalKDof n c`, `0 < c`, `3 ≤ V(G).ncard`, 2EC, no rigid |
| `ChainExtraction.lean:1295` (`chainData_extract`) | `hG : G.IsMinimalKDof n 0`, `G.Simple`, `4 ≤ V(G).ncard`, no rigid |

Every other occurrence is threading (the Theorem55 spine, the Thm-5.6 /
`molecular_conjecture` family, `Realization.lean`'s Case-III entries,
`Arms.lean`'s producer). The deeper leaves (`chainWalk_trichotomy`,
`chainData_or_cycleData_of_noRigid`) **already use the per-graph form**
`hfresh : ∃ e₀ : β, e₀ ∉ E(G)` — the repair extends their convention
upward. No differently-named universal supply binder exists elsewhere
(grepped `∉ E(G')` / `∃ e₀`).

Key topology fact: the leaf producers (`case_II_realization_all_k`, Arms'
`case_III_hsplit_producer_all_k`, `case_III_realization_all_k`/`_realization`,
`chainData_extract`) each consume the supply **only at their own ambient
`G`** — their recursion is IH-shaped (handed in), not internal. Only the
recursion drivers (the Theorem55 spine via `minimal_kdof_reduction_all_k`'s
case handlers closing over `hfresh`, and `minimal_kdof_reduction`'s internal
strong induction) instantiate at *varying* graphs, all minimal.

### Exact target signatures

**Tier 1 — leaf producers get the plain per-graph existential** (matching
the landed `chainWalk_trichotomy` convention). The binder moves after
`(G : Graph α β)` since it mentions `G`; call sites reorder mechanically.

- `Graph.chainData_extract` (ChainExtraction.lean:1277),
  `case_III_hsplit_producer_all_k` (Arms.lean:954),
  `case_III_realization_all_k` / `case_III_realization`
  (Realization.lean:2597/2633), `case_II_realization_all_k`
  (CaseII.lean:296): replace the universal binder with

  ```lean
  (hfresh : ∃ e₀ : β, e₀ ∉ E(G))
  ```

  and the application becomes `obtain ⟨e₀, he₀⟩ := hfresh`. Arms:992 passes
  its `hfresh` to `chainData_extract` unchanged (same type).

**Tier 2 — recursion drivers get the minimality-conditioned universal.**

- `Graph.minimal_kdof_reduction` (Reduction.lean:614; KT Thm 4.9,
  `thm:minimal-kdof-reduction`) — the `0`-dof form it actually needs:

  ```lean
  (hfresh : ∀ G' : Graph α β, G'.IsMinimalKDof n 0 → ∃ e₀ : β, e₀ ∉ E(G'))
  ```

  application at :659 becomes `obtain ⟨e₀, he₀⟩ := hfresh G hG`.

- The Theorem55.lean family ×10 (`theorem_55_minimalKDof_k_all_k`,
  `theorem_55_minimalKDof_gen`, `theorem_55_gen`, `theorem_55_minimalKDof_k`,
  `theorem_55_all_k`, `theorem_55_d3`, `rankHypothesis_of_theorem_55_d3`,
  `rankHypothesis_genuine_of_theorem_55_gen`,
  `rankHypothesis_of_theorem_55_gen`, `molecular_conjecture`) — the all-`c`
  form (the spine's induction visits every deficiency):

  ```lean
  (hfresh : ∀ (c : ℤ) (G' : Graph α β), G'.IsMinimalKDof n c → ∃ e₀ : β, e₀ ∉ E(G'))
  ```

  (in `rankHypothesis_of_theorem_55_d3`, `n` is the literal `3`). The spine's
  split arms instantiate for the Tier-1 leaves: `hsplitPos` passes
  `hfresh c G hG`, `hsplitZero` passes `hfresh 0 G hG` (both `hG` in scope,
  Theorem55.lean:2564–2578); the Thm-5.6 family threads `hfresh` whole
  (same type). The headline target, in full:

  ```lean
  theorem PanelHingeFramework.molecular_conjecture
      [Nonempty α] [Finite α] [Finite β] [DecidableEq β] {n : ℕ}
      (hk1 : 1 ≤ k) (hD : 6 ≤ Graph.bodyBarDim n) (hn : Graph.bodyBarDim n = screwDim k)
      (hfresh : ∀ (c : ℤ) (G' : Graph α β), G'.IsMinimalKDof n c → ∃ e₀ : β, e₀ ∉ E(G'))
      (G : Graph α β) (hV : 2 ≤ V(G).ncard) (hspan : V(G) = Set.univ) (hSimple : G.Simple) :
      (∃ F : BodyHingeFramework k α β, F.graph = G ∧
          (∀ e, F.supportExtensor e ≠ 0) ∧ F.IsInfinitesimallyRigid)
        ↔ (∃ Q : PanelHingeFramework k α β, Q.graph = G ∧
          (∀ e, Q.toBodyHinge.supportExtensor e ≠ 0) ∧ Q.toBodyHinge.IsInfinitesimallyRigid)
  ```

  Only the `hfresh` line changes anywhere in the family. No `2 ≤ V(G').ncard`
  conjunct is added to the binder: it buys nothing for satisfiability and
  would cost a discharge obligation per site.

### Satisfiability — both halves compile-checked against the landed tree

Two spikes ran green via `lean_run_code` this session (as `example`s over
`import CombinatorialRigidity.Molecular.Deficiency`), so the reshaped
hypothesis is provably satisfiable, not just plausibly:

1. **Minimality bounds the edge count** (the one genuinely new lemma; home:
   `Deficiency.lean`, which owns `IsMinimalKDof`):

   ```lean
   theorem Graph.edgeSet_ncard_add_deficiency_le_of_isMinimalKDof
       [DecidableEq β] [Finite α] [Finite β] {G : Graph α β} {n : ℕ} {k : ℤ}
       (hD : 1 ≤ bodyBarDim n) (hne : V(G).Nonempty) (hG : G.IsMinimalKDof n k) :
       (E(G).ncard : ℤ) + G.deficiency n ≤ bodyBarDim n * ((V(G).ncard : ℤ) - 1)
   ```

   Proof (spiked, ~15 lines): take a base `B` of `matroidMG` — minimality
   makes every edge-fiber meet `B`, so `E(G) ⊆ Prod.fst '' B` and
   `|E(G)| ≤ |B|`; conclude by the corank bridge
   `isBase_ncard_add_deficiency_eq` (Deficiency.lean:2266).

2. **Headroom derives the conditioned supply** (same home):

   ```lean
   theorem Graph.freshEdgeSupply_of_card_lt
       [DecidableEq β] [Finite α] [Finite β] {n : ℕ} (hD : 1 ≤ bodyBarDim n)
       (hcard : bodyBarDim n * (Nat.card α - 1) < Nat.card β) :
       ∀ (c : ℤ) (G' : Graph α β), G'.IsMinimalKDof n c → ∃ e₀ : β, e₀ ∉ E(G')
   ```

   Proof (spiked, ~35 lines): if `E(G') = univ` then either `V(G') = ∅`
   (contradiction: an edge forces a vertex, and `hcard` makes `β` nonempty)
   or lemma 1 + `deficiency_nonneg` + `|V(G')| ≤ Nat.card α` give
   `|β| = |E(G')| ≤ D·(|α|−1) < |β|`.

### Witness plan (the non-vacuity regression test)

Instance `n := 3`, `k := 2`, `α := Fin 2`, `β := Fin 7` (`bodyBarDim 3 = 6 =
screwDim 2`; headroom `6·(2−1) = 6 < 7`). Two named decls in a new small
file `Molecular/AlgebraicInduction/Nonvacuity.lean` (Theorem55.lean is past
the LoC tripwire; the file is reachable from the root so CI compiles it):

1. the supply witness — `Graph.freshEdgeSupply_of_card_lt` applied at that
   instance (hypotheses close by `norm_num`/`decide`);
2. the end-to-end witness — `molecular_conjecture` **fully applied** at an
   explicit one-edge graph `K₂ : Graph (Fin 2) (Fin 7)` (constructed
   literally, like the counterexample snippet above; `hV`/`hspan`/`hSimple`
   discharged concretely), yielding a closed `Prop` with every hypothesis of
   the headline discharged at a concrete instance. Any future regression to
   an unsatisfiable binder breaks this decl. A one-sentence blueprint remark
   on `thm:molecular-conjecture` records the witness.

### The `[Finite β]` dependency map (adjudicates route 1)

`[Finite β]` is **structurally load-bearing at the foundation of the
deficiency/matroid layer**, not incidental plumbing:

- `matroidMG` lives on ground type `β × Fin (bodyHingeMult n)`, and its
  independence characterization `matroidMG_indep_iff` (Deficiency.lean:159)
  requires `[Finite β]` because the vendored matroid-union subsystem is
  finite-ground-type-only: `Matroid.union_indep_iff`
  (`Matroid/Constructions/Union.lean:220`) and the whole
  rank/polymatroid theory there (`polymatroid_of_adjMap`:250,
  `adjMap_rank_eq`:480) assume a finite ground type (the port is rebased on
  the `FiniteCircuitMatroid` constructor). Everything about `IsMinimalKDof`
  — including `loopless_of_isMinimalKDof`, the rank bridges
  (`rank_add_deficiency_eq`:2255), and both spiked lemmas above — flows
  through this.
- The genericity device (`GenericityDevice.lean`, ~24 occurrences) uses
  `[Finite β]` in the finrank/algebraic-independence machinery over
  `ends : β → α × α`.
- The remaining ~dozens of uses (edge-set `Set.toFinite` calls across the
  induction files) are incidental in isolation, but moot given the above.

So route 1 (`[Infinite β]` + per-graph finiteness) is **not a repair — it is
a framework-layer rebuild** (an infinitary matroid-union subsystem plus a
re-derived deficiency theory). Dead. Route 2 (bounded supply under
`[Finite β]` with headroom threaded through the statements) is subsumed by
the verdict in improved form: conditioning on minimality replaces per-site
headroom arithmetic with an invariant the recursion already maintains
(`splitOff_isMinimalKDof` et al. re-establish minimality at every visited
graph), so no count bookkeeping enters any statement; the headroom
hypothesis appears only in the optional derivation lemma
`freshEdgeSupply_of_card_lt` and the witness.

**Flagged, not chosen — the zero-hypothesis ideal.** The supply hypothesis
could in principle vanish entirely by letting `splitOff` *reuse* a removed
label (`e₀ := eₐ`): mathematically sound (labels are arbitrary), but it
weakens the `e₀ ∉ E(G)` side condition every `splitOff` lemma and the
Case-II/III row-transport proofs case on (e.g. CaseII.lean:291's
`e₀ ∉ E(G)` / `e₀ ∈ E(Gab)` row split), i.e. an invasive rework of the
`splitOff` family across the defeq-fragile zone for purely cosmetic gain.
Recorded as a possible far-future cleanup; not part of this repair.

### The Phase-22a seam (deliverable 4)

`notes/Phase22a.md` ~440 ruled out "option (ii) `β = E(G)`" for the
parent-`ends` impedance, with the parenthetical "`hfresh` forces spare
labels in `β`". Re-examined: **nothing landed depends on the false
universal form.** The landed artifact of that decision
(`exists_ends_of_graph` + the edge-restricted `hends` relaxation) does not
consume `hfresh` at all, and the ruled-out-ness survives the repair — under
the conditioned supply, `β := ↥E(G)` still fails, because the ambient `G`
is itself a minimal graph the conditioned `hfresh` covers, and it would
have `E(G) = univ`. The later restatement at ~564 already gives the
supply-free reason ("`minimal_kdof_reduction` runs over fixed `β` with
`splitOff` drawing fresh labels"), which stays correct verbatim. Optional
(rides with F3): reword the ~440 parenthetical to cite the conditioned form.

### Status surfaces until the repair lands (deliverable 5)

- **ROADMAP** Phase-23 row: already carries "✓ Complete, **modulo the
  `hfresh` repair**" + pointer — keep until F2 lands, then drop the clause.
- **README** (¶ "…is now a theorem in the development") and
  **home_page/index.md** (same ¶ + row 23): as of this design pass they
  carried the completion claim unannotated; this commit adds a one-sentence
  honesty clause ("statement-level repair of the fresh-edge-label
  hypothesis in progress — as landed it is unsatisfiable, making the
  headline statements vacuous; see `notes/FreshEdgeSupply-design.md`").
  F2 (or F3) removes the clauses when the witness lands.
- **Blueprint**: no interim annotation — the affected nodes get their real
  restatement in F1 (`\leanok` stays: the decls compile; the defect is
  statement strength, which the restated prose then reflects). The
  supply-describing passages to restate: `panel-layer.tex` 243/302/346/450,
  `case-iii.tex` 1443 ("every graph leaves some edge name unused" — the
  false form, verbatim), `case-ii.tex` (Lemma 6.8 preamble),
  `molecular-induction.tex` 1565 (`lem:chain-data-extract`, "with fresh
  edge names available") + `thm:minimal-kdof-reduction`'s proof prose.

### Leaf decomposition (each sized to one sitting)

- **F1 — the reshape (Lean + blueprint, one commit).** Apply the Tier-1/
  Tier-2 signatures above across the six carrier files (~15 decls), rewrite
  the three application sites (`hfresh G hG` / `hfresh` per tier), fix the
  spine's split-arm instantiations (`hfresh c G hG` / `hfresh 0 G hG`,
  Theorem55.lean:2568/2576) and any call-site argument reorders from the
  Tier-1 binder move; sync the docstrings that narrate the old form
  (Reduction.lean:610–612 "it holds whenever `β` is not exhausted…",
  `molecular_conjecture`'s `hfresh` paragraph at Theorem55.lean:3074,
  Realization/Arms/CaseII preamble mentions) and restate the blueprint
  passages listed under *Status surfaces* (per the structural-edit gate:
  grep `blueprint/src/` per reshaped decl; `checkdecls` can't catch
  surviving names). Full `lake build` + `lake lint` + `checkdecls`. Risk:
  low — statement-level only; proof bodies change at exactly three lines.
- **F2 — satisfiability + witness (Lean + blueprint remark, one commit).**
  Land the two spiked lemmas in `Deficiency.lean` (names above; proofs are
  the spikes verbatim, modulo golf) + the two-decl
  `Nonvacuity.lean` witness per the witness plan; blueprint remark on
  `thm:molecular-conjecture`; drop the README/home_page/ROADMAP honesty
  clauses (or defer the drop to F3 if F2 runs long).
- **F3 — close-out (docs-only, one commit; may merge into F2 if slim).**
  Compress this doc to a ≤3-line verdict + pointer (per `notes/CLAUDE.md`),
  flip S1 in `notes/Phase23-cleanup.md`, optional Phase22a.md:440
  parenthetical reword, re-point the round's hand-off at R1 (which resumes
  with the *repaired* statements as its calibration target).

## Recon deliverables — disposition

- Route + exact signatures + leaf decomposition — **done** (*Verdict*).
- `[Finite β]` dependency map — **done** (grounded in
  `matroidMG_indep_iff`, the vendored union subsystem, GenericityDevice).
- Satisfiability witness plan — **done** (both enabling lemmas
  compile-checked; witness instance pinned).
- Phase-22a seam — **done** (no landed dependence; cosmetic reword only).
- Status-surface plan — **done** (annotations landed with this pass;
  removal scheduled in F2/F3).

No open decisions remain at the route level. F1/F2 discretion is limited to
cosmetics: binder placement/naming, witness-file naming, and proof golf.
