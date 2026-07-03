# Fresh-edge supply (`hfresh`) repair — design recon

**Verdict (2026-07-02; F1–F3 landed):** the `hfresh` binder threaded through
the Theorem-5.5 spine and `molecular_conjecture` was kernel-unsatisfiable
(the all-loops-at-one-vertex graph has `E(G) = univ`); repaired to a
minimality-conditioned two-tier supply, with satisfiability lemmas
(`Deficiency.lean`) and a compile-checked non-vacuity witness
(`Nonvacuity.lean`). Full recon (route adjudication, exact signatures,
compile-checked spikes): git history for this file. Landed summary:
`notes/Phase23-cleanup.md` *Decisions made* (F1/F2/F3 entries).

## E — consumer-surface packaging (design-settle, 2026-07-03)

**E2 landed (2026-07-03):** the build below is in tree, verbatim except one
forced file-location change — `Graph.bodyBarDim_eq_screwDim_sub_one` lives in
`PanelLayer.lean`, not `RigidityMatrix/Basic.lean` as §E.3 pinned (the latter
is a `module` file and cannot import the non-`module` `BodyBar/Framework.lean`
that defines `Graph.bodyBarDim`; full account in `notes/FRICTION.md`
*[process] A design doc's pinned lemma "home" can be unbuildable …*). Landed
summary: `notes/Phase23-cleanup.md` *Decisions made* (E2 entry). E3 (the
docstring sweep, §E.6) is next.

**Adjudicated direction (owner, 2026-07-03; not re-litigated here):** the
consumer-facing headline decls in
`CombinatorialRigidity/Molecular/AlgebraicInduction/Theorem55.lean` are
re-packaged so a consumer supplies (i) a single `3 ≤ n`-shaped hypothesis in
place of the `hk1 : 1 ≤ k` / `hD : 6 ≤ Graph.bodyBarDim n` /
`hn : Graph.bodyBarDim n = screwDim k` plumbing (the landed bridge
`Graph.eq_add_one_of_bodyBarDim_eq_screwDim` forces `k = n − 1`), and (ii) an
explicit cardinality hypothesis
`hcard : Graph.bodyBarDim n * (Nat.card α - 1) < Nat.card β` in place of the
higher-order `hfresh` binder (derived internally via the landed
`Graph.freshEdgeSupply_of_card_lt`). The `hfresh`-threading general forms
stay as the internal engine. Everything below is compile-spiked against the
landed tree (2026-07-03, `lean_run_code`, all green); the reshape is
**statement-level only** — no motive or framework-layer change is needed.

### E.1 Arithmetic trace (verified against the landed definitions)

- `Graph.bodyBarDim n = n(n+1)/2` (`BodyBar/Framework.lean:61`);
  `screwDim k = (k+2).choose 2` (`Molecular/RigidityMatrix/Basic.lean:87`).
- **`3 ≤ n ⟺ 6 ≤ bodyBarDim n`** (values 0,1,3,6,10,…; `bodyBarDim 2 = 3`),
  so the single `3 ≤ n` is *exactly* the old `hD`.
- **Old ⟹ new:** `(hk1, hD, hn)` forces `k = n − 1` (the landed bridge,
  `PanelLayer.lean:2043`) and `3 ≤ n` (from `hD`). **New ⟹ old:** `3 ≤ n`
  gives `hk1` (`1 ≤ n − 1`, omega), `hD` (helper `six_le_bodyBarDim` below),
  and `hn` at `k := n − 1` (helper `bodyBarDim_eq_screwDim_sub_one`:
  `screwDim (n−1) = (n+1).choose 2 = (n+1)n/2 = bodyBarDim n`, needing
  `1 ≤ n` for the ℕ-subtraction `(n−1)+2 = n+1`). Exact repackaging — no
  generality lost or gained on the arithmetic side.
- **`hcard ⟹ hfresh`** is the landed `freshEdgeSupply_of_card_lt`
  (`Deficiency.lean:2803`; needs `1 ≤ bodyBarDim n`, from `hD`). Not
  conversely: `hcard` is strictly stronger as a supply witness, so a consumer
  holding an exotic `hfresh` without the label headroom calls the internal
  engine form — exactly the public/engine division adjudicated.

### E.2 Public-surface census (verified pins + callers, 2026-07-03)

Callers = Lean call sites in the landed tree; pins = `blueprint/src/`
`\lean{}` sites (all in `algebraic-induction/panel-layer.tex`). No decl gets
a thin wrapper: every public form has zero callers to keep stable (only the
Nonvacuity witness consumes `molecular_conjecture`, and it is restated in the
same commit), so wrapper indirection buys nothing and the headline must end
ergonomic per the owner direction.

| decl | pin | callers | verdict |
|---|---|---|---|
| `molecular_conjecture` | `thm:molecular-conjecture` | Nonvacuity witness | **reshape in place** (owner: the headline itself ends ergonomic) |
| `theorem_55_gen` | `thm:theorem-55` (co-pin) | none | **reshape in place** (exists purely as the public 0-dof corollary) |
| `theorem_55_all_k` | `thm:theorem-55-d3-instance` (co-pin) | `theorem_55_d3` | **delete — merge into the reshaped `theorem_55_d3`** (the two landed statements are byte-identical; post-reshape a duplicate is indefensible — S2 precedent; the role-accurate name survives) |
| `theorem_55_d3` | `thm:theorem-55-d3-instance` (co-pin) | none | **reshape in place at literal `n := 3`** (its `hD`+`hn` at `k = 2` jointly force `n = 3` via the bridge, so the `{n}` binder was vacuous generality) |
| `theorem_55_minimalKDof_k` | unpinned | `theorem_55_d3`, `rankHypothesis_of_theorem_55_d3` | **internal engine, unchanged** |
| `theorem_55_minimalKDof_gen` | `thm:theorem-55` (co-pin, engine role stated in the node's note) | 3 internal | **internal engine, unchanged** |
| `theorem_55_minimalKDof_k_all_k` | unpinned | `theorem_55_minimalKDof_gen` | **internal engine (carry-threaded spine), unchanged** |
| `rankHypothesis_of_theorem_55_gen` | `thm:theorem-55-6` | none | **reshape in place** |
| `rankHypothesis_genuine_of_theorem_55_gen` | unpinned | `rankHypothesis_of_theorem_55_gen`, `molecular_conjecture` | **internal engine (the Thm-5.6 genuine-hinge witness form), unchanged** |
| `rankHypothesis_of_theorem_55_d3` | `thm:theorem-55-6-d3` | none | **reshape in place** (`hfresh` → literal-6 `hcard`; already at `n := 3`) |
| `rankHypothesis_deficiency_of_theorem_55_d3` | `cor:theorem-55-d3-spanning` | none | **unchanged** (no `hfresh`, no arithmetic plumbing — takes the GP realization as input; already ergonomic) |
| `freshEdgeSupply_witness` (Nonvacuity.lean) | none (prose-cited nowhere) | `molecular_conjecture_witness` | **delete** (the witness discharges `hcard` directly post-reshape; the engine-tier satisfiability keeps its named home, `freshEdgeSupply_of_card_lt`) |
| `molecular_conjecture_witness` (Nonvacuity.lean) | `rem:molecular-conjecture-nonvacuous` (`\texttt` mention) | none | **restate against the reshaped headline** (E.4) |

### E.3 Exact reshaped signatures (all compile-spiked)

**Two new helper lemmas** (both spiked with the proofs below):

```lean
-- home: CombinatorialRigidity/BodyBar/Framework.lean (bodyBarDim's
-- definition file, per the engineering convention; deep-upstream touch —
-- run a FULL `lake build` before `lake lint` in the build leaf)
theorem Graph.six_le_bodyBarDim {n : ℕ} (hn : 3 ≤ n) :
    6 ≤ Graph.bodyBarDim n := by
  rw [Graph.bodyBarDim, Nat.le_div_iff_mul_le (by norm_num)]
  calc 6 * 2 = 3 * 4 := by norm_num
    _ ≤ n * (n + 1) := Nat.mul_le_mul hn (by omega)

-- home: CombinatorialRigidity/Molecular/RigidityMatrix/Basic.lean, the
-- "screwDim k numeric arithmetic" kit section (screwDim's file; the
-- converse of the forward bridge, which stays in PanelLayer.lean —
-- co-locating the pair is a possible future sweep, out of scope here)
theorem _root_.Graph.bodyBarDim_eq_screwDim_sub_one {n : ℕ} (hn : 1 ≤ n) :
    Graph.bodyBarDim n = screwDim (n - 1) := by
  rw [Graph.bodyBarDim, screwDim, Nat.choose_two_right,
    show n - 1 + 2 = n + 1 by omega, show n + 1 - 1 = n by omega, Nat.mul_comm]
```

**The type-level `k := n − 1` verdict: ℕ-subtraction directly in the
framework types.** The general-`d` public forms state
`BodyHingeFramework (n - 1) α β` / `PanelHingeFramework (n - 1) α β` /
`HasGenericFullRankRealization (n - 1) n G`. Spike findings:

- At the witness instantiation `n := 3`, a statement written against literal
  `BodyHingeFramework 2 (Fin 2) (Fin 7)` **`exact`-closes** against the
  reshaped conclusion — `(3 - 1 : ℕ)` is defeq to `2` (kernel `Nat.sub`
  reduction), with no `show`/`norm_num`/cast step. `decide`-style hypothesis
  discharge is unaffected.
- The alternative `(hk : n = k + 1)`-equation shape was rejected: it keeps
  two binders plus a coupling equation on the surface — exactly the plumbing
  the owner killed. Accepted cost of `n - 1`: display of the subtraction in
  generic-`n` goals; consumers wanting a clean `k` use the engine forms.
- Internal derivation (identical in all four general/`d=3` reshapes, spiked):
  `hk1` by `omega` from `3 ≤ n`; `hD := Graph.six_le_bodyBarDim hd`; `hn`
  via `Graph.bodyBarDim_eq_screwDim_sub_one (by omega)`; `hfresh` via
  `Graph.freshEdgeSupply_of_card_lt (by omega) hcard` (the `omega` closes
  `1 ≤ bodyBarDim n` from `hD` in context). Then a one-line term-mode
  application of the unchanged engine decl.

The four reshaped general/`d = 3` signatures (hypothesis lists exact;
conclusions unchanged except `k ↦ n - 1` resp. the literal instance):

```lean
theorem PanelHingeFramework.molecular_conjecture
    [Nonempty α] [Finite α] [Finite β] [DecidableEq β] {n : ℕ}
    (hd : 3 ≤ n)
    (hcard : Graph.bodyBarDim n * (Nat.card α - 1) < Nat.card β)
    (G : Graph α β) (hV : 2 ≤ V(G).ncard) (hspan : V(G) = Set.univ)
    (hSimple : G.Simple) :
    (∃ F : BodyHingeFramework (n - 1) α β, F.graph = G ∧
        (∀ e, F.supportExtensor e ≠ 0) ∧ F.IsInfinitesimallyRigid)
      ↔ (∃ Q : PanelHingeFramework (n - 1) α β, Q.graph = G ∧
        (∀ e, Q.toBodyHinge.supportExtensor e ≠ 0) ∧
          Q.toBodyHinge.IsInfinitesimallyRigid)

theorem PanelHingeFramework.theorem_55_gen [DecidableEq β] [Finite α]
    [Finite β] {n : ℕ} (hd : 3 ≤ n)
    (hcard : Graph.bodyBarDim n * (Nat.card α - 1) < Nat.card β)
    (G : Graph α β) (hG : G.IsMinimalKDof n 0) (hV : 2 ≤ V(G).ncard) :
    (G.Simple → PanelHingeFramework.HasGenericFullRankRealization (n - 1) n G) ∧
      HasPanelRealization (n - 1) n G

theorem PanelHingeFramework.rankHypothesis_of_theorem_55_gen
    [Nonempty α] [Finite α] [Finite β] [DecidableEq β] {n : ℕ}
    (hd : 3 ≤ n)
    (hcard : Graph.bodyBarDim n * (Nat.card α - 1) < Nat.card β)
    (G : Graph α β) (hne : V(G).Nonempty) (hspan : V(G) = Set.univ)
    (hSimple : G.Simple) :
    ∃ Q : PanelHingeFramework (n - 1) α β, Q.graph = G ∧
      Q.toBodyHinge.RankHypothesis (G.deficiency n)
```

The two `d = 3` instances state the headroom bound with the **literal `6`**
(`d = 3` statements elsewhere use concrete numerals; the bridge to the
`bodyBarDim`-form the derivation lemma wants is `by simpa [Graph.bodyBarDim]`,
spiked):

```lean
theorem PanelHingeFramework.theorem_55_d3 [DecidableEq β] [Finite α] [Finite β]
    (hcard : 6 * (Nat.card α - 1) < Nat.card β)
    (G : Graph α β) (hG : G.IsMinimalKDof 3 0) (hV : 2 ≤ V(G).ncard) :
    (G.Simple → PanelHingeFramework.HasGenericFullRankRealization 2 3 G) ∧
      HasPanelRealization 2 3 G
-- proof: theorem_55_minimalKDof_k (by decide) (by decide)
--   (Graph.freshEdgeSupply_of_card_lt (n := 3) (by decide)
--     (by simpa [Graph.bodyBarDim] using hcard)) G hG hV

theorem PanelHingeFramework.rankHypothesis_of_theorem_55_d3
    [Nonempty α] [Finite α] [Finite β] [DecidableEq β]
    (hcard : 6 * (Nat.card α - 1) < Nat.card β)
    (G : Graph α β) (hne : V(G).Nonempty) (hspan : V(G) = Set.univ)
    (hSimple : G.Simple) :
    ∃ Q : PanelHingeFramework 2 α β, Q.graph = G ∧
      Q.toBodyHinge.RankHypothesis (G.deficiency 3)
```

Notes: the three landed `set_option linter.unusedDecidableInType false in`
suppressions (on `rankHypothesis_of_theorem_55_d3`,
`rankHypothesis_of_theorem_55_gen`, `molecular_conjecture`) stay — the spike
confirms the linter still fires on the reshaped forms without them, and the
existing justification is unchanged; the Thm-5.5 forms need none
(`IsMinimalKDof` uses the instance in the type). The reshaped decls bind no
`k` (the file's `variable {k : ℕ}` no longer auto-binds into them — spiked).

### E.4 `Nonvacuity.lean` witness update

- **Delete `freshEdgeSupply_witness`** (census). Rewrite the module header:
  the file's job narrows to "the reshaped headline is fully instantiable" —
  `hcard` is a closed arithmetic statement, so the F-arc's unsatisfiable-
  binder failure mode is now structurally impossible on the public surface;
  the file still guards against regression to an uninstantiable surface.
- **Restate `molecular_conjecture_witness`** with the same iff-statement as
  landed (literal `BodyHingeFramework 2 (Fin 2) (Fin 7)`,
  `Graph.singleEdge 0 1 0`) and the proof term (spiked verbatim):

```lean
  PanelHingeFramework.molecular_conjecture (n := 3) (by norm_num)
    (by simp only [Nat.card_fin]; decide)
    (Graph.singleEdge (0 : Fin 2) 1 (0 : Fin 7))
    (by rw [Graph.vertexSet_singleEdge]; exact (Set.ncard_pair (by decide)).ge)
    (Set.eq_univ_of_forall (fun x => by fin_cases x <;> simp))
    (Graph.singleEdge_simple (by decide) 0)
```

  All hypotheses are `norm_num`/`decide`-style at `n := 3`, `α := Fin 2`,
  `β := Fin 7`, per the dispatch requirement.

### E.5 Blueprint sync scope (all in `panel-layer.tex`; statements untouched)

Node *statements* need no edit — they already say "at any dimension
`n ≥ 3`", which the reshaped Lean now matches *more* literally, and rule 13
keeps the supply bookkeeping out of statements. The touch-points:

1. `thm:theorem-55-d3-instance` `\lean{}` pin (~l. 325): drop
   `theorem_55_all_k`; pin `theorem_55_d3` alone (same-commit with the
   deletion, per the per-slice `checkdecls` gate).
2. Its *Formalization note* (~l. 362–368): "Formalized as
   `theorem_55_d3`" (drop the two-name sentence); supply sentence → the
   headroom-bound sentence pointing at `rem:fresh-edge-supply`.
3. *Formalization note* under `thm:theorem-55` (~l. 317–321): keep the
   public/engine two-name division; replace "A fresh-edge supply rides as
   ambient data" with: the public form takes `3 ≤ n` and the label-headroom
   bound `D(|\alpha|-1) < |\beta|` (from which the supply is derived,
   \cref{rem:fresh-edge-supply}); the all-deficiency engine form threads the
   supply itself.
4. `rem:fresh-edge-supply` (~l. 296–315): reword "Each theorem in this
   chapter therefore carries a hypothesis providing … an unused edge label"
   to the two-tier story — the *induction engine* threads the per-graph
   supply; the *consumer-facing statements* instead carry the explicit
   headroom bound, from which the supply follows
   (`freshEdgeSupply_of_card_lt`). The unsatisfiability sentence and the
   satisfiability citations stay as written.
5. `thm:theorem-55-6` *Formalization note* (~l. 445–446): same replacement
   as (3), minus the two-name sentence.
6. `thm:theorem-55-6-d3` (~l. 448–494, currently no note): add the one-line
   headroom Formalization note (rule-13 pointer).
7. `rem:molecular-conjecture-nonvacuous` (~l. 567–576): first sentence no
   longer says the supply is "threaded through this theorem" — it enters as
   the explicit headroom bound; "the fresh-edge supply included" → "the
   label-headroom bound included". Keeps citing
   `molecular_conjecture_witness`.

No other chapter is touched: the five reshaped names are pinned only in
`panel-layer.tex` (verified 2026-07-03), and the fresh-edge notes in
`case-ii.tex` / `case-iii.tex` / `molecular-induction.tex` describe engine
nodes whose decls are unchanged. Status surfaces (README / home_page /
ROADMAP) cite `molecular_conjecture` by name only — no edit.

### E.6 Leaf decomposition

- **E2 — the build (Lean + blueprint, 1 commit, one sitting):** the two
  helpers (E.3 homes), the five in-place reshapes + `theorem_55_all_k`
  deletion, the `Nonvacuity.lean` update (E.4), the `panel-layer.tex` sync
  (E.5). Gates: **full** `lake build` warning-clean (the
  `BodyBar/Framework.lean` touch is deep-upstream — full build before
  `lake lint`), `lake lint`, `blueprint/verify.sh`, `blueprint/lint.sh`.
  Every internal re-derivation is spiked; risk is low.
- **E3 — the docstring sweep (Lean doc-comments only, 1 commit):** re-point
  the stale `theorem_55_all_k` prose mentions (10 files, verified by grep)
  at the surviving names — `theorem_55_minimalKDof_k_all_k` for
  spine-shape/branch references (`hsplitZero` etc.), `theorem_55_d3` for
  public-instance references — and re-narrate the Theorem55.lean docstrings
  that describe the old `hk1`/`hD`/`hn`/`hfresh` plumbing on the reshaped
  decls (E2 rewrites the reshaped decls' own docstrings; E3 catches the
  cross-file mentions). Done-gate:
  `grep -rn theorem_55_all_k --include='*.lean'` → 0 hits.
- Then the **owner review of the re-rendered chapter** (checkpoint #2,
  covering R1d + the reshaped statements) before R2 opens.
