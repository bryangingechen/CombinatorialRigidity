# API and tactic friction log

A long-running record of one-off mathlib API gaps, tactic limitations,
and proof-shape friction encountered while building this project. Each
entry is self-contained: future agents can either add new entries,
work an open one (upstream PR / project helper / refactor), or strike
through one that has been resolved.

This file is **append-mostly**: keep resolved entries with a
strikethrough and a "Resolved by …" note rather than deleting them.
The history is the value — a future agent picking up a similar issue
can see how it was handled before.

> **Scope.** This file holds *one-off* frictions: a specific lemma I
> needed and mirrored, a specific bug I worked around. *Cross-cutting
> lessons* — "always do X", "if you see pattern Y, prefer Z" — belong
> in `TACTICS.md` instead, which is the project's tactical reference.
> Don't bury a general rule in a `[resolved]` entry here; it won't be
> found again.

## How this file is used

- After landing a phase, review what proofs felt awkward. Did you
  reach for the same glue lemma three times? Did `grind` need an
  unusually long hint list? File an entry — and if the lesson is
  cross-cutting, lift it into `TACTICS.md` instead.
- When starting a new session, optionally browse here for a small
  upstream-able item to land alongside the main work.
- Items that turned into actual upstream candidates live under
  `Mathlib/<exact mathlib path>` (project mirror); each entry below
  links to the mirrored file when applicable.
- The "Ending a session" step in `ROADMAP.md` includes a friction
  review: do not skip it. Even "no new entries this session" is a
  useful checkpoint.

## Entry format

```
### [STATUS] Short title
- **Where it bit:** which proof / file
- **Friction:** what extra work was needed
- **Proposed fix:** named lemma / tactic / refactor
- **Status:** open / mirrored / upstreamed / wontfix / resolved
- **Mirror file (if any):** path under `Mathlib/`
```

## Open entries

### [open] `revert` ordering before `e'.ind` is finicky
- **Where it bit:** `typeI_edgeSet` proof, backward direction.
- **Friction:** To do Sym2 induction on a hypothesis `e'` while
  preserving other hypotheses depending on `e'` (here: `heG : e' ∈ S`
  and `hmap : Sym2.map some e' = s(x, y)`), we `revert` the dependent
  hypotheses first. The order of revert determines the order of
  hypotheses in the lambda after `refine e'.ind fun p q ... => ?_`. The
  correct rule is **revert in reverse order of the lambda binders**:
  for lambda `fun p q heG hne hmap`, revert `hmap hne heG`. Forgetting
  this gave a confusing "rewrite failed" error in `typeII` because
  `hmap` ended up bound to a different hypothesis.
- **Proposed fix:** none needed; this is intrinsic to `revert`/`refine`
  semantics. Documented here so the next agent doesn't redo the trial
  and error. Alternative: use `induction e' with | h p q => …` which
  generalizes context automatically.
- **Status:** wontfix (tactic-semantics issue, not a missing lemma).

### [open] `IsSparse` is not `Decidable`, blocking small-example proofs by `decide`
- **Where it bit:** Phase 2 attempt at `K₄ \ e` is Laman (deferred).
- **Friction:** `IsSparse` is `∀ s : Finset V, ℓ ≤ k * #s → (G.edgesIn ↑s).ncard + ℓ ≤ k * #s`,
  but `Set.ncard` is noncomputable. Even though the statement is morally
  decidable for finite `V`, we can't close the K₄ \ e example with
  `decide` and instead fall back on a finite case analysis.
- **Proposed fix:** add a project-internal `IsSparse'` companion that
  goes through `Finset.sym2` + `Finset.filter` for the count. Prove
  `IsSparse ↔ IsSparse'` under `[Fintype V] [DecidableRel G.Adj]`.
  Then concrete examples can use `decide`.
- **Status:** open. Acceptable for now (the K₄ \ e example was deferred
  to Phase 3 where Henneberg gives a one-liner), but worth doing if a
  later phase wants to mechanize more concrete graphs.

### [open] `simp` leaves and-grouping in `typeII` `edgesIn` decomposition
- **Where it bit:** `typeII_isLaman` sparsity, `h_decomp` proof.
- **Friction:** the `s(some u, some v)` branch of the Sym2 case-split
  reduces under `simp [edgesIn, hcoe, Set.mem_preimage, T']` to
  `(G.Adj u v ∧ p) ∧ q ↔ (G.Adj u v ∧ q) ∧ p` for the same conjuncts
  `p, q` — `simp` does not re-associate `∧`. The matching `typeI`
  proof closes on bare `simp` because the `Adj` predicate there has
  no extra `s(u, v) ≠ s(a, b)` conjunct. Adding `; try tauto` after
  the simp closes the typeII case in one extra line per branch.
- **Proposed fix:** none upstream-able; this is just `simp` not
  doing classical AC. Documented so the next agent doesn't churn
  on the `simp` set when it inevitably "almost" works.
- **Status:** wontfix (tactic limitation, not a missing lemma).

### [open] `push_neg` deprecated in favour of `push Not`
- **Where it bit:** `IsLaman.exists_degree_le_three`.
- **Friction:** `push_neg` triggers a deprecation warning. The
  replacement `push Not at hcontra` works but produces `3 < x` rather
  than `4 ≤ x`; an extra `omega` (or `Nat.add_one_le_iff`) is needed
  even though the two forms are defeq in `ℕ`.
- **Proposed fix:** none required from us; this is an upstream
  ergonomics issue. Documented here so future agents know not to
  re-litigate it.
- **Status:** wontfix (upstream concern).

## Resolved / mirrored entries

### [mirrored] `Set.ncard_pair_le` / `Set.ncard_triple_le` (unconditional pair / triple bounds)
- **Where it bit:** `typeI_edgeSet_ncard`, `typeII_edgeSet_ncard`,
  `typeI_isLaman` (`hT_le_2`), `typeII_isLaman` (`hT'_le_3`,
  `hT'_le_2` ×2).
- **Friction:** mathlib has `Set.ncard_pair` (`= 2` under `a ≠ b`)
  but no unconditional `≤ 2` companion. Bounding the cardinality of
  a literal pair/triple of new edges expanded to 3- and 5-line calc
  chains via `Set.ncard_insert_le` + `Set.ncard_singleton`, repeated
  five times across the file (the same 5-line block for each
  `T ⊆ {…, …}` sub-bound).
- **Resolution:** mirrored unconditional `≤` bounds. Each calc
  chain collapses to one `Set.ncard_pair_le _ _` (resp.
  `Set.ncard_triple_le _ _ _`) application.
- **Status:** mirrored.
- **Mirror file:** `Mathlib/Data/Set/Card.lean`.

### [mirrored] `Sym2.map_some_injective` (named specialization)
- **Where it bit:** `typeI_edgeSet_ncard`, `typeII_edgeSet_ncard`,
  `typeI_isLaman`, `typeII_isLaman` — every `Set.ncard_image_of_injective`
  application on a `Sym2.map some` image.
- **Friction:** the same four-token incantation
  `Sym2.map.injective (Option.some_injective V)` was written four
  times. It correctly typechecks but is harder to read than the
  intent ("`Sym2.map some` is injective").
- **Status:** mirrored as `Sym2.map_some_injective`.
- **Mirror file:** `Mathlib/Data/Sym/Sym2.lean`.

### [mirrored] `Sym2.exists_and_map_eq_mk_iff` (Sym2 image-membership case analysis)
- **Where it bit:** `typeI_edgeSet` (Phase 3); aborted attempt at
  `typeII_edgeSet`.
- **Friction:** Proving things of the form
  `(typeI G a b).edgeSet = (Sym2.map some '' G.edgeSet) ∪ {s(none, some a), s(none, some b)}`
  required `Sym2.ind` to expose the underlying pair `(x, y)`, then a
  4-way case analysis `rcases x with _ | u <;> rcases y with _ | v`,
  each branch closed by mixed `Sym2.eq_iff` / `Option.some.injEq` /
  `Sym2.map_mk` rewrites and `simp_all`. `aesop`, `tauto`, and bare
  `simp` each got stuck on a different sub-goal.
- **Resolution:** The right shape was a *predicate-form* simp lemma:
  `(∃ e, P e ∧ Sym2.map f e = s(x, y)) ↔ ∃ p q, f p = x ∧ f q = y ∧ P s(p, q)`.
  This is what `simp` reaches after `Set.mem_image` (a `@[simp]` lemma)
  has fired, and after any further unfolding of `e ∈ S` (e.g.
  `Set.mem_diff` for set differences), so the predicate `P` is whatever
  conjunction those unfoldings produce. The earlier sketches (e.g.
  `Sym2.map_some_mem_iff` for the `e = Sym2.map f e'` shape) didn't
  match the simp normal form and so wouldn't fire.

  With the predicate-form lemma tagged `@[simp]`, both
  `typeI_edgeSet` and `typeII_edgeSet` close in three lines:
  `ext e; induction e with | h x y => ?_; rcases x with _ | u <;>
  rcases y with _ | v <;> simp`. The companion non-`simp`
  `Sym2.mk_mem_image_map_iff` for the pre-`Set.mem_image` shape is
  also provided, alongside `f = some` specializations.
- **Status:** mirrored.
- **Mirror file:** `Mathlib/Data/Sym/Sym2.lean`.

### [mirrored] `(G.incidenceSet v).ncard = G.degree v`
- **Where it bit:** `IsLaman.two_le_degree` (Phase 2).
- **Friction:** mathlib has `card_incidenceSet_eq_degree` for
  `Fintype.card`, not for `Set.ncard`. We chained
  `← Nat.card_coe_set_eq, Nat.card_eq_fintype_card,
  card_incidenceSet_eq_degree` every time we needed it.
- **Status:** mirrored as `SimpleGraph.ncard_incidenceSet_eq_degree`.
- **Mirror file:** `Mathlib/Combinatorics/SimpleGraph/Finite.lean`.

### [mirrored] `G.edgeSet.ncard = G.edgeFinset.card`
- **Where it bit:** `IsLaman.exists_degree_le_three` and
  `top_fin_two_isLaman` (Phase 1 + 2).
- **Friction:** trivial composite of `← Set.ncard_coe_finset` and
  `coe_edgeFinset`, but written out by hand each time.
- **Status:** mirrored as `SimpleGraph.ncard_edgeSet_eq_card_edgeFinset`.
- **Mirror file:** `Mathlib/Combinatorics/SimpleGraph/Finite.lean`.

### [mirrored] `(⊤ : SimpleGraph V).edgeSet.ncard = (Fintype.card V).choose 2`
- **Where it bit:** `top_fin_two_isLaman`.
- **Friction:** mathlib's `card_edgeFinset_top_eq_card_choose_two` is
  in `Finset.card` form; the `Set.ncard` companion was missing.
- **Status:** mirrored as `SimpleGraph.ncard_edgeSet_top_eq_card_choose_two`.
- **Mirror file:** `Mathlib/Combinatorics/SimpleGraph/Finite.lean`.

### [mirrored] `Finset.coe_compl_singleton`
- **Where it bit:** `IsLaman.two_le_degree`.
- **Friction:** singleton complement coercion is the standard
  "delete one vertex" idiom, but you have to compose
  `Finset.coe_compl` and `Finset.coe_singleton` by hand.
- **Status:** mirrored.
- **Mirror file:** `Mathlib/Data/Finset/BooleanAlgebra.lean`.

### [mirrored] `Finset.card_compl_singleton`
- **Where it bit:** `IsLaman.two_le_degree`.
- **Friction:** as above for the cardinality side.
- **Status:** mirrored.
- **Mirror file:** `Mathlib/Data/Fintype/Card.lean`.
  (Sibling of `coe_compl_singleton` but lands in a different upstream
  file because `Finset.card_compl` requires `Fintype α` and lives in
  `Fintype/Card.lean`, not `Finset/BooleanAlgebra.lean`.)
