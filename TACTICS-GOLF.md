# Tactics — golf reference

This file is the project's **golfing reference**: proof patterns we
use repeatedly and the "always do X" rules that turn verbose
first-draft proofs into idiomatic ones. Read this when reviewing,
shrinking, or polishing a proof — at the `simplify` skill / cleanup
pass time, **not** during first-draft writing.

For **rescue / build-failure recovery** (when a `lake build` fails
with a mysterious Lean error), see `TACTICS-QUIRKS.md` instead — it's
symptom-indexed and lighter.

> **Friction vs. idiom.** This file holds *general* lessons — rules
> that apply across the project. One-shot frictions (a specific
> missing lemma, a specific bug) live in `notes/FRICTION.md`. Don't
> mix them: a "use X instead of Y" rule belongs here; a "I needed
> lemma Z and mirrored it" entry belongs in FRICTION.

## Sections

1. **`grind` workflow** — when to reach for `grind`, how to feed it
   hints, how to debug it when it fails.
2. **`Set.ncard` and the `toFinite_tac` autoparam** — never stage
   `.Finite` witnesses by hand.
3. **Mirror-first rule** — if you needed a lemma upstream-eligible,
   mirror it before landing the proof.
4. **`refine ⟨?_, ?_⟩` for our `def`s** — `IsLaman`, `IsTight`,
   `IsSparse`, `edgesIn` are non-reducible; expose their structure
   manually.
5. **Lifting Subtype-Sym2 equalities** — prefer `congrArg (Sym2.map
   Subtype.val)` over `rw [Subtype.mk.injEq]; subst`.
6. **`fun_prop` for continuity / differentiability** — replace explicit
   `Continuous.add` / `Continuous.comp` chains with `by fun_prop` and tag
   project helpers `@[fun_prop]` so they participate in the search.
7. **Lean LSP MCP** — when to use `lean_*` tools vs. the `Read` + `lake
   build` workflow, the local-first search order, and known-broken
   external services.
8. **`linear_combination` with rational coefficients** — pass
   `(norm := (field_simp; ring))` when the combination's scaling factor
   is a rational function (`a/(s-1)`) of an in-scope free variable; the
   default `ring` post-check fails on such denominators.
9. **Bake let-bound predicate shapes into helper signatures** — when
   factoring a cross-`.induct`-case helper that consults a `let`-bound
   predicate `P`, bake `P`'s specific lambda directly into the helper's
   parameter type instead of taking `P` abstract + an `hP_def` equation.
   The `.induct` case-binder defeq-reduces, so unification fires without
   any explicit equation argument.
10. **Collapsing indicator sums** — factor a constant out with
    `← Finset.mul_sum` before `Finset.sum_ite_eq'`; the collapse fires
    only when the `if` is the whole summand.
11. **Strong induction on a derived measure** —
    `induction hN : m G using Nat.strong_induction_on generalizing G`;
    `generalizing` is mandatory, the IH threads the measure-equation
    first (`IH _ hlt G' rfl …`), and don't `subst hN`.
12. **Iterating `+1` around a cyclic `Fin m`** — to propagate a
    consecutive-equality `f i = f (i+1)` to a global one, induct over
    `Fin.ofNat m j` on `ℕ` (not `(j : Fin m)` ascription, not
    `Fin.induction`); `Fin.ofNat_val_eq_self` returns to `i`.
13. **State a ℕ count `a − b + c` as `a + c − b`** — subtraction
    last, so the single truncating `−` lands on a provably-large-enough
    quantity (otherwise the statement is off-by-one at a boundary and
    `omega` can't prove it).
14. **"Polynomial with coefficients in a subring `R₀ ⊆ S`"** — carry as
    `(map (algebraMap R₀ S)).range` membership, not `coeffs ⊆ range`;
    the subring chains through every ring operation.
15. **LI family of `finrank`-many vectors spans `⊤`** — `LinearIndependent`
    + `Fintype.card ι = finrank` ⟹ `span (range v) = ⊤`, via
    `basisOfLinearIndependentOfCardEqFinrank` + `coe_…` + `Basis.span_eq`.
16. **`(∑ i, f i).comp g` — go pointwise** — no `LinearMap.sum_comp` exists and
    `map_sum` won't fire on `· ∘ₗ g`; discharge a `∘ₗ`-outside-`Finset.sum`
    identity with `LinearMap.ext` + `LinearMap.congr_fun` + `LinearMap.sum_apply`.

---

## 1. `grind` workflow

Most closing tactics here are `grind`. This section is the practical
reference: when to reach for it, how to feed it hints, how to debug it
when it fails, and the iteration loop we use to land proofs.

For the full reference see the Lean manual, chapter
*The `grind` tactic*. This document is the project-specific subset
plus tricks we've actually used.

### TL;DR workflow

Replace any closing `omega` / `simp` / `linarith` with `grind` first.
If it works, you're done. If it doesn't:

1. Stage facts as `have` lines so they sit on `grind`'s "whiteboard."
2. If `grind` still fails, switch to `grind?` and inspect:
   - **The suggestion line** — `grind?` prints a `grind only [...]`
     call with exactly the lemmas it actually used.
   - **The diagnostics** — when `grind` fails it dumps the whiteboard:
     known equalities, the cutsat assignment, the E-matching theorems
     it considered. Read this to see *what `grind` thinks is true*.
3. Once `grind` succeeds with hints, run `grind?` once and replace it
   with the suggested `grind only [...]` form. That's the final shape.

`grind only` is preferred over `grind` for landed proofs: it pins the
exact lemma set, doesn't drift if mathlib re-tags `@[grind]` lemmas,
and runs faster.

### Invocation forms

| Call | Effect |
|---|---|
| `grind` | Use ambient `@[grind]`-annotated library + heuristics. Default for exploration. |
| `grind [foo, bar]` | Same, plus `foo`, `bar` as one-shot hints. |
| `grind only` | Use *only* what's listed (and a small core). More deterministic. |
| `grind only [foo, bar]` | The form `grind?` recommends; what we land on. |
| `grind?` | Run, then print a `grind only [...]` suggestion. The iteration tool. |

The hint list accepts prefix tags `=`, `←`, `→`, `_=_`, `!`. These tell
`grind` how to use that particular lemma — `=` for left-to-right
rewrite, `←` for backwards reasoning, etc. (see "Annotations" below).
You don't normally write these yourself; copy them verbatim from the
`grind?` suggestion.

### How `grind` works (one paragraph)

`grind` maintains a "whiteboard" of known facts. Cooperating engines
read from and add to it: congruence closure (equality propagation),
constraint propagation, E-matching (instantiates `@[grind]`-annotated
quantified lemmas when patterns match), guided case analysis,
and theory solvers — `cutsat` for linear integer arithmetic and a
commutative ring solver. It always proves goals by deriving a
contradiction; conclusion and premises are treated symmetrically.

What this buys us beyond `omega`:
- Equational reasoning across multiple terms (congruence closure).
- Library lemmas fire automatically once their pattern matches a term
  on the whiteboard (E-matching).
- Mixed arithmetic + equational goals close in one step.

What it *doesn't* do:
- It does **not** unfold non-`abbrev` definitions. See § 4.
- It does **not** automatically apply `@[simp]` lemmas. They need a
  separate `@[grind =]` annotation. (We don't add annotations in this
  Archive directory; we pass lemmas as hints instead.)
- It is **not** for goals with combinatorially explosive case-split
  structure (large pigeonhole, N-queens, SAT-like). Different tools
  exist for those (`bv_decide`, etc.).

### Reading a `grind` failure

When `grind` can't close, it prints its whiteboard. Two sections matter:

```
[cutsat] Assignment satisfying linear constraints
  [assign] Fintype.card (Fin 2) := 5
  [assign] s.card := 2
```

This shows the *integer assignment* `cutsat` found that satisfies all
the constraints `grind` knew about. If something obviously wrong is
assigned a "free" value (e.g. `Fintype.card (Fin 2) := 5`), `grind`
didn't have the fact pinning it. Add the missing lemma as a hint
(`Fintype.card_fin`, in this case).

```
[ematch] E-matching patterns
  [thm] Nat.card_eq_fintype_card: [Nat.card #1]
  [thm] Sym2.rel_iff': [Sym2.Rel #2 #1 #0]
```

Theorems whose patterns `grind` considered. If a lemma you think
should fire doesn't appear here, its pattern didn't match (often
because of a hidden coercion, or the relevant term hasn't reached the
whiteboard yet — try a `have` to surface it).

### Annotations (reference)

You won't usually add these in this directory — we pass lemmas as
hints — but you'll see them in `grind?` output and may need them in
upstream PRs.

| Attribute | Pattern from | Meaning |
|---|---|---|
| `@[grind =]` | LHS | Rewrite LHS → RHS when LHS appears. Use for simp-style lemmas. |
| `@[grind _=_]` | both sides | Bidirectional rewriting. |
| `@[grind ←]` | conclusion | Try the lemma when its conclusion matches a goal. |
| `@[grind →]` | hypotheses | Fire when the hypotheses match the whiteboard. |
| `@[grind]` | (default) | Heuristic combination of above. |
| `@[grind <=]` | conclusion, then hypotheses | Multi-pattern; conclusion-first. |

Custom patterns:
```lean
grind_pattern foo => pat₁, pat₂ where guard cond, x =/= y
```
Fires `foo` only when both `pat₁` and `pat₂` match simultaneously.

### Tricks we've found useful

**Stage facts on the whiteboard with `have`.** If a closing `grind`
fails, lifting an intermediate fact to a `have` line (even with a
trivial proof) often makes it succeed. Example from
`IsTight.not_isSparse_of_lt`:

```lean
fun hH => by
  have := hG.edgeSet_ncard
  have := hH.edgeSet_ncard_add_le (by grind only)
  have := Set.ncard_lt_ncard (edgeSet_ssubset_edgeSet.mpr h) (Set.toFinite H.edgeSet)
  grind only
```

The three `have` lines surface facts grind couldn't synthesize on its
own (a strict subset relation, an arithmetic precondition). Once they
are on the whiteboard, the closing `grind only` finishes by linear
arithmetic alone.

**Use `(by grind)` in argument positions.** When applying a lemma like
`hH.foo (precondition)`, write `hH.foo (by grind)` rather than
`have h := …; hH.foo h`. Saves a line.

**Inject finite-cardinality facts directly.** `grind` will not derive
`Fintype.card (Fin 2) = 2` on its own. Pass `Fintype.card_fin`,
`Nat.card_fin`, or `Nat.card_eq_fintype_card` as hints whenever the
goal involves cardinalities of concrete finite types. The `[cutsat]`
diagnostic will tell you when it's missing — it'll assign a wrong
value to the cardinality.

**`grind` doesn't always pick up coercions.** A goal with `↑s` where
`s : Finset V` may need `Finset.coe_univ` (or whichever coercion lemma
applies) as an explicit hint. The `grind?` suggestion will show a `!`
prefix on lemmas it found via this kind of pattern matching.

**When in doubt, run `grind?` and copy the answer.** It is, by
construction, the minimal hint set that works for the current proof.
The `=`/`←`/`→`/`!` prefixes in the suggestion are syntactically valid
in `grind only` calls — paste verbatim.

**Default `simp` before `grind` can subsume `change` + multi-`rw` staging.**
If you find yourself writing `change ... ; rw [lemma_A] ; simp only [B, C]
; split_ifs <;> grind` to shape a goal into `grind`-ready form, try
collapsing the prologue to `simp [lemma_A]` (default simp set, not
`simp only`, and with just the lemma that's not in `@[simp]`). The
default set tends to absorb the wrapper / coercion boilerplate that
`change` was unfolding by hand, and `grind` itself does the `split_ifs`
work. `elemSkewMap_ofLp_inr_apply` in `TrivialMotions.lean` went from
6 tactic lines to 1 this way:

```lean
-- Was: change ... ; rw [elemSkewMap_apply] ; simp only [PiLp.ofLp_single,
--      Pi.single_apply] ; rcases ... <;> split_ifs <;> grind
rcases eq_or_ne i a with rfl | hia <;> simp [elemSkewMap_apply] <;> grind
```

**Keep `omega` in the back pocket.** For goals that are pure linear
integer arithmetic with no equational reasoning to do (and where you
don't need any lemma hints), `omega` is faster and more readable. We
default to `grind` because most of our goals mix arithmetic with
equational steps, but `omega` is the right call for purely arithmetic
ones.

> Three more `omega`/`grind`/`nlinarith` quirks that show up at
> first-draft time (set-aliased atoms, commutativity/distributivity,
> ℕ-quadratic bounds) live in `TACTICS-QUIRKS.md` §§ 1–3, where
> they're indexed by symptom for mid-proof lookup.

### Examples in this directory

Search the `.lean` files for `grind only` to see worked instances. The
ones worth reading first:

- `Sparsity.lean` — `IsSparse.edgeSet_ncard_add_le` exemplifies the
  "stage `Finset.univ` instantiation, then close with `grind only`"
  pattern.
- `Sparsity.lean` — `IsTight.not_isSparse_of_lt` shows the
  multi-`have` whiteboard-staging idiom.
- `Laman.lean` — the `K₂` example shows `grind only [Fintype.card_fin]`
  closing a concrete cardinality computation.
- `Henneberg.lean` — the `typeI_isLaman` / `typeII_isLaman` tightness
  branches close in one `grind only` line each (one rewrite lemma +
  one cardinality identity + one Laman fact). The typeII version
  shows that `grind` can pull in `Set.ncard_diff_singleton_of_mem`
  via E-matching from a local `s(a, b) ∈ G.edgeSet` hypothesis,
  saving an explicit `Set.ncard_ne_zero_of_mem` staging line.

### Where `grind` doesn't help

For symmetry with the above: it is also useful to know what `grind`
*won't* close, so you don't waste a cycle trying.

- **Disjointness on Sym2 patterns.** Goals like
  `Disjoint (Sym2.map some '' …) ({s(none, some a), s(none, some b)} : Set _)`
  bottom out in a case-split on the pair structure that `grind` does
  not perform. Use `rw [Set.disjoint_left]; rintro e he hpair; rcases
  hpair <;> simp at he`.
- **Pure linear arithmetic with staged `have`s.** When the closing
  step is just chaining the staged facts via `+` / `≤`, `omega` is
  faster and the proof is more readable. Reserve `grind` for goals
  that mix arithmetic with a rewrite or with E-matching against a
  library lemma.

---

## 2. `Set.ncard` and the `toFinite_tac` autoparam

**Rule of thumb:** never stage `.Finite` witnesses by hand for a
`Set.ncard_*` call. The autoparam already finds them.

Almost every cardinality lemma in `Mathlib.Data.Set.Card` takes its
finiteness premise as an *autoparam*:

```lean
theorem ncard_union_eq (h : Disjoint s t)
    (hs : s.Finite := by toFinite_tac)
    (ht : t.Finite := by toFinite_tac) : …
theorem ncard_le_ncard (hst : s ⊆ t)
    (ht : t.Finite := by toFinite_tac) : …
theorem ncard_eq_zero
    (hs : s.Finite := by toFinite_tac) : …
theorem ncard_pos
    (hs : s.Finite := by toFinite_tac) : …
theorem ncard_ne_zero_of_mem (h : a ∈ s)
    (hs : s.Finite := by toFinite_tac) : …
theorem ncard_diff_singleton_of_mem (h : a ∈ s)
    (hs : s.Finite := by toFinite_tac) : …
```

`toFinite_tac` calls `Set.toFinite`, which finds the witness from the
ambient `[Finite V]` instance. So under `[Finite V]`, every `Set` of
elements drawn from `V` (or `Sym2 V`, `Sym2 (Option V)`, etc.) is
visible as finite without preamble.

### Anti-pattern (don't do this)

```lean
have hG_fin : G.edgeSet.Finite := G.edgeSet.toFinite
have hImg_fin : (Sym2.map some '' G.edgeSet).Finite := hG_fin.image _
have hPair_fin : ({s(none, some a), s(none, some b)} : Set _).Finite :=
  Set.toFinite _
…
rw […, Set.ncard_union_eq hDisj hImg_fin hPair_fin, …]
```

Three `have` lines that the autoparam would have produced for free.
Earlier versions of `typeI_edgeSet_ncard` and `typeII_edgeSet_ncard`
each had ~9 lines of this preamble; deleting it dropped the proofs to
9 and 12 lines respectively.

### Pattern (do this)

```lean
rw […, Set.ncard_union_eq hDisj, …]
```

That's it. The autoparam fires on each missing finiteness argument.

### The one trap: `.mpr` on iff lemmas

Autoparams need to be at the call site to fire. When you grab `.mpr`
off an iff lemma, the autoparam doesn't get a chance:

```lean
-- Doesn't compile: `Set.ncard_pos` still wants its hs argument first.
have : 0 < s.ncard := Set.ncard_pos.mpr ⟨_, hmem⟩
```

Two fixes:
- Pass the witness manually:
  `(Set.ncard_pos s.toFinite).mpr ⟨_, hmem⟩`.
- Or rephrase: `Set.ncard_ne_zero_of_mem hmem` is single-argument and
  the autoparam fires. Often what you actually wanted (omega doesn't
  care about `0 <` vs `≠ 0`).

### Why this matters

The pattern `.Finite` witnesses → `Set.ncard_*` arguments was the
single biggest line-saver in the Phase 3 cleanup pass: ~14 lines
deleted across `Henneberg.lean`, with no logic touched. If you find
yourself writing `have hX_fin : X.Finite := …`, stop and check whether
the consumer has an autoparam.

---

## 3. Mirror-first rule

If a proof would benefit from a lemma that morally belongs upstream
(`SimpleGraph`, `Set.ncard`, `Finset`, `Sym2`, etc., not specific to
rigidity), put it under `Mathlib/<exact mathlib path>` in the same
commit and refactor the proof to call it. Don't inline a
hand-rolled version in a project file — that loses the upstream-able
artifact.

Concretely:
- The Lean namespace stays the upstream one (`Set`, `SimpleGraph`,
  `Sym2`, etc.). The mirror file imports the upstream module and adds
  alongside it.
- File path mirrors the upstream path exactly: a future PR is then
  copy-paste.
- The directory `CombinatorialRigidity/Mathlib/` is created
  lazily; don't pre-populate.
- Each mirrored lemma also gets a `[mirrored]` entry in
  `notes/FRICTION.md` with its mirror-file path.

See `DESIGN.md` "Mirror directory" for the full mechanics.

Why we go to this trouble: the resolved entries in
`notes/FRICTION.md` are the running list of "lemmas the project found
mathlib should have." They mature into upstream PRs. Inlining a
hand-rolled version skips that pipeline.

### Search mathlib before mirroring

Before reaching for a mirror, sweep `lean_loogle` (type pattern) or
`lean_leanfinder` (concept). The "mirror it ourselves" instinct
bloats the project surface, and mathlib's API is denser than it
looks. Cases where a planned mirror dissolved into a one-line
upstream find:

- `linearIndependent_pair_of_det_ne_zero` (dim-2 LI from determinant
  ≠ 0) → mathlib already ships
  `Matrix.linearIndependent_rows_of_det_ne_zero` (d-general).
- A bridge `Module.Dual ℝ M →ₗ[ℝ] (M → ℝ)` → mathlib ships
  `LinearMap.ltoFun R M N A`, instantiate with `R = N = A = ℝ`.
  `lean_loogle` against `(_ →ₗ[_] _) →ₗ[_] (_ → _)` returned it on
  the first try.
- An `{x : Fin 3 // x ≠ 0} ≃ Fin 2` reindex → mathlib ships
  `finSuccAboveEquiv` (`Mathlib.Logic.Equiv.Fin.Basic`).
- `LinearMap.ext_on` already packages "linear maps agree on a
  spanning set → equal", saving the explicit `LinearMap.ext fun x =>
  …; …; LinearMap.eqOn_span` block.
- "Vector `u` orthogonal to a spanning set is zero" → don't
  hand-roll `Submodule.span_induction` on the orthogonal complement;
  `Submodule.isOrtho_span` says `span 𝕜 s ⟂ span 𝕜 t ↔ ∀ u ∈ s, ∀ v
  ∈ t, ⟪u, v⟫ = 0` directly. Combined with `isOrtho_top_left` (`⊤ ⟂
  V ↔ V = ⊥`) and `span_singleton_eq_bot`, "orthogonal to a
  size-`finrank` LI family ⇒ zero" closes in ~10 lines instead of
  20+ (cf. `eq_zero_of_orthogonal_dim_two` in
  `HennebergRigidity.lean`).
- "`2 ≤ s.card` from two distinct witnesses `u ≠ v ∈ s`" → don't
  build `({u, v} : Finset _).card = 2` by hand, then `card_le_card`
  with a `Finset.mem_insert` case-split for `{u, v} ⊆ s`. Mathlib
  ships `Finset.one_lt_card : 1 < s.card ↔ ∃ a ∈ s, ∃ b ∈ s, a ≠ b`
  directly, so the entire ~10-line block collapses to
  `Finset.one_lt_card.mpr ⟨u, hu, v, hv, huv⟩`. The Phase 9 pebble
  game shipped two copies of the hand-rolled form in
  `PebbleGame/Correctness.lean`
  (`independent_brings_pebble_simpleGraph_form`
  and case-5 of `tryAddEdgeWith_eq_none_imp_exists_witness`),
  collapsed in Phase 9-cleanup C2; the `.mp` direction was already
  in use at `SparsityIComponents.lean:112, 184`.

Rule of thumb: search by *type pattern of what you need*, not by
your guess of what mathlib calls it — names drift, types don't.

---

## 4. `refine ⟨?_, ?_⟩` for our `def`s

`IsLaman`, `IsTight`, `IsSparse`, and `edgesIn` are non-reducible
`def`s. `grind` will *not* unfold them. Consequences:

- `grind` will not see through `IsLaman G ↔ G.IsTight 2 3` on its own.
  Expose the structure with `refine ⟨?_, ?_⟩` (using the `And.intro`
  for `IsTight`'s pair shape) before letting `grind` finish each
  branch.
- A goal like `(G.edgesIn ↑Finset.univ).ncard ≤ …` won't be touched
  by `grind` until you either rewrite via `edgesIn_univ` first or
  pass `edgesIn_univ` as a hint.

If we ever decide to make any of these `abbrev`, the proofs would
contract further. For now they stay `def` — see `DESIGN.md`
"Predicates as `def`s" for the trade-off.

### Unfold via `grind only [DefName]` hint

`grind only [IsTightOn]` (passing the `def` name as a hint) tells
`grind` to unfold the def on the whiteboard. This collapses
`unfold IsTightOn at h; ...; omega`-shaped bodies to one line — the
commit-18 grind-default sweep landed three such collapses on
`IsSparse.isTightOn_of_le`, `IsTightOn.union_with_bonus`, and
`IsTightOn.insert_vertex_with_edges`. Use this when the only thing
the `unfold` step does is expose the def's arithmetic content for
the closer; the explicit `refine ⟨?_, ?_⟩` is still needed when the
def has structural cases `grind` needs to dispatch separately.

---

## 5. Lifting Subtype-Sym2 equalities

**Rule of thumb:** to deduce `s(u, w) = s(a, b)` (a `Sym2 V` equality)
from `s(⟨u, _⟩, ⟨w, _⟩) = s(⟨a, _⟩, ⟨b, _⟩)` (a `Sym2 (Subtype p)`
equality, e.g. on `{w // w ≠ v}`), use `congrArg (Sym2.map Subtype.val)
heq` followed by `simpa`. Don't reach for `rw [Sym2.eq_iff] at heq;
rcases …; rw [Subtype.mk.injEq] at h1 h2; subst h1; subst h2`.

### Anti-pattern (don't do this)

```lean
intro heq
rw [Sym2.eq_iff] at heq
rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
· rw [Subtype.mk.injEq] at h1 h2
  subst h1; subst h2; exact hnab hadj
· rw [Subtype.mk.injEq] at h1 h2
  subst h1; subst h2; exact hnab hadj.symm
```

Six lines of bookkeeping per `Sym2`-disjunct, repeated for the swapped
arm.

### Pattern (do this)

```lean
intro heq
have : s(u, w) = s(a, b) := by simpa using congrArg (Sym2.map Subtype.val) heq
rcases Sym2.eq_iff.mp this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
exacts [hnab hadj, hnab hadj.symm]
```

The `congrArg` lifts the `Sym2 (Subtype p)` equality through the
underlying-value map; `simpa` unfolds `Sym2.map Subtype.val s(⟨u, _⟩,
⟨w, _⟩)` to `s(u, w)` via `Sym2.map_mk` + `Subtype.coe_mk`. Then
`Sym2.eq_iff.mp` case-splits the `V`-level equality with `⟨rfl, rfl⟩`
patterns directly.

### Why this matters

The `Subtype.mk.injEq` chain forces the proof-author to track which
endpoint of which arm got which renaming, and `subst` rewrites the
goal in two passes. The `congrArg` form keeps the proof at the level
of the underlying type for the entire case analysis — once `s(u, w) =
s(a, b)` is on the whiteboard, any `Sym2 V`-fact (here `¬G.Adj a b`)
applies directly.

This pattern recurs whenever `Sym2` wraps a sub-typed pair. The
`typeII_iso_of_three_neighbors` `(some, some)` arm is the canonical
example in this directory.

### Pattern (the other direction): `Sym2 V` equality → `G.edgeSet` subtype equality

Inverse situation: given `h_eq : s(u, v) = s(a, b)` (a `Sym2 V` equality)
and a function on `G.edgeSet` that is **Sym2-symmetric by construction**
(e.g., `RigidityMap`, built via `Sym2.lift`), lift `h_eq` to a subtype
equality on `G.edgeSet` and rewrite — *don't* unfold first and then case-
split the two orientations.

```lean
-- Goal: `(G.RigidityMap p) p' ⟨s(u, v), he⟩ = 0` given `h_eq : s(u, v) = s(a, b)`
-- and `h_target : (G.RigidityMap p) p' ⟨s(a, b), _⟩ = 0` (or its unfolded form).
rw [show (⟨s(u, v), he⟩ : G.edgeSet) = ⟨s(a, b), h_eq ▸ he⟩ from Subtype.ext h_eq]
-- now apply `h_target`
```

The anti-pattern this replaces: `simp only [rigidityMap_apply]` first
(unfolding to `⟪p u - p v, p' u - p' v⟫_ℝ = 0`), then
`rcases Sym2.eq_iff.mp h_eq with ⟨h1, h2⟩ | ⟨h1, h2⟩` to handle the two
orientations, with the swapped-orientation arm closing via `← neg_sub`
+ `inner_neg_neg`. That re-derives the Sym2-symmetry that `Sym2.lift`
already gave you for free, and forces the `subst`-direction workaround
(see TACTICS-QUIRKS § 4 — `rcases ⟨rfl, rfl⟩` would `subst` over
`a`/`b`).

Diagnostic for when this applies: the goal involves `f ⟨e, he⟩` where
`f`'s definition factors through `Sym2.lift`. In this project
`RigidityMap` is the headline case (`Framework.lean`). Canonical site:
`typeII_isInfinitesimallyRigid_extend` deleted-edge branch
(`HennebergRigidity.lean`).

## 6. `fun_prop` for continuity / differentiability

`fun_prop` chains continuity (and differentiability, measurability, etc.)
facts automatically; prefer it over hand-written `Continuous.add` /
`Continuous.comp` /`continuous_pi` chains. Local `Continuous` hypotheses
in scope are picked up automatically.

### Pattern

When a project helper returns a `Continuous` fact that future continuity
goals need to chain through (e.g. `continuous_rigidityMap_apply` in
`Framework.lean`), tag the helper:

```
@[fun_prop]
private theorem continuous_rigidityMap_apply ... : Continuous … := …
```

Downstream goals like `Continuous (fun p => fun i => G.RigidityMap p (preimg i))`
then close in one line:

```
have h_cont : Continuous … := by fun_prop
```

instead of the multi-line `continuous_pi (fun i => continuous_pi (fun e => …))`
nest. The Phase 5 milestone-2 `IsInfinitesimallyRigid.eventually` and
`exists_nonCollinear_rigid_placement_dim_two` use this; pre-cleanup the
continuity blocks ran 6–10 lines each, post-cleanup they're one-liners.

### When the goal mentions a project-internal `def`

`fun_prop` does *not* unfold non-reducible `def`s. If the goal mentions
`G.RigidityMap p x e` (which is a `def`), surface the underlying inner
product with a `simp only [rigidityMap_apply …]` first, then `fun_prop`.
This is what the tagged helper itself does internally.

### `Function.update` continuity

`Continuous.update` (mathlib, `Topology/Constructions.lean`) directly
closes the "pi-typed function with one coordinate replaced" pattern that
shows up in `exists_nonCollinear_rigid_placement_dim_two`'s
`p_t := fun t => Function.update p₀ c (p₀ c + t • w)`. `fun_prop` finds
it automatically.

---

## 7. Lean LSP MCP

`.mcp.json` at the repo root registers
[`lean-lsp-mcp`](https://github.com/oOo0oOo/lean-lsp-mcp). Full tool
catalog at the upstream
[`docs/tools.md`](https://github.com/oOo0oOo/lean-lsp-mcp/blob/master/docs/tools.md);
this section is the *project-specific* tactical guidance.

### TL;DR

- Run `lake build` once before the first LSP-touching call (warms up
  `lake serve`); skip if you've recently built.
- Look up a lemma by *concept*: `lean_loogle` (type pattern) or
  `lean_leanfinder` (semantic).
- Look up a lemma by *project-internal name*: `lean_local_search`.
- Look up a lemma by *current goal*: `lean_state_search` or
  `lean_hammer_premise`.
- Inspect a proof state: `lean_goal` (line for before/after, line+col
  for at-position).
- Quick "does X exist / what's its signature": `lean_hover_info` at the
  identifier's start column.
- Sanity-check the file: `lean_diagnostic_messages` instead of
  `lake build`-on-loop.

### Cold start

First `lean_goal` / `lean_diagnostic_messages` call after starting a
session triggers `lake serve`; expect a ~30-second wait or a one-time
LSP timeout. Subsequent calls in the same session are fast (≪ 1 s).
Mitigations:

- Run `lake build` *before* the first MCP call — this is the README's
  standing recommendation and avoids the cold start entirely.
- If a tool times out once, retry — the timed-out call still kicks
  `lake serve` into action.

### Search decision tree

Before reaching for any tool, decide what you're searching by:

| Question | Tool |
|---|---|
| Does `Foo.bar_baz` exist in this project? | `lean_local_search` |
| What's the project name for "X"? | `lean_local_search` (prefix match) |
| Mathlib lemma with type pattern `_ * (_ + _) = _ * _ + _ * _`? | `lean_loogle` |
| Mathlib lemma about "submodule generated by linearly independent set"? | `lean_leanfinder` |
| What closes the current goal? | `lean_state_search` |
| Which premises should I feed to `simp`/`aesop`? | `lean_hammer_premise` |

After a hit: `lean_hover_info` at the identifier's start column to
confirm the signature before invoking it in a proof.

### Avoid `lean_leansearch`

`leansearch.net` has been down for an extended period (HTTP 521 from
its Cloudflare front-end as of late 2025 / early 2026). Skip it
entirely; `lean_loogle` and `lean_leanfinder` cover the same use cases
with different query styles, and `lean_local_search` handles
project-internal lookups.

### `lean_multi_attempt` for tactic A/B testing

When you've narrowed a failing step to "one of these tactics should
close it", `lean_multi_attempt` runs several candidates against the
exact source position in one round-trip and reports which succeeded.
Faster than editing-and-rebuilding for each guess, especially when
each rebuild takes 30+ seconds. Example payload:
`["simp", "ring", "omega", "exact?", "tauto"]`.

### When the MCP is unavailable

The MCP server is a *convenience*, not a dependency. If `uvx` can't
reach PyPI, or the LSP refuses to start, or you're working from an
environment without network, the standard `Read` + `lake build`
workflow remains the source of truth: read the relevant `.lean` file,
edit, rebuild, inspect the compiler output. Don't block on MCP issues.

---

## 8. `linear_combination` with rational coefficients

`linear_combination` closes ring-level equations by accepting a linear
combination of hypotheses whose sum equals `lhs − rhs` of the goal.
Its default post-normalizer is `ring`, which **does not** simplify
divisions by a free-variable polynomial like `(s − 1)`. When the
natural scaling factor for one of the hypotheses is `c / (s − 1)`
(for some in-scope `c`), the `ring` check rejects the proof even
though the equation is correct as a rational identity. The fix is to
override the normalizer:

```lean
linear_combination (norm := (field_simp; ring))
  (c_a / (s - 1)) * h_combo + (B / (s - 1)) * h_cb_rel
```

`field_simp` clears the `(s − 1)` denominator first (using in-scope
non-zero hypotheses); `ring` finishes the polynomial identity check.
Pre-declare `have hs1_ne : s - 1 ≠ 0 := sub_ne_zero.mpr hs1` if
`field_simp` can't find the witness automatically.

**Worked example.** In Phase 7's row-LI side of
`typeII_edgeSetRowIndependent_extend`
(`MatroidIdentification.lean`), the disjoint-spans step needs to
prove `c_a · row_A + c_b · row_B = (s · c_a) · T(rowG'(eAB))` given
the constraint `(s − 1) · c_b = −(s · c_a)`. The natural combination
is `(c_a/(s−1)) · h_combo + (B/(s−1)) · h_cb_rel`, where `h_combo`
is the `(s−1)·row_A − s·row_B = s(s−1)·D` row identity from
`typeII_collinear_inner_combo`. The `c_a / (s − 1)` coefficient is
forced because the linear combination of `h_combo` must produce
`c_a · row_A`, which requires `(s − 1) · coeff = c_a`. The default
`ring`-only check fails; the `(field_simp; ring)` override closes
the goal in one line. Without this override, the alternative is a
~30-line manual unfold of `c_b` followed by the linear combination
on the cleared-denominator form — the savings vs. the manual route
were the C3 cleanup's main lever (Phase 7 cleanup round).

**When to reach for it.** Whenever you'd write
`linear_combination ... / x * h` and the post-normalizer fails: try
`(norm := (field_simp; ring))` before pre-deriving the cleared form
manually. The cost is one `field_simp` invocation; the win is
keeping the proof at the level of the algebraic identity rather
than its denominator-cleared variant.

## 9. Bake let-bound predicate shapes into helper signatures

When a function's body has `let P : V → Bool := fun w => …` and you
want to factor a cross-`.induct`-case helper that consults `P`'s
shape, the naïve extraction (a top-level helper taking `P` as a
parameter) doesn't work: the helper's body can't `simp only [P, …]`
unfold because `P` is a free variable from its point of view. The
standard workaround — pass `P`'s shape as a `hP_def : ∀ w, P w = …`
equation argument, optionally with a `:= by rfl` default — adds
plumbing or relies on autoParam to elide it. **The shorter route**:
bake `P`'s specific lambda directly into the helper's parameter
type. At each `.induct` callsite the case-binder `P` (let-bound by
`.induct` to that exact lambda) defeq-reduces, so Lean unifies the
helper's bound `fun w => …` with the callsite's `P` without any
explicit equation argument.

### Pattern

```lean
-- Helper: bake `P`'s lambda into the parameter's type.
lemma TryReachPebbleResult.reachable_newOrient_of_addEdgePred
    {D : PartialOrientation V} {k ℓ : ℕ} {u v start : V}
    (r : TryReachPebbleResult D
           (fun w => decide (0 < D.peb k w) && decide (w ≠ u) && decide (w ≠ v))
           start)
    (hD : Reachable k ℓ D) (h_outle : ∀ x, D.out x ≤ k) :
    Reachable k ℓ r.newOrient := …
```

```lean
-- Callsite (inside a `.induct` `case` whose body let-binds `P`
-- to exactly that lambda): no `hP_def`, no `simp [P]` plumbing.
case case3 D hnotin hnotin_rev h_outle hthr P r hr_eq ih =>
  …
  exact ih (r.reachable_newOrient_of_addEdgePred hD h_outle) h
```

### Worked example

Phase 9-cleanup C2 hit this with `tryAddEdgeWith`. Three `.induct`
consumers (`tryAddEdgeWith_reachable`, `_isSome`,
`_eq_none_imp_exists_witness`) each duplicated an 8-line case3/case4
preamble that decoded `r.hP`, derived `D.out r.target < k`, and
applied `r.reachable_newOrient` — six copies, ~48 LoC of
duplication. The pre-refactor audit's "out of scope" reading
proposed hoisting `P` to a top-level `private def`, which would have
required changing `tryAddEdgeWith`'s body shape and the `.induct`
case-binder signature; the bake-into-signature route landed the same
collapse without touching either.

### When it doesn't apply

- If callsites need to pass *different* lambdas (a generic reusable
  helper across multiple predicate shapes), keep `P` abstract and
  take `hP_def` as a hypothesis.
- If you can't get to a place where `r : TryReachPebbleResult D P …`
  is in scope with `P` let-bound (no `.induct`-style binding), there
  is no defeq channel for the unification.

## 10. Collapsing indicator sums — `← Finset.mul_sum` before `Finset.sum_ite_eq'`

`Finset.sum_ite_eq'` (and `Finset.sum_ite_eq`) collapses `∑ x, if x = a
then f x else 0` to `f a`, but **only fires when the `if` is the whole
summand** — `simp [Finset.sum_ite_eq']` silently no-ops on
`∑ x, c * (if x = a then 1 else 0) * g x` because a constant factor `c`
(or a trailing `g x`) sits outside the indicator. The fix is to first
factor the constant out with `← Finset.mul_sum`, then normalize each
summand to `if x = a then (1 * g x) else 0` via `ite_mul` / `one_mul` /
`zero_mul` (and `mul_ite` / `mul_one` / `mul_zero` for a leading
factor), at which point `Finset.sum_ite_eq'` collapses it.

Concretely (Phase 15 `rigidityRow_eq`, expanding a signed-incidence row
`∑ x, b·((ite_v − ite_u))·m x` to `b·(m v − m u)`):

```lean
simp only [mul_assoc, ← Finset.mul_sum, mul_sub, sub_mul, ite_mul, one_mul,
  zero_mul, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
```

The diagnostic that you've hit this: a `simp only [Finset.sum_ite_eq',
…]` whose `Finset.sum_ite_eq'` argument the linter then flags as
*unused* — the indicator never reached the collapsible shape. Reach for
`← Finset.mul_sum` (constant factor) or restructure the summand before
re-adding it.

## 11. Strong induction on a derived measure (`induction hN : m G using Nat.strong_induction_on`)

To induct on a *derived* `ℕ` measure of an object (`V(G).ncard`,
`E(G).ncard`, …) rather than a structural argument, the idiom is

```lean
intro G
induction hN : V(G).ncard using Nat.strong_induction_on generalizing G with
| _ N IH =>
  intro hG hV2   -- the hypotheses you didn't pre-`intro`
  …
```

Two things to know, both of which bit in Phase 20's
`Graph.minimal_kdof_reduction` (KT Theorem 4.9, the `|V|`-induction):

- **`generalizing G` is mandatory** — otherwise the IH is fixed to the
  *current* `G` and is useless. The motive then quantifies over every
  object of the measure's value, and the IH reads
  `IH : ∀ m < N, ∀ G, V(G).ncard = m → <hyps> → <goal>`.
- **The IH carries the measure-equation `V(G').ncard = m` as an explicit
  argument**, threaded *first*, before the object's own hypotheses. So a
  recursive call on a smaller `G'` is
  `IH _ hlt G' rfl hG' hG'2` (the `rfl` discharges `V(G').ncard =
  V(G').ncard`), and the strict-decrease proof `hlt : V(G').ncard < N`
  uses `hN ▸ (the measure-drop lemma)` to rewrite `N` back to
  `V(G).ncard`. **Do not `subst hN`** — `hN : V(G).ncard = N` binds the
  abstract `N` the goal and `IH` are stated against; substituting it
  re-expresses the goal in `V(G).ncard` and desyncs from `IH`'s `< N`.
  Keep `hN` and `rw [hN]` / `hN ▸` locally where you need the concrete
  count.

## 12. Iterating `+1` around a cyclic `Fin m` (`Fin.ofNat`-based ℕ-induction)

To turn a *consecutive* equality `∀ i : Fin m, f i = f (i + 1)` (the
`+1` being cyclic `Fin m` addition) into a *global* one
`∀ i, f i = f 0` — the "constant around a cycle" step — three obvious
moves fail and one works:

- `(j : Fin m)` for `j : ℕ` does **not** coerce: the parser reads it as
  a type ascription, so you get *"Type mismatch: j has type ℕ but is
  expected to have type Fin m"* (and `(↑j : Fin m)` / `Nat.cast` trip
  *"failed to synthesize NatCast (Fin m)"* — the `NatCast` instance
  wants the literal `n+1` shape, not `Fin m` under `[NeZero m]`).
- `Fin.induction` is for `Fin (n+1)` with the **non-wrapping**
  `Fin.succ : Fin n → Fin (n+1)`, a different operation from cyclic
  `+1`.

The idiom (used in `rankHypothesis_zero_of_cycle`'s
`isTrivialMotion_of_isInfinitesimalMotion_cycle`,
`Molecular/AlgebraicInduction/`):

```lean
have hofNat : ∀ p : ℕ, Fin.ofNat m p + 1 = Fin.ofNat m (p + 1) := fun p => by
  apply Fin.ext; simp [Fin.add_def, Nat.add_mod]
have hnat : ∀ j : ℕ, f (Fin.ofNat m j) = f 0 := by
  intro j
  induction j with
  | zero => rw [Fin.ofNat_zero]
  | succ p ih => rw [← hofNat, ← hstep, ih]
have := hnat i.val
rwa [Fin.ofNat_val_eq_self] at this   -- Fin.ofNat m ↑i = i
```

`Fin.ofNat m : ℕ → Fin m` is the canonical (`[NeZero m]`) cyclic map;
`Fin.ofNat_zero`, `Fin.ofNat_val_eq_self`, and the one-line `hofNat`
successor fact (`Fin.ext` + `simp [Fin.add_def, Nat.add_mod]`, since
both sides are `(p+1) % m`) are all you need. The cyclic index type
`Fin m` *is* the cycle — no `Graph`-walk/connectivity primitive is
required to chain the per-step equalities.

## 13. State a ℕ count `a − b + c` as `a + c − b` (subtraction last)

When the conclusion of a lemma is a natural-number count of the form
`a − b + c` (a free residual after adding `c` and removing `b`), write
it with the **subtraction last**: `a + c − b`. The two are equal in ℝ /
ℤ but **not** in ℕ, where `−` truncates at `0`: at the boundary `b = a`
(so `a − b = 0`), `(a − b) + c = c` but the intended value is
`a + c − b = c`… only when `c ≥ b − a`. The failure shows up as the
*statement* being off-by-one at an extreme case — and then `omega` can't
prove it, because it's genuinely false in ℕ as written.

Concrete instance (`finrank_pinnedMotionsOn_of_isInfinitesimallyRigidOn_vertexSet_inter_eq_singleton`,
`Molecular/AlgebraicInduction/Pinning.lean`): the free-isolated-body count
`|Vᶜ| − |t| + 1` is correct in ℝ, but at the extreme `t = {r} ∪ Vᶜ` the ℕ
form `(|Vᶜ| − |t|) + 1` reads `1` while the true value `|(V ∪ t)ᶜ|` is `0`
(since `|t| = |Vᶜ| + 1 > |Vᶜ|`). Restating as `|Vᶜ| + 1 − |t|` (the `+1`
*inside*, before the `−|t|`) is non-negative throughout (`|t| ≤ |Vᶜ| + 1`)
and `omega` closes it from the partition facts. Rule of thumb: do the
additions first so the single truncating `−` lands on a provably-large
enough quantity.

## 14. "Polynomial with coefficients in a subring `R₀ ⊆ S`" — carry as `(map (algebraMap R₀ S)).range` membership, not `coeffs ⊆ range`

To prove a `MvPolynomial σ S` built from `+`/`−`/`*`/`C r`/`X`/`det` has all
its coefficients in a subring `R₀ ⊆ S` (e.g. *rational coefficients*, `R₀ = ℚ`,
`S = ℝ`), do **not** propagate the `coeffs ⊆ Set.range (algebraMap R₀ S)` form
up the construction directly — that set is not closed under the ring
operations in any usable API. Instead carry **membership in the subring**
`(MvPolynomial.map (algebraMap R₀ S)).range : Subring (MvPolynomial σ S)`: it is
a genuine `Subring`, so `Subring.add_mem` / `sub_mem` / `mul_mem` / `sum_mem` /
`zero_mem` chain through every constructor, `C r ∈ range` reduces to `r ∈ range`
(via `map_C`), `X a` is a fixed point (`map_X`), and the determinant is closed
(`Matrix.det_mem_range_of_entries`, mirrored). Convert to the `coeffs ⊆ range`
form *only at the boundary* — when feeding a consumer that wants it — via
`MvPolynomial.mem_range_map_iff_coeffs_subset`.

Concrete instance (`normalsJoinPoly`/`panelSupportPoly`/`annihRowPoly`
`_mem_range_map`, `Molecular/AlgebraicInduction/PanelLayer.lean`, Phase 22d): the
genericity-device rank polynomial's coefficient-rationality (footnote-6 bridge)
propagates as `… ∈ (MvPolynomial.map (algebraMap ℚ ℝ)).range`, bottoming on the
`complementIso` matrix entry's rationality and `X`'s integer coefficients;
`exists_polynomial_ne_zero_of_linearIndependent_at_coeffs_subset_range` does the
final `det`-and-convert. (FRICTION *[mirrored]* `Matrix.det_mem_range_of_entries`.)

## 15. LI family of `finrank`-many vectors spans `⊤`

To prove `Submodule.span R (Set.range v) = ⊤` from a `LinearIndependent R v`
whose index `ι` has `Fintype.card ι = Module.finrank R V`, route through
`basisOfLinearIndependentOfCardEqFinrank h hcard : Basis ι R V` (the LI family,
having exactly `finrank`-many members, *is* a basis) and `Basis.span_eq`. Two
gotchas: the basis needs `[Nonempty ι]` (supply it inline, e.g.
`⟨⟨(0,1), by decide⟩⟩` for a subtype index), and `Basis.span_eq` produces
`span (range ⇑(basisOf…)) = ⊤`, whose coercion is only *defeq* to `v` — finish by
rewriting `coe_basisOfLinearIndependentOfCardEqFinrank` to turn `⇑(basisOf…)` back
into `v` before the goal matches.

When the LI family is **subtype-valued** (`v : ι → ↥S` for a submodule `S`) but
the LI you have is on the coercion (`fun i => (v i : M)`, e.g. an extensor
landing in the ambient `ExteriorAlgebra` while you want it in a graded piece),
lift the independence across the inclusion with
`(LinearMap.linearIndependent_iff S.subtype (Submodule.ker_subtype _)).1` — the
`subtype ∘ v`-vs-`v` composite is defeq, so no `simp` glue is needed.

Concrete instance (`span_omitTwoExtensor_eq_top`,
`Molecular/RigidityMatrix.lean`, Phase 22e — KT eq. (6.45) / Claim 6.12 N1): the
6 omit-two `2`-extensors of 4 affinely-independent points, LI by Lemma 2.1 in the
ambient exterior algebra, lift into `ScrewSpace 2 = ⋀²ℝ⁴` (finrank `6 =
binom(4,2)`) and span it.

## 16. `(∑ i, f i).comp g` — go pointwise, there is no distributing simp lemma

A `LinearMap` identity with a `∘ₗ` (or `.comp`) sitting *outside* a
`Finset.sum` in the **left** argument — `(∑ i, c i • f i).comp g = ∑ i, c i • (f i).comp g`
— does **not** fall to `simp [LinearMap.smul_comp, …]`: there is no
`LinearMap.sum_comp`, and `map_sum` won't fire because `· ∘ₗ g` isn't recognized as
the hom being mapped over the `∑`. Don't hunt for the distribution lemma.

**Pattern.** Drop to pointwise evaluation: `LinearMap.ext fun x => ?_`, pull the
hypothesis to `x` with `have hx := LinearMap.congr_fun h x`, then `simpa only
[LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply,
<per-term restriction at x>, LinearMap.zero_apply] using hx`. The `sum_apply` pushes
the `∑` inside, and each summand's `.comp single` collapses by a named restriction
lemma evaluated at `x` (supply it as a `have e : ∀ j, … = … := fun j =>
LinearMap.congr_fun (restriction_lemma …) x` if `simp` can't synthesize the
endpoint side conditions). Concrete instance (`candidateRow_ac_eq_neg`,
`Molecular/RigidityMatrix.lean`, Phase 22e — KT eq. (6.44)): the eq.-(6.43) column
combination's `ab`/`ac`-sums collapse to their block-functional sums via
`hingeRow_comp_single_tail` evaluated pointwise.
