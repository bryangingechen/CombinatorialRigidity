# Tactics and idioms

This file is the project's tactical reference. It collects the proof
patterns we use repeatedly and the small "always do X" rules that make
the difference between a clean proof and a verbose one.

If you are about to write a `Set.ncard` proof, or invoke `grind`, or
reach for a mirror lemma, skim the relevant section first.

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

**Keep `omega` in the back pocket.** For goals that are pure linear
integer arithmetic with no equational reasoning to do (and where you
don't need any lemma hints), `omega` is faster and more readable. We
default to `grind` because most of our goals mix arithmetic with
equational steps, but `omega` is the right call for purely arithmetic
ones.

**`omega`/`grind` treat `set`-aliased terms as opaque atoms.** When a
proof opens `set name := expr with name_def` and later receives a
hypothesis mentioning `expr` literally (typically from a downstream
lemma call), the two views are defeq but `omega`/`grind` see them as
distinct atoms and won't bridge across. Fix with one explicit
`rw [← name_def] at h_expr_form` (or `rw [name_def] at h_alias_form`)
before invoking the tactic. The `set` tactic's substitution scope is
bounded by *current* goals/hypotheses, not future tactic outputs —
this is intrinsic, not a bug. Same pattern bites `grind`. See
`IsLaman.typeII_reverse_blocker` in `Henneberg.lean` for a worked
case.

**`omega` doesn't carry commutativity or distributivity on atoms.**
If `omega` has `k * #s` on one side and `#s * k` on the other (or
`k * #(s ∪ t) + k * #(s ∩ t)` vs. `k * #s + k * #t`), it sees four
unrelated atoms and fails. Pre-normalize: `rw [mul_comm]` for
commutativity, or stage a `have h_mul : … := by rw [← Nat.mul_add,
← Nat.mul_add, Finset.card_union_add_card_inter]` for distributivity,
then hand the multiplied identity to omega alongside the unmultiplied
facts. (One-liner alternative: `linear_combination k * h.symm`, but
this requires `Mathlib.Tactic.LinearCombination`.) `IsTightOn.union_inter`
in `Sparsity.lean` is the canonical worked case.

**ℕ-quadratic bounds: `Nat.le_mul_self`.** `nlinarith` over ℕ
doesn't reliably close `4 * d + 2 ≤ (d + 1) * (d + 2)`-shaped goals
from scratch — ℕ-subtraction truncates and it can't recover the
squaring. Expand the quadratic with `ring`-via-`have`, surface
`d ≤ d * d` via `Nat.le_mul_self d`, then close with `omega`.
Worked case: `top_fin_two_isGenericallyRigid` in `Framework.lean`.

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

## 8. Tactic quirks and Lean idioms

A reference table of "you'll hit this once and lose a build cycle,
then never again." Skim the headers when a proof goes sideways with a
confusing error.

### `subst` between two free variables picks the wrong one

When `h : a = b` has both sides free in scope, `subst h` eliminates
one — and Lean's heuristic is "the *less-recently-introduced* free
variable when both qualify." Two recurring traps:

- `rcases Sym2.eq_iff.mp h_eq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩` inside
  an `induction e with | h u v => …` after a `by_cases h_eq : s(u, v)
  = s(a, b)`: the `rfl` patterns substitute *the theorem binders
  `a, b`* (older) rather than the case-split intros `u, v` (newer).
  A follow-up `have hflip : p b - p a = …` then fails with `Unknown
  identifier b`.
- `by_cases hvc : v = c; · subst hvc`: substitutes `c` (the function
  signature variable, older) and leaves `v`. Subsequent uses of `c`
  fail.

**Fix:** bind the equalities to named hypotheses and use `rw`, which
doesn't eliminate from the context:

```lean
rcases Sym2.eq_iff.mp h_eq with ⟨h1, h2⟩ | ⟨h1, h2⟩
· rw [h1, h2]; …
· rw [h1, h2, /- sign flip -/]; …
```

When `grind` is the closer it papers over this — both branches close
regardless of which variables remain. Reach for named hypotheses
only when downstream tactics depend on a specific name.

### `simp only` leaves residual subterms that block `rw` motives

If you `simp only […]` and then a follow-up `rw [h]` fails with
*motive is not type correct*, citing a hypothesis (like `he`) that
doesn't appear in the displayed goal — suspect a `simp`-produced
residual subterm hiding inside an `Eq` proof. Insert `change
<displayed clean form>` between the `simp only` and the `rw`:

```lean
simp only [rigidityMap_apply, Pi.zero_apply, Function.comp_apply]
change ⟪p u - p v, x (some u) - x (some v)⟫_ℝ = 0
rw [h1, h2]; …
```

The `change` re-elaborates the goal at the surface type, discarding
the residual. Canonical case: `typeII_isInfinitesimallyRigid_extend`
in `Henneberg.lean`.

### `set name := fun t => …` + `simp [name]` doesn't unfold lambdas

`simp [name]` on a `set`-introduced abbreviation whose body is a
lambda often fails (or worse, gives a `⊢ sorry () c = …`-style
elaboration glitch). Prefer `let` plus explicit `have`-lemmas that
state the reductions you need:

```lean
let p_t : ℝ → Framework V 2 := fun t => Function.update p₀ c (p₀ c + t • w)
have h_p_t_c : ∀ t, p_t t c = p₀ c + t • w :=
  fun _ => Function.update_self c _ p₀
have h_p_t_ne : ∀ t v, v ≠ c → p_t t v = p₀ v :=
  fun _ v hvc => Function.update_of_ne hvc _ p₀
```

Reference the `have`-lemmas in downstream reasoning rather than
trying to round-trip through `simp [p_t]`.

### `interval_cases` is for free variables, not function applications

`interval_cases (Fintype.card V)` enumerates the cases but does
**not** substitute `Fintype.card V` in the context — so an arm's
`Fintype.card V = 2` won't close by `rfl`. `interval_cases` only
performs `subst` on free *variables*.

**Fix:** for value equations on function applications, derive the
equation as a named hypothesis via `omega` (or `decide`, etc.) and
hand it to downstream lemmas explicitly:

```lean
by_cases hV3 : 3 ≤ Fintype.card V
· -- high branch
· -- low branch
  have hcard2 : Fintype.card V = 2 := by
    have := IsLaman.edgeSet_ncard …
    omega
  exact h.eq_top_of_card_eq_two hcard2
```

Canonical case: `IsLaman.isGenericallyRigidInj_two_of_card` in
`LamanTheorem.lean`.

### Dot notation only consults the type's head namespace

Two related traps:

- **Sub-namespace lookup fails.** Inside `namespace SimpleGraph.Henneberg`,
  with `h : G.IsLaman`, writing `h.typeII_reverse_blocker …` looks up
  `SimpleGraph.IsLaman.typeII_reverse_blocker`, **not**
  `SimpleGraph.Henneberg.IsLaman.typeII_reverse_blocker`. Error
  appears as ``And.typeII_reverse_blocker not found`` because Lean
  unfolds `IsLaman → IsTight → And` while searching. Fix: call by
  explicit name from inside the sub-namespace —
  `IsLaman.typeII_reverse_blocker h …` resolves correctly via the
  partial-prefix lookup.
- **Same-name wrapper recurses.** Inside `theorem
  EdgeSetRowIndependent.mono`, writing `hI.mono h` resolves `.mono`
  to *the function being defined* (Lean prefers the head namespace
  of the term's *stated* type before unfolding), not the upstream
  `LinearIndepOn.mono` you intended. Spell out the upstream name
  explicitly when wrapping a same-named upstream lemma.

### `congr_fun` does not apply to `EuclideanSpace`

`EuclideanSpace ℝ ι` is `PiLp 2 (fun _ => ℝ)`, not `ι → ℝ`. Even
though the carrier coerces, `congr_fun h 0` errors out with
`Application type mismatch`. To extract a coordinate, route through
a continuous map (norm, inner product) or use `EuclideanSpace.equiv`
/ `PiLp.equiv` for an explicit conversion. Same caveat for `Sym2 V` —
projection there goes through `Sym2.lift`, not `congr_fun`.

### `simp_all` can cross-contaminate with destructive equality hypotheses

If `simp_all` encounters `hij : 0 = X`, it may rewrite *every*
occurrence of `0` in the context to `X` — including inside
hypotheses you wanted to keep. When `simp_all` produces a confusing
residual goal involving a hypothesis you expected to eliminate,
suspect cross-rewriting. Route through a derived quantity that
doesn't trigger it:

```lean
have h_norm : ‖p i‖ = ‖p j‖ := congrArg _ hij
revert h_norm <;> simp [hp_def]
```

### `linearIndependent_fin2` leaves `![v₀, v₁] 0 / 1` unsimplified

After `rw [linearIndependent_fin2] at hLI`, the destructured form
carries `![v₀, v₁] 0` and `![v₀, v₁] 1` at the indexing layer, which
won't match patterns like `p₀ c - p₀ a` in downstream goals. Always
pair with the matrix-indexing simp set:

```lean
rw [linearIndependent_fin2] at hLI
simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hLI
```

then `push Not`, `obtain`, etc.
