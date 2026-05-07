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
- The directory `Archive/CombinatorialRigidity/Mathlib/` is created
  lazily; don't pre-populate.
- Each mirrored lemma also gets a `[mirrored]` entry in
  `notes/FRICTION.md` with its mirror-file path.

See `DESIGN.md` "Mirror directory" for the full mechanics.

Why we go to this trouble: the resolved entries in
`notes/FRICTION.md` are the running list of "lemmas the project found
mathlib should have." They mature into upstream PRs. Inlining a
hand-rolled version skips that pipeline.

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
