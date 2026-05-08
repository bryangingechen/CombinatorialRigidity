# Phase 5 — Laman's theorem, (⇐) direction (work log)

**Status:** in progress (planning only — no code yet).

This file is the per-phase work record. See `../ROADMAP.md` for the
high-level plan and `../DESIGN.md` for cross-cutting design choices.

## Current state

Phase 5 is about to begin. Target: the (⇐) direction of Laman's
theorem,

```
theorem IsLaman.isGenericallyRigid_two {V : Type*} [Fintype V]
    {G : SimpleGraph V} (h : G.IsLaman) : G.IsGenericallyRigid 2
```

plus the bridge to the iff statement
`isGenericallyRigid_two_iff_exists_isLaman_le` via
`IsGenericallyRigid.mono`. The (⇒) direction (Lovász–Yemini matroid
duality) is **deferred to Phase 6** — it requires a rigidity-matroid
API that Phase 4 deliberately did not stand up. The iff statement
lands in `LamanTheorem.lean` from the first commit, *composed* from
two named directional theorems (one of which is `sorry`-blocked for
Phase 5 milestone 3, the other for Phase 6).

The proof of (⇐) is a Henneberg induction on `Fintype.card V`:

* **Base.** `K₂` is generically rigid in dim 2
  (Phase 4: `top_fin_two_isGenericallyRigid 2`).
* **Step.** Given Laman `G` on `n ≥ 3` vertices, the strengthened
  decomposition `IsLaman.exists_typeI_or_typeII_reverse` gives Laman
  `G'` on `n − 1` vertices plus a Henneberg-iso `G ≃g typeI/II G' …`.
  Induction on `G'`; the per-move rigidity-preservation lemmas
  (`typeI_isGenericallyRigid_two`, `typeII_isGenericallyRigid_two`)
  plus iso transport lift the conclusion back to `G`.

So (⇐) breaks into three milestones, each likely a small commit
cluster:

1. **Reverse decomposition** — `IsLaman.exists_typeI_or_typeII_reverse`
   (in `Henneberg.lean`) via the Henneberg blocker argument.
2. **Move preservation** — `typeI_isGenericallyRigid_two` and
   `typeII_isGenericallyRigid_two` in `Henneberg.lean`.
3. **Induction** — fill in `IsLaman.isGenericallyRigid_two` (the
   milestone-0 sorry); the iff's (⇐) arm completes automatically
   thanks to the structured composition.

Milestones 1 and 2 are independent and can be worked in either order.

## Architectural choices made up front

These extend `../DESIGN.md` *Choices to revisit*; if any turns out
wrong, revisit there.

- **(⇐) only; (⇒) is Phase 6.** ROADMAP §5 commits to the iff
  statement — that lands in `LamanTheorem.lean` from the first commit
  with the (⇒) arm as `sorry`. (⇒) needs the Lovász–Yemini equality
  "rigidity matroid = (2,3)-count matroid in dim 2," which is its own
  multi-session sub-project on top of a `RigidityMatroid.lean`. Phase 4
  *Architectural choices* explicitly kept the rigidity matroid out of
  scope; reversing that within Phase 5 would balloon the phase. Phase 6
  picks it up if and when warranted.

- **Henneberg-blocker route, not matroid bypass.** The reverse lemma
  is proved combinatorially via the classical Whiteley/Jordán argument:
  if every non-adjacent neighbor pair of a degree-3 vertex `v` blocks
  the Type II reverse, a `(2, 3)`-tight set in `G` is forced to violate
  sparsity. Pure graph theory; matches the project's existing
  `IsSparse` / `IsTight` / `edgesIn` style. Path 2 (matroid bypass)
  was rejected for the same reason as the (⇒) deferral above.
  ROADMAP §5 *Carryover from Phase 3* and DESIGN.md *Why Henneberg*.

- **Specialize to `d = 2` at the Phase 5 boundary.** Per
  Phase 4 *Architectural choices*, every Phase 4 result is general
  in `d`. Phase 5 is responsible for the `d = 2` specializations:
  `IsGenericallyRigid.card_mul_le_two` (`2 * #V ≤ #E + 3`, one-line
  corollary of `IsGenericallyRigid.card_mul_le`) and the per-move
  rigidity-preservation lemmas. The move-rigidity proofs are
  intrinsically d=2 — the "place new vertex off the line through
  neighbors" / rotation-trick arguments are dimension-2 facts.
  General-`d` Henneberg is mathematically harder and not on the
  critical path.

- **Reverse lemma signature.** The Phase-3 deferred theorem:
  ```
  theorem IsLaman.exists_typeI_or_typeII_reverse [Fintype V]
      {G : SimpleGraph V} (h : G.IsLaman) (hV : 3 ≤ Fintype.card V) :
      ∃ (v : V) (G' : SimpleGraph {w : V // w ≠ v}), G'.IsLaman ∧
        ((∃ a b, a ≠ b ∧ Nonempty (G ≃g typeI G' a b)) ∨
         (∃ a b c, a ≠ b ∧ c ≠ a ∧ c ≠ b ∧ G'.Adj a b ∧
          Nonempty (G ≃g typeII G' a b c)))
  ```
  The same shape as `exists_typeI_or_typeII_iso` plus the `G'.IsLaman`
  conjunct. The iso version is *not* superseded — it stays as the
  natural building block; the strengthened version composes the
  Laman-claim on top.

- **Move-preservation lemmas live in `Henneberg.lean`.** The
  `typeI_isLaman` / `typeII_isLaman` lemmas already live there; the
  `_isGenericallyRigid_two` companions land alongside, exposing the
  per-move parallel structure. Cost: `Henneberg.lean` will need to
  import `Framework.lean` (today it doesn't); `Framework.lean` is a
  leaf in the import DAG so this is a forward edge, not a cycle. An
  alternative was a separate `HennebergRigidity.lean`; rejected
  because the lemma counts are small.

## Lemma checklist

Listed by milestone. Items live in `LamanTheorem.lean` unless tagged
otherwise. Helpers and signatures will refine as proofs open up;
treat the names below as working names.

### Milestone 0 — First commit (smallest concrete unit) — done

- [x] `LamanTheorem.lean` created. Three named theorems per the
  structured-`sorry` layout: `IsLaman.isGenericallyRigid_two`
  (sorry, milestone 3), `IsGenericallyRigid.exists_isLaman_le`
  (sorry, Phase 6), and the composed iff
  `isGenericallyRigid_two_iff_exists_isLaman_le` (no sorry; `mp`
  is `.exists_isLaman_le`, `mpr` rcases's the Laman subgraph and
  routes through `.isGenericallyRigid_two.mono`).
- [x] `IsGenericallyRigid.card_mul_le_two` — one-liner via
  `hG.card_mul_le` (the `d = 2` specialization is defeq;
  `2 * (2+1) / 2 = 3`).
- [x] `IsGenericallyRigid.iso` — iso transport for generic rigidity
  in `Framework.lean`, plus the underlying
  `IsInfinitesimallyRigid.iso`. Built via a direct `LinearEquiv`
  between the two rigidity-map kernels (precomposition with `φ`)
  and `LinearEquiv.finrank_eq`. ~30 lines for the
  `IsInfinitesimallyRigid` half plus a 3-line `obtain`-`exact` for
  the `IsGenericallyRigid` lift.

### Milestone 1 — Reverse decomposition (`Henneberg.lean`)

The Henneberg blocker / "good vertex" argument; cf. Whiteley
§3 / Jordán §3.1.

- [ ] (Helper, working name) `IsTight.union_of_inter_card_ge_two` —
  closure of the `(k, ℓ)`-tight-set lattice under union when the
  intersection has size `≥ ⌈ℓ/k⌉ + 1` (or the Phase-5-specific form
  needed). Belongs in `Sparsity.lean`. Refine signature once the
  blocker proof is written.
- [ ] (Helper, working name) `IsLaman.tight_blocking_neighborhood` —
  if every non-adjacent pair among `v`'s degree-3 neighbors fails to
  give a Laman `G'`, there is a `(2, 3)`-tight `S ⊆ V \ {v}`
  containing all three neighbors. Working name; refine as the proof
  takes shape.
- [ ] `IsLaman.exists_typeI_or_typeII_reverse` — strengthened
  decomposition. Re-uses `IsLaman.exists_typeI_or_typeII_iso` for
  the iso half; the new content is the `G'.IsLaman` claim, by case
  split on degree-2 (typeI, automatic) vs degree-3 (typeII, blocker
  argument).

The exact helper count and signatures will firm up only mid-proof —
Whiteley §3.1 uses 2–3 auxiliary lemmas. Expect 1–2 mirror candidates
(probably around `Set.ncard` set-arithmetic or `SimpleGraph.induce`
edge counting).

### Milestone 2 — Move preservation in dim 2 (`Henneberg.lean`)

The classical "Henneberg moves preserve rigidity" arguments. Both go
through a *specific* placement extension; the conclusion is then
"`IsGenericallyRigid` in dim 2" (existence of a rigid placement, not
genericity in the algebraic-geometry sense).

- [ ] `typeI_isGenericallyRigid_two` — Type I preserves generic
  rigidity. Construction: extend a rigid placement `p'` of `G'` to a
  placement `p` of `typeI G' a b` by placing the new vertex off the
  line through `p' a` and `p' b`. The two new rigidity-matrix rows
  are linearly independent; rank-nullity gives `dim ker p = dim ker p'`.
- [ ] `typeII_isGenericallyRigid_two` — Type II preserves generic
  rigidity. Trickier: deletes edge `s(a, b)`, adds three new edges.
  Plan: pick a placement extension where the new vertex's edges
  recover the deleted constraint plus one new constraint
  (rotation/limit argument). Decide the formalization mechanics
  during proof, not during planning.

These are the linear-algebra heart of (⇐). Likely surfaces 1–3 mirror
candidates around `LinearMap.ker` / `Submodule.finrank` rank-counting,
plus possibly an "affinely-independent points off a line" or "rank of
augmented matrix" lemma.

### Milestone 3 — Induction (fills milestone-0 sorry)

- [ ] Replace milestone-0's `sorry` body of
  `IsLaman.isGenericallyRigid_two` with the actual proof. Strong
  induction on `Fintype.card V`. Base: `n = 2` via `top_fin_two_isLaman`
  + `top_fin_two_isGenericallyRigid 2` and `IsLaman.iso` /
  `IsGenericallyRigid.iso`. Step: `exists_typeI_or_typeII_reverse` +
  per-move preservation + iso transport.

No additional theorem is needed for the iff arm: milestone 0's
structured form already routes (⇐) through
`IsLaman.isGenericallyRigid_two`, so once this `sorry` is filled in
the iff's `mpr` arm completes automatically.

## Decisions made during this phase

### Phase-local choices and proof techniques

- **`IsInfinitesimallyRigid.iso` proof structure: build the kernel
  iso directly, not via `Submodule.map`.** First attempt routed the
  proof through `(ker H).map Φ.toLinearMap = ker G` and
  `LinearEquiv.finrank_map_eq`. Stalled on a `SetLike` membership-
  form mismatch after `rintro` (see FRICTION). Refactored to a
  direct `LinearEquiv` between the two kernel subtypes; the
  membership obligations there are `q'.2`-typed and `LinearMap.mem_ker.mp/mpr`
  works without bridging. Cleaner, ~30 lines.

### Promoted to TACTICS / FRICTION / DESIGN

- *`Exists.imp` doesn't transport across changing-binder-type
  existentials* → FRICTION [resolved].
- *`rw [LinearMap.mem_ker]` fails on `SetLike`-coerced membership
  after `Submodule.mem_map` destructure* → FRICTION [resolved].

## Blockers / open questions

- **Affine-spanning side condition for Type I preservation.** The
  textbook proof places the new vertex generically, then argues
  "kernel doesn't grow because the new rows are independent." The
  cleanest formalization may want an affinely-spanning hypothesis on
  `p'` (so `p` remains affinely spanning after extension). Phase 4
  did not ship `finrank_trivialMotions_eq_of_affinelySpanning`; if the
  Type I proof wants it, fill in then. Phase 4 hand-off explicitly
  flagged this as the deferred-API surface most likely to be needed.

- **Henneberg-blocker proof length.** Textbook proofs of the reverse
  decomposition are 1–2 pages; the formalization will be
  longer. If milestone 1 sprawls past ~3 sessions, reassess: perhaps
  an internal lemma about tight-set lattices belongs in
  `Sparsity.lean` as a named theorem rather than a private helper, or
  a refactor of `exists_nonadj_among_three_neighbors` is warranted.

## Hand-off / next phase

Milestones 0 (LamanTheorem stub + d=2 corollary + iso transport) is
complete. The next session attempts **Milestone 1**: the Henneberg
blocker proof of `IsLaman.exists_typeI_or_typeII_reverse` (in
`Henneberg.lean`).

Read Whiteley §3.1 or Jordán §3.1 for the textbook argument before
starting; expect 1–3 helper lemmas to surface, plausibly around
tight-set unions in `Sparsity.lean`. Milestones 1 and 2 are
independent — if the blocker proof stalls, milestone 2 (Type I
preservation in `Henneberg.lean`, which will also need to import
`Framework.lean` for the first time) is a clean parallel target.
Milestone 3 (induction) is ready once milestone 1 *and* both
move-preservation lemmas land.
