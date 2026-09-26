# Phase 40e — PENCIL-X0 / CUT/BRIDGE: cut vertices and bridges (work log)

**Status:** in progress (opened design-first 2026-09-26). STEPS' first group (`notes/Phase40-design.md`
§3 STEPS). It lands the standing hypotheses (H) in Lean and the CUT and BRIDGE steps, (MC-52) and
(MC-53): a cut vertex or a chain of bridges is a fibre product, so `X₀` attaining at both pieces
gives it at `G`. Build 1 landed (H), CUT and the single bridge: seven of nine nodes are green.
Build 2's first half landed the general-`k` fibre lemma: eight of nine nodes are green. A recon
(not committed) ruled out an `X0Attains`-induction route for the theorem and tested the numeric
route's building blocks — see *Hand-off*.
**Next: build 2's second half**, the general-`k` theorem `thm:pencil-x0-bridge` — see *Hand-off*.

## Current state

**Build 1 landed.** Nine nodes, with statements from `ledger.py --brief '(MC-52)' '(MC-53)'` and
the (H) header of `K-main.md`: seven in `main-component.tex` §`sec:main-component-cut`,
`lem:deficiency-cut-vertex` in `deficiency.tex`, `lem:block-rank-cut-vertex` in
`rigidity-matrix.tex`. Seven are green. Two are red: `lem:pencil-bridge-fibre` and
`thm:pencil-x0-bridge`.

**Build 2's first half landed:** `lem:pencil-bridge-fibre` (general `k`), in `Cut.lean`, with
explicit path hypotheses per *Architectural choices* — `pathVertex a x b : Fin (k + 2) → α` is the
extended sequence, and `Graph.exists_liftingRestrict_eq_of_bridgePath` is the restriction-onto
lemma. **A simplification found while building it, not in the original informal proof
(`K-main-MC14.md`'s (MC-53) block): restriction-onto needs only that `a` is `V₁`'s unique gateway**
(no other `V₁` body has an edge leaving `V₁`) — extend `z₁` by the single affine function already
witnessing its own condition at `a`. This needs no admissibility of `q`, no case split on `k`, and
no reference to the path bodies' own non-collinearity (the informal proof's route, which does
split on `k = 0, 1, \ge 2`). Re-derived and compiler-checked before writing it into the blueprint
(`CLAUDE.md` *Working* — a transcribed proof can diverge from what the carrier actually needs).
**The lemma is minimal, not the full path bundle**: it takes `hsub`, `hxV₁`, `ha`, `hb : b ∉ V₁`,
`hpath`, `hsep`, `hz₁` — no `V₂`, no `V(G) = V₁ ∪ V₂ ∪ range x`, no injectivity of `x`, mirroring
how `exists_liftingRestrict_eq_of_bridge` (build 1's single-bridge case) takes no `V₂` either.
**The next concrete commit is build 2's second half**, the theorem `thm:pencil-x0-bridge`, which
turns the last node green.

## Architectural choices made up front

The coordinator's adjudication (2026-09-26) of the STEPS pre-build recon (one opus pass; the verdicts
are in `notes/Phase40-design.md` §3 STEPS):

- **The step contract.** A step concludes `G.X0Attains K` from `Gᵢ.X0Attains K` at smaller graphs in
  the same `Graph α β`. It picks one picture generic for the pieces and main for `G`, chooses heights
  in one fibre (`MvPolynomial.exists_mem_eval_ne_zero₂`), and ends at `Graph.x0Attains_of_exists`.
  CUT and BRIDGE need nothing of the pieces beyond `X0Attains`; (H) at `G` gives its main-picture
  polynomial.
- **(H) is `Graph.IsX0Graph`** (simple, connected, degree `≥ 2`), the working name kept; `h3` follows.
- **BRIDGE for `k ≥ 1`: explicit path hypotheses**, not a chain structure. The chain type is
  designed at CHAIN's open, with its consumers (the ears, COVERAGE's chain detection).
- **The PI's decisions, verbatim** (2026-09-26; also `notes/pencil/adjudications.md`):

  ```adjudication
  PI decisions, 2026-09-26, on this recon's verdict (verbatim answers to the coordinator's questions):
  1. ORBIT risk: "After 40e opens+builds" — land 40e's open and its CUT/BRIDGE build first, then the read-only ORBIT recon (opus) before the next sub-phase opens.
  2. Grouping: "Accept" — 40e = CUT/BRIDGE; the six later groups go into the design doc as a provisional order, with letters minted only as each opens.
  3. Placement: "Deficiency/Bricks" — the cut-vertex deficiency laws in `Molecular/Deficiency.lean` and the rank identity in `Bricks.lean`, per the ROADMAP convention (a lemma lives with its definition), as FLAT did in 40c.
  4. CUT/BRIDGE faithfulness: "Let's formalize the if and leave only if as an explicit todo item."
  ```

## Lemma checklist

Every item but the last two landed in build 1 (standard axioms).

- [x] **(H)**: `Graph.IsX0Graph`, `Graph.three_le_ncard_closedNbhd`,
  `Graph.IsX0Graph.three_le_ncard_closedNbhd` → `def:pencil-x0-standing`.
- [x] **Rank congruence**: `PanelHingeFramework.finrank_span_rigidityRows_ofNormals_congr` →
  `lem:pencil-rank-congr`.
- [x] **Restriction**: `Graph.liftingRestrict` (+ `_apply`), `Graph.liftingRestrict_mem_liftingSpace`,
  `pencilConfigPoint_liftingRestrict`, `restrictPoly`, `eval_restrictPoly` →
  `lem:pencil-lifting-restrict`.
- [x] **Cut-vertex deficiency** (`Deficiency.lean`): `Graph.deficiency_add_le_of_cutVertex`,
  `Graph.deficiency_eq_add_of_cutVertex`, also pinning `Graph.partitionDef_split_of_vertexTwoCut`
  (Phase 39's D5 debt, consumed here) → `lem:deficiency-cut-vertex`.
- [x] **Cut-vertex rank** (`Bricks.lean`): `BodyHingeFramework.finrank_span_rigidityRows_cutVertex_eq`
  → `lem:block-rank-cut-vertex`.
- [x] **Cut-vertex fibre**: `Graph.exists_liftingRestrict_eq_of_cutVertex` → `lem:pencil-cut-fibre`.
- [x] **CUT**: `Graph.X0Attains.of_cutVertex` → `thm:pencil-x0-cut`.
- [x] **Single bridge**: `exists_dotProduct_eq_of_linearIndependent`,
  `Graph.exists_liftingRestrict_eq_of_bridge`, `Graph.X0Attains.of_bridge`, in `Cut.lean` and
  pinned nowhere yet. Build 2 keeps them as its `k = 0` case or replaces them.
- [x] **Onto (the fibre lemma)**: `pathVertex`, `pathVertex_zero`, `pathVertex_eq_or_exists`,
  `Graph.exists_liftingRestrict_eq_of_bridgePath`, in `Cut.lean` → `lem:pencil-bridge-fibre`. The
  gateway argument (*Current state*) replaces the informal proof's `q_a, q_b`/`q_x`/zero-affine
  case split — none of it is needed for onto-ness.
- [ ] **BRIDGE, the theorem** (not spiked) → `thm:pencil-x0-bridge`.
  - Deficiency: KT Lemma 3.6 at the last bridge, then A1 `deficiency_removeVertex_of_degree_eq_one`
    along the pendant path (pin A1 if used: D5 debt).
  - Rank: `le_finrank_span_rigidityRows_of_cut`, iterated.
  - The theorem needs the fuller path bundle the fibre lemma didn't: `V₂`, `hxV₂`,
    `V(G) = V₁ ∪ V₂ ∪ range x`, injectivity of `x` — for the exact vertex/edge counts the rank and
    deficiency identities need. Add them at the theorem's own hypothesis list (or thread through a
    second application of the fibre lemma for the `V₂` side, reversing `x` and `e` — untried,
    check before relying on it).
- [ ] **Tracked, not a close gate:** the "only if" halves of (MC-52)(iv) and (MC-53)(iv)
  (`notes/Phase40-design.md` §3 STEPS).

## Blockers / open questions

- None load-bearing. The theorem is engineering, not a math gap: the numeric route (rank/deficiency
  iterated over the path, never forming an intermediate `X0Attains`) is confirmed sound and its
  building blocks tested (*Hand-off*); what remains is writing the per-step cut-edge facts and the
  numeric telescoping wrapper, twice (deficiency, rank), then the `V₂`-side fibre-lemma reversal
  and the final assembly. Sizeable enough that one recon pass landed no code — see *Hand-off*.

## Hand-off / next phase

**Next: build 2's second half, the theorem** → `thm:pencil-x0-bridge`, in `Cut.lean`. **Not an
X0Attains induction on `k`** — a recon this session (compiler-checked, not committed) ruled that
out: peeling one path vertex at a time via the single-bridge theorem needs `X0Attains` at the
peeled-off single vertex, which is **false** (`Graph.IsAdmissiblePicture`'s closed-neighbourhood
clause needs 3 linearly independent picture points at a body whose closed neighbourhood is just
itself, impossible). This confirms the coordinator's original ROUTE hypothesis. The theorem must
instead compute the **rank inequality and deficiency equality as bare numbers**, iterating the
landed cut bricks directly over the path — never forming an intermediate `X0Attains` claim — then
combine once via `Graph.x0Attains_of_exists`, exactly as `thm:pencil-x0-cut`/`Graph.X0Attains.of_
bridge` (build 1, `k = 0`) already do. Concretely, the tested plan:

- **Use a bare `Fin.snoc x b : Fin (k + 1) → α` tail sequence for the iteration lemmas — not
  `pathVertex a x b`.** `pathVertex`'s double nesting (`Fin.snoc (Fin.cons a x) b`) makes the
  index identity for an *interior* position (`pathVertex a x b (i.castSucc.succ) = x i`) fight
  `simp`; the bare `Fin.snoc x b` version has both endpoint identities close on `simp` alone
  (`(Fin.snoc x b) i.castSucc = x i`, `(Fin.snoc x b) (Fin.last k) = b`, both verified). `a` and
  the first path edge (`a` to `x 0`, or `a` to `b` at `k = 0`) are irrelevant to the deficiency/
  rank-of-the-tail computation below; keep them only in the *outer* one-shot cut (`V₁` vs. the
  tail) where the fibre lemma's own `hgate`-style argument already covers them.
- **Deficiency, tested and ready to reuse verbatim**: for `u` with no self-loop and
  `1 ≤ Graph.bodyBarDim n`, `(G.induce ({u} : Set α)).deficiency n = 0` — proved via
  `Graph.numParts`/`Graph.crossingEdges`/`Graph.partitionDef_one` (`numParts ≤ 1` on a singleton
  vertex set forces every `partitionDef` value `≤ 0`, and `≥ 0` is `partitionDef_one`). This is
  the base case KT Lemma 3.6 (`Graph.deficiency_eq_of_cutEdges_ncard_le_one`) needs at each peeled
  vertex (`(REST_j.induce {x j}).deficiency n = 0`, so peeling contributes exactly `+1` each).
- **The peeling induction, set algebra tested**: define, for `j : ℕ`,
  `restSet j := V₂ ∪ (x '' {i : Fin k | j ≤ i.val})` (so `restSet 0 = V₂ ∪ range x`,
  `restSet k = V₂`). For `j < k`, `restSet j = insert (x ⟨j, hj⟩) (restSet (j + 1))` — the
  `ext`/`rcases eq_or_lt_of_le`/`Fin.ext` proof is written and compiles standalone. Apply KT-3.6
  (deficiency) and `BodyHingeFramework.le_finrank_span_rigidityRows_of_cut` (rank) at each step
  with `V₁ := {x ⟨j, hj⟩}`, cut edge = the tail's `e' j` (linking `x j` to `Fin.snoc x b j.succ`);
  `Graph.induce_induce_of_subset` (`Mathlib/Combinatorics/Graph/Delete.lean`,
  `(G.induce S).induce T = G.induce T` for `T ⊆ S`) collapses `(G.induce (restSet j)).induce
  (restSet j \ {x ⟨j, hj⟩})` back to `G.induce (restSet (j + 1))` in one step. Wrap the per-step
  identity in a numeric induction (on `m := k - j`, or a fresh `∀ j ≤ k, …` downward induction) to
  telescope `k` steps. **Not yet done**: proving the per-step `cutEdges = {e' j}` /
  `hC_ext`/`hcut_mem` facts from `hpath`/`hsep` (needs `x j`'s *other* ambient neighbour, at
  `e' (j - 1)` or the outer bridge edge if `j = 0`, to lie outside `restSet j`, and no third edge
  at `x j` — both follow from `hsep` the same way the fibre lemma's `hgate` derivation did, but
  not yet written for this shape), and the numeric telescoping wrapper itself, **for both
  deficiency and rank** (the rank step additionally needs the nonzero-hinge and rank-congruence
  bookkeeping `Graph.X0Attains.of_bridge`'s proof already carries, generalized per step).
- **Then**: the outer one-shot cut (`V₁` vs. `restSet 0`), the `V₂`-side application of the fibre
  lemma (`Graph.exists_liftingRestrict_eq_of_bridgePath` with `V₁ := V₂`, `a := b`, `hb := a ∉ V₂`,
  and the path reversed — untried, flagged already), and the final `Graph.x0Attains_of_exists`
  assembly mirroring `Graph.X0Attains.of_bridge`'s structure with the `+5(k+1)` / `+6k` counts
  worked out above (*Lemma checklist*).
- **Hygiene (coordinator's note, still open)**: don't touch build 1's `exists_dotProduct_eq_of_
  linearIndependent` / `Graph.exists_liftingRestrict_eq_of_bridge` / `Graph.X0Attains.of_bridge`
  until the theorem lands — they're the only working `k = 0` proof right now, so deleting them
  first would be a regression. Once the theorem exists, check whether it specializes to `k = 0`
  in one line (`x := Fin.elim0`) making all three redundant; if so, delete them and sweep every
  `.lean`/`blueprint/`/`notes/` cross-reference in that same commit (no orphan).
- Gates: `lake build`, `lake lint`, `blueprint/verify.sh`, `blueprint/lint.sh`.

**Then 40e's close.** The read-only ORBIT recon runs before the next group opens (PI). `scratch/`
still holds `S40eTracked.lean`'s `rigidContract_induce_simple` (CONTRACT-R) and the curve-limit
lemma (SPLITOFF), for those groups. The coordinator removes `scratch/` once 40e no longer needs it.

## Decisions made during this phase

- **2026-09-26 — opened design-first from one opus recon.** The coordinator re-ran its three spike
  files: exit 0, no warnings, no `sorry`. `Graph.X0Attains.of_cutVertex` and
  `Graph.X0Attains.of_bridge` use `[propext, Classical.choice, Quot.sound]`. The six tracked items
  are settled in `notes/Phase40-design.md` §3 STEPS, and the later groups are recorded there by
  code.
- **2026-09-26 — build 1: the spike transcribed.** The cut-vertex deficiency laws went in a new
  section at the end of `Deficiency.lean`, after the vertex-2-cut split they specialize. The rank
  identity went in `Bricks.lean`'s 2-cut section. There its proof is shorter than the spike's: the
  private helpers `mem_sup_infinitesimalMotions_induce` (at `u = v`) and
  `rigidityRows_eq_union_induce` do the work. **Headline axioms:** `Graph.X0Attains.of_cutVertex`,
  `Graph.X0Attains.of_bridge`, `Graph.deficiency_eq_add_of_cutVertex` and
  `BodyHingeFramework.finrank_span_rigidityRows_cutVertex_eq` all use
  `[propext, Classical.choice, Quot.sound]`.
- **2026-09-26 — build 2's first half: the fibre lemma re-derived, not transcribed.** The informal
  proof (`K-main-MC14.md`'s (MC-53) block) splits on `k = 0, 1, \ge 2` and leans on the path
  bodies' non-collinearity. A compiler-checked re-derivation found this unnecessary for onto-ness:
  extending `z₁` by the single affine function witnessing its own condition at `a` (`V₁`'s unique
  gateway) works uniformly, for any `k`, without admissibility. Blueprint prose for
  `lem:pencil-bridge-fibre` rewritten to match (dropped `q` admissible, added the explicit
  edge-separation clause `hsep` already encodes). Axioms: `[propext, Classical.choice,
  Quot.sound]`.
