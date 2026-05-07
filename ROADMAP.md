# Combinatorial Rigidity — Roadmap

This directory aims to formalize a slice of **combinatorial rigidity theory**
in mathlib style, culminating in **Laman's theorem** (1970): a graph on
`n ≥ 2` vertices is generically rigid in the plane iff it contains a
spanning subgraph with `2n − 3` edges in which every subgraph on `k ≥ 2`
vertices has at most `2k − 3` edges. Such graphs are called *Laman graphs*
or *minimally rigid* graphs in the plane.

The work is expected to span multiple sessions. This file is the canonical
hand-off document: read it first when picking up the project.

> Design rationale (why these choices and not others) lives in
> `DESIGN.md`. Open it only when you actually need to question a
> decision; otherwise this file is sufficient.

## Directory layout

```
Archive/CombinatorialRigidity/
├── ROADMAP.md         this file — must-read every session
├── DESIGN.md          rationale for cross-cutting design choices
├── TACTICS.md         tactical reference: grind, ncard, mirror rule
├── notes/             per-phase work logs + cross-cutting logs
│   ├── PhaseN.md      lemma checklist + decisions + hand-off for Phase N
│   └── FRICTION.md    long-running API/tactic friction log
├── Mathlib/           mirror for upstream-eligible lemmas (see DESIGN.md)
│   └── …/             each file mirrors its eventual upstream path
├── EdgesIn.lean       Phase 1 — `edgesIn` selector
├── Sparsity.lean      Phase 1 — `IsSparse`, `IsTight`
├── Laman.lean         Phase 1+2 — `IsLaman` and downstream
├── Henneberg.lean     Phase 3 — `typeI`, `typeII` and downstream
└── …                  later phases get their own files
```

## Status

| Phase | File(s) | Status |
|---|---|---|
| 1. Sparsity | `EdgesIn.lean`, `Sparsity.lean`, `Laman.lean` | ✓ Complete (see `notes/Phase1.md`) |
| 2. Laman graphs | `Laman.lean` | ✓ Complete (see `notes/Phase2.md`) |
| 3. Henneberg moves | `Henneberg.lean` | ✓ Complete (see `notes/Phase3.md`) |
| 4. Frameworks | `Framework.lean` | Not yet created |
| 5. Laman's theorem | `LamanTheorem.lean` | Not yet created |

Phase-level details (per-phase lemma checklists, decisions made during
that phase, hand-off notes) live under `notes/PhaseN.md`. Read those
when picking up a phase or reviewing how an earlier phase was finished.

Add lemmas in the file that introduces the relevant definition; a
lemma about `IsSparse` belongs in `Sparsity.lean`, not in `Laman.lean`,
even if it is first used there. When starting a new phase, create the
corresponding `notes/PhaseN.md` file in your first commit.

## Mathematical roadmap

We follow the **Henneberg construction** route, which is elementary and
matches mathlib's combinatorics style. The matroid-theoretic route via
`Mathlib.Combinatorics.Matroid` is left as a future alternative framing.

### Phase 1 — Sparsity (`EdgesIn.lean`, `Sparsity.lean`, `Laman.lean`)

Complete. Defines `edgesIn`, `IsSparse`, `IsTight`, `IsLaman` and the
basic API (monotonicity, subgraph preservation, global edge bound,
vertex partition). See `notes/Phase1.md` for the full lemma list and
phase-specific decisions.

### Phase 2 — Laman graphs (`Laman.lean`)

Complete. Builds the Laman API on top of the Phase 1 `IsLaman`
definition: the `(2, 3)`-tightness `iff` unfolding, the K₂ base case
(promoted to a named theorem), and the degree results that feed into
the Henneberg induction (minimum degree ≥ 2 for `n ≥ 3`; existence of
a degree-2-or-3 vertex). See `notes/Phase2.md` for the full lemma list
and phase-specific decisions.

### Phase 3 — Henneberg moves (`Henneberg.lean`)

Complete. Type I and Type II moves on simple graphs (fresh vertex as
`none : Option V`, old vertices via `some`). Both moves preserve the
Laman property (`typeI_isLaman`, `typeII_isLaman`); both edge-set
decompositions land (`typeI_edgeSet[_ncard]`, `typeII_edgeSet[_ncard]`).
Iso transport (`IsSparse.iso`, `IsTight.iso`, `IsLaman.iso`, plus
`Iso.image_edgesIn`) lifts Laman across graph isomorphisms. The
`K₄ \ e` worked example (`top_fin_four_minus_edge_isLaman`) ties
these together. The structural decomposition iso
`IsLaman.exists_typeI_or_typeII_iso` says every Laman graph on
`n ≥ 3` vertices is iso to a Type I or Type II move on *some* `G'`;
`G'` is the induced subgraph (plus a bridging edge for typeII).

The strengthened "the same `G'` is Laman" version
(`IsLaman.exists_typeI_or_typeII_reverse`) is **not** delivered: it
requires the classical Henneberg blocker argument, since the typeII
reverse can fail for an arbitrary non-adjacent pair (concrete
6-vertex counter-example in `notes/Phase3.md` "Decisions made"). It
is treated as a Phase 5 prerequisite — see §5 below.

See `notes/Phase3.md` for the full lemma list and phase-specific
decisions.

Both moves additionally preserve generic rigidity (proved later in
`Framework.lean`).

### Phase 4 — Frameworks and infinitesimal rigidity (`Framework.lean`)

Definitions:
- `Framework V d := V → EuclideanSpace ℝ (Fin d)` — a `d`-dimensional placement.
- `SimpleGraph.RigidityMatrix G p` — the `#E × d·#V` matrix encoding edge length
  derivatives. Concretely: row indexed by edge `{u, v}` has block
  `(p u − p v)` at columns for `u` and `−(p u − p v)` at columns for `v`.
- `SimpleGraph.IsInfinitesimallyRigid G p d` — null space of the rigidity
  matrix has dimension equal to the dimension of trivial motions
  (`d + d·(d−1)/2` for `#V ≥ d`).
- `SimpleGraph.IsGenericallyRigid G d` — there exists a placement `p` such
  that `G` is infinitesimally rigid at `p` (equivalently, the rigidity matrix
  has full rank for some `p`, hence on a Zariski-open set of placements).

Lemmas to develop:
- Trivial motions form a subspace of dimension `d·(d+1)/2` (when `#V ≥ d`).
- Generic rigidity depends only on `G` (not on the chosen generic `p`).
- Generic rigidity is monotone: `G ≤ G'` and `G` rigid → `G'` rigid.
- For `d = 2`: a generically rigid graph on `n ≥ 2` vertices has `≥ 2n − 3` edges.

### Phase 5 — Laman's theorem (`LamanTheorem.lean`)

The main theorem:
```
theorem SimpleGraph.IsGenericallyRigid_two_iff_hasLamanSubgraph
    {V : Type*} [Fintype V] (G : SimpleGraph V) (h : 2 ≤ Fintype.card V) :
    G.IsGenericallyRigid 2 ↔
      ∃ H : SimpleGraph V, H ≤ G ∧ H.IsLaman
```

Two directions:
- **(⇐)** Henneberg induction: `K₂` is rigid; both Henneberg moves preserve
  generic rigidity; hence every Laman graph is generically rigid; hence so
  is every supergraph. Needs the strengthened decomposition theorem
  `IsLaman.exists_typeI_or_typeII_reverse` — see *Carryover from Phase 3*
  below.
- **(⇒)** If `G` is generically rigid, the rigidity matroid has full rank,
  so there is a basis (an independent edge set) of size `2n − 3`. The
  spanning subgraph on those edges is `(2, 3)`-tight by the matroid property.

The hard direction needs the equality of the **rigidity matroid** and the
**(2, 3)-count matroid** in dimension 2 — the deepest part of the proof.
Lovász–Yemini gave a clean argument; Whiteley's polarity is another route.

#### Carryover from Phase 3

`IsLaman.exists_typeI_or_typeII_reverse` — the strengthened decomposition
theorem that *also* asserts `G'.IsLaman` — is needed for the (⇐) direction
of Laman's theorem (Henneberg induction needs to apply IH to a Laman `G'`).
Phase 3 delivered the iso-only half (`IsLaman.exists_typeI_or_typeII_iso`)
but punted on the Laman claim because the typeII reverse fails for an
arbitrary non-adjacent neighbor pair (counter-example in
`notes/Phase3.md`). Two ways forward:

1. **Henneberg blocker argument.** Classical proof: among the three
   pairs of `v`'s neighbors at least one is non-adjacent (already proven
   as `IsLaman.exists_nonadj_among_three_neighbors`); show that *if every
   non-adjacent pair fails to give a Laman `G'`*, then a tight set in `G`
   is forced to violate sparsity, contradiction. Several pages of graph
   theory, but a self-contained combinatorial argument.
2. **Bypass via the matroid route.** Reformulate (⇐) without strong
   induction on `G'`. E.g., prove "every Laman graph is generically rigid"
   by induction on edge count rather than vertex count, or by using the
   (2,3)-count matroid directly.

Path 1 is closer to mathlib's existing graph theory style; path 2 might be
more elegant if Phase 4 produces a clean rigidity-matroid API.

## Engineering conventions

- **Namespace.** Everything sits inside `SimpleGraph` or
  `CombinatorialRigidity`. No top-level identifiers.
- **Vertex types.** Use `V : Type*` and add `[Fintype V]` only where needed.
  Edge counts use `Set.ncard` so we don't force `Fintype` everywhere.
- **Cardinalities.** Use `Set.ncard` for sets and `Finset.card` for finsets.
  Avoid `ℕ`-subtraction; rephrase `a ≤ b − c` as `a + c ≤ b`.
- **Style.** Module docstrings at the top of each file (`/-! # Title -/`).
  One declaration ↔ one purpose. Comments only when *why* is non-obvious.
- **Imports.** Each file imports the minimum it needs. `Sparsity.lean`
  should import only `SimpleGraph.Basic` + `Set.Card` + minor friends.
- **Decidability.** Add `[DecidableEq V]` / `[DecidableRel G.Adj]` only when
  needed for a specific finset construction. Many definitions can stay
  noncomputable via `Set.ncard`.
- **Predicates are `def`s, not `abbrev`s.** `IsSparse`, `IsTight`,
  `IsLaman`, and `edgesIn` are non-reducible. `grind` will not unfold
  them on its own. To break an `IsTight`/`IsLaman` goal into parts use
  `refine ⟨?_, ?_⟩`; for an `edgesIn` membership use the corresponding
  `mem_*` simp lemma. See `TACTICS.md` § 4 for the full discussion.
- **Missing mathlib lemmas.** If you need a lemma that genuinely
  belongs upstream, put it under `Mathlib/<exact mathlib path>` so
  promotion is later a copy-paste. The directory is created lazily;
  don't pre-populate. See `DESIGN.md` "Mirror directory".
- **Tactic notes.** Practical guidance on `grind` (preferred closing
  tactic in this directory), the `Set.ncard` autoparam pattern, the
  mirror-first rule, and other cross-cutting idioms all live in
  `TACTICS.md`. When in doubt, read it — the section TL;DRs are
  short and save iteration time.

## Per-session workflow

### Starting a session

1. **Read this file end-to-end.** It's short on purpose.
2. `git log --oneline BC-rigidity` to see what the last session did.
3. `lake build CombinatorialRigidity.Laman` (or the leftmost
   active phase's file) to confirm the tree still compiles cleanly
   on its own.
4. Identify the active phase from the Status table. Open
   `notes/PhaseN.md` for that phase if it exists. If the phase has not
   started yet, open ROADMAP's planning section for that phase below
   and create `notes/PhaseN.md` in your first commit (template below).
5. Check `TACTICS.md` if you haven't seen the `grind?` → `grind only`
   workflow or the `Set.ncard` autoparam pattern before.
6. Optional: skim `notes/FRICTION.md` for an open upstream-eligible
   item to land alongside this session's main work. Small mirror PRs
   shipped here mature into mathlib upstream-able patches.

### Working

- Use `TaskCreate` for short-lived intra-session todos. They don't
  persist across sessions.
- Use `notes/PhaseN.md` for lemma-level state that should outlast the
  session (in-progress lemma list, blockers, design choices made
  during this phase).
- When you add a lemma, put it in the file that introduces the
  relevant *definition*, not the file that first uses it. (Lemma
  about `IsSparse` → `Sparsity.lean`, even if first invoked in
  `Laman.lean`.)
- Run `lake build <leftmost active file>` before committing.

### Ending a session

Before committing, do a **friction review** — this is mandatory, not
optional. It is what keeps the project's API gaps from accumulating
silently.

1. **Re-read the lemmas you proved this session.** For each one:
   - Did any rewrite chain feel longer than it should have?
     (Two-rewrite glue lemmas — `coe_X` then `card_X` — are the
     usual culprit.)
   - Did `grind` need an unusually long hint list, or fail in a way
     you worked around rather than understood?
   - Did you hit a deprecation, missing simp lemma, or awkward
     typeclass dance?
2. For each genuine instance:
   - If the missing lemma is **upstream-eligible** (a fact about
     `SimpleGraph`, `Set.ncard`, `Finset`, etc., not specific to
     rigidity), mirror it under
     `Mathlib/<exact mathlib path>` in this commit. The Lean
     namespace stays the upstream one. See DESIGN.md "Mirror
     directory" for the mechanics; refactor the calling proof to use
     the new mirror lemma.
   - If it's **project-internal** (about our `edgesIn`, `IsSparse`,
     etc.), put it in the file that owns the relevant definition.
   - In all cases, add an entry to `notes/FRICTION.md` (open or
     resolved/mirrored as appropriate). Even a one-line entry is
     valuable.
3. **No new entries this session is fine** — but check before commit.

After the friction review, **leave the project so the next agent
can start from ROADMAP.md alone.** That is the contract: ROADMAP.md
plus the active `notes/PhaseN.md` should be enough to identify the
next concrete task without reading any source file or commit history.

This means in the same commit:

- **Update `notes/PhaseN.md`** — the active phase's "Current state",
  "Next", and "Blockers" sections so a cold reader can resume.
- **Move deferred items to where they will land.** A lemma punted
  from Phase 2 to Phase 3 belongs in Phase 3's "Lemmas to develop"
  list with a one-line rationale, not as a footnote in Phase 2.
  Forward-looking TODOs stranded under closed phases rot.
- **If the phase finished:**
  - Flip its row in the Status table to ✓.
  - **Compress its planning section in this file** to a one-paragraph
    summary plus a pointer to `notes/PhaseN.md`. Phase 1's section is
    the canonical model. The lemma list and decisions live in
    `notes/PhaseN.md`; ROADMAP carries the hand-off summary.
- **If you answered a "Choices to revisit" entry** in `DESIGN.md`,
  update it.

Sanity check before commit: re-read the active phase's section. If
you can't summarize the next agent's first task in one sentence, the
section needs more compression or more pointer-discipline.

### Template for `notes/PhaseN.md`

When starting a phase, seed the file with sections like:

```markdown
# Phase N — <name> (work log)

**Status:** in progress.

## Current state
<one-paragraph: what's done, what's mid-stream, what's the next concrete step>

## Lemma checklist
- [x] `lemma_a` — done
- [ ] `lemma_b` — in progress; blocked on …
- [ ] `lemma_c`

## Decisions made during this phase
- <phase-local trade-offs; cross-cutting ones go in DESIGN.md>

## Blockers / open questions
- …

## Hand-off / next phase
<written when the phase finishes; what unlocks the next phase>
```

`notes/Phase1.md` is a complete-phase example.

## References

- G. Laman, *On graphs and rigidity of plane skeletal structures*, J. Engrg.
  Math. **4** (1970), 331–340.
- L. Lovász and Y. Yemini, *On generic rigidity in the plane*, SIAM J.
  Algebraic Discrete Methods **3** (1982), 91–98.
- J. Graver, B. Servatius, H. Servatius, *Combinatorial Rigidity*, AMS GSM 2,
  1993. — main textbook reference.
- T. Jordán, *Combinatorial rigidity: graphs and matroids in the theory of
  rigid frameworks*, MSJ Memoirs, 2016. — modern survey.
- A. Nixon, B. Schulze, W. Whiteley, surveys on rigidity matroids.
