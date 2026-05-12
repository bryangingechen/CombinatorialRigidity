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
│   ├── FRICTION.md    long-running API/tactic friction log
│   └── PERFORMANCE.md build-time + profiling notes — read before a perf pass
├── Mathlib/           mirror for upstream-eligible lemmas (see DESIGN.md)
│   └── …/             each file mirrors its eventual upstream path
├── EdgesIn.lean       Phase 1 — `edgesIn` selector
├── Sparsity.lean      Phase 1 — `IsSparse`, `IsTight`
├── Laman.lean         Phase 1+2 — `IsLaman` and downstream
├── Henneberg.lean     Phase 3 — `typeI`, `typeII` and downstream
├── Framework.lean     Phase 4 — frameworks, rigidity map
├── HennebergRigidity.lean  Phase 5 milestone 2 — per-move rigidity preservation
├── LamanTheorem.lean  Phase 5+6 — Laman's theorem (both directions)
└── …                  later phases get their own files
```

## Status

| Phase | File(s) | Status |
|---|---|---|
| 1. Sparsity | `EdgesIn.lean`, `Sparsity.lean`, `Laman.lean` | ✓ Complete (see `notes/Phase1.md`) |
| 2. Laman graphs | `Laman.lean` | ✓ Complete (see `notes/Phase2.md`) |
| 3. Henneberg moves | `Henneberg.lean` | ✓ Complete (see `notes/Phase3.md`) |
| 4. Frameworks | `Framework.lean` | ✓ Complete (see `notes/Phase4.md`) |
| 5. Laman's theorem (⇐) | `LamanTheorem.lean`, `HennebergRigidity.lean` | ✓ Complete (see `notes/Phase5.md`) |
| 6. Laman's theorem (⇒) | `LamanTheorem.lean`, `RigidityMatroid.lean` | Not yet started |

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

Both moves additionally preserve generic rigidity (TODO in Phase 5,
because the proof needs the typeII reverse blocker argument).

### Phase 4 — Frameworks and infinitesimal rigidity (`Framework.lean`)

Complete. Defines `Framework V d` as `V → EuclideanSpace ℝ (Fin d)`,
the `RigidityMap G p` as an `ℝ`-linear map (the matrix view via
`LinearMap.toMatrix` is deferred until needed), `IsInfinitesimallyRigid
G p` as the kernel-dimension bound `dim ker ≤ d(d+1)/2`, and
`IsGenericallyRigid G d` as existence of an infinitesimally rigid
placement. Ships the basic `RigidityMap` API (`Framework.finrank`,
`rigidityMap_apply`, `rigidityMap_ker_mono`,
`rigidityMap_finrank_range_le`), the graph-monotonicity corollaries
(`IsInfinitesimallyRigid.mono`, `IsGenericallyRigid.mono`), the main
edge-count theorem `IsGenericallyRigid.card_mul_le` (`d * #V ≤ #E +
d(d+1)/2` for any generically rigid graph), and the K₂ worked example
`top_fin_two_isGenericallyRigid`. The `TrivialMotions` API (textbook
identification of kernel with rigid motions) and the
`finrank_trivialMotions_eq_of_affinelySpanning` lemma are deferred —
neither is on the critical path for Phase 5. See `notes/Phase4.md` for
the full lemma list and phase-specific decisions.

### Phase 5 — Laman's theorem, (⇐) direction (`LamanTheorem.lean`, `HennebergRigidity.lean`)

Complete. The main iff statement lives in `LamanTheorem.lean`:
```
theorem SimpleGraph.isGenericallyRigid_two_iff_exists_isLaman_le
    {V : Type*} [Fintype V] (G : SimpleGraph V) (h : 2 ≤ Fintype.card V) :
    G.IsGenericallyRigid 2 ↔
      ∃ H : SimpleGraph V, H ≤ G ∧ H.IsLaman
```
*composed* from two named directional theorems —
`IsLaman.isGenericallyRigid_two` for (⇐), proved in Phase 5, and
`IsGenericallyRigid.exists_isLaman_le` for (⇒), `sorry`-blocked and
resolved in **Phase 6** (see §6 below).

**(⇐) recap.** Henneberg induction on `Fintype.card V`. K₂ base case
via `top_fin_two_isGenericallyRigidInj 1` + iso transport. Inductive
step via `IsLaman.exists_typeI_or_typeII_reverse` (strengthened
decomposition with `G'.IsLaman`, proved via the Henneberg blocker
argument) plus per-move rigidity preservation
(`typeI_isGenericallyRigidInj_two` /
`typeII_isGenericallyRigidInj_two`, both unconditional). The Type II
move's collinearity gap is discharged by `IsInfinitesimallyRigid.
eventually` (openness of IR via `LinearIndependent.eventually`) plus
a perpendicular perturbation packaged in
`exists_nonCollinear_rigid_placement_dim_two`. See `notes/Phase5.md`
for the full lemma list and proof techniques.

### Phase 6 — Laman's theorem, (⇒) direction (`LamanTheorem.lean`, `RigidityMatroid.lean`)

If `G` is generically rigid in dim 2, the rigidity matroid has full
rank, so there is a basis (a row-independent edge set) of size
`2n − 3`. The spanning subgraph on those edges is `(2, 3)`-tight by
the matroid property; combined with Phase 5's (⇐) the iff closes.

The deep step is the equality of the **rigidity matroid** and the
**(2, 3)-count matroid** in dimension 2. Lovász–Yemini's argument is
the standard reference; Whiteley's polarity is another route.

Phase 4 deliberately kept `Framework.lean` matroid-agnostic (see
DESIGN.md *Notion- and matroid-agnostic core*). Phase 6 stands up
`RigidityMatroid.lean` on top, then fills in
`IsGenericallyRigid.exists_isLaman_le` in `LamanTheorem.lean`,
completing the iff. A concrete plan lives in `notes/Phase6.md` once
Phase 6 starts.

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
- **No prose counts in shared docs.** Don't write "Phase X surfaced
  N upstream candidates" or similar in `ROADMAP.md`, `DESIGN.md`, or
  `TACTICS.md` — counts drift the moment a new phase mirrors more
  lemmas. Link to `notes/FRICTION.md` "Mirrored" (or the mirror
  directory listing) as the source of truth instead.

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

   **Concrete signals.** Friction almost certainly happened if you
   wrote any of the following — each is a candidate FRICTION entry,
   not a "standard idiom" to dismiss:
   - `change` or `show` to make `rw` / `simp` find a pattern (the
     un-reduced lambda or `def`-predicate is the gap).
   - A multi-rewrite chain (3+ `rw` arguments) for one mathematical
     step — usually a missing fused lemma.
   - A manual `have h : <unfolded body> := h_predicate` to surface a
     `def`-predicate's content for `omega` / `grind` (cf. TACTICS § 4
     for the `IsLaman` / `IsTight` cases — `IsInfinitesimallyRigid`
     joined the club in Phase 4).
   - `omega` or `nlinarith` failed and you added a numeric hint, a
     `ring`-normalized rewrite, or a manual `mul_comm`.
   - Two `rw` lemmas to bridge a single conversion (e.g. `coe_X` then
     `card_X`, or `Set.ncard_eq_toFinset_card'` then
     `Set.toFinset_card`) — usually a one-line mirror.

   **Bar is low.** Anything that took a build-failure → fix iteration
   deserves at minimum a one-line FRICTION entry, even if the fix was
   "obvious in hindsight". Phase 4 closed having logged zero entries
   on the first pass and six on the second — the lesson is that "this
   is just a standard mathlib idiom" is not an excuse if you spent a
   build cycle figuring it out. The next agent doesn't have your
   hindsight.

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
3. **No new entries this session is fine** — but only after you've
   walked the *Concrete signals* checklist above. "I didn't hit any"
   is fine; "I didn't think about it" is the failure mode this rule
   exists to prevent.

After the friction review, **leave the project so the next agent
can start from ROADMAP.md alone.** That is the contract: ROADMAP.md
plus the active `notes/PhaseN.md` should be enough to identify the
next concrete task without reading any source file or commit history.

This means in the same commit:

- **Update `notes/PhaseN.md`** — the active phase's "Current state",
  "Next", and "Blockers" sections so a cold reader can resume. When
  writing the *Hand-off / next phase* section, name the **smallest
  concrete commit** that moves the next phase forward, not the full
  target theorem. If you genuinely don't know whether the next lemma
  is one session's work or three, say so explicitly: "land the iso
  half; assess the Laman-preservation half once it closes" beats
  "deliver the full decomposition theorem". Phase 3 hit this trap
  with `exists_typeI_or_typeII_reverse`.
- **Move deferred items to where they will land.** A lemma punted
  from Phase 2 to Phase 3 belongs in Phase 3's "Lemmas to develop"
  list with a one-line rationale, not as a footnote in Phase 2.
  Forward-looking TODOs stranded under closed phases rot.
- **Lift on promotion.** If a `notes/PhaseN.md` decision has been
  referenced in 2+ files or by 2+ phases, promote it to `TACTICS.md`
  (general idiom) or `DESIGN.md` (cross-cutting rationale) and
  replace the Phase N entry with a one-line pointer. Cross-cutting
  lessons that stay in phase notes rot — this is the rule that
  prevents Phase notes from accumulating into 500-line documents.
- **If the phase finished:**
  - Flip its row in the Status table to ✓.
  - **Compress its planning section in this file** to a one-paragraph
    summary plus a pointer to `notes/PhaseN.md`. Phase 1's section is
    the canonical model. The lemma list and decisions live in
    `notes/PhaseN.md`; ROADMAP carries the hand-off summary.
  - **Review project organization.** Re-skim ROADMAP.md, TACTICS.md,
    and FRICTION.md (status sections). Have decisions in
    `notes/PhaseN.md` accumulated past the lift-on-promotion threshold?
    Has FRICTION.md grown unscannable? Is any DESIGN.md / ROADMAP.md
    prose-count or section-name reference stale? Apply the small fix
    in this commit if obvious; otherwise file a project-organization
    friction entry to address next phase. This step is what keeps the
    docs from drifting between phase boundaries.
- **If you answered a "Choices to revisit" entry** in `DESIGN.md`,
  update it.

Sanity check before commit: re-read the active phase's section. If
you can't summarize the next agent's first task in one sentence, the
section needs more compression or more pointer-discipline.

### Writing phase notes

`notes/PhaseN.md` is a working log, not an essay. The hand-off
contract — ROADMAP + active Phase N notes — only holds if the file
stays scannable.

**One-screen-per-entry rule.** Each "Decisions made" entry runs at
most ~8 lines. If you find yourself writing more, the implementation
specifics are leaking in; lift them to FRICTION (project-internal
idioms or mirror lemmas) or TACTICS (cross-cutting workflow rules)
and replace the Phase entry with a one-line pointer. The decision +
short rationale stay; the *how* lives elsewhere.

**Don't duplicate FRICTION explanations.** When a decision has both
a Phase entry and a FRICTION entry, the Phase entry is a pointer;
the explanation lives in FRICTION. Keep one source of truth.

**Sub-organize "Decisions made" for non-trivial phases.** If a phase
has multiple cleanup passes or many small refactors, split the
section into:
- *Phase-local choices and proof techniques* — full entries (still
  ≤ 8 lines each).
- *Promoted to TACTICS / FRICTION / DESIGN* — one-line pointers, no
  explanation. The cross-reference carries the content.
- *Cleanup pass summaries* — list of changes by file with
  cross-references, not explanations.

For small phases, a flat list under "Decisions made" is fine.

**Soft length budget.** Aim for `notes/PhaseN.md` ≤ 250 lines. If
you exceed it, run a compression pass — most likely "Decisions" has
accumulated cross-cutting lessons that should have been promoted.
Phase 3 grew to ~500 lines before the rules above existed; applying
them dropped it below 300. Phase 1 and Phase 2 (small phases) sit
near 100 lines without sub-organization.

### Template for `notes/PhaseN.md`

When starting a phase, seed the file with sections like:

```markdown
# Phase N — <name> (work log)

**Status:** in progress.

## Current state
<one-paragraph: what's done, what's mid-stream, what's the next concrete step>

## Architectural choices made up front
<optional; phase-start design decisions. Cross-cutting ones go in DESIGN.md.>

## Lemma checklist
- [x] `lemma_a` — done
- [ ] `lemma_b` — in progress; blocked on …
- [ ] `lemma_c`

## Decisions made during this phase

<For small phases, a flat list of bullets is fine. For phases with
cleanup passes or many small refactors, sub-organize as below.>

### Phase-local choices and proof techniques
- <decision + rationale, ≤ 8 lines per entry>

### Promoted to TACTICS / FRICTION / DESIGN
- *<lesson>* → TACTICS § N / FRICTION [tag] *<entry title>* / DESIGN.md *<section>*

### Cleanup pass summaries
<optional; per-file effect of any cleanup pass, with cross-references>

## Blockers / open questions
- …

## Hand-off / next phase
<written when the phase finishes; what unlocks the next phase>
```

`notes/Phase1.md` is a complete-phase example for a small phase
(flat "Decisions made"); `notes/Phase3.md` is the canonical example
for a phase with the sub-organization.

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
