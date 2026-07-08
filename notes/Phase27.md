# Phase 27 — Crux-node blueprint exposition (work log)

**Status:** in progress (opened 2026-07-08).

## Current state

Next concrete step: write the C4 (genericity vs general position, Claim 6.4)
crux exposition in `case-i.tex` / `algebraic-induction.tex` and flip its
`notes/BlueprintExposition.md` marker to `done`. Then, if the phase has room,
add the d=3 Case-III worked-case node (A2-x). **C3 (union↔contraction
non-commutativity) is done** — the expanded proof of
`lem:rigidContract-isMinimalKDof` in `case-i.tex` spells out (source-side) why
`M((G/E(H))̃) = M(G̃)/E(H̃)` is not a rename: contraction does not distribute
over the `D`-fold cycle-matroid union, and the identity holds only because the
contracted-out fibers `E(H̃)` rank-saturate the union (rigidity ⟹
`rank M(H̃) = D(|V(H)|−1) = D·r_cyc`, so the fibers pack into `D` spanning trees
on `V(H)` — KT's own Lemma-3.5 claim (3.1), p. 658), reached via the count
condition not a factor-aligned re-decomposition; ledger entry ~L488 flipped to
`done`. **C1 (contraction simplicity) is done** — a
two-paragraph connective passage before `lem:case-I-realization` in
`case-i.tex` explains why Case I trifurcates (contraction is the one Case-I
operation that identifies vertices, so it alone can break `Simple`); ledger
entry ~L254 flipped to `done`. **C2 (two-body-set splice) is done** — the
expanded connective passage after `lem:case-I-splice-seed` in `case-i.tex`
spells out the two body sets `V′ = V(H)` and `s_c = (V∖V′)∪{r}`, why the
contraction leg is rigid on `s_c` alone (the surviving edges leave the
interior `V(H)∖{r}` free), and how the shared body `r` balances the
rank count `D(|V′|−1)+D(|s_c|−1)−k = D(|V|−1)−k`; ledger entry ~L455 flipped
to `done`.

The molecular-conjecture program is mathematically complete (phases 1–26,
axiom-clean). Phase 27 is the first **post-program exposition** phase: it
adds *prose*, not Lean — every target proof is already green. The
deliverable is to take the exposition ledger (`notes/BlueprintExposition.md`)
to **zero genuinely-pending entries**.

This is a source-side (KT-math) exposition phase; its project-side sibling —
the wrong-turns narrative — is the later **RETRO** phase, not this one.

## Scope — the four unwritten Case-I cruxes (+ A2-x stretch)

All four are `[pending]` in `notes/BlueprintExposition.md`, all fold into the
`lem:case-I-realization` neighborhood of
`blueprint/src/chapter/algebraic-induction/case-i.tex`, and all state a crux
whose Lean proof is already green but whose blueprint prose is only the bare
formalized statement. The stable KT-math insight for each is **already
captured** in the ledger entry — Phase 27 writes it up in full.

## Lemma checklist

- [x] **C1 — contraction simplicity** (`rigidContract_simple` / `map_simple`;
  ledger entry ~L254). Why vertex-relabelling (`map`) is the one graph op that
  breaks `Simple` (it can manufacture both loops and parallel edges), hence
  why Case I *trifurcates*. → `case-i.tex` (done, this commit; connective
  passage before `lem:case-I-realization`).
- [x] **C2 — two-body-set splice** (`lem:case-I-realization` N6-G3-G3c; ledger
  ~L455). KT eq. (6.3)'s two splice legs live on *different* body sets
  (`V′` vs `V∖V′ ∪ {v∗}`); the contraction leg is rigid only on
  `V∖V′ ∪ {v∗}`. → `case-i.tex` (done, this commit; expanded connective passage
  after `lem:case-I-splice-seed`).
- [x] **C3 — union↔contraction non-commutativity** (`rigidContract_isMinimalKDof`,
  N4; ledger ~L488). `Matroid.Union` does not commute with contraction;
  `M((G/E(H))̃) = M(G̃)/E(H̃)` holds only via rank-saturation on a rigid
  subgraph's fibers (a count condition, not a re-decomposition). → `case-i.tex`
  (done, this commit; expanded proof of `lem:rigidContract-isMinimalKDof`,
  grounded in KT's Lemma-3.5 claim (3.1), p. 658).
- [ ] **C4 — genericity vs general position** (Claim 6.4; ledger ~L474). KT's
  single "algebraically independent over ℚ" hypothesis bundles two conditions
  (configuration non-degeneracy + rank-maximality) the formalization is forced
  to separate; KT never writes "general position". → `case-i.tex` /
  `algebraic-induction.tex`.
- [ ] **A2-x (stretch) — d=3 Case-III worked case.** The kept-as-grounding
  `case_III_candidate_dispatch` written up as the accessible on-ramp to the
  general Lemma 6.13. Full plan: `notes/CaseIII-d3-exposition.md` (5 steps).
  Fold in only if C1–C4 land with room to spare; otherwise it slides to a
  later phase.

## Blockers / open questions

None. Every target proof is green + axiom-clean; this is prose-only work,
gated by `blueprint/lint.sh` (+ `verify.sh` if any `\lean{}` / `\label{}` is
touched) and the vocabulary/authoring discipline in `blueprint/CLAUDE.md`.

Per-node discipline before writing each: re-read the target node's current
prose + proof for self-consistency (the red-node consistency gate applies
even though these nodes are green — confirm the live proof still routes
through the argument the write-up will describe), and keep the write-up
source-side (KT-math), excluding project-side formalization narration per the
ledger's inclusion criterion.

## Hand-off / next phase

Smallest next commit: the C4 (genericity vs general position, Claim 6.4;
ledger ~L497) exposition in `case-i.tex` / `algebraic-induction.tex` + its
ledger flip to `done`. Each of C1–C4 is a self-contained commit; C1, C2, and C3
landed (see checklist). The phase closes when the ledger hits 0
genuinely-pending (A2-x optional).

**Post-program phases queued after 27** (stable codenames; a number is minted
when each opens — see ROADMAP *Queued post-program phases*):
**RETROSCAN** (retroactive exposition scan of phases 1–16 + the two
un-ledgered 22b–23a candidates), **RETRO** (Formalization Retrospective + the
D1 design-doc compression, done in step; owner wants to plan the write-up in
detail at open), **RELAX** (algebraic-independence relaxation — the one
genuine *math* track), **UPSTREAM** (mathlib upstreaming of the ~50 mirrored
lemmas), and **VERSO** (the paused verso-blueprint port).

## Decisions made during this phase

- **Phase 27 scope = the 4 pending Case-I crux nodes first, A2-x as stretch**
  (owner-adjudicated 2026-07-08). The d=3 worked case is a *new* node rather
  than filling an existing pending one, so it is the lower-priority fold-in.
- **The wider deferred family is carved into separate phases, not bundled
  here.** The retroactive scan (RETROSCAN), the retrospective + design-doc
  compression (RETRO), and the optional math / upstream / port tracks each get
  their own codenamed phase; RETRO is planned in detail at open because its
  three pieces are related and the write-up approach needs thought.
