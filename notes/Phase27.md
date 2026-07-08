# Phase 27 — Crux-node blueprint exposition (work log)

**Status:** ✓ Complete (opened and closed 2026-07-08).

## Current state

Closed. The first post-program exposition phase: with the molecular-conjecture
program mathematically complete (phases 1–26, axiom-clean), this phase added
*prose*, not Lean, and took the exposition ledger
(`notes/BlueprintExposition.md`) to **zero genuinely-pending entries**. It wrote
the four pending Case-I cruxes (C1–C4) in `case-i.tex` and the optional A2-x
d=3 Case-III worked-case node in `case-iii.tex`; every target proof was already
green. Gates: `blueprint/lint.sh` + `verify.sh` green.

## Lemma checklist (all done)

- [x] **C1 — contraction simplicity** (ledger ~L254). Two-paragraph connective
  passage before `lem:case-I-realization` in `case-i.tex`: contraction is the
  one Case-I operation that identifies vertices, so it alone can break
  simplicity (a loop from a surviving edge with both ends in `V(H)`, or a
  parallel pair), unlike the subgraph operations — hence `G/E(H)` simple is a
  genuine hypothesis and Case I trifurcates (KT Lemmas 6.2/6.3/6.5).
- [x] **C2 — two-body-set splice** (ledger ~L455). Expanded passage after
  `lem:case-I-splice-seed`: the two body sets `V' = V(H)` and
  `s_c = (V∖V')∪{r}`, why the contraction leg is rigid on `s_c` alone, and how
  the shared body `r` balances `D(|V'|−1)+D(|s_c|−1)−k = D(|V|−1)−k` (KT
  eq. (6.3), Lemma 6.3 closing line).
- [x] **C3 — union↔contraction non-commutativity** (ledger ~L488). Expanded
  proof of `lem:rigidContract-isMinimalKDof`: `M((G/E(H))̃) = M(G̃)/E(H̃)` is
  not a rename — contraction does not distribute over the `D`-fold cycle-matroid
  union; it holds only because rigidity rank-saturates the fibers into `D`
  spanning trees on `V(H)` (KT Lemma 3.5 / eq. (3.1), p. 658), reached via the
  count condition.
- [x] **C4 — genericity vs general position** (ledger ~L510). Three-paragraph
  passage after `lem:case-I-realization`: KT §5.1's single
  "algebraically-independent-over-ℚ" hypothesis fuses configuration
  non-degeneracy (KT *nonparallel*) and rank-maximality (Claim 6.4 reads both
  off it; footnote 4 flags the fusion as a deliberate simplification), which the
  formalization separates into the rank/corank polynomial and a separate
  general-position polynomial, coupled by a shared non-root. Sources verified:
  KT §5.1 + footnote 4, p. 668; Claim 6.4, p. 675.
- [x] **A2-x (stretch) — d=3 Case-III worked case** (ledger ~L663). The
  `sec:…-claim612` section lead reframed as the d=3 worked case (KT §6.4.1) with
  the simplicity gains in prose; a new capstone node
  `lem:case-III-candidate-dispatch-d3` pinning `case_III_candidate_dispatch`
  (honestly green, a dep-graph leaf — correct for a worked example; its
  eq.-(6.22) bound discharged by `\uses{lem:case-III-nested-rank-lower}`); and a
  navigational `\cref` (not a `\uses` edge) from `lem:case-III`'s proof. Sources
  verified: KT §6.4.1 / Lemma 6.10 (p. 680), §6.4.2 / Lemma 6.13 (p. 692).

## Blockers / open questions

None.

## Hand-off / next phase

Closed; no exposition work remains and the ledger is at 0 genuinely-pending.
The successor phase is **not** opened by the closing commit — the queued
post-program phases stay codenamed (a number is minted only when one opens,
`PHASE-BOUNDARIES.md` *When this commit opens a phase*): **RETROSCAN**
(retroactive exposition scan of phases 1–16 + the two un-ledgered 22b–23a
candidates), **RETRO** (Formalization Retrospective + the D1 design-doc
compression, planned in detail at open), **RELAX** (algebraic-independence
relaxation — the one genuine *math* track), **UPSTREAM** (mathlib upstreaming
of the ~50 mirrored lemmas), **VERSO** (the paused verso-blueprint port). See
ROADMAP *Queued post-program phases*.

## Decisions made during this phase

- **Scope = the 4 pending Case-I cruxes first, A2-x as stretch**
  (owner-adjudicated 2026-07-08); the d=3 worked case is a *new* node, so it was
  the lower-priority fold-in. Both landed.
- **A2-x = one capstone node, arms left unpinned.** The three per-candidate
  placement facts are already pinned (`lem:case-III-candidate-row`,
  `-claim612-p2/p3-placement`), which the capstone `\uses`; pinning the
  realization-wrapper arms would bundle a four-decl node (AUTHORING D) and
  proliferate churn-prone API.
- **The wider deferred family is carved into separate codenamed phases**
  (RETROSCAN / RETRO / RELAX / UPSTREAM / VERSO), not bundled here; RETRO is
  planned in detail at its open.
