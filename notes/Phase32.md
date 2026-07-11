# Phase 32 — PROSPECT new-math round: Jacobs' conjecture + the degree-1 rank formula (work log)

**Status:** in progress (opened 2026-07-10).

Planning input: `notes/Prospect.md` (grouping 2 of the adjudicated
phase order — the L1/L2 Tier-1 entries + the L1 open recon question).
Both targets are Jackson–Jordán 2008 (*On the rigidity of molecular
graphs*, Combinatorica **28**) corollaries built on top of the landed
molecule rank formula: they consume the *statement* of
`SimpleGraph.molecule_rank_formula` (Phase 26) and the Phase-24
generic matroid surface, not proof internals.

## Current state

Just opened; no Lean or blueprint work yet. **Next concrete step:
dispatch the L1 recon** — the dependency check pinned in
`notes/Prospect.md` *Open recon questions*: verify JJ 2008 Thm 5.3 +
Lemma 5.2 against the formalized sparsity/Laman surface. Concretely:
pin the formal shape of "G² is Laman" in JJ's 3-dimensional counting
sense against the project's Phase 1–2 `(k, ℓ)`-sparsity API (the 2-D
`IsLaman` is `(2,3)`-tight; JJ's squares live on `3|V|−6` counts —
derive the statement from the source + the definition bodies, not
survey prose), map their Thm-5.3 counting argument (~1.5 pp) onto the
existing `IsSparse`/`edgesIn` lemma surface or list the missing
counting infrastructure, and produce the L1 node decomposition the
blueprint chapter will pin.

## Work items

- [ ] **L1 recon** — dependency check of JJ 2008 Thm 5.3 + Lemma 5.2
  against the formalized sparsity/Laman surface (statement pinning for
  "G² is Laman"; counting-API gap list; node decomposition for the
  chapter). Read-only; verdict in the return message.
- [ ] **L1 — Jacobs' conjecture** (JJ 2008 Thm 5.4; unconditional now
  that the rank formula is formalized): *G² is M-independent iff G² is
  Laman*, `M` the 3-D generic rigidity matroid (Phase 24). Missing
  inputs per the survey: their Thm 5.3 (G² Laman ⇒
  `|E(G²)| ≤ 3|V|−6−def(G̃)`, the ~1.5-page counting bound) and
  Lemma 5.2 (G² Laman ⇒ max degree of `G` ≤ 3). Scoped after the
  recon.
- [ ] **L2 — the degree-1 rank formula** (JJ 2008 Lemma 4.2): explicit
  `r(G²)` for graphs with degree-1 vertices (trees: `2|V|−5+|V₁|`;
  general: reduction to the ≥2-core) — the correct form of "weaken
  Cor 5.7's min-degree-≥2 hypothesis" (Prospect K2: the formula is
  false without ≥2; the literature's fix is this reduction). Short
  induction on top of `molecule_rank_formula`; statement surface
  checked alongside the L1 recon.

## Architectural choices made up front

- **Blueprint chapter deferred to the first post-recon commit.**
  Forward-mode discipline applies (the chapter, once open, is the
  phase's dep-graph / lemma index), but the node decomposition is
  exactly what the L1 recon settles — pre-committing red nodes now
  would pin a decomposition the recon may overturn (the Phase-30
  recon-first precedent). Until the chapter opens, this note's *Work
  items* is the to-do list.
- **Status-surface obligation at chapter open.** README /
  home_page/index.md / intro.tex were left untouched at this open
  (post-program precedent: their arc-level claims — phases 1–26
  complete, dep-graph fully green — remain true while no chapter is
  open). The commit that opens the chapter introduces red nodes and
  new-math scope, so it must sync intro.tex (the *Reading this
  blueprint* "every node is green" / development-complete phrasing +
  the *Organization* enumerate) and the README / home_page arc
  summaries in the same commit.

## Blockers / open questions

- The L1 recon's questions (above); nothing else blocks.

## Hand-off / next phase

Dispatch the **L1 recon** (read-only; verdict = "G² is Laman"
statement pinning + Thm 5.3 / Lemma 5.2 dependency map against the
Phase 1–2 API + the L1 node decomposition, with L2's statement surface
checked alongside). The first build commit after it opens the
forward-mode blueprint chapter from that decomposition and discharges
the status-surface obligation above.

## Decisions made during this phase

- (none yet)
