# Phase 35 — COPLANAR: multigraph KT Conjecture 1.2 (work log)

**Status:** ✓ Complete (opened and closed 2026-07-18; single-body
addendum 2026-07-18 — `≥ 2`-body hypothesis dropped, see *Decisions made*).

Recovered the **full multigraph strength** of KT Conjecture 1.2 and
Theorem 5.6 by stating the panel side in KT's own hinge-coplanar
(containment) model, retiring the PROSPECT K1 wall (`notes/Prospect.md`
K1). Planning input `notes/Coplanar.md` (folded here at open). Primary
source: Katoh–Tanigawa, *A proof of the molecular conjecture*, Discrete
Comput. Geom. **45** (2011); verified pointers under *Citations*.

Deliverables (all in `Molecular/AlgebraicInduction/Theorem55.lean`, root
`Molecular` namespace; blueprint `sec:molecular-coplanar-multigraph` in
`blueprint/src/chapter/algebraic-induction/panel-layer.tex`, four nodes,
all green; axioms of all four decls = `[propext, Classical.choice,
Quot.sound]`, verified at close):

- `HasCoplanarPanelRealization` — the containment-model realization
  predicate (`def:coplanar-panel-realization`).
- `theorem_55_6_multigraph` (+ wrapper `theorem_55_6_multigraph_gen`,
  `d = 3` instance `theorem_55_6_multigraph_d3`) — multigraph KT
  Theorem 5.6 (`thm:theorem-55-6-multigraph`,
  `cor:theorem-55-6-multigraph-d3`).
- `molecular_conjecture_multigraph` — the multigraph Conjecture 1.2 iff
  (`thm:molecular-conjecture-multigraph`).

## Hand-off / next phase

The phase is closed; no work remains here. Next per ROADMAP *Queued
post-program phases*: **PIN** (the 2-d molecular conjecture via
Jackson–Jordán 2008's pin-collinear body-and-pin route) is the next
phase to open — unplanned, so opening it starts with its own
survey/planning note (mint the phase number in that commit; open
checklist in `PHASE-BOUNDARIES.md`). Also queued: UPSTREAM, VERSO
(ROADMAP queue). The Phase-35 single-body follow-up is discharged (the
addendum below).

## Decisions made during this phase

- **Recon-first, chapter opened on the R0–R3 verdicts** (2026-07-18):
  a compiler probe built the whole W2+W3+W4 route sorry-free at the
  landed signatures before the chapter opened (empty gap map; the
  motion-space restriction identity
  `infinitesimalMotions_eq_of_isLink_supportExtensor` and the per-edge
  extension `exists_extensor_in_two_panels_grade` were already in
  tree), so the chapter transcribed the kernel-checked probe — the
  transcribed-proof-vs-carrier discipline discharged by construction.
- **User adjudications** (2026-07-18): loops admitted (KT's loopless
  §2.5 convention disclosed in `rem:coplanar-conventions`); the `d = 3`
  wrapper follows the landed `rankHypothesis_of_theorem_55_{gen,d3}`
  pattern. (The initial "`hV` kept, single-body drop deferred" call was
  reversed the same day — the addendum below.)
- **Single-body addendum** (2026-07-18). User adjudication verbatim:
  "landing shape = 'Phase-35 addendum (Recommended)' — one commit
  appended under Phase 35: statements strengthened in place,
  notes/Phase35.md + ROADMAP §35 record the follow-up as discharged,
  queued entry removed. No new phase number; ROADMAP row stays ✓
  Complete." Dropped `hV : 2 ≤ V(G).ncard` from all four public decls
  (now `hspan`-only, `hne` derived internally via `Set.univ_nonempty`);
  the `2 ≤ |V|` strip-and-re-add core is extracted as
  `theorem_55_6_multigraph_of_two_le`, and the single-body branch is a
  constant nonzero normal + `exists_extensor_in_two_panels_grade` (an
  Opus recon spike kernel-checked the four `hspan`-only decls first).
  Corrected the `molecular_conjecture_multigraph` docstring's false "`≥ 2`
  essential for the same reasons as the simple case" claim: the
  containment model escapes the meet-model degeneracy, so `≥ 2` is *not*
  essential here (`rem:coplanar-single-body`). Axioms of all four decls
  unchanged (`[propext, Classical.choice, Quot.sound]`, re-verified).
- **W1 is a per-witness realization predicate, no rank**:
  `HasCoplanarPanelRealization G F normal` = `F.graph = G` + per-body
  nonzero normal + total-over-`β` nonzero extensor + per-link
  `ExtensorInPanel` containment; the rank rides the theorem's ∃ (same
  `F`), per the blueprint's def/theorem split. The landed meet-model
  `IsHingeCoplanar` (`∃ P, P.toBodyHinge = F`) is deliberately not
  reused.
- **Proof shape** = the bare-`.2` analogue of
  `rankHypothesis_genuine_of_theorem_55_gen`: strip to a minimal
  spanning subgraph, realize by `theorem_55_minimalKDof_gen … .2` (no
  simplicity), extend by `dite` over
  `exists_extensor_in_two_panels_grade`, motion identity on
  `F.withGraph G'`, conclude via `rigidityMatrix_prop11`. W4's (⇐) is a
  bare repackage — the containment witness already is a
  `BodyHingeFramework`.
- **The meet-model simple-graph theorems are retained, no refactor**:
  for simple graphs they are the stronger concrete statements;
  `fmlnote:molecular-conjecture-multigraph`'s falsity finding stands as
  load-bearing exposition, ending in a pointer to the containment
  section.
- **W5 / close** (2026-07-18): status surfaces rescoped (README,
  home_page, intro.tex, formalization.yaml — new main-result +
  alignment + fidelity entries, axioms verified), Prospect K1 closed,
  `rem:fresh-edge-supply` carried-declaration list extended with the
  new pins. No exposition-ledger entries (empty gap map — no
  reroute/decompose insight to record).

## Citations (verified for this note)

- Katoh, Tanigawa, *A proof of the molecular conjecture*, Discrete
  Comput. Geom. **45** (2011) — project-canonical (ROADMAP
  *References*). Pointers verified against the `.refs` copy during the
  R2 cross-check (2026-07-18): Conjecture 1.2 and the hinge-coplanar
  definition p. 648; the multigraph (parallel edges, **no self-loops**)
  convention §2.5 p. 654; nonparallel realizations and the
  Π(v)-arbitrary-choice convention §5.1 p. 668; Lemma 5.3
  (coincident-panel double-edge realization) pp. 669–670; Theorem 5.6
  and its strip-realize-re-add proof (bare 5.5 consumption + the
  projective move) p. 670. Earlier verification of the same pointers:
  `notes/Phase23-cleanup.md` (2026-07-04).
