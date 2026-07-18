# Phase 35 — COPLANAR: multigraph KT Conjecture 1.2 (work log)

**Status:** in progress (opened 2026-07-18, recon-first; R0–R3 verdicts
accepted and the blueprint chapter opened 2026-07-18).

Planning input: `notes/Coplanar.md` (thin pointer; survey content folded
here at open). Target: recover the **full multigraph strength** of KT
Conjecture 1.2 and Theorem 5.6 by stating the panel side in KT's own
hinge-coplanar (containment) model, retiring the PROSPECT K1 wall
(`notes/Prospect.md` K1). Primary source: Katoh–Tanigawa, *A proof of
the molecular conjecture*, Discrete Comput. Geom. **45** (2011);
verified pointers under *Citations* below.

## Current state

**Build slice 3 landed** (2026-07-18): the multigraph molecular-conjecture iff
`molecular_conjecture_multigraph` (root `Molecular`) is in `Theorem55.lean` and
`thm:molecular-conjecture-multigraph` is green — **all four nodes of
`sec:molecular-coplanar-multigraph`** (a subsection of
`blueprint/src/chapter/algebraic-induction/panel-layer.tex`) **are now green;
the Lean content of the phase is complete.** Slices 1–2 landed the W1 predicate
`HasCoplanarPanelRealization`, the multigraph Theorem 5.6
`theorem_55_6_multigraph`, its consumer wrapper `theorem_55_6_multigraph_gen`,
and the `d = 3` instance `theorem_55_6_multigraph_d3`. **Next concrete step:
W5 — status-surface reconciliation** (docs-only, no Lean; see *Hand-off* and the
checklist). Landing W5 closes the phase.

## Recon verdicts (R0–R3, returned + accepted 2026-07-18)

Grounded in decl bodies and the `.refs/` KT copy; the R0 composition was
settled by a compiler probe (a scratch import of
`Molecular/AlgebraicInduction/Theorem55`, deleted after the run), which
built the whole W2+W3+W4 composition **sorry-free on the first pass**
(axioms: `propext`, `Classical.choice`, `Quot.sound`).

- **R0 — GO, gap map empty.** Every step composes at the landed
  signatures:
  - *Motion-space restriction identity*: one application of the
    framework-general
    `BodyHingeFramework.infinitesimalMotions_eq_of_isLink_supportExtensor`
    (`AlgebraicInduction/Pinning.lean`). No `reaimSub` analogue is
    needed or adapted — that machinery re-aims the meet model's `ends`
    selector; the M2 carrier's `supportExtensor` is a free field, so
    the extension is a dependent-if override.
  - *Per-edge extension*: already in tree —
    `exists_extensor_in_two_panels_grade` (`PanelLayer.lean`; **any**
    two normals, no transversality/nonzero hypotheses; covers
    transversal, coincident, and loop cases uniformly; the homogeneous
    counterpart of KT's projective move, p. 670).
  - *Rank composition*: M2 span conjunct →
    `finrank_span_rigidityRows_add_finrank_infinitesimalMotions`
    (+ spanning) → `finrank_infinitesimalMotions_le_of_graph_le` +
    `screwDim_add_deficiency_le_finrank_infinitesimalMotions` →
    `rigidityMatrix_prop11` — line-for-line the
    `rankHypothesis_genuine_of_theorem_55_gen` shape with the
    `.1 hG'Simple` consumption replaced by the bare `.2` conjunct of
    `theorem_55_minimalKDof_gen`.
- **R1(i) — off-`E(G)` labels.** Carry the total-over-β
  `∀ e, F.supportExtensor e ≠ 0` conjunct on the coplanar side verbatim
  (the extension supplies it freely; the body side and the ⇐ direction
  need it). The landed `HasPanelRealization` is *not* the W3 payload
  (per-link nonzero only, span-form rank); the W1 predicate = M2 +
  total-β nonzero. The landed `IsHingeCoplanar` is the meet model
  (`∃ P, P.toBodyHinge = F`) — do not reuse it.
- **R1(ii) — loops.** KT's multigraph convention **excludes**
  self-loops (§2.5 p. 654). The route handles them for free (the strip
  drops them, the extension re-adds them at `n₁ = n₂`, loop rigidity
  rows vanish); the probe compiled with no `Loopless` hypothesis.
- **R1(iii) — plumbing.** Same wrapper repackaging verbatim
  (`Graph.freshEdgeSupply_of_card_lt`, `six_le_bodyBarDim`,
  `bodyBarDim_eq_screwDim_sub_one`); compiled in the probe.
- **R2 — KT-faithfulness: no refutation.** M2 + total-β nonzero +
  all-body normals *is* KT's hinge-coplanar panel-hinge model at full
  multigraph strength (Conjecture 1.2 p. 648; coplanarity definition
  §5.1 p. 668 — vacuous at isolated bodies, so the all-body ∃-normal
  packaging is equivalent; coincident panels allowed, Lemma 5.3
  pp. 669–670; the Theorem-5.6 proof p. 670 consumes the **bare** 5.5
  conclusion — KT's own route). Two strengthening-direction deviations
  disclosed in `rem:coplanar-conventions`: loops admitted vs KT's
  loopless convention; homogeneous model admits panels/hinges at
  infinity (already the landed convention).
- **R3 — witness forms.** No M2 link-recording analogue is needed: the
  M2 form has no `ends` selector, and W4 consumes the W3 output
  directly (probe-checked).
  `rankHypothesis_genuine_recordsLinks_of_theorem_55_gen` serves only
  the simple-graph generic-lift consumers, out of scope here.

**Re-pricing:** W2+W3 land as **one theorem** (~100 lines,
probe-reproducible) plus the W4 iff (~50 lines); no genuinely new
brick. The phase's Lean content is small; W1 naming and W5 docs carry
the rest.

## Work-item checklist

- [x] **R0–R3 recon** (2026-07-18; verdicts above).
- [x] **Adjudications + chapter open** (2026-07-18; four red nodes in
  `sec:molecular-coplanar-multigraph`, statements pinned to the probe
  signatures; the contradicting fmlnotes in `panel-layer.tex`
  reconciled in the same commit).
- [x] **Build slice 1 (W1 + W2/W3):** minted `HasCoplanarPanelRealization`
  (per-witness realization predicate, no rank) and landed
  `theorem_55_6_multigraph` at the pinned signature (2026-07-18);
  `def:coplanar-panel-realization` + `thm:theorem-55-6-multigraph` green.
- [x] **Build slice 2 (wrapper):** consumer-facing form
  `theorem_55_6_multigraph_gen` (`hd : 3 ≤ n`, label-headroom `hcard`) +
  `d = 3` instance `theorem_55_6_multigraph_d3` (2026-07-18);
  `cor:theorem-55-6-multigraph-d3` green, wrapper exposed on
  `thm:theorem-55-6-multigraph`.
- [x] **Build slice 3 (W4):** `molecular_conjecture_multigraph` (the multigraph
  conjecture iff, containment model, probe_W4 shape) landed;
  `thm:molecular-conjecture-multigraph` green (2026-07-18).
- [ ] **W5 — status-surface reconciliation:** intro.tex / README /
  home_page "simple-graph case" attributions; `formalization.yaml`
  (alignment via `#print axioms`); `notes/Prospect.md` K1 close-out;
  extend `rem:fresh-edge-supply`'s carried-declaration list with the
  new pins. (The two `panel-layer.tex` fmlnote rescopes already landed
  with the chapter open.)

## Blockers / open questions

None. R0–R3 are settled; the statement-design points are adjudicated
(*Decisions made*).

## Hand-off / next phase

Next concrete commit: **W5 — status-surface reconciliation** (docs-only, no
Lean; the phase's last work item — landing it closes Phase 35, so run the
phase-close checklist, `PHASE-BOUNDARIES.md`). Per the checklist:
- reconcile the "simple-graph case" attributions in `intro.tex` / `README.md` /
  `home_page` now that the multigraph iff is proved
  (`molecular_conjecture_multigraph`);
- align `formalization.yaml` (run `#print axioms` on the phase's new decls);
- close out `notes/Prospect.md` K1 (the containment-model wall is retired);
- extend `rem:fresh-edge-supply`'s carried-declaration list with the new pins
  (`theorem_55_6_multigraph{,_gen,_d3}`, `molecular_conjecture_multigraph`).

If W5 runs large, split the `formalization.yaml` / `#print axioms` alignment
from the prose-attribution edits into two commits.

## Decisions made during this phase

- **User adjudications on the recon verdicts (2026-07-18),** transcribed
  verbatim; they override any conflicting earlier phase-note text:
  - *Loops:* "Admit loops (Recommended)" — the W3/W4 theorems are stated
    loop-admissible; the blueprint discloses KT's no-self-loop
    convention (§2.5 p. 654) explicitly (`rem:coplanar-conventions`), so
    the "full strength" claim is honest in both directions.
  - *`hV ≥ 2`:* "Let's leave this as a TODO for a later phase." — Phase
    35 keeps `hV : 2 ≤ V(G).ncard` (the kernel-checked shape); dropping
    it (single-body branch mirroring `rankHypothesis_of_theorem_55_gen`)
    is recorded as a queued follow-up in ROADMAP *Queued post-program
    phases*, not a Phase-35 checklist item.
  - *d=3 wrapper:* "Follow landed pattern (Recommended)" — W3 also
    exposes the consumer-facing wrapper per the landed simple-graph 5.6
    pattern (build slice 2).
- **W1 is a per-witness realization predicate, no rank** (2026-07-18, build
  slice 1): `HasCoplanarPanelRealization G F normal` (root `Molecular`, args
  `G F normal` explicit) carries only the realization data — `F.graph = G`,
  per-body nonzero normal, total-over-`β` nonzero extensor, per-link
  `ExtensorInPanel` containment — matching `def:coplanar-panel-realization`'s
  per-witness prose ("is a realization ... when"). The rank is *not* in the
  def; `theorem_55_6_multigraph` concludes `∃ F normal,
  HasCoplanarPanelRealization G F normal ∧ F.RankHypothesis (G.deficiency n)`,
  exposing the witness so the rank rides the same `F` (the probe's raw ∃-body,
  packaged through W1). The recon's "W1 = M2 + total-β nonzero" described the
  theorem *payload*; the def drops the rank per the blueprint's def/theorem
  split (theorem "attaining the deficiency rank"). Proof = the bare `.2`
  analogue of `rankHypothesis_genuine_of_theorem_55_gen`: strip / realize `G'`
  via `theorem_55_minimalKDof_gen … .2` / extend by `dite` over
  `exists_extensor_in_two_panels_grade` / motion identity
  `infinitesimalMotions_eq_of_isLink_supportExtensor` on `F.withGraph G'` /
  `rigidityMatrix_prop11`.
- **Build slice 2 = thin consumer wrapper + d3 instance** (2026-07-18):
  `theorem_55_6_multigraph_gen` derives `hD`/`hn`/`hfresh` from `hd : 3 ≤ n` +
  `hcard` (via `six_le_bodyBarDim` / `bodyBarDim_eq_screwDim_sub_one` /
  `freshEdgeSupply_of_card_lt`) and applies `theorem_55_6_multigraph` at
  `k = n − 1`; `theorem_55_6_multigraph_d3` is its `n := 3` instance (`K 2`
  return type by kernel `Nat.sub` defeq, `bodyBarDim 3 = 6` by unfold) — the
  exact `rankHypothesis_of_theorem_55_{gen,d3}` pattern, minus the single-body
  branch (`hV ≥ 2` retained). Pinning: `cor:theorem-55-6-multigraph-d3` →
  d3 instance; the wrapper added as a 2nd `\lean{}` name on
  `thm:theorem-55-6-multigraph` (both forms prove that node's `n ≥ 3` statement;
  the internal `theorem_55_6_multigraph` stays for W4).
- **Build slice 3 = W4 iff** (2026-07-18): `molecular_conjecture_multigraph`
  (root `Molecular`, `hd`/`hcard`/`hV`/`hspan`) states the LHS identically to the
  simple-graph `molecular_conjecture`, RHS = a rigid `HasCoplanarPanelRealization`
  witness. (⇒) copies `molecular_conjecture`'s `def(G̃) = 0` derivation
  (`screwDim_add_deficiency_le_finrank_infinitesimalMotions` +
  `rankHypothesis_zero_iff`) then feeds `theorem_55_6_multigraph_gen` at `def = 0`;
  (⇐) is a bare `obtain`/repackage — the containment witness already *is* the
  body-hinge framework, no `toBodyHinge` coercion. Sorry-free on first build.
- **Blueprint chapter opened only on the R0/R1 verdicts** (2026-07-18;
  the Phase-32/34 precedent): the chapter transcribes the
  *kernel-checked probe*, not a session-derived route — the
  transcribed-proof-vs-carrier discipline discharged by construction.
- **The meet-model simple-graph theorems are retained, no refactor**
  (2026-07-18, from the planning survey, W5): for simple graphs they are
  the stronger, more concrete statements; the
  `fmlnote:molecular-conjecture-multigraph` meet-model falsity stands as
  load-bearing exposition, now ending in a pointer to the containment
  model section rather than a strongest-supported claim.

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
