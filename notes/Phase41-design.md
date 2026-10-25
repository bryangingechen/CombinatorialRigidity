# Phase 41 — RECONCILE-FORMAL: design (cross-phase plan and recon)

**Status:** opened 2026-10-24 with the PI. Sub-phase **41a** (CARRIER) closed 2026-10-24, work log
`notes/Phase41a.md`: the field `isLink_ends` is on `PanelHingeFramework`, and no main result's
statement changed. Sub-phase **41b** (RESTATE) opened 2026-10-24 with the PI's decisions in §1b,
work log `notes/Phase41b.md`. MULTIGRAPH and UNSTATED are tracked by code (§3) and get letters when
they open. The PI's decisions on item 1's recon (KT's nonparallel panels) are §1c. Items 2–8 have
landed: Theorems 5.5 and 5.6 conclude KT's nonparallel panels for simple `G`, and
`molecular_conjecture` and the multigraph rows ask nondegenerate hinges on `E(G)` only. Item 9's
design pass, on the generic panel theorems, is in §2; the PI's decision on their body bound is
§1e, item 9a restated them, and item 9b made their rank formula a main result. The PI's answers in
advance (2026-10-25: S18, RESTATE's close, free strengthenings, M1's loops) are §1f. Item 10's
design pass, on the generic body-hinge theorems, is §2's last arc, with one adoption under §1f.3
(one body). Next concrete task: 41b's item 10a, the body-hinge restatement.

The phase is the last part of the RECONCILE program (`notes/Reconcile.md`, with its standing rules
in §2 and the plan of this phase in §3 *The phase*). Its input is PROSE's findings report
`notes/Prose-report.md`, and every finding's home stays the ledger `notes/Prose-findings.md`. This
file is the single entry point for the phase: the PI's decisions at the open (§1) and at RESTATE's
open (§1b), the recons (§2), the sub-phases (§3) and the open questions (§4).

## 0. Target

- **S2** (`F-122`, `F-125`, `F-128`): `PanelHingeFramework` records for each edge label a pair of
  bodies, `ends`, which nothing ties to the edge's ends. So KT Theorem 5.6's main result
  (`rankHypothesis_of_theorem_55_gen`) is met at deficiency zero by the framework whose normals are
  all zero. The fix is a field of the structure.
- **S1** (`F-207`; the pins of `F-206`, `F-216`, `F-221`): the generic panel and body-hinge
  theorems of `GenericLift/` take `hends` (every label is an edge of `G`) and `hfresh` (every
  minimal `k'`-dof-graph misses a label), which contradict each other at every minimal
  `k`-dof-graph. So the theorems are vacuous there.
- Within the same sub-phases: S13, S18, G6 (the generic panel theorem's own row),
  `cor:theorem-55-d3-spanning`, the footprint's docstrings that round 3 moved here, and `F-323` and
  `F-324`. Then M1 (the multigraph generic body-hinge theorem, JJ 2010 Theorem 6.1) and the claims
  no declaration states (S22–S25, S31, S3, S16, S19, G5, `F-061`'s forest lemma).

## 1. The PI's decisions at the open (2026-10-24)

The PI read the recon's verdict (§2) and its six questions. The PI's answer, verbatim:

> 1. Agreed. A it is
> 2. Sounds good
> 3. What KT states is a minimum here; if we can get something stronger, we should consider it too
> 4. Agreed
> 5. Agreed
> 6. OK.

What each answer settles:

1. **Design A.** The field `isLink_ends` goes on the one carrier `PanelHingeFramework`, so a
   framework whose selector misses an edge's ends cannot be built. Rejected: design C, a field-free
   carrier for the internal machinery with the condition only on predicates and statements.
2. **`molecular_conjecture`'s `2 ≤ |V(G)|` relaxes to `V(G).Nonempty`**, since with nondegeneracy
   asked only on `E(G)` the bound is no longer forced (its docstring). The multigraph rows
   (`molecular_conjecture_multigraph`, `theorem_55_6_multigraph_gen`) also ask nondegeneracy only
   on `E(G)`.
3. **KT's conclusion is the floor, and stronger forms are considered.** Checked against KT 2011
   (`.refs/`): a hinge is by definition a `(d − 2)`-dimensional affine subspace (KT §1), so every
   hinge of a KT panel-hinge framework is nondegenerate; Theorem 5.5 gives a realization that is
   *nonparallel* when `G` is simple: for distinct bodies `u`, `v`, `Π(u) ∩ Π(v)` is
   `(d − 2)`-dimensional (KT §5.1, p. 668). That is stronger than `IsGeneralPosition`, which asks
   only that two distinct bodies' homogeneous normals be independent, so two parallel panels
   qualify (corrected at RESTATE's open; the open read the two as equal). Theorem 5.6 states only
   the rank. So the floor is nondegenerate hinges on `E(G)` in Theorem 5.6's restated conclusion,
   and KT's nonparallel for simple `G` in Theorem 5.5's, of which `theorem_55_minimalKDof_gen`
   gives only general position (§1b.4). RESTATE's open settled the stronger candidates (§1b.1–2).
4. **`IsHingeCoplanar` constrains only the hinges on `E(G)`**, not those at unused labels.
5. **`F-323` and `F-324` are in**: the three main results' unused `[DecidableEq β]` and
   `theorem_55_minimalKDof_gen`'s derivable `hD` are dropped with RESTATE's restatements, with the
   binders round 3 kept for them.
6. **Four sub-phases** (§3), the plan's (a) split into CARRIER and RESTATE. Letters are minted as
   each opens; only 41a now.

## 1b. The PI's decisions at RESTATE's open (2026-10-24)

The coordinator put five questions, from the RESTATE open's recon (§2, *RESTATE's open recon*):
(1) general position in Theorem 5.6's conclusion, for every `G` or for simple `G`; (2) the generic
form as G6's row; (3) dropping `HasGenericFullRankRealization`'s last conjunct; (4) KT's nonparallel
against `IsGeneralPosition`: close the gap, or record a divergence; (5) the multi-commit trial. The
PI's words, verbatim (the first before the questions, the last after the coordinator explained 1 and
3 again):

> I will push after we've completed the RESTATE phase.

> 1. Can you explain this in more detail? I've forgotten the context around this.
> 2. OK, sounds good.
> 3. Hmm, I don't understand this either, and the G.graph = G sounds like this is related to 1?
> 4. We should close the gap here as KT is one of our key results.
> 5. OK, I guess that sounds like we should drop the multi-commit trial.

> Thanks; yes, let's go with your recommendations on 1 and 3 then.

What each answer settles:

1. **Theorem 5.6 concludes general position, for simple `G`.** `rankHypothesis_of_theorem_55_gen`
   keeps `hSimple` and concludes `∃ Q, Q.graph = G ∧ Q.IsGeneralPosition ∧` the rank (KT's
   nonparallel once item 4 builds it). It is stronger than the floor at no cost: the proof's normals
   are in general position already, and with the field general position gives nondegenerate hinges
   on `E(G)` of a simple `G`. "For every `G`" is false in the meet model, at the floor too: at a
   double edge both hinges are the meet of the same two panels (§2). Multigraphs keep the
   containment model (`theorem_55_6_multigraph_gen`).
2. **G6's row is the rank formula**, for every realization with generic normals, the iff its
   corollary: `PanelGeneric.lean`'s rank formula restated with `hcard` for `hfresh`, without `ends`
   or `hends`, over every framework on `G`; its non-vacuity witness at the single edge.
3. **`HasGenericFullRankRealization`'s last conjunct goes**, in its own commit, with the two `hswap`
   hypotheses of `Coupling.lean` and the hand-built link sites the field gives (§2).
4. **KT's nonparallel is closed in RESTATE**: Theorem 5.5's conclusion states KT §5.1's nonparallel
   for simple `G`, not only general position. The route and the cost are 41b's item 1.
5. **The multi-commit trial is dropped** (dispatch-log F53; `e0aa1a73`).

And **the push waits for RESTATE's close**: CI has not run since 2026-10-15, so its first run of
41a's `module` conversion (P2–P5) follows RESTATE's close.

## 1c. The PI's decisions after item 1's recon (2026-10-24)

The coordinator put the item-1 recon's two open options (§2, *KT's nonparallel recon*; §4) to the
PI: (1) route A (nonparallel in the induction's motive, KT's eq. (6.1)) against route B (the
planned upgrade at the end of Theorem 5.5); (2) nonparallel in the conclusion of the d = 3 wrapper
`exists_rankHypothesis_isGeneralPosition4`. On (2) the PI chose the option labelled "Yes, add it
(Recommended)". On (1) the PI first asked, verbatim:

> Is route B the stronger result since it doesn't use the stronger hypothesis?

The coordinator explained that Theorem 5.5's statement is the same under both routes: route B's
intermediate lemmas keep their hypotheses (valid for every `k`, including `k = 0`), while route A's
would conclude nonparallel at every step, mirroring KT's eq. (6.1), at the cost of `1 ≤ k` on about
a dozen of them. The PI then chose the option labelled "Route B (Recommended)".

What each answer settles:

1. **Route B.** As §2's arc plans (items 4a–4c), with the induction untouched; route A is
   rejected.
2. **The d = 3 wrapper concludes `IsNonparallel` too.** It takes one more polynomial factor at its
   choice of normals, and lands with item 5, which already restates the wrapper, after item 4a
   gives the predicate. `exists_rankHypothesis_isGeneralPosition4_of_two_le` gains it where the
   wrapper's proof needs it.

## 1d. The PI's decision on F-330 (2026-10-25)

The coordinator asked: "`molecular_conjecture` is restated: G is body-hinge rigid (nondegenerate
hinges on its edges) iff it has a rigid panel-hinge realization (nondegenerate hinges on its
edges). Its (⇒) proof now goes through Theorem 5.6, whose panels are nonparallel, so the panel side
could also state that the panels are nonparallel at no proof cost (finding F-330; a scratch Lean
witness compiles). That is stronger than KT's conjecture, which asks only for genuine hinges.
Should the panel side state it?" The options were "Add nonparallel (Recommended)" (beside the
nondegenerate hinges), "Replace with nonparallel" (instead of them) and "Leave as is". The PI chose
the option labelled "Add nonparallel (Recommended)".

What the answer settles: the panel side of `molecular_conjecture` states
`Q.graph = G ∧ Q.IsNonparallel ∧ (∀ e ∈ E(G), Q.toBodyHinge.supportExtensor e ≠ 0) ∧
Q.toBodyHinge.IsInfinitesimallyRigid`; the body-hinge side is unchanged.

## 1e. The PI's decision on the generic panel theorems' body bound (2026-10-25)

The coordinator asked: "The restated generic panel theorems (the rank formula over every framework
on G with generic normals, and its iff, G6's row) need only `V(G).Nonempty`, not `2 ≤ |V(G)|`:
Theorem 5.6's main form already covers one body, and the recon's spike compiles both versions.
Relax it, as you did for `molecular_conjecture` (§1.2)?" The options were "Relax to Nonempty
(Recommended)" and "Keep 2 ≤ |V(G)|". The PI chose the option labelled "Relax to Nonempty
(Recommended)".

What the answer settles: the rank formula and the iff take `hne : V(G).Nonempty` for
`hV : 2 ≤ V(G).ncard`, which the spike's `_of_nonempty` forms compile, and their names are the
planned unsuffixed ones (`finrank_span_rigidityRows_of_isGenericNormals`,
`isInfinitesimallyRigidOn_of_isGenericNormals_iff`).

## 1f. The PI's answers in advance (2026-10-25)

Given while item 9a built. The PI asked: "Are there any other questions that might come up? I
should answer them now in case I'm away later." The coordinator put four questions:

1. **Item 11 (S18).** "Item 11 (finding S18): the blueprint's `prop:rigidity-matrix-prop11` states
   the rank formula (KT Prop. 2.3) at a generic realization of a multigraph, but its Lean pin only
   proves it *assuming* the generic bound `dim Z ≤ D + def` (`hgen`); no pin shows a generic
   realization meets that bound. How should it be fixed?" The PI asked: "Is this node one from
   KT?" The coordinator checked KT 2011 (p. 655): Proposition 2.3 is in KT's preliminaries,
   credited by KT to Jackson–Jordán [15], and is about generic **body-hinge** frameworks on
   multigraphs ((i) `rank R(G,p) = D(|V|−1) − k`, (ii) `def(G̃) = k`, (iii)
   `rank M(G̃) = D(|V|−1) − k` are equivalent); the node states it for a generic **panel-hinge**
   realization of a multigraph, which is false in the project's meet model (the double edge on
   two bodies); the pin `rigidityMatrix_prop11` is a body-hinge statement, conditional on `hgen`.
   Re-asked: "Item 11: KT Prop. 2.3 (Jackson–Jordán's, as KT credit) is about generic body-hinge
   frameworks on multigraphs; the node wrongly says panel-hinge (false for multigraphs in our
   model), and its Lean pin is conditional on the generic bound. How should RESTATE fix it?"
   Options: "KT's body-hinge form, conditional (Recommended)", "Panel-hinge, simple graphs",
   "Both". The PI chose "KT's body-hinge form, conditional (Recommended)".
2. **After RESTATE closes.** "When RESTATE closes (items 9b–12, then the close checklist), what
   should the loop do? You said you'd push after RESTATE; that push is CI's first run of 41a's
   module conversion." Options: "Stop for your push (Recommended)", "Continue: open MULTIGRAPH",
   "Continue: open UNSTATED". The PI chose "Stop for your push (Recommended)".
3. **Free strengthenings.** "Standing policy: when a build finds a conclusion can be strengthened
   at no proof cost (like F-330's nonparallel panels), or a hypothesis relaxed that the proof
   doesn't need (like the body bound you just relaxed), may I adopt it without asking?" Options:
   "Adopt, record it (Recommended)" (adopt when it changes only the theorem at hand, no other
   row's statement and no pencil row, and follows a pattern the PI already approved; recorded in
   the design doc as the coordinator's call under this authorization; anything else still goes to
   the PI) and "Always ask me". The PI chose "Adopt, record it (Recommended)".
4. **M1 and loops** (design doc §4). "If MULTIGRAPH opens (now or later), its first decision
   (design doc §4): M1's multigraphs and loops. A loop's hinge constrains nothing and never
   crosses a partition. Allow loops by relaxing the upper bound's hinge condition to non-loop
   links, or assume `G.Loopless`?" Options: "Allow loops (Recommended)" (relax the upper bound's
   nondegeneracy to non-loop links; if the open's recon finds it costs more than about one extra
   commit, come back to the PI), "Assume loopless", "Decide at the open". The PI chose "Allow
   loops (Recommended)".

What each answer settles:

1. **Item 11 restates `prop:rigidity-matrix-prop11` as KT state it**: a generic body-hinge
   framework on a multigraph (KT p. 655, credited to Jackson–Jordán), proved in the conditional
   form (the bound gives the formula), citing item 10's generic body-hinge theorem for simple
   graphs. It is repinned unconditionally when MULTIGRAPH's M1 lands (§3's MULTIGRAPH row). The
   node's panel-hinge reading is the ledger's `F-331`, whose disposition is item 11.
2. **RESTATE's close stops the loop for the PI's push** (41b's *Close* line), which is CI's first
   run of 41a's module conversion.
3. **The standing policy on free strengthenings**: the coordinator adopts, without asking, a
   conclusion strengthened at no proof cost or a hypothesis relaxed that the proof does not need,
   when it changes only the theorem at hand (no other row's statement, no pencil row) and follows
   a pattern the PI already approved, and records it here as the coordinator's call under this
   authorization; anything else still goes to the PI. 41b's statement-change rule points here.
4. **M1 allows loops** (§4): the upper bound's nondegeneracy is relaxed to non-loop links; if
   MULTIGRAPH's open recon finds that this costs more than about one extra commit, the question
   goes back to the PI.

## 2. The open's recon (2026-10-24; Claude Opus 5.5, read-only, at `95e2f418`)

**Evidence**, committed in `notes/reconcile-formal/`:
- `S2Witness.lean`, a Lean witness outside the library (`lake env lean
  notes/reconcile-formal/S2Witness.lean`; no errors, three standard axioms). It models the field
  on a mirror structure `LinkedPHF`.
- `carrier_inventory.py`, the reference count from the built `.ilean` files (`python3
  notes/reconcile-formal/carrier_inventory.py`): **32 modules, 167 declarations, 648 references**
  (`ofNormals` 601, `withNormal` 14, `reaimSubLink` 9, `reaim` 6, `withGraph` 5, `reaimSub` 5,
  `ofParam` 4, `withMomentNormals` 4). Only 9 direct structure literals exist: five constructor
  bodies in `PanelHinge.lean`, the three `reaim*` and the single-body framework at
  `Theorem55.lean:2566`.

**Corrections to the plan's premises.** Round 1's "~70 sites in 21 files" and round 3's "257
declarations in 33 files" are not reproducible; the count above replaces them.
`BodyHingeFramework.withGraph` cannot break link-recording, since that structure has no selector.
`rankHypothesis_of_theorem_55_gen` already takes `hcard` (`Theorem55.lean:2542`); S1's change
from `hfresh` to `hcard` is the `GenericLift/` theorems'.

**The field.** `isLink_ends : ∀ e ∈ E(graph), graph.IsLink e (ends e).1 (ends e).2`. It is
equivalent, by one line each way, to the edge-restricted `hends` and to the "up to swap" conjunct
of `HasGenericFullRankRealization` (`PanelHinge.lean:680`). Rejected: the total form `∀ e, …`
(it forces `E(G)` to be the whole label type, S1's vacuity in the carrier), and deriving `ends`
from `G.endsOf` (every computation that fixes an orientation would need sign bookkeeping:
`panelRow`, `normalRow`, the genericity device's `annihRowPoly`, Case III's relabelled selectors).

**The field alone does not close S2** (`zeroPHF_rankHypothesis_zero`): the zero-normal framework
with `ends := G.endsOf` meets the field and is rigid on any preconnected spanning graph, hence
meets `RankHypothesis 0`. Adding `∀ e ∈ E(G), Q.toBodyHinge.supportExtensor e ≠ 0` to the
conclusion excludes it (`zeroPHF_not_nondegenerate`). `molecular_conjecture` already asks for
nondegenerate hinges, so for it the field alone closes S2.

**Proposed restatements** (RESTATE settles them, with §1.3's stronger forms):
- `rankHypothesis_of_theorem_55_gen`, without `[DecidableEq β]`: `∃ Q, Q.graph = G ∧ (∀ e ∈ E(G),
  Q.toBodyHinge.supportExtensor e ≠ 0) ∧ Q.toBodyHinge.RankHypothesis (G.deficiency n)`. The
  single-body branch holds trivially (no edges).
- `molecular_conjecture`: the same iff with `∀ e ∈ E(G), … ≠ 0` on both sides; the
  `(⇒)` direction already uses nondegeneracy only at links
  (`screwDim_add_deficiency_le_finrank_infinitesimalMotions`, `PanelLayer.lean:1580`).
- The panel generic theorem (G6's row): `(∀ Q, Q.graph = G → Q.IsGenericNormals →
  Q.toBodyHinge.IsInfinitesimallyRigidOn V(G)) ↔ G.deficiency n = 0` under `hd`, `hcard`, `hV`,
  `hspan`, `hSimple`; no `ends`, no `hends`. The rank formula likewise.
- The body-hinge theorem (`HingeGeneric.lean:1005`): `hcard` for `hfresh`; no `ends`, `hends` or
  `hD`; genericity `IsGenericHingePoints G q` over rows indexed by `E(G)`.

**Construction sites, the friction, `reaimSub`, `reaim`, `withGraph`** (CARRIER's; closed at 41a).
The open's class scan (T 29, P 75, H at most 56, R 4, X 2 declarations) was superseded by CARRIER's
spike: 123 declarations in 27 of the 32 files, H at 65 (`notes/Phase41a.md` item 4; FRICTION *The
link field…*); the four R statements on the splitting-off were fixed at item 3. The link proof is a
last argument of the constructors, filled in by `link_tac`, so the common sites need no edit
(TACTICS-QUIRKS § 120: `rw [hG]` on a graph argument fails, while `subst` and `simp only` work);
the four scattered link lemmas became the predicate `RecordsLinks` and its graph-operation lemmas
(item 2). `reaimSub` was retired at item 1; at item 6 `rigidityMatrix_prop11`'s `hC` moved to
links, `reaim` was deleted and `withGraph` takes `hle : G' ≤ P.graph` (the field from
`RecordsLinks.mono`); at item 7 the link-recording Theorem 5.6 form's proof became
`rankHypothesis_genuine_of_theorem_55_gen`'s, and the form was deleted.

**S1 after S2.** The field is `hends` restricted to `E(G)`, so the panel theorems need neither
`ends` nor `hends`, and S1 reduces to `hfresh` → `hcard`, genericity over rows indexed by `E(G)`, and
`IsGenericHingePoints` oriented by the links. The families stay indexed by the label type, with
conditions only on `E(G)` (the body-bar precedent, `BodyBar/GenericLift.lean:190–213`); a subtype
index would need transport for `ofHinge`, `MvPolynomial (β × …)`, `induce` and `mulTilde`. The
extraction lemma (`GenericityDevice.lean:491–498`) already returns linking indices with
nondegeneracy only at links. Folded in: S13 (genericity reads only the `E(G)` coordinates), S18
(`prop:rigidity-matrix-prop11` restated conditionally; its `hC` moved to links at 41a's item 6) and
`cor:theorem-55-d3-spanning` (derived from `theorem_55_d3` under `hcard`, with general position
and nondegenerate hinges on `E(G)`, `_hSimple` dropped, `F-126`).

**`BodyHingeFramework`** needs no structural change: it has no selector and its rows read `IsLink`
(`RigidityMatrix/Basic.lean:243`). M1 can reuse `theorem_55_6_multigraph` (`Theorem55.lean:2903`),
whose nonzero hinges are each spanned by points in the panels, so the witness transplant of
`HingeGeneric.lean:751` carries over.

**`F-323` and `F-324`.** `F-323` costs no commit for the two S2 main results (drop the binder, add
`classical`; precedent `rankHypothesis_of_theorem_55_d3`, :2619), and one small commit for the two
multigraph rows unless they are restated anyway (§1.2 restates them). `F-324` is about one commit:
`theorem_55_minimalKDof_gen` (:2107), the `hD` chain below it (`F-293`, `F-297`, `F-298`, about
ten signatures) and seven call sites; the spanning-trees theorem's `hD` goes with S1.

**RESTATE's open recon** (2026-10-24; Claude Opus 5.5, read-only, at `3a627b3d`). Evidence:
`notes/reconcile-formal/RestateWitness.lean` (`lake lean`; no errors, three standard axioms).
- **KT** (`.refs/`): nonparallel is defined for simple graphs (§5.1, p. 668); Theorem 5.5 reads
  "(nonparallel, if G is simple)" (p. 670); Theorem 5.6 states only the rank. `IsGeneralPosition`
  (`PanelHinge.lean:402`) is the weaker, projective condition (§1.3, corrected).
- **Q1.** In the meet model parallel edges get one hinge: at the double edge on two bodies
  (`n = 2`), deficiency 0, no framework with nonzero hinges on `E(G)` reaches the rank
  (`restated_theorem56_false_at_banana`). `hSimple` enters at `rankHypothesis_of_theorem_55_gen`
  (`Theorem55.lean:2343`); for simple `G` general position is kept by the re-aimed strip (as the rows
  form's `:2241` does), vacuous at one body, and gives nondegenerate hinges
  (`supportExtensor_ne_zero_of_isGeneralPosition`). Precedent at d = 3:
  `exists_rankHypothesis_isGeneralPosition4` (`Theorem56.lean:201`).
- **Q2.** The generic form is G6's "rank formula likewise", strictly stronger than the iff, which
  follows from it with `exists_isGenericNormals`. Existing: `PanelGeneric.lean:403` (rank formula),
  `:490` (iff), `HingeGeneric.lean:885`, `:954`, `:996`; all carry `hfresh`, `hspan`, `hSimple`, a
  bare `ends` and a total `hends`. Witness: `Graph.singleEdge 0 1 0` on `Fin 2`/`Fin 4`, minimal
  1-dof (`Nonvacuity.lean:267`).
- **Q3.** The last conjunct is the field once `Q.graph = G` (`lastConjunct_of_field`,
  `hasGenericFullRankRealization_iff`). Eight producers, thirteen destructurers and one discard
  (Cases I–III, `Theorem55.lean`, `GenericityDevice.lean:863`); two helpers die
  (`ofNormals_recordsLinks_of_hends`, `ofNormals_endsOf_recordsLinks`); one node,
  `def:rank-hypothesis` (`panel-layer.tex:522`, prose at `:549` and `:773`).
- **Others.** `hswap` of `Coupling.lean:72` and `:105` follow from the field
  (`hswap_of_recordsLinks`). The field gives the hand-built link conditions at `CaseII.lean:461`,
  `:508`, `CaseIII/Realization.lean:365`–`370`, `:913`–`918`, `Theorem55.lean:620`, `:2133`–`2150`,
  `:2240`–`2269`, not those at `CaseII.lean:685`, `:924` (a link of `G`, not of the framework's
  `Gab`). §3's list missed the d = 3 wrapper `exists_rankHypothesis_isGeneralPosition4`, pinned at
  `molecule-modelling.tex:663`.

**KT's nonparallel recon** (41b's item 1; 2026-10-24; Claude Opus 5.5, design pass, at
`c45211e2`). Evidence: `notes/reconcile-formal/NonparallelWitness.lean` (`lake lean`; no errors or
warnings, its six `#print axioms` the three standard axioms). The names below are the witness's.
- **The affine coordinate is the last.** `homogenize` appends `1` last (`Extensor.lean:55`,
  `def:homogeneous-coords`), so the panel of a normal `n` is `{x | Fin.init n ⬝ᵥ x + n last = 0}`
  (`homogenize_dotProduct`): its first `k + 1` coordinates, `Fin.init n`, are its direction, KT's
  `c(v)` in `Π(v) = {x | x · c(v) + 1 = 0}` (§5.1, p. 668). The d = 3 dictionary and the
  affine-position lemma of `HingeGeneric.lean` read the last coordinate so too. The coordinator's
  hypothesis that coordinate 0 is the affine one is refuted.
- **The predicate.** KT (p. 668): two panels are nonparallel if they meet in a
  `(d − 2)`-dimensional affine subspace, and a framework on a simple graph is nonparallel if any
  two distinct bodies' panels are (Jackson and Jordán's "nondegenerate", JJ 2010 §7; KT footnote
  3). On the carrier, KT's independence of `c(u)` and `c(v)`, `IsNonparallel P` is
  `∀ a b, a ≠ b → LinearIndependent K ![Fin.init (P.normal a), Fin.init (P.normal b)]`.
  Equivalently `e_last`, `n_a`, `n_b` are independent: the meet is not at infinity
  (`dir_pair_iff_triple`). It implies `IsGeneralPosition` (`IsNonparallel.isGeneralPosition`); its
  two panels meet (`exists_common_point`), in the solutions of a rank-2 system; and it is strictly
  stronger: at d = 2 the normals `(1, 0, 0)`, `(1, 0, 1)` are independent and their lines
  `x₀ = 0`, `x₀ = −1` never meet (`generalPosition_not_nonparallel`). No such predicate exists
  (bare-name search of `CombinatorialRigidity/` and `.lake/packages/`; mathlib's
  `AffineSubspace.Parallel` is on affine subspaces). **Range: all of `α`**, as `IsGeneralPosition`:
  KT ask it on `V`, the device below gives `α` free, and it is vacuous on one body (Theorem 5.6's
  single-body branch).
- **`1 ≤ k` is needed and already there.** At `k = 0` directions lie in `K¹`, so no two bodies are
  nonparallel (`not_isNonparallel_k0`). Theorem 5.5 has `hk1`; no main result gains a hypothesis.
- **The device already avoids parallel pairs.** For `1 ≤ k` coordinates 0 and 1 are direction
  coordinates, so the polynomial of `exists_generalPosition_polynomial` (the product of the
  leading minors on them) is nonparallel at every non-root (`isNonparallel_of_eval_ne_zero`), and
  the moment curve is nonparallel at distinct parameters (`momentCurve_nonparallel`: its direction
  is the moment curve one degree down). No parameter condition beyond injectivity.
- **Route B, the plan: upgrade at the end.** A generic full-rank realization of a loopless graph
  gives a nonparallel one of the same rank (`exists_nonparallel_of_generic`, sorry-free): the rank
  polynomial at its normals (`exists_rankPolynomial_of_le_finrank_linking`) times that product, a
  common non-root, and the deficiency bound (`finrank_span_rigidityRows_add_deficiency_le`). It is
  the device's form of KT Lemma 5.2 (p. 669), KT's rotation to a nonparallel realization of no
  smaller rank. The induction (`theorem_55_minimalKDof_k_all_k`, the base producers, Cases I–III,
  `HasGenericFullRankRealization`) is untouched; only `theorem_55_minimalKDof_gen` applies it.
- **Route A, rejected: nonparallel in the motive.** It survives every step (each producer takes
  its normals at a non-root of a product with that polynomial, or relabels them), but as the
  predicate fails at `k = 0`, about a dozen producers with no bound on `k` gain `1 ≤ k` (the two
  `_gp_gen` base producers, `hasGenericFullRankRealization_of_rigidOn_ofNormals`,
  `hasGenericFullRankRealization_of_couple_blockTriangular_ofNormals_set_kdof`,
  `case_III_realization_of_rank`, the three arm realizations, `cycle_realization`,
  `chainData_interior_realization_hρGv`, `chainData_dispatch_floor_of_discriminator`), each a
  restated node, in one switch commit (an unused `hk` fails `unusedArguments`). It buys KT's
  eq. (6.1) at full strength, which the formal proof never uses.
- **Statements and proofs (route B).** Statements: `theorem_55_minimalKDof_gen`'s simple conjunct,
  passed through `theorem_55_minimalKDof_k`, `theorem_55_d3` and
  `theorem_55_minimalKDof_gen_witness`. Proofs only: `rankHypothesis_genuine_of_theorem_55_gen`
  and the rows form, which read general position off the strip realization.
  `exists_rankHypothesis_isGeneralPosition4` is untouched by items 4a–4c: it reads
  `rankHypothesis_genuine_of_theorem_55_gen`, which states nothing of the normals, and re-chooses
  them; a third polynomial factor adds nonparallel to it, which the PI sanctioned (§1c.2), at
  item 5.
- **Order.** Item 4 after items 2 and 3 (the new predicate is born without the link conjunct, and
  both 3 and 4c edit `theorem_55_minimalKDof_gen`) and before item 5, whose Theorem 5.6 then states
  `IsNonparallel` off the strip realization, whose normals `reaimSubLink` keeps; else
  `thm:theorem-55-6` is restated twice. The commits are 41b's items 4a–4c.

**Item 9's recon** (41b's item 9; 2026-10-25; Claude Opus 5.5, design pass, at `8c2d4475`).
Evidence: `notes/reconcile-formal/PanelGenericWitness.lean` (`lake lean`: no errors or warnings, its
six `#print axioms` the three standard axioms; `#lint` on a copy: no errors in 15 declarations). It
states the planned declarations under their planned names, in its own namespace.
- **No Lean consumer outside the file.** `PanelGeneric.lean` is imported only by the root module.
  The mentions in `HingeGeneric.lean`, `Pencil/Steer.lean:371`,
  `Pencil/MainComponent/Bridge.lean:31`, `Pencil/Engine.lean:84`, `:321`, `:341` and
  `BodyBar/GenericLift.lean:26`, `:241` are docstrings, so no pencil statement or proof changes,
  and the cascade is docstrings, pins and status rows.
- **The predicate is the framework's, `Q.IsGenericNormals`**: every subfamily of rows at the edges
  of `Q.graph` (`∀ i ∈ s, i.1 ∈ E(Q.graph)`) that is independent at some normal assignment is
  independent at `Q`'s normals, with the rows `normalRow Q.ends`. The families stay indexed by the
  label type. Rejected: `IsGenericNormals G ends q` restricted to `E(G)` (the same content, read
  through two more arguments at every use), and the old predicate under a new quantifier (it reads
  the rows of every label, against S13, so the theorem would assume more).
- **The selector's orientation does not matter.** Exchanging a label's ends negates both its
  extensor (`panelSupportExtensor_swap`) and its hinge row, so `normalRow` is unchanged
  (`normalRow_eq_of_swap`; the remark after `def:generic-normals` says so). Two selectors that
  record the links give the same rows at `E(G)` (`normalRow_eq_of_recordsLinks`), so the predicate
  reads only the graph and the normals (`isGenericNormals_iff_of_graph_eq`). "A swapped end negates
  a row" holds of the mixed row `Q.toBodyHinge.panelRow ends` (hinge row from `ends`, extensor
  from `Q.ends`), which the transplant handles by its `±1`, and of item 10's `hingePointRow`.
- **Signatures** (compiled; all in `PanelHingeFramework`, the last three renamed, as their
  statements no longer mention `ofNormals`):
  - `exists_isGenericNormals_abundance [Finite α] [Finite β] (G) (ends) (hlinks : RecordsLinks G
    ends) : ∃ P ≠ 0, ∀ q, eval q P ≠ 0 → (ofNormals G ends q).IsGenericNormals`. The spike
    derives it from the old lemma; in place, the old proof (its product over every subfamily) with
    the new hypothesis ignored at its last line (not compiled).
  - `exists_isGenericNormals [Infinite K] [Nonempty α] [Finite α] [Finite β] (G) : ∃ Q, Q.graph = G
    ∧ Q.IsGenericNormals`, at `G.endsOf`.
  - `exists_independent_normalRow_of_le_finrank [Finite α] [Finite β] (Q) {ends} (hends :
    RecordsLinks Q.graph ends) (hC : ∀ e ∈ E(Q.graph), …) (hN)`, concluding `∃ s, (∀ i ∈ s, i.1 ∈
    E(Q.graph)) ∧ Nat.card s = N ∧` independence of `normalRow ends` at `Q`'s normals: no `G`, no
    `hQends` (the field), and the sign taken only at edges. Its `±1` route stays, so the worked
    cases of `TACTICS-QUIRKS.md` (`:1747`, `:3564`) keep their target.
  - `supportExtensor_ne_zero_of_isGenericNormals (hk1) {Q} (hloop : Q.graph.Loopless) (hq) : ∀ e ∈
    E(Q.graph), Q.toBodyHinge.supportExtensor e ≠ 0` (was `…_ofNormals_ne_zero_…`).
  - `finrank_span_rigidityRows_of_isGenericNormals [Infinite K] [Finite α] [Finite β] {n} (hd : 2 ≤
    n) (hcard : bodyBarDim n * (Nat.card α - 1) < Nat.card β) (G) (hV : 2 ≤ V(G).ncard) (hspan)
    (hSimple) (Q : PanelHingeFramework K (n - 1) α β) (hQ : Q.graph = G) (hq : Q.IsGenericNormals)
    : (finrank (span Q.toBodyHinge.rigidityRows) : ℤ) = screwDim (n - 1) * (V(G).ncard - 1) -
    G.deficiency n`: Theorem 5.6's binders; `hk1`, `hn`, `hfresh`, `ends`, `hends`,
    `[DecidableEq β]` and `[Nonempty α]` gone (the last from `hV`).
  - `isInfinitesimallyRigidOn_of_isGenericNormals_iff`, the same binders: `(∀ Q, Q.graph = G →
    Q.IsGenericNormals → Q.toBodyHinge.IsInfinitesimallyRigidOn V(G)) ↔ G.deficiency n = 0`.
- **The composition.** The witness is Theorem 5.6's main form `rankHypothesis_of_theorem_55_gen`,
  not the genuine one: its nonparallel panels give nondegenerate hinges on `E(G)`
  (`IsNonparallel.isGeneralPosition`, `supportExtensor_ne_zero_of_isGeneralPosition`), and it takes
  `hd` and `hcard` as they are. The transplant runs at `Q0` with `Q`'s selector (both fields give
  `RecordsLinks Q0.graph Q.ends`); genericity of `Q` carries the extracted rows, all at edges, to
  `Q`'s normals, where each is a rigidity row (`panelRow_mem_rigidityRows_of_link`, at `Q`'s field);
  the upper bound (`finrank_span_rigidityRows_add_deficiency_le`) asks nondegeneracy at links only.
- **One body (for the PI).** The composition needs only `V(G).Nonempty`, as Theorem 5.6's main form
  covers one body: the rank formula and the iff compile under it
  (`…_of_nonempty`). The plan keeps §2's `hV`; relaxing it, as §1.2 did for `molecular_conjecture`,
  is the PI's call (§4).
- **Not planned:** an abundance over every framework on `G`, whatever its selector
  (`exists_isGenericNormals_abundance'`, compiled), at the cost of the three orientation lemmas.
- **G6's witness** (compiled): at the single edge on `Fin 2`/`Fin 4`, `n = 2`, some framework has
  generic normals and each such has rank `3 · (2 − 1) − 1 = 2`. In `Nonvacuity.lean` it reads the
  private `singleEdge_isMinimalKDof_one` and needs a `public import` of `PanelGeneric`.
- **Cascade.** Renames: the blueprint pins (`generic-lift.tex:379`, `:465`, `:505`),
  `formalization.yaml:501` and `:803`, and the docstrings `HingeGeneric.lean:52`, `:362`, `:883`,
  `:949` and `Steer.lean:371`. Statements: `def:generic-normals` and its fmlnote, the four lemma
  nodes, `thm:panel-generic-rank` (proof `\uses` `thm:theorem-55-6` for the genuine form) and
  `cor:panel-generic-rigid`, the fmlnotes after the transplant and the corollary, and the section's
  opening prose. Docstrings that become false: `RecordsLinks.of_forall` (`PanelHinge.lean:125`,
  "the generic panel and body-hinge theorems"), the genuine form's (`Theorem55.lean:2091`, "the
  generic panel and hinge-point theorems read the witness's rows"). The S1 scope sentences (README
  `:162`, `home_page/index.md:142`, `intro.tex:266`, ROADMAP `:1042`, `formalization.yaml:503`,
  `:795`, `:808`) say both theorems are vacuous at minimal graphs; after 9a only the body-hinge
  one is (9a rewrites `:808` with its row's names, 9b the others). The names that survive
  (`normalRow`, `normalRow_eq_panelRow`, `IsGenericNormals`, the abundance) keep their docstring
  mentions in `Engine.lean`, `Bridge.lean` and `BodyBar/GenericLift.lean` true.
- **Split.** 9a the restatement, 9b G6's row and witness (`notes/Phase41b.md`). No twin is needed:
  no other file reads the six declarations, so the predicate and its consumers switch together.
  Item 10 is not reached: `HingeGeneric.lean` does not import this file, `BodyHingeFramework` has
  no selector for a framework-level predicate, and `hingePointRow`'s sign does follow the
  selector. What carries over (hypotheses, not compiled): Theorem 5.6's binders, and its main form
  as the witness if item 10's transplant (`HingeGeneric.lean:751`) takes nondegeneracy on `E(G)`.

**Item 10's recon** (41b's item 10; 2026-10-25; Claude Opus 5.5, design pass, at `ce98d5ec`).
Evidence: `notes/reconcile-formal/HingeGenericWitness.lean` (`lake lean`: no errors or warnings,
its nine `#print axioms` the three standard axioms; `#lint` on a copy: no errors in 18
declarations). It states the planned declarations under their planned names, in its own namespace,
and proves the abundance, the nondegeneracy, the witness assembly and the rank formula in place,
from the library's proofs with the changes below. Claims marked *hypothesis* were not compiled.
- **No Lean consumer outside the file.** `HingeGeneric.lean` is imported by the root module and by
  `Pencil/Arms.lean`, which (with `Pair.lean`, `Motive.lean`, `MainComponent/Configuration.lean`
  and `Flat.lean`) uses only the screw-map declarations (`screwEquivOfLinearEquiv`, its
  `_mk_extensor`, `finrank_span_rigidityRows_mapExtensor`), unchanged. No restated name occurs in
  Lean code outside the file (a word grep of `CombinatorialRigidity/`, by bare name). Docstrings
  outside it that become false: `RecordsLinks.of_forall`'s (`PanelHinge.lean:125`, "and of the
  generic body-hinge theorems") and the genuine form's (`Theorem55.lean:2091`, "and the generic
  hinge-point theorems read the witness's rows"). Those at `ProjectiveInvariance.lean:27`,
  `Engine.lean:261` and `PanelHinge.lean:374` name declarations or a step that stay. So no twin,
  and no pencil statement or proof moves.
- **The predicate: `IsGenericHingePoints G q`, at every selector that records the links of `G`.**
  `BodyHingeFramework` has no selector, and exchanging a label's ends negates its `hingePointRow`
  (`hingePointRow_eq_neg_of_swap`: the extensor is the points', the hinge row is antisymmetric). So
  the predicate quantifies the selector: for every `ends` with `RecordsLinks G ends`, every
  subfamily of rows at the edges of `G` that is independent at some assignment is independent at
  `q`. At one such selector it is the same condition (`isGenericHingePoints_iff_of_recordsLinks`,
  by a sign per index, `linearIndependent_hingePointRow_iff_of_recordsLinks`): the blueprint's
  "ends in a fixed order", whose remark that the order does not matter becomes that lemma. It reads
  only the points at the edges (`isGenericHingePoints_congr`, S13's body-hinge side). Rejected:
  `G.endsOf` in the definition (`[Inhabited α]` in every statement naming the predicate); an
  existential selector (equivalent by the same lemma, which a consumer with its own selector would
  need anyway); rows indexed by links `(e, u, v)` (selector-free, but the abundance engine and the
  extraction `exists_independent_panelRow_subfamily_of_le_finrank` are indexed by `β × t × t`).
- **Signatures** (compiled; namespace `BodyHingeFramework`, the restated names unchanged):
  - `IsGenericHingePoints (G : Graph α β) (q : β × Fin k × Fin (k + 1) → K) : Prop`.
  - New: `hingePointRow_eq_neg_of_swap`, `linearIndependent_hingePointRow_iff_of_recordsLinks`,
    `isGenericHingePoints_iff_of_recordsLinks (h : RecordsLinks G ends) : IsGenericHingePoints G q
    ↔ ∀ s, (∀ i ∈ s, i.1 ∈ E(G)) → (∃ q', LinearIndependent K (hingePointRow ends q' ·)) →
    LinearIndependent K (hingePointRow ends q ·)` (on `s`), and `isGenericHingePoints_congr (h : ∀
    e ∈ E(G), ∀ i b, q (e, i, b) = q' (e, i, b)) : IsGenericHingePoints G q ↔ IsGenericHingePoints
    G q'`. Bare names searched in `CombinatorialRigidity/`, mathlib and `Matroid`: free.
  - `exists_isGenericHingePoints_abundance [Finite α] [Finite β] (G)` and
    `exists_isGenericHingePoints [Infinite K] [Finite α] [Finite β] (G)`: `G` for `ends`, the
    conclusions otherwise unchanged (affine independence at every label kept). The proof builds the
    coordinate family per selector inside `key` and takes the product over the (finitely many)
    selectors and the subfamilies, so neither asks `[Nonempty α]`.
  - `supportExtensor_ofHinge_ne_zero_of_isGenericHingePoints (hk1) {G} (hloop) {q} (hq :
    IsGenericHingePoints G q) : ∀ e ∈ E(G), (ofHinge G …).supportExtensor e ≠ 0`: no `ends`,
    `hends`; the proof reads `G.endsOf`, with an end of the edge as the default body.
  - `exists_hingePoints_independent_hingePointRow [Infinite K] [Finite α] [Finite β] {n} (hk1) (hn)
    (hcard : bodyBarDim n * (Nat.card α - 1) < Nat.card β) (G) (hne : V(G).Nonempty) (hspan)
    (hSimple) {ends} (hends : RecordsLinks G ends) : ∃ q₀ s, (∀ i ∈ s, i.1 ∈ E(G)) ∧ (Nat.card s :
    ℤ) = … ∧ LinearIndependent …`: `hfresh`, `hV`, the total `hends`, `[DecidableEq β]` and
    `[Nonempty α]` gone, the indices at edges added.
  - `finrank_span_rigidityRows_ofHinge_of_isGenericHingePoints`,
    `isInfinitesimallyRigidOn_ofHinge_isGenericHingePoints_iff` and `…_iff_spanningTrees`: binders
    `[Infinite K] [Finite α] [Finite β] {n} (hk1) (hn) (hcard) (G) (hne) (hspan) (hSimple)`, the
    rank formula then `{q} (hq : IsGenericHingePoints G q)`, the two iffs `∀ q, IsGenericHingePoints
    G q → …`. Gone: `hfresh`, `ends`, `hends`, `hV`, `[DecidableEq β]`, `[Nonempty α]`, and the
    last's `hD` (`hn ▸ three_le_screwDim hk1`; the open recon's "goes with S1").
  - `hk1` and `hn` stay, not Theorem 5.6's `hd`: the hinge points are then `Fin k × Fin (k + 1)`,
    while the `hd` form has `Fin (n - 1) × Fin ((n - 1) + 1)`, its parentheses forced by `open
    scoped Graph`'s `G - S` notation (TACTICS-QUIRKS § 48: `n - 1 + 1` does not parse), and item
    11's target `rigidityMatrix_prop11` is in the `k`-form. The `hd` form is a one-line instance
    (`…_of_two_le`, compiled, not planned).
- **The transplant takes nondegeneracy on `E(G)`, so Theorem 5.6's main form is the witness**, as
  at 9a. The proof substitutes `k = n - 1` (`Graph.eq_add_one_of_bodyBarDim_eq_screwDim`) and takes
  `Q0` from `rankHypothesis_of_theorem_55_gen` (`hd` from `hk1` and `hn`), whose nonparallel panels
  give nondegenerate hinges at the edges (`IsNonparallel.isGeneralPosition`,
  `supportExtensor_ne_zero_of_isGeneralPosition`). Spanning points come from the panel meet at the
  edges only; a label outside `E(G)` gets a fixed family with a nonzero first vector, so the
  simultaneous move and the affine read-back still run over every label, and the unit-scalar
  transport is used at edges. The extraction already asks nondegeneracy at links only and returns
  linking indices. The rank formula reads the witness and the genericity at `G.endsOf`.
- **One body, adopted under §1f.3** (the coordinator's call under the PI's standing authorization,
  recorded here): `hV : 2 ≤ V(G).ncard` becomes `hne : V(G).Nonempty` in the witness assembly, the
  rank formula and both iffs. The proof does not need the bound (Theorem 5.6's main form covers one
  body), it changes only these theorems, the spanning-trees row being the theorem at hand, and it
  follows §1e's pattern.
- **The row's witness at a minimal graph** (compiled): the triangle in the plane (`n = 2`, `k = 1`)
  with the labels of `SimpleGraph.shadowGraph` (`Sym2 (Fin 3) ⊕ Fin 13`: 19 labels, `3 · 2 < 19`),
  simple and spanning, `0`-dof (`Graph.isKDof_zero_of_triangle`) and minimal (a base of `M(2·K₃)`
  has 6 elements and the copies of two edges are 4;
  `top_fin_three_shadowGraph_isMinimalKDof_zero_two`). Some hinge-point assignment is generic, and
  the framework at every generic one is infinitesimally rigid: the row's reverse direction, with
  the trees from `deficiency_eq_zero_iff_exists_spanningTrees`. `Nonvacuity.lean` needs a `public
  import` of `HingeGeneric`, and its private `top_fin_three_shadowGraph_isKDof_zero` (at `n = 3`)
  generalizes to `3 ≤ bodyBarDim n` for both rows (hypothesis).
- **The docstring-label check's two findings** (`HingeGeneric.lean:476`, `:485`): the leads of
  `dualBodyMap_hingeRow` and `mapExtensor_rigidityRows` open with the bare label
  `lem:screw-map-rows`, which pins `finrank_span_rigidityRows_mapExtensor` only. "(a step of
  `lem:screw-map-rows`)" clears both (the check run on a scratch copy of the tree: total 0), as for
  `equivExteriorPower_lineExtensor` (`F-243`); `blueprint/lint.sh` check 9's baseline goes 2 → 0.
- **Cascade.** Blueprint, `generic-lift.tex`: the chapter opening's genuine-form sentence (`:11`),
  the section opening (`:1020`–`1046`: the main form, hinges at the edges), `def:generic-hinge-points`
  (fourth and fifth pins, the orientation iff and the congruence), the remark after it and its
  fmlnote (`:1076`–`1105`), `lem:hinge-point-witness` (`V` nonempty; proof `\uses`
  `thm:theorem-55-6` for `thm:theorem-55-6-genuine` and `def:genuine-hinge-realization`, the latter
  if its prose no longer needs it), `thm:bodyhinge-generic-rank` and the two corollaries (`V`
  nonempty), the fmlnote after the tree-packing corollary (`:1527`–`1547`, as 9a's after
  `cor:panel-generic-rigid`); `body-hinge.tex:79`–`83`, `:156`–`158` ("at least two vertices", the
  fresh-label supply). Lean docstrings: `HingeGeneric.lean`'s header (`:29`–`61`),
  `hingePointRow_eq_panelRow`'s, the eight restated declarations', and the two outside. The yaml row
  (`formalization.yaml:491`) and its `alignment` note (`:808`–`818`). The S1 scope sentences:
  README `:162`–`177`, `home_page/index.md:142`–`151`, `intro.tex:266`–`278`, ROADMAP §34
  `:1042`–`1047`. `fidelity.divergences` (`:658`) stays true: the theorem is for simple graphs, M1
  pending. Ledger: `F-207`'s and `F-252`'s body-hinge halves, `F-216` and `F-221` (the pins no
  longer carry the selector or "every label is an edge"), `F-212`'s body-hinge side (S13).
- **Not planned:** an abundance polynomial in the edge coordinates only (its product runs over
  every subfamily and every label's reference minor; stating it needs a `vars` conjunct); moving
  `RecordsLinks` out of the `PanelHingeFramework` namespace, now that a body-hinge predicate reads
  it (a FRICTION candidate).
- **Split.** 10a the statement layer in one commit: no twin, as nothing outside reads the
  declarations, and the restated row lands with its witness and its yaml row (41b's *Architectural
  choices*). 10b the scope sentences, docs only (`notes/Phase41b.md`).
- **Item 11 in view** (§1f.1): the predicate serves a consumer with its own recording selector
  (`isGenericHingePoints_iff_of_recordsLinks`), and the rank formula shares `rigidityMatrix_prop11`'s
  `k`-form; a Lean bridge from it to that lemma's `hgen` (rank–nullity) is item 11's if it wants
  one (hypothesis). **No PI item.**

## 3. Sub-phases, by code

| Code | Letter | Contents | Commits |
|---|---|---|---|
| **CARRIER** | 41a (closed 2026-10-24) | done: `reaimSub` retired; the link predicate, its lemmas and the fill-in tactic; the four R statements; the spike; the switch (the field, 123 declarations in 27 files) and the footprint's docstrings; `withGraph` restricted; `reaim` deleted with `hC` on links; the two genuine forms merged (`notes/Phase41a.md`) | 9, besides the build-time detour P1–P5 |
| **RESTATE** | 41b (opened 2026-10-24) | S2's main results and nodes (with `F-323`, §1.2–1.4); `cor:theorem-55-d3-spanning`; S1's panel and body-hinge theorems (with S13 and `F-324`); G6's row; round 1's scope sentences on the degenerate hinges removed (`formalization.yaml`, README, home page, `intro.tex`, ROADMAP; their selector half went in 41a's item 5b); non-vacuity witnesses at minimal graphs for these rows; S18 (the conditional statement or a repin on the generic forms, after S1; its `hC` moved to links in 41a's item 6); the remaining footprint docstrings; the link conjuncts the field makes redundant (the coordinator's call at 41a's close): the rows form `finrank_span_rigidityRows_genuine_recordsLinks_of_theorem_55_gen` and `exists_rankHypothesis_isGeneralPosition4_of_two_le` (`Theorem56.lean`), and `exists_independent_normalRow_of_le_finrank`'s `hQends` (`PanelGeneric.lean`), with the d = 3 wrapper `exists_rankHypothesis_isGeneralPosition4`; from the PI's decisions at its open (§1b): Theorem 5.6 with general position, G6's row as the rank formula, `HasGenericFullRankRealization`'s last conjunct, and KT's nonparallel in Theorem 5.5's conclusion | 13–16 (`notes/Phase41b.md`) |
| **MULTIGRAPH** | — | M1: the multigraph generic body-hinge theorem (JJ 2010 Theorem 6.1), loops allowed (§1f.4); then `prop:rigidity-matrix-prop11`, restated by 41b's item 11 as KT's body-hinge form proved conditionally, repinned unconditionally on M1 (§1f.1) | 3–5 |
| **UNSTATED** | — | the claims no declaration states, the report's estimates: S22 1–2, S23 1, S24 2–3, S25 1, S31 2–3, S3 0–2, S16 1, S19 0–3, G5 3–5, `F-061` 1–2; after CARRIER, since S3 and S19 touch carrier code (`case_II_placement_eq612`) | 13–23 |

**Why the switch was one commit** (CARRIER): under the lint gate a field cannot be staged file by
file without a temporary twin structure, as an unused proof argument fails `unusedArguments`;
Phase 22l's lesson, API first and switch last (`notes/Phase22l.md` *Architectural choices*).

The program closes with the phase: ROADMAP's RECONCILE bullet compressed, and the ledger's last
`reported` entries given dispositions (`notes/Reconcile.md` §3).

## 4. Open questions

- **KT's nonparallel** (§1b.4): settled by §2's *KT's nonparallel recon* (route B, 41b's items
  4a–4c) and by the PI's decisions in §1c (route B; the d = 3 wrapper concludes `IsNonparallel`).
- **M1 and loops**: settled by the PI in advance (§1f.4): loops allowed, the upper bound's `hC`
  relaxed to non-loop links (a loop's constraint is vacuous, and a loop never crosses a partition);
  if MULTIGRAPH's open recon finds that this costs more than about one extra commit, the question
  goes back to the PI. JJ 2010 Theorem 6.1 (EJC 31, p. 582) is a maximum-rank statement for
  2-edge-coloured multigraphs; the row's "every generic realization" is the project's
  strengthening.
- **The generic panel theorems on one body** (§2, *Item 9's recon*): settled by the PI (§1e), the
  rank formula and the iff take `V(G).Nonempty`; landed with 41b's item 9a.
