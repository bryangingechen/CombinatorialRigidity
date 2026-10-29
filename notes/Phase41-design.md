# Phase 41 — RECONCILE-FORMAL: design (cross-phase plan and recon)

**Status:** opened 2026-10-24 with the PI. Sub-phase **41a** (CARRIER) closed 2026-10-24, work log
`notes/Phase41a.md`: the field `isLink_ends` is on `PanelHingeFramework`, and no main result's
statement changed. Sub-phase **41b** (RESTATE) closed 2026-10-25, work log `notes/Phase41b.md`:
S1's and S2's main results are restated on the linked carrier as the PI decided at its open and
during it (§1b–§1f). Theorems 5.5 and 5.6 conclude KT's nonparallel panels for simple `G`; the
molecular conjecture and the multigraph rows ask nondegenerate hinges on `E(G)` only; the generic
panel and body-hinge theorems hold at every generic realization of every simple graph on one body
or more, the panel rank formula a twentieth main result; and `prop:rigidity-matrix-prop11` is KT
Proposition 2.3 in conditional form. §2's RESTATE arcs are compressed to cited verdicts. The PI's
push ran CI green (*Build & deploy site* at `4c892cb6` and `ae6a852c`, 2026-10-25). Sub-phase
**41c** (MULTIGRAPH) opened 2026-10-28 with the PI (§1g) and closed the same day, work log
`notes/Phase41c.md`: M1, the generic body-hinge theorem, holds for every multigraph, loops allowed,
and KT Proposition 2.3 is proved as KT state it at every generic hinge-point assignment; §2's
MULTIGRAPH arc is compressed to a cited verdict. The same day the PI set UNSTATED's scope, took
§4(a) into it, and asked for a recon of §4(b), the label bound, now the code RELABEL (§1h, §3);
UNSTATED's open recon is in §2, and so is RELABEL's (route B, a transport at the boundary, proved
in a witness; 6–9 commits). On 2026-10-29 the PI took RELABEL by route B and opened it as **41d**
(§1i), work log `notes/Phase41d.md`, with a read-only recon of `minimal_kdof_reduction`'s `hfresh`
as its last item; UNSTATED follows, expected as 41e. **Next:** 41d's item B1.

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
  `F-324`. Then M1 (the multigraph generic body-hinge theorem, JJ 2010 Theorem 6.1), the label
  bound dropped from the main results (RELABEL, 41d; §1h, §1i), and the claims no declaration
  states (S22–S25, S31, S3, S16, S19, G5, `F-061`'s forest lemma), with §4(a).

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

## 1g. The PI's decisions at MULTIGRAPH's open (2026-10-28)

After the push ran CI green, the coordinator asked two questions. The PI's answers, verbatim:

> Q: "Phase 41b is closed and CI is green. Which Phase 41 sub-phase opens next (as 41c)?"
> A: "MULTIGRAPH (Recommended)" (the option described as: "3–5 commits. M1: the generic body-hinge
> theorem for multigraphs (Jackson–Jordán 2010, Thm 6.1), with loops allowed as you decided in
> §1f.4. Then KT Prop. 2.3 (`prop:rigidity-matrix-prop11`) gets an unconditional pin, finishing
> item 11.").

> Q: "How should the sub-phase run once it's open?"
> A: "/coordinate-phase loop".

The run configuration: the 10-run cap lifted; mechanical fixups pre-authorized; Sonnet and Opus
both dispatchable.

What each answer settles:

1. **MULTIGRAPH opens as 41c** (`notes/Phase41c.md`): M1 with loops allowed (§1f.4), then the
   unconditional pin of `prop:rigidity-matrix-prop11` (§1f.1). UNSTATED stays for the PI after it.
2. **41c runs as a `/coordinate-phase` loop**, under the configuration above.

## 1h. The PI's decisions after MULTIGRAPH's close (2026-10-28)

The coordinator put four questions. The PI's answers, verbatim (the option descriptions are the
coordinator's wording on the question form; the bracketed lines are the coordinator's notes):

> Q: "Phase 41d would open UNSTATED, the last sub-phase of Phase 41, with 13–23 commits estimated. It covers S22–S25, S31, the optional S3, S16 and S19, G5 (def:blockingWitness, def:dof-generic, the Plücker expansion) and F-061's forest lemma. Under your RECONCILE call ("kind E is formalized, not restated"), each gets a declaration and a repin. What scope should the open use?"
> A: "Full list (Recommended)" (the option described as: "Every item, the optional S3, S16 and S19 included, as Reconcile.md §1 and §3(c) plan it. The open's recon sizes and orders them.")

> Q: "The design doc's §4 leaves two options open for you. (a) Relax rigidityMatrix_prop11's hC to the non-loop links: free under your §1f.3 policy, but no caller needs it. (b) Drop the label bound hcard from M1 and KT Proposition 2.3: this needs a transport to a larger label type and is not sized. 41d is Phase 41's last sub-phase. Should it take either?"
> A: "Can you explain (b) in more detail?"
> [The coordinator explained what `hcard` is, why the fresh-label supply needs it, a user's workaround (relabel into a bigger type), what dropping it needs, and that Theorem 5.6 and the panel theorem carry the same bound, then re-asked (a)/(b).]
> A: "So I definitely want to include (a) since it seems free. Regarding (b), is some kind of tracking of labeling inevitable here? Should we have set the graph theory up in a way that uses more explicit maps rather than trying to reuse types?"
> [The coordinator answered (below), then asked:] Q: "Should 41d take on (b), dropping the label bound? It sits on Theorem 5.5 (as hfresh), Theorem 5.6, both forms of the molecular conjecture, the generic panel theorem, M1 and KT Prop. 2.3: about seven main results. The likely fix is one relabelling transport at the boundary (embed β into β ⊕ Fin N; rows, deficiency, matroid rank and genericity unchanged), with the internal induction kept as is. (a), the free hC relaxation, is already in."
> A: "Recon (b), every row (Recommended)" (the option described as: "A read-only recon item in 41d sizes one transport that drops the bound from every main result carrying it. It comes back to you with an estimate before any build.")

> Q: "How should the loop run? Last time (41c) the 10-run cap was lifted, mechanical fixups were pre-authorized, and Sonnet and Opus were both dispatchable."
> A: "Same as 41c (Recommended)" (the option described as: "No run cap; mechanical fixups (rescue §1) pre-authorized; Sonnet and Opus dispatchable; stop when 41d closes.")

> Q: "When 41d closes, Phase 41 and the RECONCILE program close with it. ORIGAMI is next (attended). What should the loop do at the close?"
> A: "Stop for your push (Recommended)" (the option described as: "As at 41b's close: the loop stops and you push. ORIGAMI opens later, with you.")

Later the same session, after these answers:

> "I'm thinking that UNSTATED might end up being 41e if the labeling stuff turns out to be a big project; let's keep that open as a possibility."

What each answer settles:

1. **UNSTATED's scope is the full list**: every item of `notes/Reconcile.md` §1 and §3(c), the
   optional S3, S16 and S19 included, and §4(a) (answer 2). Its open's recon sizes and orders them
   (§2, *UNSTATED's open recon*).
2. **§4(a) is in UNSTATED**: `rigidityMatrix_prop11`'s `hC` asked at the links between distinct
   bodies. **§4(b) gets a read-only recon** that sizes one relabelling transport dropping the
   label bound from every main result carrying it, and returns to the PI with an estimate before
   any build: the first item of RELABEL (§3).
3. **The loop runs as 41c's**: no run cap, mechanical fixups (rescue §1) pre-authorized, Sonnet and
   Opus dispatchable.
4. **At Phase 41's close the loop stops for the PI's push**; ORIGAMI opens later, with the PI.
   Answers 3 and 4 were given for 41d as Phase 41's last sub-phase; if RELABEL opens first,
   whether its close also stops the loop is asked at its open.
5. **No letter is minted yet.** RELABEL may open first, as 41d, with UNSTATED as 41e; the PI
   chooses after RELABEL's recon. UNSTATED's open recon is recorded under its code (§2) so that
   either open transcribes it.

**The coordinator's answer to the PI's design question** (the coordinator's, not the PI's; the
framing for RELABEL's recon, not a verdict). KT's induction adds edges (the split-off adds `ab`), and
in Lean a new edge needs a name: a fixed label type with a budget (`hcard`/`hfresh`), a type that
grows (`Graph α (Option β)` per step), or an infinite one. Mathlib's `Graph α β` keeps subgraphs,
deletion, contraction and `induce` in fixed types, which the induction leans on; a growing type moves
a transport into every step, and an infinite `β` clashes with the families indexed by the whole label
type under `[Finite β]` (§2). So the fix belongs once, at the boundary: a transport along `β ↪ β'`.

## 1i. The PI's decisions after RELABEL's recon (2026-10-29)

The coordinator put four questions, from *RELABEL's recon* (§2). The PI's answers, verbatim (the
option descriptions are the coordinator's wording on the question form):

> Q: "RELABEL's recon found that a boundary relabelling (route B) drops the edge-label bound from all six main results that carry it: Theorem 5.5, Theorem 5.6, both molecular conjectures, the generic panel theorem and M1. It is fully compiler-checked, about 6–9 commits, and 23 declarations lose the hypothesis, all strengthenings. Take RELABEL?"
> A: "Yes, route B (Recommended)" (the option described as: "Transport at the boundary along β ↪ β ⊕ Fin N; the induction keeps hfresh internally. Steps: B1 the embedding and minimality transfer, B2 the pullbacks and the spine, B3 the cascade and texts, plus open and close.")

> Q: "If RELABEL is taken, which sub-phase opens as 41d? The recon recommends RELABEL first: UNSTATED's item U11 (def:dof-generic) builds on the restated HingeGeneric.lean, and U10 then has no bound to meet. No other item depends on the order."
> A: "RELABEL as 41d (Recommended)" (the option described as: "RELABEL opens now as 41d; UNSTATED follows as 41e with its scope as already decided (full list plus (a)).")

> Q: "KT Theorem 4.9's induction principle (minimal_kdof_reduction, not a main result) also takes hfresh, and route B can't reach it: dropping it would need route A's deficiency-chain rework. Keep hfresh there?"
> A: "Recon dropping it" (the option described as: "A later recon sizes the deficiency chain's rework under the weaker hypothesis e₀ ∉ E(G − v); comes back to you.")

> Q: "Your earlier "stop for your push at the close" was given for Phase 41's last sub-phase. If RELABEL runs first, what should the loop do when RELABEL closes?"
> A: "We will stop between phases and also if we start running out of context; I will not push until the end of phase 41 though."

What each answer settles:

1. **RELABEL is taken, by route B, and is 41d** (`notes/Phase41d.md`): the transport at the boundary
   along `β ↪ β ⊕ Fin N`, the induction keeping `hfresh` inside, in the steps B1–B3 of §2's arc,
   with the statement changes it lists (each a dropped hypothesis).
2. **UNSTATED follows, expected as 41e**, with its scope as §1h set it (the full list, with §4(a));
   its letter is minted at its own open.
3. **`minimal_kdof_reduction`'s `hfresh` gets a read-only recon item in 41d** that sizes route A's
   combinatorial half (the deficiency chain under `e₀ ∉ E(G − v)`) and returns to the PI with an
   estimate before any build. The coordinator places it last, so that its question reaches the PI
   at the stop between sub-phases.
4. **The loop stops between sub-phases** (so at 41d's close) and when the coordinator's context
   runs low. The PI pushes only at Phase 41's close; this supersedes §1h's answer 4 only as to
   timing between sub-phases.

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

**`BodyHingeFramework`** needs no structural change: it has no selector and its rows read `IsLink`
(`RigidityMatrix/Basic.lean:243`). M1 can reuse the multigraph Theorem 5.6
(`theorem_55_6_multigraph_gen`), whose nonzero hinges are each spanned by vectors of the panels, so
the witness transplant of `HingeGeneric.lean` carries over (confirmed by *MULTIGRAPH's open recon*
below).

**RESTATE's arcs** (closed with 41b on 2026-10-25, compressed at its close to cited verdicts; the
full arcs are in git up to `810cb2d6`). Each verdict landed as `notes/Phase41b.md` records, and the
evidence files stay in `notes/reconcile-formal/`.

**Proposed restatements, S1 after S2, `F-323` and `F-324`** (the open's recon; landed in 41b). The
restatements were settled with §1.3's stronger forms and the PI's decisions at RESTATE's open and
after it (§1b–§1f): `rankHypothesis_of_theorem_55_gen` without `[DecidableEq β]`, concluding
nonparallel panels; `molecular_conjecture` with nondegenerate hinges on `E(G)` on both sides, its
`(⇒)` direction using nondegeneracy only at links
(`screwDim_add_deficiency_le_finrank_infinitesimalMotions`); the generic panel and body-hinge
theorems without `ends`, `hends` and `hfresh`, under `hcard`. The field is `hends` restricted to
`E(G)`, so S1 reduced to `hfresh` → `hcard` and genericity over rows at the edges of `G`. The
families stay indexed by the label type, with conditions only on `E(G)` (the body-bar precedent,
`BodyBar/GenericLift.lean`), as a subtype index would need transport for `ofHinge`,
`MvPolynomial (β × …)`, `induce` and `mulTilde`. `F-323` cost no commit for the two S2 main
results (the binder dropped, `classical` added) and went with item 7 for the multigraph rows;
`F-324` was item 3.

**RESTATE's open recon** (2026-10-24; Claude Opus 5.5, read-only, at `3a627b3d`). Evidence:
`notes/reconcile-formal/RestateWitness.lean` (`lake lean`; no errors, three standard axioms). KT
define nonparallel panels for simple graphs (§5.1, p. 668); Theorem 5.5 reads "(nonparallel, if G
is simple)" (p. 670); Theorem 5.6 states only the rank. `IsGeneralPosition` is the weaker,
projective condition (§1.3, corrected). In the meet model a double edge's two hinges coincide, so at
the double edge on two bodies no framework with nonzero hinges on `E(G)` reaches the rank
(`restated_theorem56_false_at_banana`): `hSimple` stays, and multigraphs keep Phase 35's model
(§1b). G6's row is the rank formula, strictly stronger than the iff (§1b). The last conjunct of
`HasGenericFullRankRealization` is the field once `Q.graph = G` (`lastConjunct_of_field`; item 2),
as is `Coupling.lean`'s `hswap` (`hswap_of_recordsLinks`).

**KT's nonparallel recon** (41b's item 1; 2026-10-24; Claude Opus 5.5, design pass, at `c45211e2`).
Evidence: `notes/reconcile-formal/NonparallelWitness.lean` (`lake lean`; no errors or warnings, its
six `#print axioms` the three standard axioms); the names below are the witness's. The affine
coordinate of a normal is its last (`homogenize`, `def:homogeneous-coords`), so a panel's direction
is the normal's first `k + 1` coordinates, `Fin.init n`, KT's `c(v)` in
`Π(v) = {x | x · c(v) + 1 = 0}` (§5.1, p. 668). `IsNonparallel` asks the directions of any two
distinct bodies of `α` to be linearly independent: KT's nonparallel panels (p. 668; Jackson and
Jordán's "nondegenerate", JJ 2010 §7, KT footnote 3). It implies `IsGeneralPosition` and is strictly
stronger (`generalPosition_not_nonparallel`, at d = 2); it fails at `k = 0`
(`not_isNonparallel_k0`), where Theorem 5.5's `hk1` already stands. **Route B, adopted:** a generic
full-rank realization of a loopless graph gives a nonparallel one of the same rank, at a common
non-root of the rank polynomial at its normals and the general-position product, which for `1 ≤ k`
is nonparallel at each of its non-roots (`exists_nonparallel_of_generic`,
`isNonparallel_of_eval_ne_zero`); it is the device's form of KT Lemma 5.2 (p. 669), KT's rotation to
a nonparallel realization of no smaller rank. Only `theorem_55_minimalKDof_gen` applies it, and the
induction is untouched (items 4a–4c). **Route A**, nonparallel in the motive, would have put `1 ≤ k`
on about a dozen producers to buy KT's eq. (6.1) at full strength, which the formal proof never
uses; the PI rejected it (§1c). The `d = 3` wrapper `exists_rankHypothesis_isGeneralPosition4` takes
a third polynomial factor for nonparallel panels (§1c.2; item 5).

**Item 9's recon** (41b's item 9; 2026-10-25; Claude Opus 5.5, design pass, at `8c2d4475`).
Evidence: `notes/reconcile-formal/PanelGenericWitness.lean` (`lake lean`: no errors or warnings, its
six `#print axioms` the three standard axioms; `#lint` on a copy: no errors in 15 declarations).
Landed as items 9a and 9b. No Lean consumer outside `PanelGeneric.lean`, so no pencil statement
moved and no twin was needed. Genericity is the framework's, `Q.IsGenericNormals`, over the rows
`normalRow Q.ends` at the edges of `Q.graph`. The selector's orientation does not matter: exchanging
a label's ends negates both its extensor and its hinge row (`normalRow_eq_of_swap`), so genericity
reads only the graph and the normals (`isGenericNormals_iff_of_graph_eq`). The witness is Theorem
5.6's main form, whose nonparallel panels give nondegenerate hinges on `E(G)`; the transplant asks
nondegeneracy at links only. One body: the PI's §1e. Not planned: an abundance over every framework
on `G`, whatever its selector (`exists_isGenericNormals_abundance'`, compiled in the witness).

**Item 10's recon** (41b's item 10; 2026-10-25; Claude Opus 5.5, design pass, at `ce98d5ec`).
Evidence: `notes/reconcile-formal/HingeGenericWitness.lean` (`lake lean`: no errors or warnings,
its nine `#print axioms` the three standard axioms; `#lint` on a copy: no errors in 18
declarations). Landed as items 10a and 10b. No restated name occurs in Lean outside
`HingeGeneric.lean` (`Pencil/Arms.lean` uses only the screw-map declarations), so no twin was
needed and no pencil statement moved.
- **The predicate** `IsGenericHingePoints G q` quantifies the selector: every `ends` with
  `RecordsLinks G ends`, as `BodyHingeFramework` has no selector and exchanging a label's ends
  negates its `hingePointRow` (`hingePointRow_eq_neg_of_swap`). At one recording selector it is the
  same condition (`isGenericHingePoints_iff_of_recordsLinks`), and it reads only the points at the
  edges (`isGenericHingePoints_congr`, S13's body-hinge side). `hk1` and `hn` stay, not Theorem
  5.6's `hd` (TACTICS-QUIRKS § 48; `rigidityMatrix_prop11` is in the `k`-form).
- **The witness** is Theorem 5.6's main form, as the transplant takes nondegeneracy on `E(G)`; the
  row's witness at a minimal graph is the triangle in the plane with the labels of
  `SimpleGraph.shadowGraph` (19 labels, `3 · 2 < 19`), a minimal 0-dof-graph.
- **One body, adopted under §1f.3** (the coordinator's call under the PI's standing authorization,
  recorded here): `hV : 2 ≤ V(G).ncard` becomes `hne : V(G).Nonempty` in the witness assembly, the
  rank formula and both iffs. The proof does not need the bound (Theorem 5.6's main form covers one
  body), it changes only these theorems, the spanning-trees row being the theorem at hand, and it
  follows §1e's pattern.
- **Not planned:** an abundance polynomial in the edge coordinates only (its product runs over
  every subfamily and every label's reference minor; stating it needs a `vars` conjunct); moving
  `RecordsLinks` out of the `PanelHingeFramework` namespace, now that a body-hinge predicate reads
  it (a FRICTION candidate).
- **Item 11 in view** (§1f.1): the predicate serves a consumer with its own recording selector
  (`isGenericHingePoints_iff_of_recordsLinks`), and the rank formula shares `rigidityMatrix_prop11`'s
  `k`-form. Item 11's conditional form needed no Lean bridge from it to that lemma's `hgen`
  (rank–nullity, hypothesis); the unconditional repin is MULTIGRAPH's (§3).

**MULTIGRAPH's open recon** (41c's open; 2026-10-28; Claude Opus 5.5, design pass, at `ae6a852c`;
compressed at 41c's close to a cited verdict, the full arc in git up to `79df20c0`). Evidence:
`notes/reconcile-formal/MultigraphWitness.lean` (`lake lean`: no errors or warnings, its eleven
`#print axioms` the three standard axioms; `#lint` on a copy: no errors in 15 declarations), which
proved every statement in the namespace `Recon41cMultigraph`; items 1–3 transcribed it
(`notes/Phase41c.md`). M1's lower bound starts from the multigraph Theorem 5.6
(`theorem_55_6_multigraph_gen`), whose hinges lie in the panels and so are extensors of panel
vectors by definition (`exists_extensor_eq_of_extensorInPanel`, the one new leaf); the rank formula
and its two iffs lose `hSimple` and nothing else. JJ 2010 Theorem 6.1 (EJC 31, p. 582, against
`.refs/`) is a maximum-rank statement for 2-edge-coloured multigraphs and never mentions loops,
which the formalization admits, as a loop constrains no motion. Loops cost one commit (§1f.4): the
upper bound uses `hC` only at edges between two parts, so it asks it at `u ≠ v` (item 1, 24 caller
wraps in 18 files). KT Proposition 2.3 (p. 655) is the three-way equivalence at every generic
hinge-point assignment (item 3), pinned by `prop:rigidity-matrix-prop11`; `rigidityMatrix_prop11`,
which Theorem 5.6's proofs use, moved to `prop:rank-formula-of-motion-bound`, as the KT label's
`\uses` would otherwise cycle through `lem:hinge-point-witness`. Not planned: §4's two open
questions (taken up in §1h); the generic panel theorems stay for simple graphs, as in the meet
model a double edge's two hinges coincide (§1b.1).

**UNSTATED's open recon** (2026-10-29; Claude Opus 5.5, design pass, at `3b9f766b`; recorded under
the code, so that the sub-phase that opens as UNSTATED transcribes it into its work log). Evidence:
`notes/reconcile-formal/UnstatedWitness.lean` (`lake lean`: no errors or warnings, its seven
`#print axioms` the three standard axioms; `#lint` on a copy: only `unusedArguments` at four `Prop`
targets, which carry the instances of the planned theorems). It proves S22, S24's rank form, S25 with
`def:blockingWitness`, S19, §4(a) and S16's one new step, and states the other targets as `Prop`s
that elaborate (names below are the witness's, in `ReconUnstated`). Every node, pin and declaration
was re-read at `3b9f766b`, as the report predates RECONCILE's rounds and 41a–41c.

*Corrections to the plan.* G5's packing move and `lem:forest-surgery-unsplit` are settled: the
descent calls `lem:packing-move`'s pin since round 3 (`F-087`, `9840dd2c`), and the second node was
restated as its pin's case and filled in round 2 (`F-091`, `F-234`, `43c5c8d7`); G5 is the other
three. S19 touches no carrier code: `lem:case-I` as PROSE stated it (`85e0e4f8`, before the
report) takes the contraction's realization at the target rank, so its identity is arithmetic from
KT Lemma 3.5, as its proof's first paragraph says; the block-form rank addition with content is the
proof's, and stays prose under the crux carve-out. Only S3 touches `case_II_placement_eq612` (§3's
row said both). `F-061`'s forest lemma backs no blueprint claim at HEAD (round 2 replaced "any
spanning forest" by the star forest), so it lands with a new node. S31 needs no label bound: on
`G.shadowGraph`, whose labels carry their own supply (`lem:molecule-graph-carrier`), as the molecule
rank formula is stated, so it does not wait on RELABEL.

*The checklist*, in the recommended order: the isolated one-commit items first, the zone's
one-commit items next, then the items with a rebuild-heavy or crux footprint, and last the two that
need their own recon. No item depends on another, except that `def:blockingWitness` lands with S25.
"Zone" is the fragility zone (`Molecular/AlgebraicInduction/`, `Molecular/RigidityMatrix/`, the
ScrewSpace carrier).
- **U1. S25 and `def:blockingWitness`** (`F-041`; `F-038`, `F-008`'s part). New
  `SimpleGraph.IsBlockingWitness G k ℓ s := ℓ ≤ k * s.card ∧ k * s.card < (G.edgesIn ↑s).ncard + ℓ`
  beside `IsSparse` (`Sparsity.lean`), with `not_isSparse_of_isBlockingWitness`; and
  `PartialOrientation.runPebbleGameWith_isBlockingWitness` (`PebbleGame/Correctness.lean`): under
  `ℓ < 2k`, a `.inl w` return from the empty orientation on a list of edges of `G` (`hmem` only)
  gives `G.IsBlockingWitness k ℓ w.V'`, by `runPebbleGameWith_witness_bridges` and
  `certifies_against` (proved). `def:blockingWitness` pinned and filled; `thm:pebble-game-correct`
  gains the pin. Outside the zone. 1 commit.
- **U2. S24** (`F-051`). `Matroid.Union_rk_eq`, the rank of every `X` in the union of a finite family
  in `Union_pow_rk_eq`'s form (proved), and `Matroid.Union_indep_iff_count`,
  `(Matroid.Union Ms).Indep X ↔ ∀ Y ⊆ X, Y.ncard ≤ ∑ i, (Ms i).rk Y`, by `Union_pow_indep_iff_count`'s
  proof (`S24IndepTarget`); `Matroid/Constructions/Union.lean` (ported from Peter Nelson's
  `Matroid`: credit). `thm:matroid-partition-rank` pins both; its note goes. 1 commit.
- **U3. S23** (`F-083`). `Graph.circuit_diff_isSpanningTreePacking` (`Induction/Operations.lean`):
  for a circuit `X` of `M(G̃)` and `e ∈ X`,
  `(((G.mulTilde n) ↾ (X \ {e})).induce (G.fiberSpan n X)).IsSpanningTreePacking (bodyBarDim n)`
  (`S23Target`), by `circuit_induces_isTight`, `isSparse_diff_singleton_of_isCircuit` carried to
  the induced graph, `IsTight.connected` and `isSpanningTreePacking_of_isTight`; the friction is the
  `induce`/`restrict` bookkeeping (`E = X \ {e}`, `V = V(X)`). `lem:circuit-induces-rigid`'s third
  pin; its note goes. 1 commit.
- **U4. S22** (`F-101`). `Graph.minimal_kdof_reduction_sequence` (`ForestSurgery/Reduction.lean`):
  `Relation.ReflTransGen` of a step relation (`KTReductionStep`: to a minimal `0`-dof-graph, by a
  split-off at a vertex of degree two or the contraction of a proper rigid subgraph) from `G` to a
  double edge, under `minimal_kdof_reduction`'s `3 ≤ D` and `hfresh` (proved, ~40 lines from that
  principle, `isMinimalKDof_ncard_le_two_trichotomy`, `splitOff_isMinimalKDof` and
  `rigidContract_isMinimalKDof`). `thm:minimal-kdof-reduction` pins it beside (ii)'s; the note's
  first sentence goes. It carries `hfresh`, as the principle does; neither is a main result. 1 commit.
- **U5. S19** (`F-116`). `BodyHingeFramework.case_I_rank_add_iff` (proved): for a proper rigid `H`
  with `r ∈ V(H)` and frameworks `F`, `F₂`, if `rank R(F₂) = D(|V(G/E(H))| − 1) − def` of the
  contraction, then `rank R(F) = D(|V(G)| − 1) − def(G̃)` iff
  `rank R(F) = D(|V(H)| − 1) + rank R(F₂)`, by `rigidContract_deficiency_eq` and
  `rigidContract_vertexSet_ncard`, with no minimality (the node's `G` minimal is a special case).
  Additive, beside the block-pin criteria in `Pinning.lean`; no fragile proof is touched.
  `lem:case-I` pins it first; its note's "No pinned theorem mentions the contraction" is rewritten;
  the three block-pin pins stay (the first is live) unless the label check moves them. 1 commit.
- **U6. §4(a)** (no ledger entry: a new ID). `rigidityMatrix_prop11`'s `hC` becomes
  `∀ e u v, F.graph.IsLink e u v → u ≠ v → F.supportExtensor e ≠ 0` (`rigidityMatrix_prop11'`,
  proved: one argument fewer); its three callers in `Theorem55.lean` wrap
  (`fun e u v h _ => hC e u v h`). `prop:rank-formula-of-motion-bound` asks the hinge at the edges
  whose ends differ. Zone, mechanical. 1 commit.
- **U7. S16** (`F-124`). `hasPanelRealization_of_generic` without `[G.Loopless]` (`S16Target`): the
  framework is `Q.toBodyHinge` with the hinge at each loop at `u` replaced by `C(n_u, n_w)` for a body
  `w ≠ u` (`2 ≤ |V(G)|`), which lies in `u`'s panel (`exists_extensor_eq_panelSupportExtensor_gen`)
  and is nonzero by general position; the rows' span is unchanged, as a loop's rows are zero
  (`span_rigidityRows_eq_of_eq_off_loops`, proved). `GenericityDevice.lean`, zone; the three callers
  pass the instance today, so check for a now-unused `have : G.Loopless`. The node's note on loops
  goes. 1 commit.
- **U8. `F-061`'s forest lemma.** `BodyHingeFramework.exists_independent_rigidityRows_of_isForest`
  (`ForestTarget`): for a forest `T ≤ F.graph` (`Graph.IsForest`) with a nonzero hinge at each edge,
  `D − 1` rows per edge, jointly independent, in `exists_independent_rigidityRows_of_starForest`'s
  shape. Route: induction on `|E(T)|` removing a pendant edge (`IsForest.exists_isPendant`,
  `IsForest.anti`); its rows stay independent on the assignments supported at the pendant body,
  where the others vanish, and `linearIndependent_sum_pinned_block` joins them.
  `RigidityMatrix/Basic.lean`, zone: an interface change there rebuilds the molecular chain. A new
  node after `lem:own-end-rows-independent`. 1–2 commits.
- **U9. The Plücker expansion** (`F-059`). The coordinates of `extensor v` in
  `(Pi.basisFun K (Fin (d+1))).exteriorPower j` are the Plücker coordinates times KT's sign
  (`PluckerTarget`), by mathlib's `exteriorPower.basis_repr_apply` and `ιMultiDual_apply_ιMulti`
  (the minor), against `pluckerCoord`'s `orderEmbOfFin` submatrix: the friction is the index bridge
  (`Set.powersetCard.ofFinEmbEquiv` against `Finset.orderEmbOfFin`) and a transpose.
  `Molecular/Extensor.lean`, the chain's root (a full rebuild). A lemma node after
  `def:plucker-coords`; its note goes. 1–2 commits.
- **U10. S31** (`F-174`, `F-183`). `SimpleGraph.molecular_rigid_iff_square_rigid` (`S31Target`),
  under `[Nonempty V]` and `hmin`: some selector recording the links of `G.shadowGraph` and centres
  distinct at each edge give an infinitesimally rigid molecular framework iff `G²` has an
  infinitesimally rigid placement. (⇒) nondegenerate hinges (`lineExtensor_ne_zero_of_ne`) and
  `screwDim_add_deficiency_le_finrank_infinitesimalMotions` give `def = 0`, then
  `molecule_generic_rigid` at `exists_isGenericPlacement`; (⇐) the rigid placement bounds the generic
  rank (`finrank_range_rigidityMap_le_genericRank`), `molecule_rank_formula` and
  `deficiency_nonneg` give `def = 0`, and `exists_molecular_rankHypothesis_generalPosition` (its
  bound met by `card_shadowLabel_lt`) with `rankHypothesis_zero_iff` gives the framework, its
  centres distinct by general position. `Molecule/Application.lean`. The theorem's second pin; its
  note's last sentences go. A crux node: its exposition-ledger entry is re-read. 1–2 commits.
- **U11. `def:dof-generic`** (`F-008`'s part). **Needs its own read-only recon** (the
  definition-faithfulness gate). The witness's candidates: `dof F = D(|V(G)| − 1) − rank R(G,p)`, and
  `IsMaxRankHingePoints G q` (nondegenerate at the non-loop links, and at every `E' ⊆ E(G)` the rows
  of `ofHinge (G ↾ E') q` of the largest rank over the hinge-point assignments with that property),
  which the paragraph after `lem:generic-hinge-points-nondegenerate` derives from
  `IsGenericHingePoints` for loopless `G`. Open: which carrier stands for "all realizations of `G`";
  loops, whose hinge points genericity leaves free; whether KT Proposition 2.3 then holds at every
  such realization (a main result's statement, the PI's). `GenericLift/HingeGeneric.lean`, after
  RELABEL if RELABEL restates that file. 1–2 commits.
- **U12. S3** (`F-150`; the dead pin, `F-152`'s part). A declaration for
  `lem:case-II-realization-placement` as stated, from a realization of `G_v^{ab}`: the count in
  steps 7–14 of `case_II_realization_all_k`'s proof extracted as a lemma (a realization of
  `G_v^{ab}` of rank `N` gives `rank R(G, q₀) ≥ N + D − 1`; `D(|V(G)| − 1) − 1` at a rigid one),
  which `case_II_realization_all_k` then calls; `case_II_placement_eq612`, dead and unmeetable in
  Cases II and III, deleted with the repin (the deletion gate). **Needs a compiler-checked spike
  first**: a route-composition question inside a ~600-line proof in `CaseII.lean`, zone. 2 commits.
- **Close**: the ledger's remaining `reported` and `left` entries given dispositions and ROADMAP's
  RECONCILE bullet compressed (`notes/Reconcile.md` §3), if UNSTATED is Phase 41's last sub-phase.

*Estimate.* U1–U7 one commit each, U8–U11 one or two, U12 two; with U11's recon and U12's spike, the
open's transcription and the close, **15–21 commits** (the report's 13–23).

**RELABEL's recon** (2026-10-29; Claude Opus 5.5, design pass, at `e51acb76`; recorded under the
code, so that the sub-phase that opens as RELABEL, if the PI takes it, transcribes it). Evidence:
`notes/reconcile-formal/RelabelWitness.lean` (`lake lean`: no errors or warnings, its eight
`#print axioms` the three standard axioms; `#lint` on a copy: no errors in 25 declarations). It
proves every composition of route B below with no `sorry`; names are the witness's, in
`Recon41Relabel` namespaces.

*The list.* Six of the 20 main results of `formalization.yaml` carry the bound, each visibly as a
hypothesis: `theorem_55_minimalKDof_gen` (Theorem 5.5, `hfresh`), and `hcard : D(|α| − 1) < |β|` on
`rankHypothesis_of_theorem_55_gen` (Theorem 5.6), `molecular_conjecture`,
`molecular_conjecture_multigraph`, `finrank_span_rigidityRows_of_isGenericNormals` and
`isInfinitesimallyRigidOn_ofHinge_isGenericHingePoints_iff_spanningTrees` (M1). The other fourteen
state none; the molecule rank formula meets it inside (below). Theorem-level nodes whose pins carry
it: `thm:theorem-55`, `thm:theorem-55-d3-instance`, `cor:theorem-55-d3-spanning`,
`thm:theorem-55-6-genuine`, `thm:theorem-55-6`, `thm:theorem-55-6-d3`, `thm:theorem-55-6-rows`,
`thm:theorem-55-6-multigraph` (both pins), `cor:theorem-55-6-multigraph-d3`,
`thm:molecular-conjecture`, `thm:molecular-conjecture-multigraph`, `thm:panel-generic-rank`,
`cor:panel-generic-rigid`, `thm:bodyhinge-generic-rank`, `cor:bodyhinge-generic-rigid`,
`cor:bodyhinge-generic-tree-packing`, `prop:rigidity-matrix-prop11`, `thm:panel-hinge-iff-molecular`
(`Molecule/Modelling.lean`) and `thm:minimal-kdof-reduction` (`hfresh` on the minimal
`0`-dof-graphs); lemma-level, `lem:hinge-point-witness`, `lem:theorem-56-general-position`
(`Molecule/Theorem56.lean`), `lem:case-II-realization`, `lem:case-III`, `lem:chain-cycle-dichotomy`,
`lem:chain-data-extract` and `lem:pencil-jj-chart`. In Lean, 18 declarations take `hcard` and 16
`hfresh`; `Deficiency.lean` has only the derivative `freshEdgeSupply_of_card_lt`, which turns the
first into the second. `rem:fresh-edge-supply` lists the panel-layer nodes only. No main result
states `IsHingeCoplanar`.

*The precedents.* The pencil realization theorem (`Pencil/MainComponent/Statements.lean`; its
reduction `_of_X0` is in `Pencil/X0.lean`, which §3's row named) avoids the bound twice over. Its
own induction **recycles**: the split-off at a body `x 0` of degree two gives the new edge `ab` the
label `e 0` of the ear's edge `a − x 0` (`G.splitOff (x 0) a b (e 0)`,
`MainComponent/SplitOff.lean`, with the selector `Function.update ends (e 0) (a, b)`,
`RecordsLinks.update_splitOff`), and compares two frameworks with two selectors
(`finrank_span_rigidityRows_splitOff_special`); its principle `pencil_reduction` asks no supply.
Where it calls KT Theorem 5.6 (Jackson and Jordán's equality, `Bridge.lean`) it **transports at the
boundary**: it relabels into `β ⊕ Fin (3|α| + 1)` (`Graph.embedEdges`), where the supply holds, and
its conclusion reads no label. The molecule rows fix the labels **by construction**: those of
`G.shadowGraph` are `Sym2 V ⊕ Fin (6(|V| − 1) + 1)`, whose second summand no edge uses and which
meets `hcard` (`card_shadowLabel_lt`, its one caller `molecule_rank_lower_bound`); their statements
take a `SimpleGraph V` and name no label type. Mathlib's `Graph` has only the vertex map
(`Maps.lean`), but the `Matroid` package has `Graph.edgeMap` and `Graph.edgePreimg`
(`Matroid/Graph/Map.lean`, already in the import closure), and `embedEdges` is `edgeMap` at an
embedding (`embedEdges_eq_edgeMap`). Nothing there relates the cycle matroid to an edge map, so
minimality goes through deficiencies (T5).

*Route A, recycling inside the induction: breaks at Case III.* `G.splitOff v a b eₐ` is `G_v^{ab}`
with `ab` labelled `eₐ`, as every link of `eₐ` meets `v`; and the genericity device's variables are
the normals, `α × Fin (k + 2)` (`exists_rankPolynomial_of_le_finrank_linking`), none per label. Case
II would carry over: `case_II_realization_all_k` already compares a framework on `G` (selector
`G.endsOf`) with one on `G_v^{ab}` (selector `Q.ends`), as the pencil step does, and its own use of
`e₀ ∉ E(G)` needs only `e₀ ∉ E(G − v)`; but it passes the hypothesis to the deficiency chain
(`splitOff_isMinimalKDof_of_pos`, `dof_tracking`, `circuit_splitOff_meets_fiber`,
`edgeSet_mulTilde_splitOff_diff_fiber`, `removeVertex_le_splitOff`), which would be reproved under
the weaker one. Case III breaks: `ChainData` carries one label `e₀` with `e₀_fresh` for the
split-off at every interior vertex of the chain. `e₀_ne_edge` makes `shiftEdgeCycle i`
duplicate-free (`nodup_shiftEdgeCycle`), so `shiftEdgePerm i` is the label permutation carrying the
split-off at `v₁` to the one at `vᵢ` (`splitOff_isLink_shiftRelabel_iff`, `Operations.lean`); and
`chainData_dispatch_interior_of_discriminator` (`CaseIII/Realization.lean`) builds one selector
`ends₀` that gives `e₀` the ends `(v₂, v₀)` and the two chain edges at `v₁` their own, so it needs
`e₀ ≠ edge 0, edge 1`. Recycled, when `E(G)` uses every label, the only labels the split-off at `v₁`
frees are `edge 0` and `edge 1`, a different pair at each interior vertex: the shift is no longer
one cycle on a duplicate-free list, and `ends₀` cannot hold both pairs of ends at one label. That is
a redesign of Case III's chain machinery (`CaseIII/`, 7,198 lines, 3,136 of them in `Relabel/`, and
`ChainData`), in the fragility zone, needing its own design recon before any estimate. The supply
threads through `hfresh` binders in 16 declarations, `e₀ ∉ E(…)` binders in 35 (`Reduction.lean` 10,
`EdgeSplitting.lean` 10, `CaseIII/Realization.lean` 4, `CaseIII/Relabel/Basic.lean` 4,
`SplitOffDeficiency.lean` 4, `Operations.lean` 2, `ChainExtraction.lean` 1) and uses of `e₀_fresh`
in 14. **Not recommended.**

*Route B, a boundary transport along `inl : β ↪ β ⊕ Fin (D(|α| − 1) + 1)`: feasible, proved.* The
induction and every proof inside it stay, with `hfresh`; each main result applies its landed form at
`β ⊕ Fin N`, where `freshEdgeSupply_of_card_lt` gives the supply, and pulls the framework back.
- *The graph.* `embedEdges` keeps the bodies, simplicity and the deficiency (landed, `Bridge.lean`).
  Minimality transports through deficiencies (T5): deleting an edge of a minimal `c`-dof-graph
  raises the deficiency (`deficiency_lt_of_isMinimalKDof`), and conversely
  (`isMinimalKDof_of_deficiency_lt`), by KT eq. (2.4) and `matroidMG_restrict_mulTilde`, as
  `exists_isMinimalKDof_spanning_subgraph` argues; the restriction commutes with the relabelling
  (`embedEdges_restrict_diff`). About 90 lines, the only new mathematics.
- *Rows and motions* (T1, T2). The pullback `bhComap` of a body-hinge framework on `G.embedEdges ι`
  has the same rigidity rows, as sets (`bhComap_rigidityRows`), and the same motions; the pullback
  `phComap` of a panel-hinge framework keeps the normals and takes the selector `ends ∘ ι`, whose
  link field is three lines. Nonparallel panels, general position, the hinges at the edges, the rank
  and `HasCoplanarPanelRealization`'s nonzero hinge at every label come back unchanged.
- *Genericity: no transport*, against the coordinator's hypothesis. `IsGenericNormals` and
  `IsGenericHingePoints` stay on `G`; the generic theorems use `hcard` only to call Theorem 5.6 for
  their witness, and at the bound-free Theorem 5.6 their landed proofs compile with the binder
  deleted and nothing else changed (the witness's copies: both molecular conjectures, the panel rank
  and its iff, M1 with its rank formula, iff and witness assembly, and KT Proposition 2.3).
- *The existential conclusions.* Theorems 5.5 and 5.6, in the genuine, rows, simple and multigraph
  forms, are each a 10–20-line transport of the landed form (`theorem_55_minimalKDof_gen'`,
  `rankHypothesis_genuine_of_theorem_55_gen'`,
  `finrank_span_rigidityRows_genuine_recordsLinks_of_theorem_55_gen'`,
  `rankHypothesis_of_theorem_55_gen'`, `theorem_55_6_multigraph_gen'`). `[Finite β]` stays, as
  `β ⊕ Fin N` must be finite; the genuine and rows forms lose `[DecidableEq β]`, which only the
  supply used (the linter flags it); Theorem 5.5 keeps it, for `IsMinimalKDof`.

*Which statements change* (the PI's call: each loses a hypothesis). 23 declarations: the six main
results; their `d = 3` forms (`theorem_55_minimalKDof_k`, `theorem_55_d3`,
`rankHypothesis_deficiency_of_theorem_55_d3`, `rankHypothesis_of_theorem_55_d3`,
`theorem_55_6_multigraph_d3`); the other forms of Theorem 5.6
(`rankHypothesis_genuine_of_theorem_55_gen`,
`finrank_span_rigidityRows_genuine_recordsLinks_of_theorem_55_gen`, `theorem_55_6_multigraph`,
`theorem_55_6_multigraph_gen`); the generic theorems' other forms
(`isInfinitesimallyRigidOn_of_isGenericNormals_iff`, `exists_hingePoints_independent_hingePointRow`,
`finrank_span_rigidityRows_ofHinge_of_isGenericHingePoints`,
`isInfinitesimallyRigidOn_ofHinge_isGenericHingePoints_iff`,
`tfae_finrank_span_rigidityRows_ofHinge_deficiency`); and the molecule chain's three
(`exists_rankHypothesis_isGeneralPosition4` and its `_of_two_le`,
`exists_molecular_rankHypothesis_generalPosition`; by grep the same pattern, not compiled). The
internal forms keep `hfresh` (`theorem_55_minimalKDof_k_all_k`,
`hasGenericFullRankRealization_of_theorem_55_gen`, `theorem_55_6_multigraph_of_two_le`, Cases II and
III, the chain extraction). Not covered: `minimal_kdof_reduction` (`thm:minimal-kdof-reduction`, KT
Theorem 4.9's principle, and UNSTATED's U4 after it), whose split step names a fresh label for a
predicate on `Graph α β`, so no pullback applies; dropping it would be route A's combinatorial half
(the deficiency chain under `e₀ ∉ E(G − v)`), and no main result needs it. No pencil row moves:
`lem:pencil-jj-chart` may keep `hfresh`, as its caller relabels already. `G.shadowGraph`'s padding
becomes unneeded; keeping it moves no statement (dropping it would change
`lem:molecule-graph-carrier` and U10's statement).

*The plan*, if the PI takes RELABEL by route B:
- **B1.** `embedEdges` moved up to `Deficiency.lean`, beside `freshEdgeSupply_of_card_lt` (or
  defined as `edgeMap`), with its graph lemmas, T5 and the padded supply; `def:pencil-embed-edges`
  moved to the chapter of `rem:fresh-edge-supply`, its name kept. A full rebuild of the molecular
  chain. 1 commit.
- **B2.** T1 and T2 after the induction (in `Theorem55.lean` or a file it imports that imports
  `PanelHinge.lean`, not in `RigidityMatrix/Basic.lean` or `PanelHinge.lean`, which would rebuild
  the chain); the spine's five transports, the main results keeping their names and the
  supply-taking forms renamed (the deletion gate). 1–2 commits.
- **B3.** The cascade: the binder deleted in the `d = 3` forms, the conjectures, `PanelGeneric.lean`
  (2), `HingeGeneric.lean` (5), `Theorem56.lean` (2) and `Modelling.lean` (1), and at the callers
  (`Nonvacuity.lean`, `Application.lean`); `rem:fresh-edge-supply` rewritten, the fmlnotes at the
  nodes above dropped, and `formalization.yaml`'s rows (M1's and the panel row's "more than D(|V|−1)
  edge labels"). 1–2 commits.
- The open and the close.

**6–9 commits**, the open and the close included. Fragility-zone exposure: `Theorem55.lean` only, at
its main results' statements and the transports after the induction; no proof inside the induction
changes, and the witness compiled every composition against the built tree with no residual goal.

*Recommendation.* Take RELABEL, by route B: it brings six main results to their sources' statements,
which have no label bound, at about a third of UNSTATED's size, and the witness leaves no open step.
Open it before UNSTATED, as 41d: U11 (`def:dof-generic`) waits on the restated `HingeGeneric.lean`
(*UNSTATED's open recon*), U10 then has no bound to meet, and no other item depends on the order.

*For the PI* (§1h.5): whether RELABEL is taken, with the statement changes above; by which route (B
recommended; A is unsized and reaches Case III); which of RELABEL and UNSTATED opens as 41d; and, if
RELABEL is taken, whether `minimal_kdof_reduction` keeps `hfresh` (recommended: no main result needs
it). The PI's answers are §1i: route B, as 41d, and a recon of dropping `hfresh` there (41d's item R).

## 3. Sub-phases, by code

| Code | Letter | Contents | Commits |
|---|---|---|---|
| **CARRIER** | 41a (closed 2026-10-24) | done: `reaimSub` retired; the link predicate, its lemmas and the fill-in tactic; the four R statements; the spike; the switch (the field, 123 declarations in 27 files) and the footprint's docstrings; `withGraph` restricted; `reaim` deleted with `hC` on links; the two genuine forms merged (`notes/Phase41a.md`) | 9, besides the build-time detour P1–P5 |
| **RESTATE** | 41b (closed 2026-10-25) | done: `HasGenericFullRankRealization`'s link conjunct and `F-324`'s derivable `hD`s dropped; `IsNonparallel`, and Theorems 5.5 and 5.6 with their `d = 3` instances concluding it for simple `G` (route B, §1c); `molecular_conjecture` on one body or more, hinges on `E(G)`, nonparallel panels (§1d); the multigraph rows and `IsHingeCoplanar` on `E(G)`; `cor:theorem-55-d3-spanning` from `theorem_55_d3`; S1's panel and body-hinge theorems at every generic realization on `G` under `hcard`, one body or more (§1e, §1f.3); G6's row, the twentieth main result; witnesses at the single edge and the triangle; S18 as KT Proposition 2.3, conditional (§1f.1); the scope and degenerate-hinge sentences; the link conjuncts the field makes redundant (`notes/Phase41b.md`) | 23, the open and the close included (planned 13–16) |
| **MULTIGRAPH** | 41c (closed 2026-10-28) | done: the upper bound asked at the non-loop links (§1f.4); M1, the generic body-hinge theorem (JJ 2010 Theorem 6.1) for every spanning multigraph, loops allowed, from the multigraph Theorem 5.6, with witnesses at the double edge and the double edge with a loop; KT Proposition 2.3 as KT state it, at every generic hinge-point assignment, pinned by `prop:rigidity-matrix-prop11`, its conditional form under `prop:rank-formula-of-motion-bound` (§1f.1) (`notes/Phase41c.md`) | 6, the open, the re-read and the close included (planned 3–5), besides three verification fixups |
| **RELABEL** | 41d (opened 2026-10-29 with the PI, §1i) | the bound on the edge labels (`hcard`, `hfresh`) dropped from the main results that carry it (§1h.2), by route B (§1i.1). Its recon (§2, *RELABEL's recon*): six main results carry it, and 23 declarations' statements change; route B, a transport at the boundary along `inl : β ↪ β ⊕ Fin N` with the induction untouched, is proved in full by the witness `notes/reconcile-formal/RelabelWitness.lean`, and genericity needs no transport; route A, recycling a label inside the induction, breaks at Case III's chain. Items B1 (`embedEdges` moved up, minimality through deficiencies), B2 (the pullbacks and Theorems 5.5 and 5.6), B3 (the cascade, the blueprint and `formalization.yaml`), then R, a read-only recon of dropping `hfresh` from `minimal_kdof_reduction` that returns to the PI (§1i.3) (`notes/Phase41d.md`) | 7–10: the arc's 6–9, the open and the close included, and R's record |
| **UNSTATED** | — (follows RELABEL, expected as 41e; its letter minted at its own open, §1i.2) | the claims no declaration states, the full list (§1h.1), with §4(a): twelve items sized and ordered by its open's recon (§2, *UNSTATED's open recon*), U1–U12; `def:dof-generic` needs its own recon and S3 a spike; only S3 touches carrier code (`case_II_placement_eq612`) | 15–21, the open and the close included (the report: 13–23) |

**Why the switch was one commit** (CARRIER): under the lint gate a field cannot be staged file by
file without a temporary twin structure, as an unused proof argument fails `unusedArguments`;
Phase 22l's lesson, API first and switch last (`notes/Phase22l.md` *Architectural choices*).

The program closes with the phase: ROADMAP's RECONCILE bullet compressed, and the ledger's last
`reported` entries given dispositions (`notes/Reconcile.md` §3).

## 4. Open questions

- **KT's nonparallel** (§1b.4): settled by §2's *KT's nonparallel recon* (route B, 41b's items
  4a–4c) and by the PI's decisions in §1c (route B; the d = 3 wrapper concludes `IsNonparallel`).
- **M1 and loops**: settled by the PI in advance (§1f.4): loops allowed, the upper bound's `hC`
  relaxed to non-loop links (a loop's constraint is vacuous, and a loop never crosses a partition).
  MULTIGRAPH's open recon found the cost one commit, 41c's item 1 (§2), so it did not go back to
  the PI. JJ 2010 Theorem 6.1 (EJC 31, p. 582) is a maximum-rank statement for 2-edge-coloured
  multigraphs; the row's "every generic realization" is the project's strengthening.
- **The generic panel theorems on one body** (§2, *Item 9's recon*): settled by the PI (§1e), the
  rank formula and the iff take `V(G).Nonempty`; landed with 41b's item 9a.
- **Dropping `hcard` from M1 and KT Proposition 2.3** (§2, *MULTIGRAPH's open recon*): the PI
  asked for a read-only recon of one transport that drops the bound from every main result carrying
  it (§1h.2), RELABEL's first item (§3). The recon (§2, *RELABEL's recon*) found route B, a
  transport at the boundary proved in a witness, at 6–9 commits; the PI took route B and opened
  RELABEL as 41d (§1i.1).
- **`minimal_kdof_reduction`'s `hfresh`** (KT Theorem 4.9's principle, not a main result; route B
  cannot reach it, §2): the PI asked for a recon of dropping it (§1i.3), 41d's item R, which sizes
  route A's combinatorial half (the deficiency chain under `e₀ ∉ E(G − v)`) and returns to the PI
  before any build.
- **Relaxing `rigidityMatrix_prop11`'s `hC` to the non-loop links**: in UNSTATED (§1h.2), its item
  U6 (§2, *UNSTATED's open recon*).
