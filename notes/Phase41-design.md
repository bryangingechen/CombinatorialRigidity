# Phase 41 — RECONCILE-FORMAL: design (cross-phase plan and recon)

**Status:** ✓ closed 2026-10-29 (opened 2026-10-24 with the PI), in five sub-phases, each with its
work log. **41a** (CARRIER, closed 2026-10-24, `notes/Phase41a.md`): the field `isLink_ends` is on
`PanelHingeFramework`, and no main result's statement changed. **41b** (RESTATE, closed
2026-10-25, `notes/Phase41b.md`): S1's and S2's main results restated on the linked carrier as the
PI decided at its open and during it (§1b–§1f): Theorems 5.5 and 5.6 conclude KT's nonparallel
panels for simple `G`; the molecular conjecture and the multigraph rows ask nondegenerate hinges
on `E(G)` only; the generic panel and body-hinge theorems hold at every generic realization of
every simple graph on one body or more, the panel rank formula a twentieth main result; and
`prop:rigidity-matrix-prop11` is KT Proposition 2.3 in conditional form. **41c** (MULTIGRAPH,
opened and closed 2026-10-28, §1g, `notes/Phase41c.md`): M1 holds for every multigraph, loops
allowed, and KT Proposition 2.3 as KT state it, at every generic hinge-point assignment. **41d**
(RELABEL, opened and closed 2026-10-29, §1h–§1i, `notes/Phase41d.md`): by route B, a transport at
the boundary, no main result bounds the edge labels. **41e** (UNSTATED, opened and closed
2026-10-29, §1j–§1k, `notes/Phase41e.md`): each claim of the full list (§1h.1) and §4(a) has a
declaration and a pin, with item R before U4, PAD before U10, and KT Proposition 2.3 and M1 at
KT's own genericity (M1K). §2's arcs are compressed to cited verdicts, and the PI's decisions
(§1–§1k) stand verbatim. The close closed the RECONCILE program (`notes/Reconcile.md`). **Next:**
nothing in this phase: the loop stopped for the PI's push, and ORIGAMI opens next, with the PI
(ROADMAP *Queued post-program phases*).

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
  states (UNSTATED, 41e; S22–S25, S31, S3, S16, S19, G5, `F-061`'s forest lemma), with §4(a),
  item R's build and the padding of the molecule's labels dropped (§1j).

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

## 1j. The PI's decisions at UNSTATED's open (2026-10-29)

The coordinator put four questions on one form, then a follow-up, from 41d's *Blockers*
(`notes/Phase41d.md`) and the run configuration. The PI's answers, verbatim (the question texts,
option labels and option descriptions are the coordinator's wording on the form; the answers are
the PI's selections; the bracketed paragraph is the coordinator's note):

> Q: "41d's item R: KT Theorem 4.9's reduction principle (minimal_kdof_reduction, not a main result, no callers) can drop its fresh-label hypothesis hfresh in one commit. A recon proved its whole chain in a witness under the weaker e₀ ∉ E(G − v), where the new edge reuses the label of an edge at v. If placed in 41e before U4 (S22, the reduction-sequence theorem), U4 assumes nothing of the labels, and 41e grows to 16–22 commits. Take it?"
> A: "Drop it, P at every label (Recommended)" (the option described as: "hsplit receives P at every label outside E(G − v): a strict strengthening. One commit in 41e, before U4.")

> Q: "hasGenericFullRankRealization_of_theorem_55_gen (the third pin of thm:theorem-55-6-rows; nothing calls it) still takes hfresh after 41d. Restated over the bound-free rows form, a three-line repackage, it would drop both hfresh and [DecidableEq β]. That is a free strengthening under your standing §1f.3 policy. Take it in 41e?"
> A: "Restate it in 41e (Recommended)" (the option described as: "A three-line repackage that drops hfresh and [DecidableEq β]. It rides along with an early 41e item; no new commit.")

> Q: "41d's close also reported three loose ends and recommended no action: (1) card_shadowLabel_lt is uncalled, and lem:molecule-graph-carrier still states 'more than 6(|V|−1) labels', which no result needs (dropping the padding would change that statement and U10's); (2) thm:theorem-55-6-rows has a \uses edge to thm:theorem-55-6-genuine with no Lean basis; (3) three bound-free forms are pinned but called by no main result. Should 41e act on any of them?"
> A: "Why did 41d recommend no action? Were these just out of scope at the time?"
> [The coordinator answered: mostly scope, as 41d's hygiene rule changed statements only as §1i and the arc said. (1) The summand `Fin (6(|V|−1)+1)` of `G.shadowGraph`'s labels existed only to meet the bound 41d removed, and KT's graph has no spare labels; dropping it changes `lem:molecule-graph-carrier`'s statement and the label type under the three molecule results, U10's included; the cost is small (one lemma deleted, about 8 type ascriptions inside proofs in `JacobsCounting.lean` and 2 sites in `Nonvacuity.lean`, one blueprint node), and U10 touches the same surface. (2) The edge predates 41d: the blueprint says the rows form uses Theorem 5.6, the Lean builds it from Theorem 5.5; a one-line blueprint fix. (3) Not a defect: the bound-free forms are pinned beside their main results on purpose. Then it re-asked (1) and (2):]
> Q: "Given that explanation: should 41e take either cheap tidy-up? (1) Drop G.shadowGraph's label padding: its type becomes Graph V (Sym2 V), card_shadowLabel_lt is deleted, and lem:molecule-graph-carrier loses 'more than 6(|V|−1) labels'. It is done before or with U10, which touches the same surface; about one commit or less. (2) Repoint thm:theorem-55-6-rows's \uses edge to what its Lean actually uses (Theorem 5.5), a one-line rider. The pinned uncalled forms (item 3) stay either way."
> A: "Drop the padding (with U10), Fix the \uses edge" (two options selected, described as: "Simplify the label type to Sym2 V, delete card_shadowLabel_lt, and restate lem:molecule-graph-carrier and U10 to match." and "A one-line blueprint rider on an early 41e commit.")

> Q: "How should the loop run for 41e (UNSTATED, the claims no declaration states, U1–U12, 15–22 commits)? Under 41d: no run cap, mechanical fixups (rescue §1) pre-authorized, Sonnet and Opus dispatchable, and stops between sub-phases and when the coordinator's context runs low. 41e is planned as Phase 41's last sub-phase, so its close would also close Phase 41 and the RECONCILE program, then stop for your push."
> A: "Same as 41d (Recommended)" (the option described as: "No run cap; mechanical fixups pre-authorized; Sonnet and Opus dispatchable. Stop when 41e closes (closing Phase 41) or when context runs low.")

What each answer settles:

1. **Item R is taken, in form (b)** (§2, *Item R's recon*). `Graph.minimal_kdof_reduction`
   (`Molecular/Induction/ForestSurgery/Reduction.lean`) drops `hfresh`, and its split case `hsplit`
   is given `P` at `G.splitOff v a b e₀` for every label `e₀ ∉ E(G − v)`, a strict strengthening;
   the source is `notes/reconcile-formal/ReductionWitness.lean`. It is one build commit in 41e,
   placed before U4, so that U4 (S22, KT Theorem 4.9 (i)) is stated without `hfresh`.
2. **The rows form is restated.**
   `PanelHingeFramework.hasGenericFullRankRealization_of_theorem_55_gen`, the third pin of
   `thm:theorem-55-6-rows`, is restated over the bound-free rows form, dropping `hfresh` and
   `[DecidableEq β]`, a free strengthening (§1f.3). It rides on an early 41e item, with no commit
   of its own.
3. **`G.shadowGraph`'s padding is dropped, with U10.** Its type becomes `Graph V (Sym2 V)`,
   `card_shadowLabel_lt` is deleted (the deletion gate), and `lem:molecule-graph-carrier` and U10
   are restated to match. U10's "its bound met by `card_shadowLabel_lt`" (§2, *UNSTATED's open
   recon*) goes entirely: since 41d's B3, U10 has no label bound to meet.
4. **The `\uses` edge is fixed.** `thm:theorem-55-6-rows`'s edge to `thm:theorem-55-6-genuine`,
   which its Lean does not back, is repointed to what its Lean uses, Theorem 5.5
   (`thm:theorem-55`), as a one-line rider on an early 41e item. The pinned forms that no main
   result calls (41d's third report) stay.
5. **UNSTATED is 41e, and the loop runs as in 41d**: no run cap, mechanical fixups (rescue §1)
   pre-authorized, Sonnet and Opus dispatchable. 41e is planned as Phase 41's last sub-phase, so
   the loop stops when 41e closes, which closes Phase 41 and the RECONCILE program, for the PI's
   push (§1i.4); and when the coordinator's context runs low.

**The placements** are the open's (recorded in `notes/Phase41e.md`, not the PI's): item R's build is
its own commit immediately before U4; the riders of answers 2 and 4 ride on U6, the earliest item
that edits both `Theorem55.lean`, where the rows form is (the three callers of
`rigidityMatrix_prop11`), and `panel-layer.tex`, the chapter of `thm:theorem-55-6-rows`, and a
mechanical one (U7 edits `Theorem55.lean` only if a `have` goes unused at its callers); the padding
drop is its own commit (PAD) immediately before U10, as it is mechanical across four Lean files
while U10 is a crux node with an uncompiled route.

## 1k. The PI's decision after U11's recon (2026-10-29)

The coordinator put §4's *KT Proposition 2.3 at KT's own genericity* to the PI on one form, after
U11's recon (§2, *U11's recon*) and before U11's build. The question text and option descriptions
are the coordinator's wording; the answer is the PI's selection:

> Q: "U11 will formalize def:dof-generic's genericity as IsMaxRankHingePoints: rank as large as any nondegenerate hinge-point realization, at every edge set. That is KT's own sense, and every assignment 'generic for row independence' satisfies it. The recon compiled KT Proposition 2.3 (rank formula ⇔ deficiency ⇔ matroid rank) at every such realization, which is stronger than prop:rigidity-matrix-prop11's current pin. Taking it repins that node to KT's statement exactly and moves formalization.yaml's Jackson–Jordán Thm 6.1/Cor 6.3 alignment row (not a main result): ~20 Lean lines, no extra commit if taken now, one if later. M1 (a main result) could follow the same way, ~1 extra commit (its rank formula is compiled, the iff is not). Should 41e take either?"
> A: "Prop 2.3 and M1" (the option described as: "Prop 2.3 in U11 as above, plus M1 (a main result) at KT's genericity in its own commit after U11: about one more commit.")

What it settles:

1. **KT Proposition 2.3 at KT's genericity rides on U11.** `prop:rigidity-matrix-prop11` is
   restated with a hinge-point assignment generic in `def:dof-generic`'s sense
   (`IsMaxRankHingePoints`), KT's statement exactly, and pinned first by the witness's
   `tfae_finrank_span_rigidityRows_ofHinge_deficiency_of_isMaxRankHingePoints`, transcribed;
   today's pin, at row-independence genericity, follows from it by the bridge and stays as the
   form the chain uses. `formalization.yaml`'s Jackson–Jordán Thm 6.1 / Cor 6.3 alignment row is
   re-read and restated with it. No commit of its own.
2. **M1 at KT's genericity, its own commit after U11** (41e's item M1K). M1, the main result
   `isInfinitesimallyRigidOn_ofHinge_isGenericHingePoints_iff_spanningTrees`, and its rank
   formula hold at every maximum-rank hinge-point assignment. The rank formula is U11's
   `finrank_span_rigidityRows_ofHinge_of_isMaxRankHingePoints`; the iff is new, about one commit.
   Its shape (a sibling that becomes the `main_results` row, the generic form derived from it by
   the bridge, or the main result restated in place, renamed) is the item's to settle, with the
   row, its description and its non-vacuity witnesses re-read and the axioms re-checked.

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

**UNSTATED's open recon** (2026-10-29; Claude Opus 5.5, design pass, at `3b9f766b`; landed as 41e's
items, and compressed at 41e's close to a cited verdict, the full arc in git up to `1ff52359`).
Evidence: `notes/reconcile-formal/UnstatedWitness.lean` (`lake lean`: no errors or warnings, its
seven `#print axioms` the three standard axioms; `#lint` on a copy: only `unusedArguments` at four
`Prop` targets, which carry the instances of the planned theorems), in `ReconUnstated`. It proved
S22, S24's rank form, S25 with `def:blockingWitness`, S19, §4(a) and S16's one new step, and stated
the other targets as `Prop`s that elaborate. Every node, pin and declaration was re-read at
`3b9f766b`; the checklist was transcribed at 41e's open into `notes/Phase41e.md` and re-read there
at `0a63c7ef`, after 41d. That checklist, with item R before U4, U4 without `hfresh`, the riders on
U6 and the padding dropped before U10 (§1j), records what landed, each declaration by name. The
items, in the recon's order (the isolated one-commit items, then the fragility zone's, then the
rebuild-heavy and crux ones, then the two that needed a recon or a spike): **U1** S25 with
`def:blockingWitness`, **U2** S24, **U3** S23, **U4** S22, **U5** S19, **U6** §4(a), **U7** S16,
**U8** `F-061`'s forest lemma, **U9** the Plücker expansion, **U10** S31, **U11** `def:dof-generic`
and **U12** S3, each one commit, U12 two with its spike. *Corrections to the plan:* G5's packing
move and `lem:forest-surgery-unsplit` were already settled (round 3's `F-087`, round 2's `F-091`),
so G5 was the other three; S19 touched no carrier code, its identity being arithmetic from KT Lemma
3.5; only S3 touched `case_II_placement_eq612`; `F-061`'s forest lemma backed no claim at HEAD and
landed with a new node; S31 needed no label bound. Two planned forms changed with the PI's answers
(§1j): U4 had carried `hfresh` (item R, below, dropped it), and U10's "its bound met by
`card_shadowLabel_lt`" went, as since 41d's B3 it had no bound to meet. Adopted under §1f.3 at
landing, the coordinator's calls: U7 without `[Finite α]` (`d04cbf9e`; the built framework needs
no finiteness of the bodies) and U10 without `[Nonempty V]` (`0a0817a0`; both sides hold at
`V = ∅`); U10's proof runs through the dictionary `molecular_finrank_motions_eq_square_ker`, as
`molecule_generic_rigid` and `molecule_rank_formula` pin corollaries of that node. Estimate 15–21
commits (the report's 13–23); with R, PAD and M1K, 41e planned 18–24.
  - **U11's recon** (41e's item *U11, recon*; 2026-10-29; Claude Opus 5.5, design pass, at
    `5b521137`). Evidence: `notes/reconcile-formal/DofGenericWitness.lean` (`lake lean`: no errors
    or warnings, its seven `#print axioms` the three standard axioms; `#lint` on a copy: no errors in
    9 declarations), in `ReconDofGeneric`; it superseded `UnstatedWitness.lean`'s G5 copy.
    **Verdict: the candidates are faithful in reading (a), with Q2's loop convention; one build
    commit, landed as U11 (`80d2a46f`).** KT's genericity (§2.4, p. 654, after JJ 2010 §6) is the
    largest rank of `R(G,p)` and of its edge-induced submatrices over the realizations of `G`.
    *Q1, the carrier.* (a) `ofHinge G q` over the hinge-point assignments whose hinges are
    nondegenerate, which up to the choice of the points are the realizations: the sources' reading.
    (b) Any supporting extensor admits frameworks that are no realization, and with zero allowed the
    welded maximum, as a degenerate hinge welds its bodies. (c) Panel-hinge frameworks share a
    hinge at parallel edges. *Q2, loops.* A loop's rows are zero whatever its hinge
    (`span_rigidityRows_eq_of_eq_off_loops`), so nondegeneracy is asked only at the links between
    distinct bodies, the project's convention since §1f.4 and §1h.2; a degenerate hinge at a loop
    then counts as generic, where KT have no loops. *Q3.* `dof` (in `ℤ`, with `V = V(G)`) and
    `IsMaxRankHingePoints` are faithful. The cheapest witness is a graph with no link between
    distinct bodies, the single loop; satisfiable at the single and double edge, the triangle and
    the double edge with a loop; not vacuous (`not_isMaxRankHingePoints_banana_of_eq`); every
    assignment generic for row independence qualifies, loops allowed
    (`isMaxRankHingePoints_of_isGenericHingePoints`). *Q4, KT Proposition 2.3.* It holds at every
    maximum-rank realization (`tfae_finrank_span_rigidityRows_ofHinge_deficiency_of_isMaxRankHingePoints`,
    compiled): a generic `q₀` has the formula, a maximum-rank `q` has at least its rank, and the
    deficiency bound caps it. A strengthening of the pin, so for the PI (§4), who took it with M1
    (§1k).
  - **U12's spike** (41e's item *U12, spike*; 2026-10-29; Claude Opus 5.5, at `9c67712f`).
    Evidence: `notes/reconcile-formal/CaseIIPlacementWitness.lean` (`lake lean`: no errors or
    warnings, its three `#print axioms` the three standard axioms; `#lint` on a copy: no errors in 3
    declarations), in `ReconCaseIIPlacement`. **Verdict: the route composes with no `sorry`, and the
    node as stated is what the lemma carries; landed as planned as U12 (`90dc64a4`).** The count
    `case_II_placement_rank`: a realization of `G_v^{ab}` with nondegenerate hinges and rank at
    least `N`, the label of `ab` outside `E(G − v)` and `t ≠ 0` give `(G, q₀)`, with
    `q₀(v) = q(a) + t q(b)`, nondegenerate hinges and rank at least `N + D − 1`. The node's form
    `case_II_placement` takes it at a realization rigid on `V(G_v^{ab})`, and
    `case_II_realization_all_k` calls it at `t = 1`, its statement unchanged and its proof from
    about 710 lines to 290. The rows of `G_v` enter through the row space, so the route uses neither
    `exists_independent_panelRow_transport` (`lem:case-II-placement-old-rows`, uncalled since and
    kept pinned at the close's review, `notes/Phase41e.md` *Decisions made*) nor
    `_subfamily_of_rigidOn_linking`. `case_II_placement_eq612`, dead and unmeetable in Cases II and
    III, was deleted under the deletion gate.

**RELABEL's recon** (2026-10-29; Claude Opus 5.5, design pass, at `e51acb76`; landed as 41d's
B1–B3, and compressed at 41d's close to a cited verdict, the full arc in git up to `8ea9f2b1`).
Evidence: `notes/reconcile-formal/RelabelWitness.lean` (`lake lean`: no errors or warnings, its
eight `#print axioms` the three standard axioms; `#lint` on a copy: no errors in 25 declarations),
which proved every composition of route B with no `sorry`, in `Recon41Relabel` namespaces; B1–B3
transcribed it (`notes/Phase41d.md`). Six of the 20 main results carried the bound: KT Theorem
5.5's supply `hfresh` (`theorem_55_minimalKDof_gen`), and `hcard : D(|α| − 1) < |β|` on KT
Theorem 5.6 (`rankHypothesis_of_theorem_55_gen`), both molecular conjectures, the generic panel
rank formula and M1. 23 declarations lost one hypothesis each; the induction's internal forms keep
`hfresh` (`theorem_55_minimalKDof_k_all_k`, `hasGenericFullRankRealization_of_theorem_55_gen`,
`theorem_55_6_multigraph_of_two_le`, Cases II and III, the chain extraction). **Route B, adopted**
(§1i.1): each main result applies its supply-taking form at `β ⊕ Fin (D(|α| − 1) + 1)` along `inl`,
where `freshEdgeSupply_of_card_lt` gives the supply, and pulls the framework back, as the pencil
realization theorem already relabelled where it calls KT Theorem 5.6 for Jackson and Jordán's
equality (`Graph.embedEdges`, then in `Bridge.lean`). The relabelling keeps the bodies, simplicity
and the deficiency; minimality transports through deficiencies (T5, the only new mathematics, by
KT eq. (2.4) and `matroidMG_restrict_mulTilde`); the pullbacks `bhComap` and `phComap` keep the
rows, the motions and the normals (T1, T2); and genericity needs no transport, the generic theorems
and KT Proposition 2.3 compiling with the binder deleted. **Route A**, recycling a label inside the
induction, breaks at Case III's chain (`ChainData.e₀_fresh`, one fresh label for every interior
split-off, which `shiftEdgePerm` and the selector `ends₀` of
`chainData_dispatch_interior_of_discriminator` need): a redesign of `CaseIII/` in the fragility
zone. **Not covered:** `minimal_kdof_reduction` (KT Theorem 4.9's principle, and UNSTATED's U4
after it), whose split step names a fresh label for a predicate on `Graph α β`, so no pullback
applies; dropping its `hfresh` would be route A's combinatorial half, the deficiency chain under
`e₀ ∉ E(G − v)` (*Item R's recon*, below). `G.shadowGraph`'s padding is unneeded and stays, as
dropping it would move `lem:molecule-graph-carrier` and U10's statement; since B3,
`exists_molecular_rankHypothesis_generalPosition` takes no bound, so U10 (*UNSTATED's open recon*,
"its bound met by `card_shadowLabel_lt`") has none to meet, and `card_shadowLabel_lt` is uncalled.
Estimate 6–9 commits, the open and the close included; landed in 7 (the open `d9707048`, B1
`c6bc7762` and its corrective `7287795e`, B2 `9d6a43d9`, B3 `953367f0`, R `8ea9f2b1`, the close).
Its *For the PI* went to the PI, whose answers are §1i.

**Item R's recon** (41d's item R; 2026-10-29; Claude Opus 5.5, read-only, at `953367f0`; the PI's
§1i.3; landed as 41e's item R, `836bb645`, and compressed at 41e's close to a cited verdict, the
full arc in git up to `1ff52359`). Evidence: `notes/reconcile-formal/ReductionWitness.lean` (`lake
lean`: no errors or warnings, its six `#print axioms` the three standard axioms; `#lint` on a copy:
no errors in 15 declarations), in `Graph.Recon41Reduction`, a primed name being the landed
declaration under `e₀ ∉ E(G − v)`. **Verdict: route A's combinatorial half holds; one commit.** The
principle `minimal_kdof_reduction` had no caller and called one lemma that takes the label,
`splitOff_isMinimalKDof` (KT Lemma 4.8(i)). The formal `G.splitOff v a b e₀` deletes every edge
labelled `e₀` and adds `ab` as `e₀`, so it is `G_v^{ab}` exactly when `e₀ ∉ E(G − v)`
(`fmlnote:graph-operations`); as `eₐ` and `e_b` are the only edges at `v`, the label `eₐ` is always
admissible (KT p. 660: `G_v^{ab}` is isomorphic to `G` with `vb` contracted, which keeps `eₐ` on
`ab`).
- *Sub-question 1, each use of `e₀ ∉ E(G)`, read from the bodies.* `removeVertex_le_splitOff`,
  `edgeSet_mulTilde_splitOff_diff_fiber` and `circuit_splitOff_meets_fiber` need only that a link
  avoiding `v` is not `e₀`: **GO**, one line each. The upper bound `splitOff_deficiency_le` of
  `dof_tracking` needs only that no crossing edge other than `e_b` is `e₀`: **GO**, about 20 lines;
  its lower bound asks nothing of `e₀`. `splitOff_isMinimalKDof` passes the hypothesis on: **GO**,
  and `eₐ ≠ e_b` is then unused. `splitOff_isMinimalKDof_of_pos` (KT Lemma 4.8(ii), Case II's):
  **NO-GO** as a local change, and not needed; its forest surgery uses the full hypothesis, route
  A's algebraic half, which §1i left out.
- *Sub-question 2, `hsplit` without `hfresh`.* **Form (b)**,
  `(∀ e₀, e₀ ∉ E(G − v) → P (G.splitOff v a b e₀)) → P G`, gives `P` at every formal `G_v^{ab}` and
  implies the landed principle (`minimal_kdof_reduction_of'`), a strict strengthening:
  recommended. **Form (a)**, `P` at one admissible label, is not a strengthening. Faithful: KT state
  Theorem 4.9 as the sequence (p. 666), and the blueprint's clause (b) names `G_v^{ab}` with no
  label, so `thm:minimal-kdof-reduction`'s statement stays.
- *Sub-question 3, U4.* It drops `hfresh`, its split step asking `e₀ ∉ E(G − v)`; under the landed
  principle a graph that uses every label has no split step, which is why U4 carried `hfresh`.
- *Not recommended:* a relabelling inside the step (at `Option β`), which reaches the principle with
  no statement change, about 120–150 uncompiled lines; route B's pullback cannot reach it, as `P` is
  a predicate on `Graph α β`.
- *Statements changed* (route A, form (b)): `minimal_kdof_reduction`, `splitOff_isMinimalKDof`,
  `circuit_splitOff_meets_fiber` and `splitOff_deficiency_le`, all strengthenings, with a helper
  (`notMem_edgeSet_removeVertex`) and weaker forms of `removeVertex_le_splitOff` and
  `edgeSet_mulTilde_splitOff_diff_fiber`, whose landed forms keep their callers; no file of
  `AlgebraicInduction/` edited; four blueprint nodes. Estimate 1 commit, before U4.
- *For the PI.* Drop `hfresh` (recommended), with `hsplit` given `P` at every admissible label
  (recommended, a strengthening) or at one (a weaker theorem, at the same cost); or keep it (no
  cost, U4 as planned). **Answered** (§1j.1): dropped, `hsplit` given `P` at every admissible label,
  in 41e before U4.

## 3. Sub-phases, by code

| Code | Letter | Contents | Commits |
|---|---|---|---|
| **CARRIER** | 41a (closed 2026-10-24) | done: `reaimSub` retired; the link predicate, its lemmas and the fill-in tactic; the four R statements; the spike; the switch (the field, 123 declarations in 27 files) and the footprint's docstrings; `withGraph` restricted; `reaim` deleted with `hC` on links; the two genuine forms merged (`notes/Phase41a.md`) | 9, besides the build-time detour P1–P5 |
| **RESTATE** | 41b (closed 2026-10-25) | done: `HasGenericFullRankRealization`'s link conjunct and `F-324`'s derivable `hD`s dropped; `IsNonparallel`, and Theorems 5.5 and 5.6 with their `d = 3` instances concluding it for simple `G` (route B, §1c); `molecular_conjecture` on one body or more, hinges on `E(G)`, nonparallel panels (§1d); the multigraph rows and `IsHingeCoplanar` on `E(G)`; `cor:theorem-55-d3-spanning` from `theorem_55_d3`; S1's panel and body-hinge theorems at every generic realization on `G` under `hcard`, one body or more (§1e, §1f.3); G6's row, the twentieth main result; witnesses at the single edge and the triangle; S18 as KT Proposition 2.3, conditional (§1f.1); the scope and degenerate-hinge sentences; the link conjuncts the field makes redundant (`notes/Phase41b.md`) | 23, the open and the close included (planned 13–16) |
| **MULTIGRAPH** | 41c (closed 2026-10-28) | done: the upper bound asked at the non-loop links (§1f.4); M1, the generic body-hinge theorem (JJ 2010 Theorem 6.1) for every spanning multigraph, loops allowed, from the multigraph Theorem 5.6, with witnesses at the double edge and the double edge with a loop; KT Proposition 2.3 as KT state it, at every generic hinge-point assignment, pinned by `prop:rigidity-matrix-prop11`, its conditional form under `prop:rank-formula-of-motion-bound` (§1f.1) (`notes/Phase41c.md`) | 6, the open, the re-read and the close included (planned 3–5), besides three verification fixups |
| **RELABEL** | 41d (opened and closed 2026-10-29 with the PI, §1i) | done: the bound on the edge labels (`hcard`, `hfresh`) dropped from the six main results that carried it (§1h.2), by route B, a transport at the boundary with the induction untouched (§1i.1; §2's *RELABEL's recon*): `embedEdges` moved up with minimality through deficiencies (B1), the pullbacks and KT Theorems 5.5 and 5.6 without the bound (B2), the cascade, the blueprint and `formalization.yaml` (B3); and R, a read-only recon of dropping `hfresh` from `minimal_kdof_reduction` (§1i.3; §2's *Item R's recon*: route A's combinatorial half, proved in a witness, 1 commit, for the PI) (`notes/Phase41d.md`) | 7, the open, a corrective and the close included (planned 7–10) |
| **UNSTATED** | 41e (opened and closed 2026-10-29 with the PI, §1j; Phase 41's last sub-phase) | done: the claims no declaration states, the full list (§1h.1) with §4(a), as U1–U12, sized and ordered by its open's recon (§2, *UNSTATED's open recon*): S25 and `def:blockingWitness` (U1), S24 (U2), S23 (U3), S22 (U4), S19 (U5), `rigidityMatrix_prop11`'s `hC` between distinct bodies (U6), S16 (U7), `F-061`'s forest lemma (U8), the Plücker expansion (U9), S31 (U10), `def:dof-generic` after its recon (U11) and S3 after its spike (U12, `case_II_placement_eq612` deleted); item R, KT Theorem 4.9's principle without `hfresh`, before U4 (§1j.1); the rows form without `hfresh` and `thm:theorem-55-6-rows`'s `\uses` edge, on U6 (§1j.2, §1j.4); `G.shadowGraph`'s padding dropped before U10, as PAD (§1j.3); KT Proposition 2.3 on U11 and M1 as M1K, at KT's own genericity (§1k) (`notes/Phase41e.md`) | 30, the open and the three-part close included: 21 within the plan's 18–24, plus the PI's §1k record and 8 verification fixups |

**Why the switch was one commit** (CARRIER): under the lint gate a field cannot be staged file by
file without a temporary twin structure, as an unused proof argument fails `unusedArguments`;
Phase 22l's lesson, API first and switch last (`notes/Phase22l.md` *Architectural choices*).

The program closed with the phase, on 2026-10-29: ROADMAP's RECONCILE bullet compressed, and every
ledger entry `done` or `left`, none `reported` (`notes/Reconcile.md` §3).

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
  RELABEL as 41d (§1i.1), which dropped the bound from all six (B1–B3).
- **`minimal_kdof_reduction`'s `hfresh`** (KT Theorem 4.9's principle, not a main result; route B
  cannot reach it, §2): the PI asked for a recon of dropping it (§1i.3), 41d's item R. Its verdict
  (§2, *Item R's recon*): route A's combinatorial half holds, proved in a witness; one commit, best
  placed in UNSTATED before U4, with `hsplit` given `P` at every label outside `E(G − v)`, a strict
  strengthening. **Answered by the PI** (§1j.1): taken in that form, as 41e's item R before U4.
- **`hasGenericFullRankRealization_of_theorem_55_gen`'s `hfresh`** (the third pin of
  `thm:theorem-55-6-rows`, internal by the RELABEL arc's count, and uncalled): B2 left it;
  restated over the bound-free rows form, a three-line repackage, it drops `hfresh` and
  `[DecidableEq β]`, a free strengthening under §1f.3. **Answered by the PI** (§1j.2): restated in
  41e, riding on U6. Of the close's reports (`notes/Phase41d.md` *Blockers*), the padding is
  dropped before U10 (§1j.3) and `thm:theorem-55-6-rows`'s `\uses` edge is fixed on U6 (§1j.4);
  the pinned forms no main result calls stay.
- **Relaxing `rigidityMatrix_prop11`'s `hC` to the non-loop links**: in UNSTATED (§1h.2), 41e's
  item U6 (§2, *UNSTATED's open recon*).
- **KT Proposition 2.3 at KT's own genericity** (§2, *U11's recon*; for the PI, not blocking
  U11). After U11, `def:dof-generic`'s genericity is formalized (`IsMaxRankHingePoints`), and every
  generic hinge-point assignment has it. The witness proves KT Proposition 2.3, the three-way
  equivalence, at every such realization, a strengthening of today's pin of
  `prop:rigidity-matrix-prop11`. Taking it repins that node (KT's statement exactly) and moves
  `formalization.yaml`'s alignment row for Jackson–Jordán Theorem 6.1 / Corollary 6.3, not one of
  the 20 main results: about 20 Lean lines, no extra commit if answered before U11 builds, one
  after. M1 (a main result) and its rank formula could follow the same way: the rank formula is
  compiled, the iff is not; about one commit. Neither is needed for U11, which adds declarations
  only. **Answered by the PI** (§1k): both, Proposition 2.3 riding on U11 and M1 as 41e's item
  M1K after it.
