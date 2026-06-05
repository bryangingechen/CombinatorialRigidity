# Phase 22a — Case I realization (work log)

**Status:** in progress (opened as Phase 22 on 2026-06-04; split into sub-phase
22a on 2026-06-04).

Stratum 5 of the molecular-conjecture program, continued: **Track A only** — the
Theorem-5.5 *Case I* realization producer that the Phase-21b genericity device
feeds. **Target:** `lem:case-I-realization` (the N6 composer) green, discharging
`theorem_55.hcontract`'s Case-I branch.

The over-broad Phase 22 (which bundled Case I, Case III at `d=3`, and the
`prop:rigidity-matrix-prop11` + `thm:theorem-55` assembly) was split using
sub-lettering on 2026-06-04: **22a** is this focused Case-I sub-phase; the
remaining territory (Case III at `d=3` + the `d=3` assembly) is parked as
**22b+** (a single planning placeholder, expected to split into multiple
sub-phases once its shape is clearer; the cut is deferred until 22a closes). The
integer phase numbers 23–26 stay stable. See *Deferred to 22b+ (Case III +
assembly)* below.

Phase 21b closed the genericity-free reductions (the accounting iffs, the
`V(G)`-relative count bridges, the device, the reusable row/glue infra) and
re-scoped the realization *producers* here after a math-first feasibility pass.
The KT math for the Case-I producer is worked out in `notes/Phase21b.md`
*Finding A/B* + *Hand-off to Phases 22–23* — **22a formalizes it, it does not
re-derive it.**

Forward-mode / **structural-edit** discipline (`blueprint/CLAUDE.md`): 22a
does *not* open a new blueprint chapter. Its producers (N4/N5/N6) **extend the
existing `algebraic-induction.tex`** — their nodes are already stubbed red there.
Program plan / reuse map / citations: `notes/MolecularConjecture.md` *Phase 22*.
Lean lands in `Molecular/{Induction,AlgebraicInduction}.lean`. Cross-cutting
rationale: `DESIGN.md` *Realization motive must be V(G)-relative*,
*Constructibility recon before a producer build*, *Phase Case-naming vs. KT's
k-bookkeeping*.

## Current state

**All Track-A *producer* bricks are GREEN, G3a (the Claim-6.4 collapse transport) is GREEN-MODULO,
G3b (the cover/shared-body/selector geometry) is GREEN, and G3c-i (the body-set-relative rank
polynomial + N7b-0) is GREEN** (N4 reduction infra; the Case-I producer bricks; N6-G1 generic
producer; N6-G2-G2a `theorem_55_generic`; G2b `map`/`collapseTo` simplicity; G2c generic coupling
producer `hasGenericFullRankRealization_of_couple_ofNormals`; **G3a `rigidContract_rigidity_transport`,
green-modulo the explicit Claim-6.4 hypothesis `htransport`; G3b
`couple_geometry_of_isProperRigidSubgraph`; G3c-i — the four body-set producer bricks
`finrank_pinnedMotionsOn_le` / `finrank_infinitesimalMotions_le_of_isInfinitesimallyRigidOn` /
`exists_independent_panelRow_subfamily_of_rigidOn_linking_set` /
`exists_rankPolynomial_of_rigidOn_linking_set`**). **The remaining red work is N6-G3-G3c's G3c-ii/iii.
A 2026-06-05 re-recon (design doc §1.8) had found G3c is NOT pure green-brick assembly** — the §1.7
"buildable G3c" framing was blind to a **body-set mismatch**: the G2c coupling (and the rank-polynomial
witness-transfer it calls) hardcode each leg rigid on its **full** `V(GH)`/`V(Gc)`, but the contraction
leg `Gc = G.deleteEdges E(H)` has `V(Gc) = V(G)` and is rigid *only* on `(V(G)∖V(H)) ∪ {r}` (G3a's
output set; the surviving edges leave the interior `V(H)∖{r}` free). G3c-i lifted the *producer* bricks
(rank polynomial + N7b-0) off the hardcoded `V(·)` to an arbitrary nonempty body set `s` / count
`D(|s|−1)`, via the body-set N1 **upper bound** `finrank_pinnedMotionsOn_le` (the N1 *equality*
`= D·|sᶜ|` is **false** for `s ⊊ V(G)`; the upper bound is all the producer needs — `dim Z ≤ D·(|sᶜ|+1)`
⟹ `≥ D(|s|−1)` rows). **G3c-i surfaced that the body-set N3 *consumer* is the genuinely-stuck half:**
re-deriving a leg rigid *on `s`* from its row count does NOT close from the count alone for a general
`s` (N3-on-`V(G)` needs the N1 *equality*, false off `V(G)`); G3c-ii must either carry the leg-specific
"complement isolated" fact `finrank (pinnedMotionsOn s) = D·|sᶜ|` as an honest `h…` (green-modulo) or
consume each leg's rigidity directly into the base glue without a rank-polynomial round-trip. KT's
eq. (6.3) splice respects exactly the body-set split (`R(G,p; E∖E′, V∖V′)`, surviving *bodies*
`V∖V′`); the honest base glue `isInfinitesimallyRigidOn_of_splice` already supports arbitrary
`sH`/`sc`. **G3c is cut into G3c-i (GREEN), G3c-ii (body-set coupling — re-recon at open per the N3
finding), G3c-iii (assembly + flip, `buildable`); G3c-ii is the next build.**
The §1.7 re-recon settled the binding `Gc ≤ G` obstruction: the
splice's contraction leg is **`G.deleteEdges E(H)`** (`≤ G`, KT eq. 6.3's `R(G,p; E∖E′, V∖V′)`),
**not** the relabelled `G.rigidContract H r` — and the contraction IH's rigidity is *transported
across the collapse map* to that `G ＼ E(H)` leg by **KT's Claim 6.4** (eq. 6.9). The G3a math-first
pass found this transport is irreducibly research-shaped (the collapse redirects surviving-edge
endpoints, so it cannot be reduced to the green linking-edge brick — recovering the un-collapsed-
endpoint rank *is* Claim 6.4); per the design-doc escalation authorization, G3a carries Claim 6.4 as
the narrow explicit hypothesis `htransport` and does the surrounding plumbing, so it is green-modulo
that one hypothesis (axiom-clean, no `sorry`). **G3b is GREEN** (the cover/shared-body/selector
geometry adapter `couple_geometry_of_isProperRigidSubgraph` — both legs `H` and `G ＼ E(H)` `≤ G`,
share the body `r`, cover `G`, are nonempty; pure graph combinatorics off `IsProperRigidSubgraph`).
The simple Case-I coupling (`hasFullRankRealization_of_couple_ofNormals`) is a complete
assembly of green bricks, and the `ends`-swap leg-transport brick that feeds the IH into it is green. The
generic-motive recon settled the IH-shape gap as a **hybrid** — Route 2 (make the simple-case *producer*
conclude GP) and Route 1 (make the *IH* generic) are two halves, not alternatives, because the composer's
adapter needs each leg in `HasGenericFullRankRealization` form while `minimal_kdof_reduction` threads only
the bare motive. **N6-G1 is GREEN** (the spike found the recon's device-GP re-expose route was a false
premise; see *Decisions* → *N6-G1 spike*). **G2a is GREEN** (2026-06-04): `theorem_55_generic` re-runs
`Graph.minimal_kdof_reduction` at the conditioned motive `Pc G := (G.Simple → GP G) ∧ bare G`. The flagged
`hsplit`-vs-`splitOff` routing sub-question is **settled**: the `Simple → GP` conjunct of the
splitting-off branch *is* KT Case III (Track B, out of 22a scope, entirely red), so the binding
obstruction is one of *scope*, not routing — G2a carries that branch's GP step as an explicit hypothesis
`hsplitGP` (Phase-21b green-modulo `h…` idiom; design doc §1.6 escalation (ii)), and likewise carries the
simple-base `hbaseGP` and the simple Case-I `hcontractGP` (the latter fed the *full conditioned IH*, the
shape G2c/N6-G3 consume). **Remaining:** N6-G3-G3c (G3a green-modulo, G3b green). No `\leanok` flip yet
(`lem:case-I-realization` stays red until G3c discharges `hcontractGP`/`hcontract` and G3a's
`htransport` is itself supplied — KT Claim 6.4 / `lem:case-III`); axiom-clean; no `sorry`.

**Green-brick inventory (resume points; full detail in *Lemma checklist* / *Decisions*).**
- **N4** `rigidContract_isMinimalKDof` — graph↔matroid contraction-minimality bridge (`\leanok`).
  Chain: N4a (`mulTilde_preconnected_of_isKDof_zero`) → N4b (`cycleMatroid_mulTilde_rigidContract`) →
  N4c (`matroidMG_rigidContract_eq_contract`, via the abstract crux
  `Matroid.Union_pow_contract_eq_contract_of_rk_saturated`) → reconciliation (+ `edgeSet_rigidContract`,
  `rigidContract_vertexSet_ncard`).
- **N5 splice / seed scaffolding** — `hasFullRankRealization_of_splice` / `…_ofNormals` / `…_ofParam`,
  the single-leg bridge `hasFullRankRealization_of_rigidOn_seed`, the forest-packing
  `Graph.IsKDof.exists_isBase_isForestPacking`, the IH-locus repackaging
  `exists_rigidOn_ofNormals_of_hasFullRankRealization`.
- **N5 rank polynomial** — producer `exists_rankPolynomial_of_rigidOn` + consumer
  `isInfinitesimallyRigidOn_ofNormals_of_rankPolynomial_ne_zero` (built on the new constructive mirror
  `exists_polynomial_ne_zero_of_linearIndependent_at`), and the *leg-restricted* four-brick chain
  (`span_panelRow_linking_eq_rigidityRows` → `…_subfamily_of_rigidOn_linking` →
  `exists_rankPolynomial_of_rigidOn_linking` → `…_rankPolynomial_ne_zero_linking`) that applies to a
  proper-subgraph leg.
- **N6a** non-simple Case-I producer `hasFullRankRealization_of_splice_of_supportExtensor` (+ leg-native
  form) — splice on *transversal hinges* `hsupp`, not general position; bare-motive.
- **Two-motive split** — `HasGenericFullRankRealization` + forgetful map `hasFullRankRealization_of_generic`.
- **(G2)** general-position factor `exists_generalPosition_polynomial` (+ helpers
  `pair_linearIndependent_of_leading_minor_ne_zero`, `pairLeadingMinorPoly`).
- **N6b/N6c** simple Case-I coupling `hasFullRankRealization_of_couple_ofNormals` (the full assembly,
  bare motive) + the G2c *generic* sibling `hasGenericFullRankRealization_of_couple_ofNormals` (same
  per-leg inputs, concludes the *strengthened* `HasGenericFullRankRealization` motive by routing the
  shared GP seed through N6-G1 instead of the device-routing bare splice).
- **N6 leg-transport** `hasGenericRealization_transport_ends` — the `ends`-swap step feeding the IH into
  the coupling (built on the swap brick `infinitesimalMotions_ofNormals_eq_of_ends_swap`).
- **N6-G1** (Route 2) generic *producer* `hasGenericFullRankRealization_of_splice_ofNormals` — concludes
  the strengthened motive `HasGenericFullRankRealization k G` from a GP seed `q₀` with both legs rigid at
  it. Realizes at `q₀` *itself* (bypassing the genericity device, whose output is NOT GP — spike finding),
  so rigidity comes from the genericity-free splice glue `isInfinitesimallyRigidOn_of_splice` and GP from
  the hypothesis. One commit (not the recon's expected 2 — the device-GP re-expose route was a false
  premise).
- **N6-G2-G2a** (Route 1, skeleton) conditioned-motive reduction `theorem_55_generic` — the generic
  sibling of `theorem_55`: `Graph.minimal_kdof_reduction` at `Pc G := (G.Simple → GP G) ∧ bare G`.
  Discharges each branch's bare conjunct from the `theorem_55`-shaped hypotheses (`hbase`/`hsplit`/
  `hcontract`) and each branch's `Simple → GP` conjunct from a carried hypothesis: `hbaseGP` (simple
  two-vertex base), `hsplitGP` (= KT Case III / Track B, out of 22a scope, carried), `hcontractGP` (=
  simple Case I, *fed the full conditioned IH* `∀ G', … → Pc G'`, the shape G2c/N6-G3 consume). Pure
  structural composition (anonymous-constructor projections), axiom-clean.
- **N6-G2-G2b** (Route 1, the combinatorial kernel) `map`/`collapseTo` simplicity — `rigidContract_simple`
  (`(G.rigidContract H r).Simple` from graph-side hypotheses on `G ＼ E(H)` under `collapseTo`) built on
  the abstract kernel `map_simple` (`(f ''ᴳ G).Simple` from no-self-collapse `hloop` + no-pair-collapse
  `hpar`). The fork has *no* `map`-simplicity API — `map` is the one op that breaks `Simple` (it can make
  loops and parallel edges), which is exactly why KT Case I trifurcates: `G/E′` simple is a *case
  hypothesis* (Lemma 6.3), its failure routed to Lemma 6.5's vertex-removal. `map_simple` is the faithful
  positive statement of that hypothesis; both lemmas in `Induction.lean`, axiom-clean.
- **N6-G3-G3a** (the Claim-6.4 collapse transport, **green-modulo**) `PanelHingeFramework.rigidContract_rigidity_transport`
  — from the contraction IH `HasGenericFullRankRealization (G.rigidContract H r)`, produce a seed `q_c`
  + rigidity of `(ofNormals (G.deleteEdges E(H)) ends q_c)` on `(V(G)∖V(H)) ∪ {r}` (the `≤ G` surviving-
  edge leg the G2c coupling consumes). The transport across the collapse map *is* KT Claim 6.4 (eq. 6.9),
  irreducibly research-shaped (the collapse redirects surviving-edge endpoints, so the green linking-edge
  brick does not apply); carried as the narrow explicit hypothesis `htransport` (Phase-21b green-modulo
  `h…` idiom). The brick is the surrounding plumbing only — axiom-clean, no `sorry`.
- **N6-G3-G3b** (cover/shared-body/selector geometry, **GREEN**)
  `PanelHingeFramework.couple_geometry_of_isProperRigidSubgraph` — from `H.IsProperRigidSubgraph G n` +
  a chosen representative `r ∈ V(H)`, the seven geometric inputs the G2c coupling consumes for legs
  `GH := H`, `Gc := G.deleteEdges E(H)`, `c := r`: `H ≤ G`, `G ＼ E(H) ≤ G`, `r ∈ V(H)`,
  `r ∈ V(G ＼ E(H))`, the cover `V(G) ⊆ V(H) ∪ V(G ＼ E(H))`, and both legs nonempty. Pure graph
  combinatorics (`vertexSet_deleteEdges` reads `V(G ＼ E(H)) = V(G)`, so `r ∈ V(G ＼ E(H))` and the
  cover are trivial); axiom-clean.
- **N6-G3-G3c-i** (body-set-relative producer bricks, **GREEN**, all in `AlgebraicInduction.lean`) —
  the four producer bricks lifted from `V(G)`/count `D(|V(G)|−1)` to an arbitrary nonempty body set
  `s`/count `D(|s|−1)`: (1) body-set N1 **upper bound** `finrank_pinnedMotionsOn_le`
  (`finrank (pinnedMotionsOn s) ≤ D·|sᶜ|`, via `pinnedMotionsOn_le_iInf_ker_proj` + the generic-`s`
  `finrank_iInf_ker_proj_eq`); (2) the helper `finrank_infinitesimalMotions_le_of_isInfinitesimallyRigidOn`
  (`dim Z ≤ D·(|sᶜ|+1)`); (3) body-set N7b-0 `exists_independent_panelRow_subfamily_of_rigidOn_linking_set`
  (`≥ D(|s|−1)` independent linking panel rows); (4) body-set rank polynomial
  `exists_rankPolynomial_of_rigidOn_linking_set`. The N1 *equality* `= D·|sᶜ|` is **false** for
  `s ⊊ V(G)` (interior bodies of `V(G)∖s` carry constraints) — the producer needs only the upper bound.

## Architectural choices made up front

- **Track A is its own sub-phase (22a).** Track A (Case I producer, full-rank,
  KT §6.2) is the tractable entry point and independent of Case III; it is what
  22a scopes. Track B (Case II/III reducible-vertex producer at `d=3`, KT §6.3 +
  §6.4.1) is the crux (Lemma 6.10, ~12 pages, the single largest proof in KT) and
  is deferred to **22b+** along with the `d=3` assembly — see *Deferred to 22b+
  (Case III + assembly)* below and `notes/MolecularConjecture.md` *Phase 22* for
  the node-by-node plan.
- **The motive is `V(G)`-relative** (`DESIGN.md` *Realization motive must be
  V(G)-relative*; carried from Phase 21b). `HasFullRankRealization` is the
  `V(G)`-relative rank `D(|V(G)|−1)`; the absolute null-space form is
  unsatisfiable for non-spanning inductive subgraphs.

## Lemma checklist

**Track A — Case I producer (full-rank, KT §6.2). This is the 22a scope.**
- [x] **N4** `lem:rigidContract-isMinimalKDof` — graph↔matroid contraction-
  minimality bridge: `G.IsMinimalKDof n 0 ∧ H proper rigid ∧ r ∈ V(H) ⟹ (G.rigidContract H
  r).IsMinimalKDof n 0`. **GREEN** (`rigidContract_isMinimalKDof`, axiom-clean, `\leanok`). The
  reconciliation assembles the green `contraction_isMinimalKDof` through N4c into the graph-level
  minimality, via `edgeSet_rigidContract` (`E(G/E(H)) = E(G)\E(H)`) + `rigidContract_vertexSet_ncard`
  (exact collapse count `|V(G/E(H))| = (|V(G)|−|V(H)|)+1`) + the def=corank bridge. Sub-bricks:
  - [x] **N4a** `mulTilde_preconnected_of_isKDof_zero` (`Deficiency.lean`) — rigid subgraph's multiplied
    graph is connected, licensing the `collapseTo r V(H)` vertex-collapse.
  - [x] **N4b** `cycleMatroid_mulTilde_rigidContract` (`Induction.lean`) — cycleMatroid under the
    vertex-collapse `map` (Whitney contraction). `cycleMatroid_contract` *does* apply at the `mulTilde`
    level (N4a ⟹ `IsRepFun`); needs `r ∈ V(H)`.
  - [x] **N4c** `matroidMG_rigidContract_eq_contract` — union-level independence bridge
    (`M((G/E(H))̃) = M(G̃)／E(H̃)`), via the new abstract crux
    `Matroid.Union_pow_contract_eq_contract_of_rk_saturated` (saturation ⟹ `Union (M／C)` and
    `(Union M)／C` agree on indep sets, count route). The crux input
    `Union_pow_isBasis'_split_of_rk_saturated` is unused by the count route but kept (abstract, green).
- [ ] **N5** `lem:case-I-splice-placement` — splice the inductive legs onto one parent placement (eq. 6.6
  panel intersections). **Decomposed math-first:** the panel-transversality "lemma" is already green;
  `withGraph` keeps the same normals so there is no two-placement splice; the genuine obstruction was
  *one seed `q₀` with both legs rigid* (the witness-transfer), now resolved into green bricks (see the
  green-brick inventory). What remains red is the *coupling into the composer* — the IH-shape gap, folded
  into N6 below.
- [ ] **N6** `lem:case-I-realization` — compose N4 + N5 + the green glue
  (`isInfinitesimallyRigidOn_union_of_inter`) + device ⇒ discharges
  `theorem_55.hcontract`. **NOT one commit — IH-motive mismatch (recon).** The composer needs each leg in
  `HasGenericFullRankRealization` (GP) form, but `minimal_kdof_reduction` threads only the *bare*
  `HasFullRankRealization`. The 2026-06-04 generic-motive recon settled this as a **hybrid** (see
  *Decisions* → *Generic-motive recon: hybrid …*): Route 2 (generic *producer*) and Route 1 (generic *IH*)
  are not alternatives — they are the two halves. Sub-nodes ordered below; **N6-G1 is the first buildable
  commit.** **Leg-transport brick GREEN:** `hasGenericRealization_transport_ends`.
  - [x] **N6-G1** `hasGenericFullRankRealization_of_splice_ofNormals` — generic *producer*. **GREEN**
    (2026-06-04, one commit). The recon planned a multi-commit device-GP re-expose (a `_generic` twin on
    each of `exists_good_realization_ofParam` → `…_relative_full_count` → `…_independent_panelRow` →
    leg-restricted → coupling). **The N6-G1a spike found that route rests on a false premise:** the device
    output `q` (from `exists_good_realization_ofParam`, ultimately `exists_finrank_dualCoannihilator_polynomial`)
    is a generic Gram-determinant non-root, *not* an `ofParam` moment-curve point — so it carries no GP and
    there is no dropped GP witness to re-expose. **The real, cheaper route:** the splice glue
    `isInfinitesimallyRigidOn_of_splice` is genericity-free and gives rigidity of `ofNormals G ends q₀` on
    all of `V(G)` *at the seed `q₀`*, which IS GP by hypothesis. So the `_generic` producer realizes at
    `q₀` itself, bypassing the device round-trip entirely (the device is only needed to certify the
    witnessed corank for the *bare* motive). One four-tuple `⟨ofNormals G ends q₀, rfl, hgp, glue⟩`.
    Axiom-clean. See *Decisions* → *N6-G1 spike*.
  - [ ] **N6-G2** the generic-motive reduction (Route 1, the structural core) — **RE-RECONNED
    2026-06-04; cut into G2a/G2b/G2c (design doc §1.6); still multi-commit, Phase-20-touching.** Supply
    each Lemma-6.3 Case-I leg's IH in `HasGenericFullRankRealization` form. The re-recon settled the motive
    as the *conditioned* `Pc G := (G.Simple → GP G) ∧ bare G` (unconditional GP is false at the parallel-K₂
    base), routing the `Simple`-failure cases (incl. KT's Lemma-6.5 degree-2-removal case) to the bare
    conjunct so `splitOff`-non-preservation is harmless. **New finding (KT §6.2 verified):** Case I
    trifurcates — only the **Lemma-6.3 legs** (rigid block `H`, contraction `G/E(H)`) need the generic IH;
    `H` simple is free via `Graph.Simple.mono`, and `G/E(H)` simplicity is the genuine new obligation.
    Sub-passes (each its own commit, re-recon at open):
    - [x] **G2a** conditioned-motive reduction skeleton. **GREEN** (`theorem_55_generic`, 2026-06-04,
      axiom-clean). `Graph.minimal_kdof_reduction` at `Pc G := (G.Simple → GP G) ∧ bare G`; bare conjunct
      reuses `theorem_55`'s `hbase`/`hsplit`/`hcontract` hypotheses, `Simple → GP` per-branch from carried
      hypotheses `hbaseGP`/`hsplitGP`/`hcontractGP`. **Flagged sub-question SETTLED:** the `Simple → GP`
      conjunct of the *splitting-off* branch **is** KT Case III (Track B), out of 22a scope and entirely
      red — so the binding obstruction is *scope*, not `splitOff`-routing. The honest in-scope shape
      carries it as `hsplitGP` (Phase-21b green-modulo `h…`; design doc §1.6 escalation (ii)), no Phase-20
      `removeVertex` re-route needed. `hcontractGP` is fed the *full conditioned IH* `∀ G', … → Pc G'` so
      G2c can extract each Lemma-6.3 leg's `GP` (`H` via `Simple.mono`, `G/E(H)` via G2b).
    - [x] **G2b** `map`/`collapseTo` simplicity (the new combinatorial fact). **GREEN** (2026-06-04,
      axiom-clean, `Induction.lean`). Built as the abstract kernel `map_simple` (`(f ''ᴳ G).Simple` from
      no-self-collapse `hloop : ∀ e x y, G.IsLink e x y → f x ≠ f y` + no-pair-collapse `hpar`) +
      its `rigidContract` specialization `rigidContract_simple` (`(G.rigidContract H r).Simple` from the
      same two hypotheses phrased on `G ＼ E(H)` under `collapseTo r V(H)`). The fork has *no*
      `map`-simplicity API (instances cover `↾`/`＼`/`-`/induce only) because `map` is the **one** op that
      breaks `Simple` — collapsing vertices can make loops *and* parallel edges. This is exactly why KT
      Case I trifurcates: `G/E′` simple is a *case hypothesis* (Lemma 6.3 p.673), its failure routed to
      Lemma 6.5's vertex-*removal* `Gv` (which does preserve `Simple`). `map_simple` is the faithful
      positive statement of Lemma 6.3's hypothesis — **not** an unconditional preservation theorem. The
      decomposition replaced the planned "research-shaped dichotomy" with this clean positive criterion:
      the dichotomy is downstream (G2c decides which of `hloop`/`hpar` holds at the realized contraction).
    - [x] **G2c** *generic coupling producer* `hasGenericFullRankRealization_of_couple_ofNormals` —
      **GREEN** (2026-06-05). The brick that wires N6-G1 to the per-leg generic IHs: the generic
      sibling of `hasFullRankRealization_of_couple_ofNormals`, identical up to the final splice. From
      the *same* per-leg inputs (each leg rigid as `ofNormals · ends ·` at its own seed + transversal
      hinges, the shape `hasGenericRealization_transport_ends` delivers from a `HasGenericFullRankRealization`
      IH), steps (i)–(iv) — the leg-restricted rank polynomials × the (G2) factor → a shared GP non-root
      `q₀` at which both legs are rigid — are verbatim; only step (v) swaps the device-routing bare splice
      `hasFullRankRealization_of_splice_ofNormals` (which loses GP through the device) for the
      device-free N6-G1 `hasGenericFullRankRealization_of_splice_ofNormals` (realizes at `q₀` itself,
      keeping GP). Concludes the strengthened motive. Axiom-clean. The remaining red work — building
      the geometric leg data (legs `H` / `G.rigidContract H r`, shared body `r`, cover, endpoint
      selector) from the conditioned IH + N4 and dispatching on `G.Simple` — is the **N6-G3 composer**.
  - [ ] **N6-G3** composer assembly — **RE-RECONNED 2026-06-05 (design doc §1.7); NOT pure leg-data
    geometry; cut into G3a/G3b/G3c.** The prior "feed N4 + the two leg IHs into G2c" framing was too
    optimistic — blind to the **`Gc ≤ G` mismatch**: the coupling needs both legs *literal subgraphs of
    `G`*, but `G.rigidContract H r` *relabels* `V(H) ↦ r` so it is **not** `≤ G` (no `rigidContract_le`
    can exist). The recon (verified vs. KT §6.2 eqs. (6.3)–(6.9)) settled this: KT's splice contraction
    leg in `R(G,p)` (eq. 6.3) is `R(G,p; E∖E′, V∖V′)` = the parent restricted to surviving edges
    `E(G)∖E(H)` = **`G.deleteEdges E(H)`** (which IS `≤ G`); the collapse to `v∗`/`r` lives on the
    *placement* side (eq. 6.7's `p_{E∖E′}`), and KT's Claim 6.4 (eq. 6.9) is the rank-transport from the
    relabelled-contraction IH to this `G ＼ E(H)`-leg rigidity. So the contraction leg's rigidity is **not
    available from any green brick** — it needs a new collapse-transport (the last research-shaped Case-I
    brick). Sub-passes (each its own commit; re-recon at open):
    - [x] **G3a** Claim-6.4 collapse-transport brick (`research-shaped`, the new analytic content) —
      `PanelHingeFramework.rigidContract_rigidity_transport`. **GREEN-MODULO (2026-06-05, axiom-clean, no
      `sorry`).** The math-first decomposition (see *Decisions* → *G3a*) found the surviving-edge transport
      does **not** reduce structurally to the green linking-edge brick: `collapseTo r V(H)` redirects each
      surviving edge's endpoints, so its support extensor uses *different panel normals* in `rigidContract`
      vs. `deleteEdges E(H)`, and recovering the rank at the un-collapsed endpoints **is** the
      algebraic-independence statement of KT Claim 6.4 — irreducibly research-shaped, no green brick
      converts a relabelled-graph rigidity into the original-endpoint rigidity. Per the §1.7 / hand-off
      escalation authorization, the Claim-6.4 transport is carried as the explicit hypothesis `htransport`
      (Phase-21b green-modulo `h…` idiom); the brick does the surrounding plumbing (extract the contraction
      IH `⟨Q, hQg, hQgp, hQrig⟩`, forward `htransport`'s seed `q_c` + surviving-edge rigidity at the
      **parent** selector `ends`, in the exact shape the G2c coupling consumes for its
      `Gc := G.deleteEdges E(H)` leg). `lem:case-III`/`thm:theorem-55` stay red; the obligation is one
      visible hypothesis pinned to KT eq. (6.9), not a `sorry`/`axiom`.
    - [x] **G3b** cover/shared-body/endpoint-selector geometry. **GREEN** (2026-06-05, axiom-clean,
      `couple_geometry_of_isProperRigidSubgraph`). Both legs now `≤ G` (`H` and `G.deleteEdges E(H)`):
      discharges the coupling's seven *geometric* inputs — `H ≤ G`, `G ＼ E(H) ≤ G`, `r ∈ V(H)`,
      `r ∈ V(G.deleteEdges E(H))`, the cover `V(G) ⊆ V(H) ∪ V(G.deleteEdges E(H))` (trivial —
      `vertexSet_deleteEdges` reads `V(G.deleteEdges E(H)) = V(G)`), and both legs nonempty — from
      `H.IsProperRigidSubgraph G n` + a chosen `r ∈ V(H)`. The parent selector `ends` and (G2b)
      `rigidContract_simple`'s `hloop`/`hpar` simplicity inputs are *IH-extraction* obligations,
      relocated to G3c (where the conditioned IH for the contraction leg is extracted under
      `(G.rigidContract H r).Simple`); G3b is the pure-geometry adapter.
    - [ ] **G3c** assembly + `theorem_55`/`theorem_55_generic` flip. **RE-RECONNED 2026-06-05 (design
      doc §1.8); NOT pure green-brick assembly — cut into G3c-i/ii/iii.** The §1.7 "buildable assembly"
      framing was blind to a **body-set mismatch**: the G2c coupling (and the rank-polynomial
      witness-transfer it calls, `exists_rankPolynomial_of_rigidOn_linking`) hardcode each leg rigid on
      its **full** `V(GH)`/`V(Gc)`, but the contraction leg `Gc = G.deleteEdges E(H)` has `V(Gc) = V(G)`
      and is rigid *only* on `(V(G)∖V(H)) ∪ {r}` (the surviving edges leave the interior `V(H)∖{r}`
      free) — exactly G3a's output set. So G3a's leg does **not** fit the coupling. The honest base glue
      `isInfinitesimallyRigidOn_of_splice` already takes arbitrary per-leg body sets `sH`/`sc`; the work
      is lifting the witness-transfer *producers* off the hardcoded `V(·)`. This is KT's own
      `R(G,p; E∖E′, V∖V′)` body restriction (eq. 6.3), collapsed away in the earlier all-of-`V`-leg
      nodes. Sub-passes (each its own commit; re-recon at open):
      - [x] **G3c-i** body-set-relative rank polynomial + N7b-0 — **GREEN** (2026-06-05, axiom-clean).
        The four *producer* bricks generalized from `V(G)`/count `D(|V(G)|−1)` to an arbitrary nonempty
        body set `s`/count `D(|s|−1)`: the body-set N1 **upper bound** `finrank_pinnedMotionsOn_le`
        (`finrank (pinnedMotionsOn s) ≤ D·|sᶜ|`, via the new `pinnedMotionsOn_le_iInf_ker_proj` +
        `finrank_iInf_ker_proj_eq`), the body-set N7b-0 helper
        `finrank_infinitesimalMotions_le_of_isInfinitesimallyRigidOn` (`dim Z ≤ D·(|sᶜ|+1)`), the
        body-set N7b-0 `exists_independent_panelRow_subfamily_of_rigidOn_linking_set`, and the body-set
        rank polynomial `exists_rankPolynomial_of_rigidOn_linking_set`. **Key math finding (sharpens
        §1.8):** rigidity on `s` bounds the null space only *above* — the N1 *equality*
        `finrank (pinnedMotionsOn s) = D·|sᶜ|` is **false** for `s ⊊ V(G)` (the interior bodies of
        `V(G)∖s` still carry hinge constraints, so the pin is *smaller* than the free `D·|sᶜ|`). The
        upper bound is all the *producer* needs (an upper bound on `dim Z` ⟹ a *lower* bound
        `D(|s|−1) ≤ #rows`, i.e. `≥ D(|s|−1)` independent rows, where the all-of-`V(G)` form had `=`).
      - [ ] **G3c-ii** body-set-relative coupling — **the body-set N3 *consumer* is the genuinely-stuck
        half (NEW finding, math-first).** A `couple_ofNormals` variant threading per-leg body sets
        `sH`/`sc` (`c ∈ sH`, `c ∈ sc`, `V(G) ⊆ sH ∪ sc`); steps (i)–(iv) thread the G3c-i body-set rank
        polynomials, then step re-derives each leg rigid *on its body set* at the shared seed `q₀` and
        finishes on the base glue `isInfinitesimallyRigidOn_of_splice`. **The re-derivation is a body-set
        N3** (`finrank rows ≥ D(|s|−1) ⟹ rigid on s`), and that **does NOT close from the count alone**
        for a general `s`: N3-on-`V(G)` upgrades `pinnedMotionsOn V(G) ≤ pinnedMotions v₀` to equality
        via the N1 *equality* `= D·|sᶜ|`; for `s ⊊ V(G)` only the upper bound holds, so the dimensions
        do not match. The clean equality needs the bodies of `sᶜ` *unconstrained off* `s` — true for the
        contraction leg (its `V(H)∖{r}` is isolated in `G ＼ E(H)`) but not a generic `s`. So G3c-ii's
        N3 needs either (a) the leg-specific "complement isolated" hypothesis (an honest `h…` carrying
        `finrank (pinnedMotionsOn s) = D·|sᶜ|`, green-modulo per the escalation rule), or (b) a body-set
        coupling that consumes each leg's rigidity *directly* (not re-derived from a rank polynomial),
        finishing on the base glue without a re-derivation N3 step. Re-recon at G3c-ii open before
        dispatch.
      - [ ] **G3c-iii** assembly + flip (`buildable` once G3c-i/ii green; the original G3c) — dispatch
        on `G.Simple`; simple branch: `H`-leg IH (`Simple.mono` + `subgraph_minimality`) on `sH := V(H)`
        + transported contraction leg (G3a + N4) on `sc := (V(G)∖V(H)) ∪ {r}` → G3c-ii body-set
        coupling → `hasFullRankRealization_of_generic`; non-simple branch: N6a directly. Discharges the
        `hloop`/`hpar` of `rigidContract_simple` when extracting the contraction leg's IH. Discharges
        `hcontractGP`/`hcontract` ⟹ `lem:case-I-realization` green-modulo (`htransport` / Claim 6.4).
  - [x] **N6a** non-simple Case I producer (KT Lemma 6.2), general-position-free. **GREEN**
    (`hasFullRankRealization_of_splice_of_supportExtensor` + leg-native form). Takes *transversal hinges*
    `hsupp` directly instead of general position `hgp`, strictly generalizing
    `hasFullRankRealization_of_splice` (now a thin GP corollary). Bare-motive, no Phase-20 touch.
  - [x] **Two-motive split** — `HasGenericFullRankRealization` (unconditional GP) + the one-line
    forgetful map `hasFullRankRealization_of_generic`, carried only through the simple Case-I cases.
    **GREEN.** `theorem_55` untouched (the spike ruled out the `(G.Simple → GP)` single-conjunct).
  - [x] **(G2) general-position polynomial factor**. **GREEN** (`exists_generalPosition_polynomial` +
    helpers): a nonzero `MvPolynomial` whose non-roots are exactly the GP assignments — the off-diagonal
    product of leading `2×2` minors, nonzero at the moment-curve seed (Vandermonde det).
  - [x] **N6b/N6c** simple Case I (KT Lemma 6.3/6.5) — the shared-seed coupling assembly. **GREEN**
    (`hasFullRankRealization_of_couple_ofNormals`). Multiplies the two legs' leg-restricted rank
    polynomials × the (G2) factor, takes a shared non-root (`MvPolynomial.exists_eval_ne_zero`),
    re-derives each leg rigid + GP at it, feeds `hasFullRankRealization_of_splice_ofNormals`.

## Deferred to 22b+ (Case III + assembly)

The remaining Phase-22 territory is parked as a single light placeholder
sub-phase **22b+** (planning; expected to split into multiple sub-phases once its
shape is clearer; the cut is deferred until 22a closes). Node plan + the KT math
live in `notes/MolecularConjecture.md` *Phase 22* (Track B) and *Phase 23*
(assembly); the node names are recorded here so nothing is lost:

- **Track B — Case II/III producer at `d=3` (the crux, KT §6.3 + §6.4.1).** This
  is `theorem_55.hsplit` (k=0 split).
  - eq. (6.12) degenerate placement (`p1(vb)=q(ab)` reproduces the `e₀` row; the
    green N7b-0/1/2/3 + glue feed it) — gives `+(D−1)`, one short.
  - **Lemma 6.10** (`d=3`, 3 candidates): Claim 6.11 (combinatorial↔linear,
    redundant `ab`-row), Claim 6.12 (extensor-span genericity via Lemma 2.1).
  - Blueprint nodes: `lem:case-II-realization` (KT's Case III), `lem:case-III`.
  - **Design-pass-first** before any build dispatch (`DESIGN.md` *Constructibility
    recon … → Scale-up: design the LAYER, not just the node*); Track B is
    research-shaped and interlocking. See `notes/MolecularConjecture.md` *Phase 22*
    *Process*.
- **Assembly (`d=3`).**
  - `prop:rigidity-matrix-prop11` `hub` brick (Phase-19 partition-contraction
    count) — a Track-independent closable target, itself multi-commit; decompose
    math-first before scheduling.
  - `thm:theorem-55` flips green once the producers land.

## Decisions made during this phase

### Phase-local choices and proof techniques
- **G3c-i GREEN: body-set producer bricks need only the N1 *upper* bound; the N1 *equality* is false
  off `V(G)`, which strands the body-set N3 *consumer* (2026-06-05).** Lifted the four leg-restricted
  producer bricks (N1, the N7b-0 helper, N7b-0, the rank polynomial) from `V(G)` to an arbitrary
  nonempty body set `s`. The crux: `finrank (pinnedMotionsOn s) ≤ D·|sᶜ|` (upper bound) holds for *any*
  `s` (`pinnedMotionsOn s ≤ ⨅ i∈s ker proj i`, finrank `D·|sᶜ|` by `iInfKerProjEquiv` for any `s`), but
  the *equality* `= D·|sᶜ|` (which N1-on-`V(G)` has, since `sᶜ` bodies are then free isolated ones) is
  **false** for `s ⊊ V(G)` — interior `V(G)∖s` bodies still carry hinge constraints. Producer side wants
  the upper bound only (`dim Z ≤ D·(|sᶜ|+1)` ⟹ `≥ D(|s|−1)` rows), so all four close green. **But the
  N3 *consumer* (re-derive rigid on `s` from the row count, needed by G3c-ii's re-derivation step)
  genuinely does NOT close from the count alone** — N3-on-`V(G)` upgrades `pinnedMotionsOn V(G) ≤
  pinnedMotions v₀` to equality *via the N1 equality*, unavailable off `V(G)`. So G3c-ii must carry the
  leg-specific complement-isolation fact `finrank (pinnedMotionsOn s) = D·|sᶜ|` as an honest `h…`
  (green-modulo) or avoid the rank-polynomial round-trip and feed each leg's rigidity straight into the
  base glue. Axiom-clean; one FRICTION ascription entry (`⨅ i∈s` standalone term needs `Submodule …`).
- **G3c re-recon: NOT pure green-brick assembly — the coupling hardcodes each leg rigid on its full
  `V(·)`, but the contraction leg is rigid only on `V∖V′ ∪ {v∗}`; cut into G3c-i/ii/iii (2026-06-05,
  docs-only).** The §1.7 "buildable G3c" was blind to a body-set mismatch: `hasGenericFullRankRealization_of_couple_ofNormals`
  (and the rank-polynomial brick `exists_rankPolynomial_of_rigidOn_linking` it calls) demand each leg
  rigid on its **full** `V(GH)`/`V(Gc)`, but `Gc = G.deleteEdges E(H)` has `V(Gc) = V(G)` and is rigid
  *only* on `(V(G)∖V(H)) ∪ {r}` (G3a's output; surviving edges leave `V(H)∖{r}` free). KT eq. (6.3)'s
  splice respects this split (`R(G,p; E∖E′, V∖V′)`); the base glue `isInfinitesimallyRigidOn_of_splice`
  already takes arbitrary `sH`/`sc`, so the work is lifting the witness-transfer producers off the
  hardcoded `V(·)`: G3c-i (body-set rank polynomial + N7b-0, research-shaped), G3c-ii (body-set coupling,
  buildable), G3c-iii (assembly + flip, buildable). Design doc §1.8; ledger entry (a). No Lean edits.
- **G3a GREEN-MODULO: the surviving-edge collapse transport does NOT reduce to the green linking-edge
  brick; KT Claim 6.4 is irreducible, carried as `htransport` (2026-06-05).** The §1.7 recon proposed
  the lever might be `infinitesimalMotions_eq_of_isLink_span_supportExtensor` (motion space sees only
  linking-edge support extensors) + the surviving-edge bijection. The math-first pass found that lever
  *does not close it*: the bijection is endpoint-relabelling, and `collapseTo r V(H)` sends a surviving
  edge's endpoints to *different* bodies, so its support extensor `panelSupportExtensor (q u) (q v)`
  uses *different normals* in `rigidContract` vs. `deleteEdges E(H)` — the spans are not equal, so the
  brick's `hspan` hypothesis fails. Recovering the rank at the un-collapsed endpoints across that relabel
  *is* the algebraic-independence content of KT Claim 6.4 (eq. 6.9) — irreducibly research-shaped, no
  green brick supplies it. Per the §1.7 / hand-off escalation authorization, carried Claim 6.4 as the
  narrow explicit hypothesis `htransport` (Phase-21b green-modulo `h…` idiom); `rigidContract_rigidity_transport`
  is then the plumbing (`let ⟨Q,hQg,hQgp,hQrig⟩ := hQ; htransport …`) packaging the seed + surviving-edge
  rigidity at the parent selector for the G2c coupling. `lem:case-III`/`thm:theorem-55` stay red.
  Axiom-clean, no `sorry`, one node-level hypothesis.
- **N6-G3 re-recon: the `Gc ≤ G` mismatch dissolves at the graph level but relocates to KT Claim 6.4
  on the placement side; cut into G3a/G3b/G3c (2026-06-05, docs-only).** The hand-off flagged the
  binding obstruction: the coupling needs both legs `≤ G`, but `G.rigidContract H r` relabels `V(H)↦r`
  so it is not `≤ G` (no `rigidContract_le` can exist). The recon (verified vs. KT §6.2 eqs. (6.3)–(6.9))
  settled it: KT's splice contraction leg is `R(G,p; E∖E′, V∖V′)` = the parent restricted to surviving
  edges = **`G.deleteEdges E(H)`** (which *is* `≤ G`); the collapse to `v∗`/`r` is purely on the
  *placement* side (eq. 6.7). So the graph-level mismatch dissolves, but the contraction IH's rigidity
  (on the *relabelled* graph) must be transported to the `G ＼ E(H)` leg — that is **KT Claim 6.4**
  (eq. 6.9, the algebraic-independence rank-transport), the **last research-shaped Case-I brick** and
  *not* a green brick. The "pure leg-data geometry" framing was too optimistic — blind to the
  placement-side obligation (the *actual-construction* sharpening of the recon rule). Cut: G3a (the
  Claim-6.4 collapse transport, research-shaped), G3b (cover/simplicity, buildable), G3c (assembly +
  flip, buildable). Design doc §1.7.
- **G2c GREEN: the *generic coupling producer* `hasGenericFullRankRealization_of_couple_ofNormals`
  is a one-line variation of the bare coupling — swap the final splice (2026-06-05).** The G2c
  deliverable turned out to be the missing *producer brick*, not a full wire-up: the bare coupling
  `hasFullRankRealization_of_couple_ofNormals` already does all the witness-transfer (shared GP seed
  `q₀`, both legs rigid at it, parent normals GP) and ends by calling the *bare* device-routing splice
  `hasFullRankRealization_of_splice_ofNormals`; the generic sibling reuses steps (i)–(iv) verbatim and
  ends with N6-G1 `hasGenericFullRankRealization_of_splice_ofNormals` (device-free, keeps GP). Dropping
  `hne_ends`/`hne` from the signature (N6-G1 bypasses the device, so it needs neither) cleared the only
  warnings. This is the brick that connects all three of N6-G1 (generic producer), the transport brick
  (consumes generic legs), and G2a/G2b (supply simplicity to extract them) — N6-G3 is now pure leg-data
  geometry. Axiom-clean, no Phase-20 touch.
- **G2a GREEN: the conditioned-motive reduction skeleton `theorem_55_generic`; the flagged routing
  sub-question is settled by *scope*, not `splitOff` routing (2026-06-04).** Built `theorem_55_generic`:
  `Graph.minimal_kdof_reduction` re-instantiated at `Pc G := (G.Simple → GP G) ∧ bare G`. Each branch's
  bare conjunct comes from the `theorem_55`-shaped hypotheses; each branch's `Simple → GP` conjunct from a
  carried hypothesis (`hbaseGP`/`hsplitGP`/`hcontractGP`). **The G2a flagged sub-question** ("does `Pc`'s
  `hsplit` survive `splitOff` routing for a simple parent?") **dissolves once you see the splitting-off
  branch's `Simple → GP` conjunct *is* KT Case III** (Track B), out of 22a scope and entirely red. So the
  binding obstruction is *scope*, not the `splitOff`-non-simplicity routing — carrying `hsplitGP` as an
  explicit hypothesis (green-modulo `h…`) is the honest in-scope shape, and no Phase-20 `removeVertex`
  re-route is needed. `hcontractGP` (simple Case I) is fed the *full conditioned IH* so G2c can extract
  each Lemma-6.3 leg's `GP`. Pure structural composition; axiom-clean. Design doc §1.6.
- **N6-G2 re-recon: condition the motive on `G.Simple`; Case I trifurcates and only the Lemma-6.3 legs
  need the generic IH; cut into G2a/G2b/G2c (2026-06-04, docs-only).** The §1.5 hand-off flagged N6-G2 as
  NEEDS-FURTHER-RECON. Settled (design doc §1.6, verified vs. KT 2011 §6.2 pp.673–676): the generic
  reduction is `minimal_kdof_reduction` re-instantiated at the *conditioned* motive
  `Pc G := (G.Simple → GP G) ∧ bare G` (unconditional GP is false at the parallel-K₂ base + non-simple
  Lemma-6.2). **New source finding:** KT's Case I is *not* a uniform contraction recursion — it
  trifurcates (Lemma 6.2 non-simple/bare, 6.3 `G/E′` simple/generic, 6.5 no-such-`G/E′` → degree-2 vertex
  *removal* `Gv`, simple-because-removal). So only the **Lemma-6.3 legs** (`H`, `G/E(H)`) need the generic
  IH; `H` simple is free (`Simple.mono`), `G/E(H)` simplicity is the genuine new obligation (no
  `map`-simplicity API in the fork). Routing `Simple`-failure cases to the bare conjunct makes
  `splitOff`-non-preservation harmless. Three passes: G2a (reduction skeleton, with a flagged
  `hsplit`-vs-`splitOff` routing sub-question to settle first), G2b (`map`-simplicity, math-first kernel),
  G2c (wire-up). Both kernels are Phase-21b-`h…`-deferral-eligible if they stall. Design doc §1.6.
- **N6-G1 spike: the device-GP re-expose route was a FALSE PREMISE; N6-G1 is one cheap commit, not a
  multi-commit device-twin build (2026-06-04).** The recon (§1.5) planned N6-G1a as "re-expose the GP
  witness the device drops". The spike traced the device output: `exists_good_realization_ofParam` →
  `exists_relative_full_count_ofParam` → `exists_good_realization` → `exists_finrank_dualCoannihilator_polynomial`,
  whose output `q` is an *arbitrary* non-root of a Gram-determinant `MvPolynomial` — **not** an `ofParam`
  moment-curve point, so `isGeneralPosition_ofParam` does not apply and there is *no* dropped GP witness.
  The right route: realize at the GP *seed* `q₀` directly. The splice glue `isInfinitesimallyRigidOn_of_splice`
  is genericity-free (it does not call the device) and already proves `(ofNormals G ends q₀).toBodyHinge`
  rigid on all of `V(G)`; `q₀` is GP by hypothesis; so the `_generic` producer
  `hasGenericFullRankRealization_of_splice_ofNormals` is just `⟨ofNormals G ends q₀, rfl, hgp, glue⟩`,
  bypassing the device. The device is needed only to certify the witnessed corank for the *bare* motive.
  Lesson lifted to DESIGN.md *Constructibility recon …* *Sharpening: trace a producer's actual output
  point …*.
- **Generic-motive recon: the route is a HYBRID — Route 2 (generic producer) + Route 1 (generic IH) are
  two halves, not alternatives (2026-06-04, docs-only).** Ground: the composer's per-leg adapter
  (`hasGenericRealization_transport_ends`, green) consumes each leg in `HasGenericFullRankRealization`, but
  `minimal_kdof_reduction` (`Induction.lean:3529`) threads only the bare `HasFullRankRealization`. Route 2
  makes the simple-case *producer* conclude GP (the device realizes at a hidden `ofParam` `q` that *is* GP
  by `isGeneralPosition_ofParam`, but `exists_good_realization_ofParam` returns a bare `∃ q`, hiding the
  witness — re-expose it). Route 1 makes the *IH* generic. Both are required: G1 (Route 2, buildable),
  then G2 (Route 1, needs-further-recon), then G3 assembly. **First buildable commit: N6-G1a** (re-expose
  GP through the device stack). Cut into N6-G1/G2/G3 in the *Lemma checklist*; design doc §1.5.
- **KT Lemma 6.7(ii) verified vs. source; absent in repo; only covers the Case-II/III branch (2026-06-04).**
  KT 2011 printed p.676 (pdf p.31): for `G` 2-edge-connected minimal `k`-dof, `|V|≥3`, **and no proper
  rigid subgraph**, (i) `|V|=3 ⟹ k=0` + nonparallel full-rank realization; (ii) `|V|≥4 ⟹ G_v^{ab}` is
  simple for any degree-2 `v`. **No `splitOff`/`rigidContract` simplicity fact exists in the project.** The
  no-proper-rigid-subgraph hypothesis means 6.7(ii) is the *Case II/III* (splitting-off) simplicity fact —
  it does NOT cover the Case-I contraction. For Case I: `Graph.Simple.mono` (`Matroid/Graph/Simple.lean:202`,
  `H ≤ G → G.Simple → H.Simple`) gives the rigid block `H` simple for free; `G/E(H)` simplicity is exactly
  KT's Lemma 6.3-vs-6.5 split (not a single fact). So G2 (Route 1) needs 6.7(ii) *for the split-off branch*
  plus a contraction-simplicity dichotomy — both new.
- **N6 composer recon: not one commit — IH-motive mismatch; leg-transport `ends`-swap brick
  (2026-06-04).** The recon (`DESIGN.md` *Constructibility recon …*) found `theorem_55.hcontract`'s IH
  (and `minimal_kdof_reduction`'s) is the *bare* `HasFullRankRealization k G'`; the simple-case coupling
  needs each leg *general-position* rigid. The two-motive split dissolves that only when the *induction*
  runs against `HasGenericFullRankRealization`, so closing the simple branch needs a *separate
  generic-motive reduction* (Phase-20 touch), and the coupling concludes only the bare motive
  (`_independent_panelRow` realizes at a device-generic `q` with no GP conjunct). Multi-commit. Built the
  first decomposable green brick `hasGenericRealization_transport_ends`: a leg's
  `HasGenericFullRankRealization` ⟹ the coupling-ready `(ofNormals GH ends qH)` at the parent selector.
  See *Blockers* / *Hand-off*.
- **N6b/N6c shared-seed coupling assembly (2026-06-04).** Built `hasFullRankRealization_of_couple_ofNormals`:
  each leg's leg-restricted rank polynomial (the parent `hends` records the leg's linking edge via
  `Graph.IsSubgraph.isLink_iff`) × the (G2) factor → triple-product shared non-root → each leg re-derived
  rigid + GP at `q₀` → `hasFullRankRealization_of_splice_ofNormals`. Honest: the inputs are the
  satisfiable per-leg single-seed rigidities at the parent selector; the parent rank is concluded. The
  `ends`-swap step supplying these from the IH lives in the (still-red) N6 composer.
- **Leg-restricted rank-polynomial chain — restrict the spanning identity to *linking* edges
  (2026-06-04).** Discharged the N6b recon's `hends`-over-all-`β` obstruction by mirroring the whole
  `exists_rankPolynomial_of_rigidOn` chain with the panel-row family + rigidity-row span restricted to the
  *linking-edge* subtype. The spanning identity then needs `hends`/`hne` only on linking edges — the form
  a proper-subgraph leg supplies (its `ends` is the parent's). The four bricks carry a `hsupp` (every
  witnessed index links) so each downstream `⊆`-inclusion draws its per-index link witness from `hsupp`.
  Coordinatization + rank-nullity verbatim from the all-edges forms.
- **N6b recon: the simple Case-I coupling is not a clean assembly — quantifier-domain gap (2026-06-04).**
  The plan applies `exists_rankPolynomial_of_rigidOn` per leg, but that brick needs `hends : ∀ e : β,
  GH.IsLink e …` (every edge label of the realized graph must link), which a proper-subgraph leg `GH ≤ G`
  does not satisfy. The type-level plan was blind to the *quantifier domain* of the brick's hypotheses (a
  fresh sharpening of the recon rule). Fixed by the leg-restricted chain above; first decomposable step
  was the `ends`-swap brick `infinitesimalMotions_ofNormals_eq_of_ends_swap`.
- **(G2) general-position polynomial factor — the off-diagonal product of leading `2×2` minors
  (2026-06-04).** `exists_generalPosition_polynomial = ∏_{(a,b) ∈ offDiag} pairLeadingMinorPoly a b`,
  `pairLeadingMinorPoly a b := X_{(a,0)}·X_{(b,1)} − X_{(a,1)}·X_{(b,0)}`. **Why fixed coords 0,1, not a
  general minor:** the *leading* (0,1) minor is exactly the one the moment-curve seed makes nonzero (its
  Vandermonde det `param b − param a`), matching `momentCurve_pair_linearIndependent`'s own proof, so the
  witnessed non-root drops out for free. The minor⟹LI helper is the coordinate-level generalization of
  `momentCurve_pair_linearIndependent`. Closes gap (G2).
- **Two-motive split — the general-position realization motive + forgetful map (2026-06-04).** Added a
  *separate* unconditional-GP motive `HasGenericFullRankRealization k G := ∃ Q, Q.graph = G ∧
  Q.IsGeneralPosition ∧ Q rigid on V(G)` + the one-line forgetful map `hasFullRankRealization_of_generic`,
  carried only through the simple Case-I cases. **Why the split, not the single-conjunct (A):** the
  `Simple`-threading spike ruled out `(G.Simple → GP)` — `splitOff` doesn't preserve simplicity (KT Lemma
  6.7), so that conjunct's IH lands on the wrong graph at `hsplit`. `theorem_55` untouched, no Phase-20
  node touched. Dissolves gap (G1) at the source: the GP motive carries the general-position seed the
  producers need (a GP parent seed is GP for every leg — `withGraph` keeps the same normals).
- **N6a — non-simple Case I producer via the `hsupp`-direct splice (2026-06-04).** Factored
  `hasFullRankRealization_of_splice`'s `hgp`→`hsupp` derivation out into a strictly-more-general producer
  `hasFullRankRealization_of_splice_of_supportExtensor` taking *transversal hinges* directly; the original
  is now a one-line corollary feeding it `supportExtensor_ne_zero_of_isGeneralPosition`. N7b-0 only ever
  needed `hsupp`, not `hgp`. KT's non-simple Lemma 6.2 sets two boundary panels equal (parallel normals ⟹
  GP fails) while retained hinges stay transversal, so the non-simple case consumes the *bare* motive and
  supplies it back — no motive strengthening, `theorem_55` untouched.
- **`Graph.Simple`-threading spike — `Simple` does NOT thread; take the two-motive split (2026-06-04,
  docs-only).** The design-pass decision was to strengthen the motive to carry general position, with two
  shapes: **(A)** one motive with a `G.Simple → GP` conjunct, or the **two-motive split**. Decisive fact:
  **`splitOff` does not preserve simplicity.** `G.splitOff v a b e₀` (`Induction.lean:572`) adds the fresh
  edge `e₀` linking `a`-`b` unconditionally; a simple `G` with an existing `a`-`b` edge becomes
  non-simple. So even the no-threading read of (A) fails: at `hsplit` a simple parent recurses on a
  possibly-non-simple split-off child, whose conditional `(child.Simple → GP)` delivers nothing for the
  simple parent. Take the split (touches no Phase-20 node; mirrors KT's own bifurcation). Design doc
  `notes/Phase22-realization-design.md` §1.4.
- **N5 rank-polynomial consumer + coupling recon found two gaps (since dissolved) (2026-06-04).** Built
  `isInfinitesimallyRigidOn_ofNormals_of_rankPolynomial_ne_zero` (the forward half of
  `exists_rankPolynomial_of_rigidOn`): a non-root `q` ⟹ the leg rigid on `V(G)` *at `q` itself* (subfamily
  LI at `q` forces `dim Z(G,q) ≤ D`, then N3). The same-commit recon on the planned coupling found two
  gaps — **(G1)** the rank-polynomial producer needs a *transversal*-rigid seed (bare IH supplies none),
  **(G2)** the splice needs GP at the shared non-root. Both were the genuine KT §6.2 panel-intersection
  geometry; (G1) was later dissolved by the two-motive split, (G2) closed by `exists_generalPosition_polynomial`.
- **N5 per-leg rank polynomial via a new constructive multivariate mirror (2026-06-04).** Built
  `exists_rankPolynomial_of_rigidOn`: a rigid leg ⟹ a single `MvPolynomial` nonzero at the seed, every
  non-root of which gives the leg's full `D(|V|−1)` `panelRow`-subfamily LI. The existing device bricks
  only return `∃ p, good`; coupling *two* legs needs the polynomial *exposed*, so mirrored
  `exists_polynomial_ne_zero_of_linearIndependent_at` (`Mathlib/LinearAlgebra/Matrix/Rank.lean`) returning
  the witnessing Gram-det minor. Reuses `exists_good_realization_ofParam`'s coordinatization verbatim;
  N7b-0 supplies the full-size `s`.
- **N5 witness-transfer prerequisites + seed route (2026-06-04).** `exists_rigidOn_ofNormals_of_hasFullRankRealization`
  repackages the IH's `Q` as an `ofNormals` (`Q` is *literally* one — `subst` the graph conjunct, close
  by defeq). The seed route is the **free `ofNormals`** space, not moment-curve `ofParam`: the `_ofParam`
  specialization silently needs the IH's free-normal realization coerced onto the moment-curve subvariety,
  a genericity gap the `∃ Q, …` motive does not supply. Couple both legs via the device's non-zero-product
  engine (`MvPolynomial.funext`). The `_ofParam` brick is kept but bypassed.
- **N5 splice + seed scaffolding, all GREEN (2026-06-04).** `hasFullRankRealization_of_splice` (composes
  splice-seed → N7b-0 → device); the leg-native `…_ofNormals` (+ the `rfl` graph-swap `ofNormals_withGraph`);
  the moment-curve `…_ofParam`; the single-leg bridge `hasFullRankRealization_of_rigidOn_seed`; and the
  forest-packing `Graph.IsKDof.exists_isBase_isForestPacking` (rigid `H` ⟹ a base of `M(H̃)` packing into
  `D` forests, `|B| = D(|V(H)|−1)`). The "row-stacking" follow-up to the packing was **ruled out** by a
  recon (over-counts by `(D−1)`, off-path — N7b-0 gives the full count from rigidity-on-`V`); the
  `_ofParam` *seed* was ruled out (subvariety-genericity gap). Both options collapsed to the free-`ofNormals`
  witness-transfer.
- **N5 decomposition recon — N5 is narrower than "splice two placements" (2026-06-04).** The
  panel-transversality "lemma" is already green (`isGeneralPosition_ofParam`); `withGraph` keeps the same
  normal, so both legs ride one normal assignment with no literal placement-gluing. The genuine
  obstruction is the **common-placement witness-transfer** (eq. 6.6). The first brick
  `hasFullRankRealization_of_splice` isolates that into satisfiable hypotheses, honest per the gate.
- **N4 constructibility recon (two passes) + N4b correction (2026-06-04).** N4 is the graph↔matroid
  correspondence Phase 20 deferred; the recon budgeted it as a several-node Whitney-style sub-build
  (connectivity-of-`H̃` → cycleMatroid-under-collapse → union-level `ext_indep`), since `Matroid.Union`
  does not commute with contraction. **N4b correction:** `cycleMatroid_contract` *does* apply — its
  `IsRepFun` hypothesis is on the **subgraph being contracted** (`H.mulTilde n`, whose `connPartition` is
  a single class by N4a), not on `(G ＼ E(H) ↾ E(H))` as the recon's paraphrase claimed. **Lesson:** read
  the vendored lemma's *exact binder*, not a paraphrase, before declaring it inapplicable.
- **N4c crux via the COUNT route, not matching re-decomposition (2026-06-04).** The union↔contraction
  crux bottoms out on the abstract `Union_pow_contract_eq_contract_of_rk_saturated`: expand *both*
  matroids to their count conditions via `Union_pow_indep_iff_count`, making the equivalence a symmetric
  `rk_submod` + `rk_mono` + `contract_rk_cast_int_eq` ℤ-arithmetic (saturation enters only as `|J| =
  k·M.rk C`). The matching re-decomposition route failed (an arbitrary `Ks` decomposition of `I ∪ J` is
  not factor-aligned). Saturation is supplied by `union_cycleMatroid_rk_saturated_of_isKDof_zero` (split
  into `rank M(H̃)` + connected cycle rank, each a `|V(H)|−1` computation). The intermediate reduction
  rewrites both sides over `S = E(G̃)\E(H̃)` via `restrict_contract_eq_contract_restrict`.
- **N4 reconciliation closed in one commit (2026-06-04).** With N4c green, `rigidContract_isMinimalKDof`
  is a clean assembly: transport both halves of `IsMinimalKDof` across N4c. The minimality half is a
  one-liner; the deficiency half is the only arithmetic (`rank_add_deficiency_eq` + `rw [hN4c]` + the
  exact count `|V(K)| = (|V(G)|−|V(H)|)+1` ⟹ `linarith` forces `def(K) = 0`). The exact count (vs. the
  `≤` form) is the genuine new fact: `r ∈ V(H)` makes the collapse image *equal* `(V(G)\V(H)) ∪ {r}`.

### Promoted to TACTICS-GOLF / TACTICS-QUIRKS / FRICTION / DESIGN
- *The fork's `Graph.Simple` API has no `map`-simplicity lemma — `map` is the one op that breaks `Simple`,
  so it needs a conditional criterion (`map_simple`), not an instance* → FRICTION [resolved] *The fork's
  `Graph.Simple` API has no `map`-simplicity lemma …*.
- *An injective `α → ℝ` from a finite/countable `α`: `Countable.exists_injective_nat` then
  `Nat.cast_injective`* → FRICTION [resolved] *An injective `α → ℝ` from a finite (or merely countable)
  `α` …*.
- *Building a subtype-indexed `panelRow` membership: pin the index with `show F.panelRow ends (e,t₁,t₂) =
  _`* → FRICTION [resolved] *A `panelRow ends i` membership `rfl` whnf-times-out …* (instance of
  TACTICS-QUIRKS § 4).
- *The recon must read the hypothesis *quantifier domain*, not just the conclusion shape* → FRICTION
  [resolved] *The Case-I N6b coupling is NOT a clean assembly …*; DESIGN.md *Constructibility recon before
  scheduling a producer build* (fresh application).
- *`rw […]` won't close a defeq goal differing only in a proof-term argument — finish with `exact lemma _
  _`* → FRICTION [resolved] *`rw […]` won't close a defeq goal whose two sides differ only in a proof-term
  argument …* (sibling of TACTICS-QUIRKS § 25).
- *`obtain ⟨a,t⟩ := e j` on a bare term doesn't rewrite `(e j).1` occurrences — `rcases hej : e j with
  ⟨a,t⟩` then `simp only [hej]`* → FRICTION [resolved] *`obtain ⟨a, t⟩ := e j` on a term …* +
  TACTICS-QUIRKS § 4.
- *`linearIndependent_rows_of_specialized_submatrix_det_ne_zero` on rows already over `ℝ` — pass `φ :=
  RingHom.id ℝ`* → FRICTION [resolved] *…specialized minor on rows already over `ℝ` …*.
- *`exists_polynomial_ne_zero_of_linearIndependent_at` — constructive rank-witnessing polynomial mirror* →
  FRICTION [mirrored] *`exists_polynomial_ne_zero_of_linearIndependent_at` …*; `Mathlib/LinearAlgebra/Matrix/Rank.lean`.
- *Repackaging a `HasFullRankRealization` witness as an `ofNormals` — `subst` the `Q.graph = G` conjunct,
  don't `rw` both sides* → FRICTION [resolved] *Repackaging a `HasFullRankRealization` witness …* (sibling
  of TACTICS-QUIRKS § 25).
- *`ofParam`↔`ofNormals` / `ofNormals`↔`withGraph` defeq across a heavy `IsInfinitesimallyRigidOn` term
  heartbeat-times-out by `rw` — state the hypothesis pre-converted, isolate the cheap defeq in a typed
  `have`; transferring `IsInfinitesimallyRigidOn` across an `infinitesimalMotions` equality needs a
  `mem_infinitesimalMotions` round-trip* → FRICTION [resolved] *But: `ofParam`↔`ofNormals` defeq …* +
  *A hypothesis stated on `(ofNormals GH ends q₀).toBodyHinge` …* (refinements of TACTICS-QUIRKS § 25).
- *N4 recon lesson + the N4b binder-paraphrase sharpening* → `DESIGN.md` *Constructibility recon before
  scheduling a producer build* (its first post-21b application).
- *`@[simps!]` projection name not resolving; bare-term field is `rfl`* → FRICTION [resolved]
  *`edgeMultiply`'s `@[simps! vertexSet]` lemma does not resolve …*.
- *`Set.ncard_iUnion_le_of_fintype` for `|⋃| ≤ ∑ ncard`* → FRICTION [resolved] *The `Set.ncard` of a
  finite-index `iUnion` is `≤ ∑ ncard` …*.
- *`H.cycleMatroid = G.cycleMatroid ↾ E(H)` for `H ≤ G`* → FRICTION [resolved] *`[matroid]`
  `H.cycleMatroid = G.cycleMatroid ↾ E(H)` …*.
- *Union↔contraction equality via the count condition `Union_pow_indep_iff_count`, not matching
  re-decomposition* → FRICTION [resolved] *`[matroid]` Union↔contraction equality …*.
- *The `V(...)` macro is greedy with a trailing binary operator — parenthesize the leading `V(…)` term* →
  FRICTION [resolved] *A `have h : … = … := by ring` whose type embeds `(V(G).ncard : ℤ) - 1 - 1` fails
  to parse*.

## Blockers / open questions

- **G3a green-modulo, G3b green, G3c-i green; the open work is N6-G3's G3c-ii/iii. The body-set N3
  *consumer* (re-derive rigid-on-`s` from the row count) is now the genuinely-stuck half (G3c-i
  finding).** All *producer* bricks are green (N4, N5, N6a, N6b/N6c, the two-motive split, (G2), N6-G1,
  G2a/G2b/G2c, the transport brick, **G3c-i's four body-set producer bricks**);
  **G3a `rigidContract_rigidity_transport` is green-modulo** the explicit Claim-6.4 hypothesis
  `htransport` (axiom-clean, no `sorry`); **G3b `couple_geometry_of_isProperRigidSubgraph` is green**
  (the geometry adapter). The `Gc ≤ G` mismatch is resolved at the graph level (the splice
  contraction leg is `G.deleteEdges E(H)` `≤ G`, KT eq. 6.3, *not* the relabelled `rigidContract`); the
  one remaining genuinely-analytic obligation is **the `htransport` hypothesis itself = KT Claim 6.4
  (eq. 6.9)**, the algebraic-independence rank-transport across the collapse map. The G3a math-first pass
  found this irreducible (the green linking-edge brick does not apply — the collapse redirects surviving-
  edge endpoints, breaking the `hspan` equality), so per the design-doc escalation it is carried as the
  node-level hypothesis. It re-enters at G3c-iii (where the composer supplies `htransport` to flip
  `lem:case-I-realization` green-modulo; KT Claim 6.4 / `lem:case-III` discharges it, deferred to 22b+).
  - **G3b — cover/shared-body/selector geometry. GREEN** (`couple_geometry_of_isProperRigidSubgraph`):
    from `H.IsProperRigidSubgraph G n` + a chosen `r ∈ V(H)`, the coupling's seven geometric inputs for
    legs `H` / `G.deleteEdges E(H)` / shared body `r` (both `≤ G`, share `r`, cover `V(G)` since
    `V(G.deleteEdges E(H)) = V(G)`, both nonempty). The parent selector `ends` and the simplicity
    `hloop`/`hpar` are IH-extraction obligations, relocated to G3c-iii.
  - **G3c — NOT pure assembly (re-reconned 2026-06-05, design doc §1.8); cut into G3c-i/ii/iii.** The
    body-set mismatch: the G2c coupling + its rank-polynomial brick hardcode each leg rigid on its
    **full** `V(·)`, but the contraction leg `G.deleteEdges E(H)` (`V = V(G)`) is rigid *only* on
    `(V(G)∖V(H)) ∪ {r}` (G3a's set; surviving edges leave `V(H)∖{r}` free). KT eq. (6.3)'s splice
    respects this (`R(G,p; E∖E′, V∖V′)`, surviving bodies `V∖V′`); the base glue
    `isInfinitesimallyRigidOn_of_splice` already takes arbitrary `sH`/`sc`. **G3c-i** (GREEN):
    body-set-relative rank polynomial + N7b-0 (rigid on nonempty `s`, count `D(|s|−1)`) via the body-set
    N1 *upper* bound. **G3c-ii** (next build, **re-recon at open**): body-set-relative coupling threading
    `sH`/`sc` — its re-derivation step is a **body-set N3** which does NOT close from the row count alone
    (the N1 *equality* is false off `V(G)`); either carry the leg-specific
    `finrank (pinnedMotionsOn s) = D·|sᶜ|` complement-isolation fact as `h…` (green-modulo) or feed each
    leg's rigidity straight into the base glue (no rank-polynomial round-trip). **G3c-iii** (`buildable`):
    the original assembly + flip, dispatch on `G.Simple`, discharging `hcontractGP`/`hcontract`.
- **Track B + assembly are deferred to 22b+** (see *Deferred to 22b+ (Case III + assembly)* above), not
  open blockers for 22a: the Case II/III producer (eq. 6.12 degenerate placement, one short, + Lemma 6.10
  at `d=3`) and the `prop:rigidity-matrix-prop11` `hub` brick + `thm:theorem-55` flip. They re-enter once
  22a closes.

## Hand-off / next phase

**Clean handoff point; next agent picks up at N6-G3-G3c-ii (the body-set-relative coupling — re-recon
at open per the body-set N3 finding below).** This commit lands **G3c-i GREEN**: the four body-set
*producer* bricks lifted from `V(G)`/count `D(|V(G)|−1)` to an arbitrary nonempty body set `s`/count
`D(|s|−1)`. Axiom-clean, no `sorry`, build + lint warning-clean. No `\leanok` / blueprint edits (the
coordinator owns the flip — see *Coordinator scope* below).

**What landed (all in `AlgebraicInduction.lean`).** (1) the body-set N1 **upper bound**
`finrank_pinnedMotionsOn_le` (`finrank (pinnedMotionsOn s) ≤ D·|sᶜ|`), via the new
`pinnedMotionsOn_le_iInf_ker_proj` (`pinnedMotionsOn s ≤ ⨅ i∈s ker proj i`) + the generic-`s`
`finrank_iInf_ker_proj_eq` (`finrank (⨅ i∈s ker proj i) = D·|sᶜ|` by `iInfKerProjEquiv`, for *any* `s`);
(2) the N7b-0 helper `finrank_infinitesimalMotions_le_of_isInfinitesimallyRigidOn` (rigid on nonempty
`s` ⟹ `dim Z ≤ D·(|sᶜ|+1)`); (3) the body-set N7b-0
`exists_independent_panelRow_subfamily_of_rigidOn_linking_set` (`≥ D(|s|−1)` independent linking panel
rows); (4) the body-set rank polynomial `exists_rankPolynomial_of_rigidOn_linking_set`.

**The G3c-i finding that re-shapes G3c-ii (math-first, important).** Rigidity on `s` bounds the null
space only *above*. The N1 **equality** `finrank (pinnedMotionsOn s) = D·|sᶜ|` — which N1-on-`V(G)` has
because `sᶜ` bodies are then free isolated ones — is **false** for `s ⊊ V(G)`: interior bodies of
`V(G)∖s` still carry hinge constraints, so the pin is *smaller* than `D·|sᶜ|`. The producer side wants
only the upper bound (`dim Z ≤ D·(|sᶜ|+1)` ⟹ `≥ D(|s|−1)` rows), so all four bricks closed green. **But
the body-set N3 *consumer* — re-derive "rigid on `s`" from the row count, which G3c-ii's witness-transfer
needs to re-derive each leg rigid at the shared seed `q₀` — does NOT close from the count alone for a
general `s`.** N3-on-`V(G)` (`isInfinitesimallyRigidOn_vertexSet_of_finrank_le`) upgrades
`pinnedMotionsOn V(G) ≤ pinnedMotions v₀` to *equality* via the N1 *equality*; off `V(G)` only the upper
bound holds, so the dimensions don't match. **G3c-ii must therefore either** (a) carry the leg-specific
complement-isolation fact `finrank (pinnedMotionsOn s) = D·|sᶜ|` as an honest `h…` (green-modulo;
satisfied by the contraction leg because its `V(H)∖{r}` is isolated in `G ＼ E(H)`, but not a generic
`s`), **or** (b) thread each leg's rigidity *directly* into the honest base glue
`isInfinitesimallyRigidOn_of_splice` (which already takes arbitrary `sH`/`sc`) at the shared seed,
*avoiding the rank-polynomial round-trip and its N3 re-derivation step* — likely the cleaner route, since
the rank polynomials are only needed to *find* the shared seed `q₀`, after which the legs' rigidity at
`q₀` could come from a different transport. **Re-recon at G3c-ii open before dispatch.**

**Next concrete task — N6-G3-G3c-ii: body-set-relative coupling.** A `couple_ofNormals` variant
threading per-leg body sets `sH`/`sc` (`c ∈ sH`, `c ∈ sc`, `V(G) ⊆ sH ∪ sc`) and finishing on
`isInfinitesimallyRigidOn_of_splice` at the shared seed `q₀`, consuming the G3c-i body-set rank
polynomials for the seed search. Settle route (a) vs (b) (above) first. G3c-iii (the original assembly +
flip dispatching on `G.Simple`, discharging `hcontractGP` / `hcontract`, supplying G3a's `htransport`,
`buildable`) follows once G3c-ii is green.

**Coordinator scope still holds (carried from the prior hand-off).** Once G3c-iii lands, **STOP**
before the blueprint flip: do **not** touch the blueprint (no `\leanok` flip or node edits), do **not**
run the phase-close checklist (ROADMAP ✓-flip, user-facing surfaces, `MolecularConjecture.md`), and do
**not** open 22b. The coordinator handles the blueprint green-modulo flip of `lem:case-I-realization`
(with an honest red Claim-6.4 node tracking `htransport`, à la 21 → 21b), the phase-close, and the
lossless 22b scaffold as a separate owner-supervised step.

The G3c-iii assembly dispatch on `G.Simple` (when it lands): **simple branch** feeds
`couple_geometry_of_isProperRigidSubgraph` (G3b) for the geometry, the `H`-leg IH (via `Simple.mono`
for `H.Simple` + `subgraph_minimality` + N4 `rigidContract_isMinimalKDof`) on `sH := V(H)`, and the
G3a-transported contraction leg on `sc := (V(G)∖V(H)) ∪ {r}` — both into the **G3c-ii body-set
coupling** (not the V(·)-hardcoded G2c coupling); the contraction leg needs
`(G.rigidContract H r).Simple` from `rigidContract_simple`'s `hloop`/`hpar` (`Induction.lean`,
discharge from `G.Simple` + rigid-subgraph data, or carry green-modulo `h…` if the dichotomy resists);
then `hasFullRankRealization_of_generic` for the bare `hcontract`. **Non-simple branch:** N6a directly.

Recurring trap (FRICTION): the heavy `IsInfinitesimallyRigidOn` defeq across `ofNormals`/`withGraph`
graph-swaps (state hypotheses pre-converted); transferring `IsInfinitesimallyRigidOn` across an
`infinitesimalMotions` equality needs a `mem_infinitesimalMotions` round-trip.

*Out of 22a scope.* Track B (Case III at `d=3`) and the `d=3` assembly (the `prop:rigidity-matrix-prop11`
`hub` brick + `thm:theorem-55` flip) are deferred to **22b+** — see *Deferred to 22b+ (Case III +
assembly)* above and `notes/MolecularConjecture.md` *Phase 22* / *Phase 23* for the node plan. The cut of
22b+ into its own sub-phases happens once 22a closes.
