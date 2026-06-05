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

**Track A's reduction infra (N4), the Case-I producer bricks, N6-G1 (generic producer), N6-G2-G2a
(the conditioned-motive reduction skeleton, `theorem_55_generic`), N6-G2-G2b
(the `map`/`collapseTo` simplicity fact), and now the G2c *generic coupling producer*
`hasGenericFullRankRealization_of_couple_ofNormals` (landed 2026-06-05) are all GREEN; the
remaining red work is the N6-G3 composer assembly (build the leg data from the IH + N4 and dispatch
on `G.Simple`, discharging `theorem_55.hcontract` / `theorem_55_generic`'s `hcontractGP`).** The simple Case-I coupling (`hasFullRankRealization_of_couple_ofNormals`) is a complete
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
shape G2c/N6-G3 consume). **Remaining:** G2b → G2c → N6-G3 (or G2c+N6-G3 merged). No `\leanok` flip yet
(`lem:case-I-realization` stays red until G2c discharges `hcontractGP`); axiom-clean; no `sorry`.

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
  - [ ] **N6-G3** composer assembly — G1/G2 (incl. G2c) all green: dispatch on `G.Simple`, feed N4
    (contraction is a smaller minimal 0-dof-graph) + the two generic-motive leg IHs through
    `hasGenericRealization_transport_ends` into the G2c generic coupling
    `hasGenericFullRankRealization_of_couple_ofNormals` (then `hasFullRankRealization_of_generic` to
    land the bare `theorem_55.hcontract`; for the non-simple branch, the bare coupling / N6a directly),
    conclude `hcontract` ⟹ `lem:case-I-realization` green. **All producer bricks are green; the
    remaining content is the geometric *leg data* construction** (legs `H` / `G.rigidContract H r`,
    shared body `r`, the `V(G) ⊆ V(H) ∪ V(G/E(H))` cover, the endpoint selector `ends`, and each leg's
    `HasGenericFullRankRealization` from the conditioned IH applied via N4 / `subgraph_minimality`).
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

- **The open blocker is the N6-G3 composer assembly — the *geometric leg-data construction*. All
  producer bricks are now GREEN** (N6-G1, the transport brick, G2a `theorem_55_generic`, G2b
  `rigidContract_simple`/`map_simple`, and now G2c `hasGenericFullRankRealization_of_couple_ofNormals`).
  Everything else under Track A is green too: N4, the N5 splice/seed/rank-polynomial bricks (all-edges +
  leg-restricted), N6a, the two-motive split, (G2), the bare N6b/N6c coupling. The residual red item:
  - **N6-G3 — the composer assembly (discharges `theorem_55.hcontract` ⟹ `lem:case-I-realization`).** No
    new analytic content remains; the work is *geometric leg data*: given `H.IsProperRigidSubgraph G n` +
    `r ∈ V(H)`, exhibit (a) the two legs `GH := H` (`hGH : H ≤ G` from `IsRigidSubgraph`) and
    `Gc := G.rigidContract H r` (`hGc : Gc ≤ G` — but note the contraction *relabels* `V(H)` to `r`, so
    `Gc ≤ G` needs care; the cover may instead be stated as `V(G) ⊆ V(H) ∪ V(Gc)` with the collapse
    image `(V(G) \ V(H)) ∪ {r}` from `rigidContract_vertexSet`); (b) the shared body `c := r`
    (`r ∈ V(H)`, `r ∈ V(Gc)`); (c) a parent endpoint selector `ends`; (d) each leg's
    `HasGenericFullRankRealization` from the conditioned IH (`H` via `Simple.mono` + `subgraph_minimality`;
    `G/E(H)` via N4 `rigidContract_isMinimalKDof` + G2b `rigidContract_simple` for simplicity), transported
    by `hasGenericRealization_transport_ends`, then fed to the G2c coupling.
  - **Open sub-question (carried from G2c-open, now N6-G3's):** `rigidContract_simple`'s `hloop`/`hpar`
    hypotheses are read off the *realized* contraction — N6-G3 must discharge them from KT Lemma 6.3's
    standing setup. Decide whether they fall out of `H.IsProperRigidSubgraph G n` + `G.Simple` directly,
    or need to be carried (deferral-eligible per the green-modulo `h…` idiom). **Also re-examine the
    `Gc ≤ G` mismatch** above: the contraction is *not* literally a subgraph of `G` (it collapses
    vertices), so the G2c coupling's `hGH`/`hGc : · ≤ G` shape may need the composer to instead splice
    against a common *relabelled* parent, or the coupling restated for the collapse. This is the genuine
    remaining design question for N6-G3.
- **Track B + assembly are deferred to 22b+** (see *Deferred to 22b+ (Case III + assembly)* above), not
  open blockers for 22a: the Case II/III producer (eq. 6.12 degenerate placement, one short, + Lemma 6.10
  at `d=3`) and the `prop:rigidity-matrix-prop11` `hub` brick + `thm:theorem-55` flip. They re-enter once
  22a closes.

## Hand-off / next phase

**Clean handoff point; next agent picks up at N6-G3 (the composer assembly).** This commit landed
**G2c GREEN** — the *generic coupling producer* `hasGenericFullRankRealization_of_couple_ofNormals` in
`AlgebraicInduction.lean`: the generic sibling of `hasFullRankRealization_of_couple_ofNormals`,
identical up to the final splice, which routes the shared GP seed `q₀` through the device-free N6-G1
`hasGenericFullRankRealization_of_splice_ofNormals` (keeping general position) instead of the
device-routing bare splice. Axiom-clean (`propext`/`Classical.choice`/`Quot.sound`, all from
`classical`/`MvPolynomial`), warning- and lint-clean. **Finding:** the G2c deliverable was the missing
*producer brick*, not a wire-up — it is the connector between N6-G1 (generic producer), the transport
brick (consumes generic legs), and G2a/G2b (supply the simplicity to extract them). With it green, **all
Case-I producer bricks are green**; N6-G3 is now pure geometric leg-data construction. No `\leanok` flip
(`lem:case-I-realization` stays red until N6-G3 discharges `theorem_55.hcontract`).

**Standing discipline — blueprint exposition ledger.** When a commit
reroutes / reworks / decomposes a node that was scoped smaller (the
"thought-one-commit → rerouted" signal), add a one-line entry to
`notes/BlueprintExposition.md` naming the *stable* KT-glossed insight the
reroute surfaced. The expanded blueprint prose itself lands at **phase-close**
(once Case I is `sorry`-free), not during recon — see that file's header.
(Mechanism agreed 2026-06-04; codification of the `blueprint/CLAUDE.md`
*Proof verbosity* carve-out deferred until the principle settles.)

**Next concrete task — N6-G3: the composer assembly (discharges `theorem_55.hcontract` ⟹
`lem:case-I-realization` green, closing 22a's target).** No new analytic content remains — every producer
brick is green. The work is *geometric leg-data construction*. Instantiate `theorem_55_generic`'s
`hcontractGP` (`AlgebraicInduction.lean:2820`) and/or `theorem_55`'s `hcontract` (`:2748`): from the
proper rigid subgraph `H` (`hrig : ∃ H, H.IsProperRigidSubgraph G n`) and a representative `r ∈ V(H)`,
build the two legs `GH := H` and `Gc := G.rigidContract H r`, the shared body `c := r`, the cover, and a
parent endpoint selector `ends`; supply each leg's `HasGenericFullRankRealization` from the conditioned IH
(`H` via `Graph.Simple.mono` + `subgraph_minimality`; `G/E(H)` via N4 `rigidContract_isMinimalKDof` for
minimality + G2b `rigidContract_simple` for simplicity), transport via `hasGenericRealization_transport_ends`,
and feed the G2c generic coupling `hasGenericFullRankRealization_of_couple_ofNormals` (then
`hasFullRankRealization_of_generic` for the bare `hcontract`; the non-simple branch uses the bare coupling
/ N6a directly).

**The two genuine open design questions for N6-G3-open (Blockers has the detail):**
1. **`Gc ≤ G` mismatch.** `G.rigidContract H r` collapses `V(H)` to `r`, so it is *not literally* a
   subgraph of `G` (no `rigidContract_le` lemma exists — confirmed). The G2c/N6-G1 coupling's
   `hGH`/`hGc : · ≤ G` shape therefore does not directly fit `Gc`; the composer must either splice against
   a common *relabelled* parent (the collapse-image graph) or the coupling be restated for the collapse.
   This is the binding obstruction and the right thing to recon first.
2. **`rigidContract_simple`'s `hloop`/`hpar`** are stated against the realized contraction. Discharge them
   from `H.IsProperRigidSubgraph G n` + `G.Simple` + `E(G) ＼ E(H)` (a surviving edge with both ends in
   `V(H)` would be a `G`-edge not in `E(H)` joining two `H`-vertices — `hloop`; two surviving edges
   collapsing to the same pair — `hpar`), or carry `(G/E(H)).Simple` as a green-modulo `h…` hypothesis on
   the simple branch (dichotomy lands with Track B). G2b's positive kernel makes either route a clean assembly.

Recurring trap (FRICTION): the heavy `IsInfinitesimallyRigidOn` defeq across `ofNormals`/`withGraph`
graph-swaps (state hypotheses pre-converted); transferring `IsInfinitesimallyRigidOn` across an
`infinitesimalMotions` equality needs a `mem_infinitesimalMotions` round-trip.

*Out of 22a scope.* Track B (Case III at `d=3`) and the `d=3` assembly (the `prop:rigidity-matrix-prop11`
`hub` brick + `thm:theorem-55` flip) are deferred to **22b+** — see *Deferred to 22b+ (Case III +
assembly)* above and `notes/MolecularConjecture.md` *Phase 22* / *Phase 23* for the node plan. The cut of
22b+ into its own sub-phases happens once 22a closes.
