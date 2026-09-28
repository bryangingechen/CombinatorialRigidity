# Phase 40 — PENCIL-X0: the `X₀` formalization of the pencil conjecture (design doc)

**Status: LIVE** (opened 2026-09-25). This is the cross-phase plan for Phase 40, the
sub-lettered home in the `notes/PhaseN-design.md` pattern (`notes/CLAUDE.md`): the target, the
index of work already done, the layer plan by **stable codes**, the proof map, the risks, and the
standing constraints. Sub-phases get a letter and a work log `notes/Phase40x.md` only when they
open. **40a = SPINE2 closed 2026-09-25** (`notes/Phase40a.md`); **40b = CARRIER closed 2026-09-26**
(`notes/Phase40b.md`); **40c = FLAT closed 2026-09-26** (`notes/Phase40c.md`); **40d = BRIDGE
closed 2026-09-26** (`notes/Phase40d.md`); **STEPS runs by group: 40e = CUT/BRIDGE closed
2026-09-26** (`notes/Phase40e.md`); **40f = CONTRACT-R closed 2026-09-26** (`notes/Phase40f.md`),
one build commit from a compiler-checked recon's spike; **40g = CHAIN closed 2026-09-27**
(`notes/Phase40g.md`), two build commits from a compiler-checked recon's spike; **40h = SHORT
closed 2026-09-27** (`notes/Phase40h.md`), six build commits and a file split from a
compiler-checked recon whose new claims (MC-179)–(MC-182) were second-read first; **40i = ORBIT
closed 2026-09-28** (`notes/Phase40i.md`), three build commits from a compiler-checked recon's
sorry-free spike with no new mathematics; **40j = SPLITOFF closed 2026-09-28**
(`notes/Phase40j.md`), two build commits from a compiler-checked recon's sorry-free spike with no
new mathematics; **40k = CONTRACT-A opened 2026-09-28** (`notes/Phase40k.md`), STEPS' last group,
design-first from a compiler-checked recon's sorry-free spike with no new mathematics, B1 next. The
ORBIT recon is done (2026-09-26, §4), and so is the second reading of its new claims
(MC-173)–(MC-176). This doc
replaces the planning note `notes/pencil/X0-formalization.md` (2026-09-25), whose content moved
here and which is now a pointer. The PI's calls behind the plan are verbatim in `notes/pencil/adjudications.md`
(the 2026-09-25 entries).

**Read §2 before doing any mathematics.** Everything the route needs exists in written,
second-read form, so the job is transcription and formalization, not re-derivation.

## 1. Target and decided calls

- **The headline.** `pencil_conjecture_of_X0` (Phase 39's closing item L0, `notes/Phase39.md`
  item 0) carries two consumer-shape hypotheses. Phase 40 discharges them.
  - `X0Dist K α β` says every simple 2EC `G` with `3 ≤ |V(G)|` has
    `HasDistinctPencilRealization K 3 G`. This is (MC-157) restricted to 2EC graphs.
  - `X0Gen K α β` says the same graphs, when `PencilNondegFeasible K G` holds, have
    `HasGenericPencilRealization K 3 G`. This is (MC-133)(ii) restricted likewise.

  **Phase 40 closes** when both are theorems and a headline carrying neither has landed.
- **Field: every infinite field** (PI, 2026-09-25): `[Infinite K]`, no `CharZero`. The informal
  proof is written in characteristic 0 modulo Jackson–Jordán, and over any infinite field modulo
  (MC-33)(i) (the (MC-166) audit). SPINE2 removes the Jackson–Jordán dependence field-generally.
- **Architecture.** The simpler `pencil_conjecture_of_arms_pair` route. The landed `hK`,
  `hbareSplit`, `pencilPair_of_splitOff_of_habitat` and
  `pencil_conjecture_of_hcontract_hK_hbareSplit_of_card` are protected: not edited and not
  consumed.
- **Held, not cancelled:** the kernels (K-res)/`kres`, (K-c) and (K-bare-c) with (α), and smark's
  O7e programme. smark is paused. They are the fallback until MOTIVES lands (§6).
- **The Jackson–Jordán route is (a), the landed KT spine at `n = 2`, weakened in place** (a
  weaker hypothesis is a stronger theorem). This is SPINE2. The TR formalization, route (b), is
  fallback only.

## 2. What is already done — the index (use it; do not redo it)

| what | where | state |
|---|---|---|
| the informal mathematics, (MC-1)–(MC-178) | `notes/pencil/workbook/K-main.md` §(K-main). Steps MC1–MC9 are in that file; MC10–MC21 are one file each, `K-main-MCnn.md` (the index is in `K-main.md`). Query with `python3 notes/ledger.py --label '(MC-89)'`, `--brief …` | written; second-read (§3's proof map, column *2nd*) |
| **the proof tree of (MC-89)** | Step MC20, *Part I — the dependency tree of (MC-89)* | audited complete: every computation it consumed is replaced by a hand proof |
| **every argument leaf of (MC-89)** | (MC-166)'s *Scope* list (Step MC20) | audited characteristic-free |
| the generic and distinct motives | Step MC19: (MC-123)–(MC-130), (MC-133), (MC-157); nondegeneracy (MC-13), (MC-14) (Step MC8) | second-read 2026-09-25 |
| the certificate leaves as hand proofs over every field | Step MC20, (MC-134)–(MC-139); characteristic-2/3/5 certificates (MC-168) | second-read |
| the consumer map and the L0 spike | `notes/Phase39-design.md` § *X₀ architecture recon (2026-09-25)* (frozen archive; the spike verbatim at its end) | transcribed into Phase 39 item 0 |
| **the `n = 2` spine** | `notes/Phase39-design.md` § *`n = 2` sizing recon (2026-09-25)* (frozen archive: diffs, one new lemma, witness statements, reproduction recipe). The site list is recomputed in `notes/Phase40a.md` | **landed**, sub-phase 40a (closed 2026-09-25) |
| Jackson–Jordán beyond ℝ (fallback only) | Step MC11's companion section, (MC-33). A complete field-general write-up, one writer and not second-read, is staged unlanded in `notes/w4-pending/JJ-field-general/` (driver `w4/jjbuild.py`) | not needed on route (a); since 40a's close, the seed of the re-scoped PIN item (ROADMAP *Queued*) |
| drivers behind every figure | `notes/scripts/w4/README.md`, the *Step MCnn's drivers* bullets; commands in `notes/scripts/README.md` | the unguarded ones are listed in *Harness debt* |
| the literature, verified | `K-main.md` *Literature, checked 2026-09-24* (Crossref data): Jackson–Jordán DCG 40 (2008) and its TR; KT 2011; Crapo–Whiteley | cite from there |
| the superseded split/contract route | `notes/pencil/W4-reopen.md` (held record), `W4-reopen-archive.md`, `workbook/W4.md` | fallback only (§6) |

**Not needed on this route, whatever their state:** the open ear cell (MC-154) (Case II-cyclic);
the second proof (MC-148) and Step MC21; the ear-cell programme of Steps MC17–MC18 beyond what
the tree cites; the relative-dof conjecture (MC-23); the census (MC-7)–(MC-9), except as a
sanity check; the closed-ear span (MC-19)(c) and its hand proof (MC-134)(c), which are not in
(MC-89)'s tree (Step MC20, Part I; CHAIN's closed ear goes through CUT and BASE, 40g). Also off the
route, by SHORT's design recon (PI decision 4(b), 2026-09-27):
- the chord gadget (MC-44);
- the `k = 4` collision lemma (MC-136) and the 2-ear gadget (MC-24);
- the exact (MC-17);
- (MC-134)(b) at `k = 3, 4`.

The `k = 3, 4` steps are (MC-181) and (MC-180), found by formalization. (MC-45)'s proof of the step
and (MC-26)'s links are superseded on the route too; they all stay proved. By SPLITOFF's design
recon (2026-09-28), (MC-31)'s bound within one for `δ ≤ 4` is off the route as well: no step
consumes it, and a remark in `thm:pencil-x0-splitoff` records it. By CONTRACT-A's design recon
(2026-09-28; the coordinator's call 8, `notes/Phase40k.md`), so are (MC-67), (MC-68) and (MC-70):
- the step consumes (MC-69)(a) as an inequality, (MC-69)(b) and (MC-71), and its proof replaces
  (MC-68)(d)'s core-freeness (§3 STEPS, the CONTRACT-A entry);
- its additivity hypothesis comes from (MC-87) at (MC-89)'s step 5, and (MC-87)'s proof uses (MC-76)
  and (S), citing no (MC-67); (MC-89) itself does not use (MC-70)'s exceptional case.

Caveat: the second reader's independent cross-check (MC-119)/(MC-120) (Step MC16 §7) uses
(MC-67)(a)–(c), so (MC-67) returns if COVERAGE ever takes that route.

## 3. Layer plan (stable codes) and the proof map

Layers are listed in dependency order. A letter is minted when a layer opens as a sub-phase.
Adjacent layers may share a sub-phase, and the grouping is decided at each open. The *labels*
column is the proof map: claims in proof order, their step, and their second-reading state.
Briefing a layer takes one call, `python3 notes/ledger.py --brief <labels>`.

### SPINE2 — the KT spine at `n = 2` → **sub-phase 40a, ✓ closed 2026-09-25** (`notes/Phase40a.md`)

**Done.** A structural edit of landed chapters: `6 ≤ Graph.bodyBarDim n` weakened to `3 ≤ …` (and
`hd : 3 ≤ n` to `2 ≤ n`) in place, and the `|V| = 3` triangle case of
`case_III_hsplit_producer_all_k` repaired. That gives `rankHypothesis_of_theorem_55_gen` and
`molecular_conjecture` at `n = 2`, and the generic-normals row rank at `(n, k) = (2, 1)`, all over
every infinite field, plus the non-spanning row-rank form BRIDGE consumes
(`PanelHingeFramework.finrank_span_rigidityRows_genuine_recordsLinks_of_theorem_55_gen`). KT 2011
fixes `d ≥ 2` throughout (p. 651, checked against the local text). The planar corollary is
Jackson–Jordán's pin-collinear theorem (*Discrete Comput. Geom.* 40(2) (2008) 258–278); at 40a's
close the PI re-scoped the queued PIN item to a second, independent proof by their route (ROADMAP
*Queued*).

### CARRIER — planar pictures, `L(q)`, `X₀` and "the generic point attains" → **sub-phase 40b, ✓ closed 2026-09-26** (`notes/Phase40b.md`)

**Done.** (MC-1)–(MC-3) are formalized in `Molecule/Pencil/MainComponent/Carrier.lean` and (split out
2026-09-27, below) `Configuration.lean`: admissible
pictures, `L(q)` and `Aff(q)`, `U` (nonempty and Zariski-open, `Graph.exists_mvPolynomial_isMainPicture`),
the `cross₃` picture→normal map, `Graph.X0Attains` and its one-witness upgrade
`Graph.x0Attains_of_exists` (`Carrier.lean`), the configuration as a pencil realization with the
`X0Dist` leg `Graph.X0Attains.hasDistinctPencilRealization` (`Configuration.lean`), (MC-3)'s
scale-and-shift rank invariance, and the
fibre-intersection lemma `MvPolynomial.exists_mem_eval_ne_zero₂`; DUAL-K made the polarity
field-general (§4). (MC-2)'s vector bundle and its irreducible closure are never formed:
`thm:pencil-x0-main-component` is green at its formalized content, with the geometry in
`rem:pencil-x0-main-component`; (MC-3)'s augmented-matrix rank split has no Lean object and is the
remark `rem:pencil-hinge-affine`. (MC-10)(a) moved to COVERAGE. The accepted design (uncurried
pictures, a single `X0Attains`, the β-headroom `_of_card` triple) and every decision are in
`notes/Phase40b.md`. **`Carrier.lean` split 2026-09-27** (before 40h's B3, PI decision 5;
`notes/Phase40h.md`), at 1 496 lines (40f's build added the lifting system with weights), the
~1500-line tripwire: along its section headers, the picture-to-normal API, its polynomial mirror,
the configuration as a pencil framework, the scale-and-shift invariance and the linear pencil
condition (CARRIER's C3–C5′) moved to new `Configuration.lean`; C1–C2 (admissible pictures, `L(q)`,
`Aff(q)`, `U`, `X0Attains`, `x0Attains_of_exists`) stayed in `Carrier.lean`, where 40h's locality
lemmas landed beside `liftingSpace` and `IsAdmissiblePicture` (890 lines at 40h's close).

### FLAT — the flat rank → **sub-phase 40c, ✓ closed 2026-09-26** (`notes/Phase40c.md`)

**Done.** (MC-4)(a)–(c) and (MC-5)(i)–(iii) are formalized in `Molecule/Pencil/MainComponent/Flat.lean`
and `Molecular/Deficiency.lean` (`main-component.tex` §`sec:main-component-flat`, and
`lem:deficiency-antitone`), transcribed from `ledger.py --brief '(MC-4)' '(MC-5)'` at the open. The
compiler-checked recon's route: the flat (primal) side through C4's rewrites, the split as the linear
equivalence `flatScrewEquiv`, (MC-4)(a) as an exact identity, (MC-4)(b) as the grade-1 relative
bound at the normals `(x_v, y_v, 1)` (BRIDGE's first bullet, folded in), (MC-5)(i) in antitone form,
and the flat witness `Graph.x0Attains_of_finrank_liftingSpace_le`. 40a's pin debt was paid on the
new node `lem:relative-deficiency-rank-bound`. The citations for `Φ` are Crapo–Whiteley 1982
Example 4.4 (pp. 72–73) and Whiteley 1996 §8.3, with no identity attributed; the codim bound
`dim L(q) ≥ 3|V| − 2|E|` stays dropped (no consumer; a corollary of (MC-4)(b)). Every decision is in
`notes/Phase40c.md`.
- [ ] **Cleanup-round item (tracked here): the wider stand-in audit.** About 28 other
  `lem:trivial-motions-rank-bound` reference sites in ten `.tex` files, against about 15 Lean
  call sites of the row-span bound (`GenericLift/{PanelGeneric,HingeGeneric}`, `CaseI`,
  `CaseII`, `CaseIII/Realization`, `Theorem55`, `Theorem56`, `Pencil/{Pair,Arms,TwoCut,X0,Steer}`;
  `generic-lift.tex` uses `prop:rigidity-matrix-prop11` as its stand-in). Repoint each site
  that means the relative bound (`lem:relative-deficiency-rank-bound`). Not a Phase-40 layer.

### BRIDGE — Jackson–Jordán's equality, as it is consumed → **sub-phase 40d, ✓ closed 2026-09-26** (`notes/Phase40d.md`)

**Done.** The equality `dim L(q) = 3 + def₂(G)` at the generic picture is formalized in
`Molecule/Pencil/MainComponent/Bridge.lean` (`main-component.tex` §`sec:main-component-jj`) for
every simple `G` with at least one body and `|N[v]| ≥ 3` at every body, anywhere in `α`, `β`, over
every infinite field, with no hypothesis on `β` and no connectivity. SPINE2 supplies the form of
(MC-33) the proof uses; the informal record is (MC-172) (Step MC11). The consumer forms are the
generic form `Graph.exists_mvPolynomial_finrank_liftingSpace_eq` (one nonzero polynomial in the
ambient picture coordinates `α × Fin 2` whose non-roots are main pictures at `3 + def₂`), the `ℓ₀`
form `Graph.IsMainPicture.finrank_liftingSpace_eq` and the existential form; with FLAT,
`Graph.x0Attains_of_deficiency_two_eq_three` (`cor:pencil-jj-flat`, (MC-89)'s step 3). The recon's
chart route: per-body rescaling moves a common non-root of SPINE2's rank polynomial, the
general-position polynomial and `∏ n(a, 2)` into the chart `(x_v, y_v, 1)`, where FLAT's bridge
reads the rank; only that chart-rank form carries SPINE2's `hfresh`, and the equality first
relabels the edges into `β ⊕ Fin (3|α| + 1)` (`Graph.embedEdges`), where
`Graph.freshEdgeSupply_of_card_lt (n := 2)` supplies it. The route never forms `IsGenericNormals`,
so the total-selector open point dissolved. Every decision is in `notes/Phase40d.md`.
- **The consumer map, for STEPS** (the recon's, derived against the definition bodies; each
  consumer multiplies the polynomials). At `G`: the existential form, through `cor:pencil-jj-flat`.
  At `H = G[W]` (both kinds of CONTRACT): the generic form at `q ∈ U(G)` and at the magnified core
  picture, and FLAT through the corollary (`def₂(H) = def₃(H) = 0`). At
  `G/H = G.rigidContract (G.induce W) r`, `r ∈ W`: the `ℓ₀` form at the contracted picture;
  `rigidContract` keeps parallel edges, as the informal `G/H` does, and its simplicity needs `H`
  induced (`K₄` contracted at a triangle is the recon's witness). At `G′ + ab`, `a ≁ b`: the generic
  form at `q ∈ U(G′)`. At `G″ = G.splitOff x a b e₀`, `a ≁ b`: the generic or `ℓ₀` form. Finding 4
  (no admissible picture without `|N[v]| ≥ 3`) bites at `G/H`'s contracted vertex (`|δ(W)| ≥ 2`,
  from 2EC; already in (MC-37)'s second reading). STEPS may also use the equality at `G`. The open
  questions of these uses are §3 STEPS's three items *Tracked from BRIDGE's design recon* (the
  slice `q′ = (q_O, Q)`, the simplicity of `G/H`, `h3` from (H)); the label-reuse sources are in
  §3 MOTIVES's β-headroom bullet.
- [ ] **Cleanup-round item (post-Phase-40): the edge-restricted, non-spanning generic-normals row
  rank**, together with the optional re-base below. It is off every consumer path. The recon
  compiled it as three declarations (in `GenericLift/PanelGeneric.lean`):
  - **The headline** `finrank_span_rigidityRows_ofNormals_of_isGenericNormals_of_recordsLinks`. It
    has the conclusion of `finrank_span_rigidityRows_ofNormals_of_isGenericNormals` with three
    hypotheses changed: no `[Nonempty α]`, no `hspan : V(G) = Set.univ`, and the total selector
    `hends : ∀ e, G.IsLink e (ends e).1 (ends e).2` weakened to
    `∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2`. Its proof is the landed pinch,
    with SPINE2's non-spanning producer
    `finrank_span_rigidityRows_genuine_recordsLinks_of_theorem_55_gen` as the witness in place of
    the spanning `rankHypothesis_genuine_recordsLinks_of_theorem_55_gen`, which gives the witness
    rank directly.
  - **`supportExtensor_ofNormals_ne_zero_of_isGenericNormals_of_ne`.** This is the seed argument
    of `supportExtensor_ofNormals_ne_zero_of_isGenericNormals`, which uses the graph only for
    `(ends e).1 ≠ (ends e).2`. It is restated per edge, under that hypothesis alone.
  - **`exists_independent_normalRow_of_le_finrank_of_recordsLinks`.** This is the transplant
    `exists_independent_normalRow_of_le_finrank` with the edge-restricted selector. It keeps, and
    also returns, the extraction's first conjunct: the extracted indices are links
    (`exists_independent_panelRow_subfamily_of_le_finrank`). So the per-edge sign comparison runs
    only at links.
  - In the headline, that link conjunct puts each extracted row among the rigidity rows
    (`panelRow_mem_rigidityRows_of_link`). The upper bound
    (`finrank_span_rigidityRows_add_deficiency_le`) needs the per-edge nondegeneracy only at links.
  - It lands either as an in-place weakening (call sites: `HingeGeneric.lean` ×2, `Steer.lean` ×1,
    the rigid corollary `isInfinitesimallyRigidOn_ofNormals_isGenericNormals_iff`, and
    `generic-lift.tex`'s `thm:panel-generic-rank`) or as an additive successor.
  - **The optional re-base, routed here from 40a (Slice 4); not taken in 40d**, since the chart
    route never touches the spanning producer. The spanning
    `PanelHingeFramework.rankHypothesis_genuine_recordsLinks_of_theorem_55_gen` is a ~10-line
    corollary of the SPINE2 row-rank form (fable-spike-checked, not landed), and its `[Nonempty α]`
    is unnecessary. Its consumers are the generic-normals and generic-hinge row ranks
    (`GenericLift/{PanelGeneric,HingeGeneric}.lean`) and `Molecule/Theorem56.lean`.

### STEPS — the local steps of the induction → by group; **CUT/BRIDGE = sub-phase 40e, ✓ closed 2026-09-26** (`notes/Phase40e.md`); **CONTRACT-R = sub-phase 40f, ✓ closed 2026-09-26** (`notes/Phase40f.md`); **CHAIN = sub-phase 40g, ✓ closed 2026-09-27** (`notes/Phase40g.md`); **SHORT = sub-phase 40h, ✓ closed 2026-09-27** (`notes/Phase40h.md`); **ORBIT = sub-phase 40i, ✓ closed 2026-09-28** (`notes/Phase40i.md`); **SPLITOFF = sub-phase 40j, ✓ closed 2026-09-28** (`notes/Phase40j.md`); **CONTRACT-A = sub-phase 40k, open** (`notes/Phase40k.md`)

**CUT/BRIDGE done** (40e). The "if" halves of (MC-52) and (MC-53) are formalized in
`Molecule/Pencil/MainComponent/Cut.lean` (`main-component.tex` §`sec:main-component-cut`):
`Graph.X0Attains.of_cutVertex` and `Graph.X0Attains.of_bridgePath` (a chain of `k + 1` bridges, any
`k ≥ 0`, by explicit path hypotheses), over (H) as `Graph.IsX0Graph`. The cut-vertex laws are
`Graph.deficiency_add_le_of_cutVertex` / `_eq_add_of_cutVertex` (`Deficiency.lean`) and
`BodyHingeFramework.finrank_span_rigidityRows_cutVertex_eq` (`Bricks.lean`). BRIDGE counts along the
path with the pendant-body rank law `BodyHingeFramework.add_le_finrank_span_rigidityRows_induce_union_singleton`
(`Bricks.lean`) and Phase 39's `Graph.deficiency_induce_union_singleton`. Both fibre lemmas need no
admissibility: extend along the one body where a piece is attached. An `X0Attains` induction along
the path is impossible (a peeled body has no admissible picture), so BRIDGE cuts once at the last
bridge and telescopes. Every decision is in `notes/Phase40e.md`; the table below stays as the proof
map for the later groups.

**CONTRACT-R done** (40f). (MC-59)(d) with (MC-39) and its side claims is formalized in
`Molecule/Pencil/MainComponent/Contract.lean` (`main-component.tex` §`sec:main-component-contract`):
`Graph.X0Attains.of_rigidContract`, at an induced core `H = G[W]` with `def₂(H) = 0` and no
outside body adjacent to two core bodies, in a 2EC `G` satisfying (H), from `X₀(G/H)` attaining
alone. The picture moves along the curve `q(t)` that shrinks the core to `r`'s picture point; the
heights are solutions of the rescaled lifting system `M(t)`, whose kernel does not jump at `t = 0`;
every solution is flat on the core, so the core's rank is its flat rank and no attainment at `H` is
needed. The general pieces sit beside their definitions: `Graph.weightedLiftingMatrix`
(`Carrier.lean`), `Graph.connected_of_isKDof_zero` (`Deficiency.lean`), the projected rank
polynomial nonzero at its witness (`CaseI.lean`) and the block coupling (`Coupling.lean`, with a
mirror lemma). Every decision is in `notes/Phase40f.md`.

**CHAIN done** (40g). BASE and (MC-20), open and closed, are formalized in
`Molecule/Pencil/MainComponent/Chain.lean` (`main-component.tex` §`sec:main-component-chain`):
`Graph.X0Attains.of_cycle` (a cycle as the edge `ab` plus the path `a…b`, `k ≥ 1`, no (H)),
`Graph.X0Attains.of_openEar` (`k ≥ 5`, `a ≠ b` in `V₁`, `a ∼ b` allowed) and
`Graph.X0Attains.of_closedEar` (`k ≥ 2`), in 40e's explicit-path format, with (H) at `G` only and
attainment at `G[V₁]` (stronger than the workbook, which also asks (H) at `G′`). The rank side is
B5′/B6′ over any two link-partitioning graphs (`Bricks.lean`; B5/B6 are their induced corollaries),
the path's rank and relative screws (MC-177)(i)(ii) and the ear rank law
`BodyHingeFramework.finrank_span_rigidityRows_ear_eq`, which holds at every adjacency (`Ear.lean`);
the deficiency side is (MC-17)'s lower half, `Graph.deficiency_induce_add_le_of_ear`. (MC-19)(b)'s
"for any flag pair" is replaced by a witness inside the fibre: the height `1` at two middle bodies
and `0` elsewhere lies in `L_G(q)` at every admissible picture, and the hexagon of (MC-134)(a) at a
collapsed picture (`p_a = p_b`) makes six ear joins independent (`k ≥ 4` for the witness, `k ≥ 5`
for six edges). The closed ear is `of_cutVertex` plus `of_cycle`, reusing the ear's labels;
(MC-21)(a)'s class theorem stays unstated (`rem:pencil-x0-ear-class`, PI decision 4). Neither
step-contract prerequisite was built (the step contract, below). `Bricks.lean`'s file-size plan is
now a tracked item of the SHORT entry below. Every decision is in `notes/Phase40g.md`.

**SHORT done** (40h). The open-ear steps with two, three and four interior bodies, the ends possibly
adjacent, are formalized in `Molecule/Pencil/MainComponent/Short.lean` (`main-component.tex`
§`sec:main-component-short`), over the line geometry (MC-179) in `Lines.lean` and the ear data over
fixed base data in `EarGen.lean`. `Graph.X0Attains.of_openEar_two` is (MC-54) at `k = 2`, under
`def₃(G[V₁]) ≤ def₃(G)` (PI decision 4(a)). `…_four` and `…_three` are (MC-180) and (MC-181), from
attainment at `G[V₁]` and at `G″ = G.splitOff (x 1) (x 0) (x 2) (e 1)`. (H) is asked at `G` only.
The count uses (MC-182) (`Graph.splitOff_deficiency_le_of_eq_left`) and the landed
`Graph.deficiency_induce_add_le_of_ear`; `Graph.deficiency_induce_le_of_ear_of_merge` is COVERAGE's
bridge from `δ = 0` to `k = 2`'s `hdef`. The route as landed:
- **`k = 2` (B5) is CHAIN's one-picture route, not EARGEN's.** The heights `0` lie in every
  `L_G(q)`. At a non-admissible picture putting `a, x₁, x₂, b` at `Y₄, Y₅, Y₀, Y₁`, the three ear
  joins are three joins of (MC-134)(a)'s closed hexagon (the hexagon witness). The route note's
  `certSquare` witness was wrong: its `Y₂`, `Y₃` sit at height `1`.
- **`k = 3, 4` (B6, B7): the base data first, then two rounds of genericity.** The base data are
  (MC-180)'s Steps 1–2, as `Graph.exists_earBase_splitOff`. Round 1 takes ear data (`G″` does not
  read `x₂`'s coordinates) where `G″` has its target rank and an admissible picture. At `k = 4` the six joins of `x₁, x₃, x₄, b`
  must also span `Λ²K⁴`, certified at one exhibited ear datum (`linearIndependent_tetra_witness`)
  through the span transfer, not by Step 4's determinant affine in `x₃`'s height. At `k = 3`, Case
  A's `⟨c, y₁ ∧ y₃⟩ ≠ 0` is written as a span bound. Round 2 takes `G`'s ear data off the bound
  `dim(ρ + Λ) ≥ min(dim W + 1, 6)` at the reinserted point and off `G`'s main-picture polynomial.
- **The collision witness (B6, reused by B7).** The span transfer asks no nonzero hinge at its
  witness. So when `W = Λ²K⁴`, `x₂` is put back at the point of `x₁`, a vanishing hinge, in place
  of Step 3's use of (MC-179)(d)'s "at least `dim W`" half at all but finitely many `t`. The
  attaining configuration comes from round 2. The uniqueness of `h_a`, `h_b` is not used.
- **Placement** (PI decision 5): `Carrier.lean` split first (new `Configuration.lean`); the
  locality lemmas in `Carrier.lean`, the `pointJoin` lemmas in `Flat.lean`, `relScrews_congr` in
  `Bricks.lean`, `finrank_span_rigidityRows_congr` in `Pinning.lean`, the meet-to-join transport in
  `Ear.lean`, `pathEdge_injective` in `Cut.lean`. Every decision is in `notes/Phase40h.md`.

**ORBIT done** (40i). The open-ear steps with one interior body, and with two with no bound on the
deficiency, both at non-adjacent ends and under `deficiencyMerged₂(G[V₁]; a, b) + 2 ≤ def₂(G[V₁])`,
are formalized in `Molecule/Pencil/MainComponent/Orbit.lean` (`main-component.tex`
§`sec:main-component-orbit`). `Graph.X0Attains.of_openEar_one` is (MC-54) at `k = 1`, under
`def₃(G[V₁]) ≤ def₃(G)` (PI decision 4(a)); `Graph.X0Attains.of_openEar_two_of_splitOff` is
(MC-176), from attainment at `G[V₁]` and at `G₁ = G.splitOff (x 1) (x 0) b (e 1)`, `G` with `x 1`
suppressed. (H) is asked at `G` only. The merged deficiency is Phase 39's A2 carrier, pinned on
`def:deficiency-merged`, and (MC-175)(iii)'s `≤` half is
`Graph.splitOff_deficiency_add_le_of_deficiencyMerged`. The route landed as the recon's:
- **U2 and (MC-174) run on the lifting system's kernel.** U2 is rank–nullity,
  `Graph.two_le_finrank_map_planeDiff` (`Carrier.lean`); (MC-174) is `exists_incidence`, its family
  restricted to `w ∈ K z₀`.
- **One base for both cells**, `Graph.exists_oneEar_base`: the ear body's picture is chosen jointly
  with a kernel point of `G′`, so neither step has the STEPS contract's one-picture shape. `k = 1`
  then needs one picture and the ear rank law; `λ₁ = 2` ((MC-169)) is automatic by admissibility.
- **`k = 2`**: the base at `G₁`, a second fibre intersection for `G₁`'s attainment, then (MC-173) in
  existence form (`exists_insertion_two`, `Lines.lean`, polynomial-free) and EARGEN's span transfer
  for the open condition, as `of_openEar_four` does. The count is (MC-175)(i)(ii), the landed
  `Graph.splitOff_deficiency_le_of_eq_left` and `Graph.deficiency_induce_add_le_of_ear`. Off route:
  (MC-173)'s chart polynomial, (MC-48)(i)/(iii), `Graph.exists_earBase_splitOff` and the
  `pointJoinFramework` instantiation (the ear law is applied at `(ofNormals …).toBodyHinge`).
- **Placement** (PI decision 5's convention): the steps and `Graph.splitOff_oneEar`,
  `splitOff_ear_two{,_simple}` in the new `Orbit.lean`, which imports `Short.lean` (for
  `induce_splitOff_ear`, `Graph.isLink_update_splitOff`, and `EarGen.lean` with it); the general
  pieces beside their definitions in `Induction/SplitOffDeficiency.lean`, `Carrier.lean`,
  `Flat.lean`, `Lines.lean` and `Induction/Operations.lean`. Every decision is in
  `notes/Phase40i.md`.

**SPLITOFF done** (40j). The split-off step at a body `x 0` of degree two whose neighbours `a ≁ b`,
the one-body ear `a − x 0 − b` on `V₁`, under `deficiencyMerged₃(G[V₁]; a, b) + 5 ≤ def₃(G[V₁])`,
is formalized in `Molecule/Pencil/MainComponent/SplitOff.lean` (`main-component.tex`
§`sec:main-component-splitoff`). `Graph.X0Attains.of_splitOff` is (MC-31)'s `δ ≥ 5` conclusion,
from attainment at `G″ = G.splitOff (x 0) a b (e 0)`, `G` with `x 0` suppressed. `hδ` is literally
Step MC11's `δ ≥ 5` (40i's `hδ₂` precedent: `pairDelta` unfolds to `deficiency − deficiencyMerged`,
`deficiency_weldPair_eq_deficiencyMerged` gives `def₃(G′/ab)`, and `bodyBarDim 3 = 6`). There is no
`ℓ₀(G″)` hypothesis: BRIDGE discharges it inside the step. (H) is asked at `G` only. The route
landed as the recon's:
- **(MC-28) is a count of motion spaces**, not the ear rank law:
  `Graph.finrank_span_rigidityRows_splitOff_special`, through
  `BodyHingeFramework.finrank_span_rigidityRows_eq_add_of_motions` (`Ear.lean`). At normals with
  `n_x = (1 − s) n_a + s n_b`, `s ≠ 0, 1`, the motions of `G` are those of `G″` with
  `S_x − S_a ∈ K·C_ab`, of codimension `D − 1`.
- **(MC-29) is one inequality**, `def₃(G″) + 1 ≤ def₃(G)`: the landed
  `Graph.splitOff_deficiency_add_le_of_deficiencyMerged` and `Graph.deficiency_induce_add_le_of_ear`
  composed, with `def₂(G″) ≤ def₂(G)` from `Graph.splitOff_deficiency_le_of_eq_left`. The reverse
  inequalities and the `[δ₂ ≥ 2]` equality are off route.
- **(MC-30)(i) runs on the lifting system's kernel** (`Graph.planeDiff_eq_zero_of_splitOff`), a
  dimension count against Jackson–Jordán at `G″`, FLAT at `G` and `def₂(G″) ≤ def₂(G)`. `G′` may
  have bodies of degree 1 (at `C₇`, `G′ = P₆`), so the workbook's `F(G′, q′)` is that kernel, not
  `L_{G′}`, and ORBIT's `two_le_finrank_map_planeDiff` (which needs `G′` admissible) is not reused.
- **(MC-30)(ii), (iv) and (MC-31): one curve, ending at the general picture.** One `s` off a finite
  set, then a polynomial line `y₀ + t·w` of flexes of `G′` (`exists_mem_forall_add_smul_eq_zero`,
  an explicit construction: the workbook's rational `P(t)` times a scalar nonzero at `t = 0`), with
  `x`'s picture moved from the special point to its generic one. The special point is not
  admissible, so the curve is necessary. Main-ness along it is `G`'s main-picture polynomial on the
  picture line, nonzero at `t = 1`, in place of (★) with (MC-4)(b), and the semicontinuity is the
  curve-limit lemma `PanelHingeFramework.finite_setOf_finrank_lt_of_curve` (`Bridge.lean`); then
  `Graph.x0Attains_of_exists`. Off route: (MC-30)(iii), and (MC-31)'s bound within one for `δ ≤ 4`
  (a remark in the theorem node): by (MC-79)(v) a `k = 1` chain with `1 ≤ δ ≤ 4` is unusable, and
  `δ = 0` is ORBIT's `of_openEar_one`.
- **Placement** (the recon's table; the coordinator's reading of PI decision 5's convention, which
  the PI may reverse at the cost of moving a few declarations): the step and its SPLITOFF-specific
  pieces in the new `SplitOff.lean`, importing only `Orbit.lean`; the curve-limit lemma in
  `Bridge.lean`, the motion count and `Graph.mem_liftingSpace_oneEar` in `Ear.lean`,
  `span_supportExtensor_ofNormals_eq` in `Cut.lean`, the two kernel lemmas in `Carrier.lean`, and the
  mirror `MvPolynomial.polynomial_eval_aeval`. No fragile-zone file is touched, nor `Contract.lean`,
  `Bricks.lean` or `Short.lean`. Every decision is in `notes/Phase40j.md`.

| step of (MC-89) | labels, in proof order | 2nd |
|---|---|---|
| CUT / BRIDGE | (MC-52), (MC-53), (MC-55)(ii), (MC-56) | ✓ (MC14) |
| BASE `C_n` | (MC-16) (closed chain), (MC-17), (MC-19)(a) → (MC-21)(a); certificate (MC-134)(a) | ✓ (MC10, MC20) |
| chains `k ≥ 5` | (MC-18)(a), (MC-16), (MC-17), (MC-19)(b) → (MC-20); cert. (MC-134)(b) | ✓ |
| chain `k = 4` | (MC-180) ← the antecedent `G′ + ear₃` (`G.splitOff (x 1) …`), (MC-179)(a), (d), (MC-182), (MC-16) in rank form, (MC-18)(a), (MC-17)'s separated count *(since 2026-09-27; (MC-24)/(MC-25) with (MC-136) off the route)* | ✓ (MC13, 2026-09-27; found by formalization the same day) |
| chain `k = 3` | (MC-181) ← the antecedent `G′ + ear₂`, (MC-179)(b)–(d) ((c) = (MC-135)(ii)'s `k = 2` step with (MC-47)(i)'s span identity), (MC-182), (MC-16) in rank form, (MC-18)(a), (MC-17)'s separated count *(since 2026-09-27; (MC-45)'s `r`-split off the route)* | ✓ (as `k = 4`) |
| chain `k = 2`, `a ≁ b`, `δ₂ ≥ 2` | (MC-176) ← the refined link (MC-173), the parametrized incidence (MC-174) ((MC-18)(b)'s form), (MC-175)(i)(ii), (MC-16) at `k = 1, 2`, (MC-18)(a)/(b)'s fibre identifications, (MC-169); orbit (i) and `dim U ≥ 2` by (MC-48)(ii)'s argument under `δ₂ ≥ 2` ((MC-175)(iii), (MC-4)(b), Jackson–Jordán at `G′ + ab` = (MC-172)). (MC-46)/(MC-138) superseded on route (2026-09-26); (MC-177) is (MC-16)'s rank form. **(MC-173) is consumed in existence form** (its four curves, as the insertion lemma `lem:pencil-insertion-two`), and **its chart polynomial is off route**: EARGEN's landed span transfer supplies the open condition (40i's design recon, 2026-09-28; ORBIT entry below) | ✓ (MC13, 2026-09-26; found by formalization the same day) |
| chain `k ≤ 2`, `δ = 0` | (MC-54) ← (MC-19)(b), (MC-18)(a)/(b), (MC-16); the Lean hypothesis is `def₃(G′) ≤ def₃(G)` (PI decision 4(a), 2026-09-27); `k = 1` with (MC-174) and (MC-48)(ii) goes to ORBIT (40i) | ✓ (MC14) |
| SPLITOFF (`k = 1`, `δ ≥ 5`) | (MC-28), (MC-29), (MC-30)(iv) → (MC-31); Jackson–Jordán at `G″`. **(MC-30)(i) runs on the lifting system's kernel** (`G′` may have bodies of degree 1), **(MC-30)(ii)'s rational curve is a polynomial line** of flexes and pictures, and (MC-31)'s semicontinuity is the curve-limit lemma; only (MC-31)'s `δ ≥ 5` conclusion is on route, its bound within one for `δ ≤ 4` off it (40j's design recon, 2026-09-28; *SPLITOFF done* above) | ✓ (MC11) |
| CONTRACT | (MC-34)–(MC-38) → (MC-39); (MC-59)(b), (c1)–(c3) → (MC-59)(d) | ✓ (MC12, MC14) |
| CONTRACT-A (additive core) | (MC-35), (MC-36), (MC-37) steps 2–3, (MC-69)(a) as an inequality, (MC-69)(b) (the chain and its by-product `S ⊆ T`) → (MC-71); Jackson–Jordán at `H` and `G/H`. **(MC-68)(d)'s core-freeness and (MC-38)'s dominance are replaced** by `S ⊆ T`, two open conditions in `ker M(0)` and a collineation; (MC-67), (MC-68) and (MC-70) are off route (40k's design recon, 2026-09-28; the CONTRACT-A entry below) | ✓ (MC15, MC12) |
| THETA | (MC-21)(b) ← (MC-21)(a), (MC-20), and (MC-139); **dissolves into COVERAGE** (PI decision 3, 2026-09-27): no named theorem, a remark | ✓ (MC20) |

- **Lean reuse.** The deficiency laws `rigidContract_deficiency_eq`,
  `deficiency_eq_of_cutEdges_ncard_le_one`, `removeVertex_deficiency_ge`,
  `deficiency_le_deficiency_of_le_vertexSet_eq`, and Phase 39 item 6's Layers A–C: the vertex
  2-cut law `deficiency_eq_of_vertexTwoCut`, the gluing identity
  `finrank_span_rigidityRows_vertexTwoCut_eq`, and the loss carriers in
  `Molecule/Pencil/TwoCut.lean`.
- **The cut-vertex deficiency law landed in 40e** (`lem:deficiency-cut-vertex`, in
  `Deficiency.lean`). Its proof consumes item 6's A4 split `partitionDef_split_of_vertexTwoCut` at a
  repeated vertex, which 40e pinned. Item 6's other leaves have no blueprint nodes (Phase 39's D5
  debt); STEPS pins each when it consumes it (40g pins `relScrews`, `jointRows` and B5/B6).
- **The step contract** (the STEPS pre-build recon, 2026-09-26; compiled end to end at CUT and at a
  single bridge, `notes/Phase40e.md`). Every step is `G.X0Attains K` from `Gᵢ.X0Attains K` at
  smaller graphs `Gᵢ : Graph α β` (same `α`, same `β`), with (H) at `G` (`Graph.IsX0Graph`: simple,
  connected, degree `≥ 2`) and structural hypotheses. The proof picks one picture generic for every
  `Gᵢ` and main for `G`, chooses heights inside the one fibre `L_G(q)`
  (`MvPolynomial.exists_mem_eval_ne_zero₂`), and ends at `Graph.x0Attains_of_exists`.
  - No step consumes more than attainment at smaller graphs satisfying (H), Jackson–Jordán at named
    graphs (a theorem since 40d) and structural facts. COVERAGE is a plain strong induction on
    `V(G).ncard`; no `Covered` predicate is needed.
  - (H) is the carried predicate, and every consumed graph satisfies it ((MC-55)(i)). 2EC is not
    carried: it is CONTRACT's step hypothesis (for `h3` at `G/H`), which COVERAGE supplies from
    2-connectivity at (MC-89)'s step 4.
  - Every consumed graph reuses labels: `splitOff` with a freed label, `G′ + ab` by relinking a
    chain edge, `G/H` keeping its own. So **STEPS forces no `β`-headroom** (§3 MOTIVES).
  - The STEPS recon expected the ear steps to need picture locality (`L`, admissibility, main-ness
    and rank read the picture only on `V(Γ)`; the rank half is 40e's
    `finrank_span_rigidityRows_ofNormals_congr`) and main-picture propagation (admissible with
    `dim L ≤ 3 + def₂` is main). **CHAIN's design recon (2026-09-27) found neither needed** by CHAIN,
    CUT/BRIDGE or CONTRACT-R: every step picks its picture as one common non-root over all of
    `α × Fin 2`, and `X0Attains` gives attaining heights at every non-root without main-ness.
    Neither was built then. **SHORT (40h) built the two locality lemmas**,
    `Graph.liftingSpace_congr` and `Graph.isAdmissiblePicture_congr` (B3–B4,
    `lem:pencil-picture-local`), beside their definitions in `Carrier.lean` (PI decision 5).
    Main-picture propagation is still unbuilt, and none of ORBIT, SPLITOFF and CONTRACT-A needs it
    (their design recons, 2026-09-28; SPLITOFF and CONTRACT-A take main-ness along their curves from
    `G`'s main-picture polynomial). For whichever later layer needs it, the compiled
    signature (proof in `scratch/40g/S40gPrereq.lean`, local to the recon's checkout; five lines from
    FLAT's `three_add_deficiency_le_finrank_liftingSpace`, no Jackson–Jordán):
    - `Graph.IsAdmissiblePicture.isMainPicture_of_finrank_le [Finite α] [Finite β] {G : Graph α β}
      {q : α × Fin 2 → K} (hq : G.IsAdmissiblePicture q) (hV : V(G).Nonempty)
      (hdim : (Module.finrank K (G.liftingSpace q) : ℤ) ≤ 3 + G.deficiency 2) : G.IsMainPicture q`.
- **The provisional grouping** (PI, 2026-09-26, "Accept"; codes until each opens, letters minted
  only then; `notes/pencil/adjudications.md`). In dependency order, with build-commit estimates:
  - **CUTBRIDGE = 40e, ✓ closed**: (MC-52), (MC-53). Estimated 3–4; took three builds and a recon.
  - **CONTRACT-R = 40f, ✓ closed** (`notes/Phase40f.md`), the `def₂`-rigid core: (MC-34)–(MC-39),
    (MC-59). Estimated 6–9; the design recon (opus, 2026-09-26) returned the whole step as one
    sorry-free spike, and it landed as one build commit (`e267d5fc`). The route is in *CONTRACT-R
    done* above; unlike the step contract, the picture moves along a curve and
    `exists_mem_eval_ne_zero₂` is not used.
  - [ ] **Tracked todo, carried past 40f's close (PI decision 2, 2026-09-26; not a 40f close gate):
    revisit the shape of CONTRACT-R's simplicity hypothesis for readability.** The theorem carries
    `hatt` (no outside body adjacent to two core bodies), as spiked. The alternative is
    `(G/H).Simple`, which needs the converse of `Graph.rigidContract_induce_simple` (about 30
    lines). *(40k's design recon, 2026-09-28: CONTRACT-A keeps `hatt` too, for parity (the
    coordinator's call 4, `notes/Phase40k.md`), and COVERAGE's natural producer at the (MC-80)
    cores, a maximality argument, is itself `hatt`-shaped. The PI decides whether that closes this
    todo.)*
  - **CHAIN = 40g, ✓ closed** (`notes/Phase40g.md`): BASE, (MC-20) open (`k ≥ 5`) and closed.
    Estimated 6–10; the design recon (opus, 2026-09-27) returned one sorry-free spike, which landed
    as two build commits (`80bcd3bb`, `1cf5b60f`). The route is in *CHAIN done* above. It pinned
    `relScrews`, `jointRows` and B5/B6 (Phase 39's D5 debt, §7), not `jointMotions`, `weldedRank`
    or A2/A3 (the δ machinery, now SHORT's). `CycleData` gets an adapter only if COVERAGE's cycle
    case produces one (PI decision 3); `ChainData` was never needed.
    - **Re-homed at the open (PI decision 4, 2026-09-27)**, each item CHAIN does not consume, to its
      first consumer: (MC-169), (MC-134)(b) at `k ≤ 4`, (MC-18)(b), the exact (MC-17), and the pins
      of `jointMotions`, `weldedRank` and A2/A3 all go to **SHORT** (the entry below); ORBIT
      consumes some of them after SHORT. (MC-19)(c) and (MC-134)(c) have **no consumer**: they are
      not in (MC-89)'s tree (Step MC20, Part I), so they join §2's *Not needed on this route*.
      (MC-21)(a)'s class theorem stays unstated (`rem:pencil-x0-ear-class`). *(SHORT's design recon,
      2026-09-27, re-homed them again: see the SHORT entry's* Re-homed and dropped.*)*
  - **SHORT = 40h, ✓ closed** (`notes/Phase40h.md`): the open ears with `k = 2, 3, 4`. The design
    recon (opus, 2026-09-27, compiler-checked) re-proved the `k = 3, 4` steps by insertion; the new
    claims (MC-179)–(MC-182) went into Step MC13, found by formalization, and a fresh reader
    second-read them before the open (PI decision 1, the ORBIT precedent). Estimated seven builds
    plus the `Carrier.lean` split; it landed as six build commits (`89a9c446` to `a3ec5a8d`) and the
    split, B3–B4 as one commit from a second recon's sorry-free spike of the `k = 4` step (EARGEN),
    and B6 before B5 (the coordinator's calls). The route is in
    *SHORT done* above. Kernel-checked in the steps spike, not landed: θ(1,2,4) meets the `k = 3`
    hypotheses, and its antecedent is θ(1,2,3) in the `k = 2` format.
    - **Re-homed and dropped** (PI decisions 2–4):
      - the `k = 1` cell (B8–B9) and (MC-175)(iii) go to **ORBIT** (below);
      - THETA ((MC-139)) dissolves into **COVERAGE**'s strong induction, with a remark and no named
        theorem;
      - (MC-44), (MC-136), (MC-24), the exact (MC-17) and (MC-134)(b) at `k = 3, 4` go to §2's *Not
        needed*;
      - the pins of `jointMotions`, `weldedRank` and A2/A3 go to their first consumer, which is not
        SHORT: ORBIT ((MC-175)(iii); at 40i's open it pins only `deficiencyMerged` and
        `partitionDef_le_deficiencyMerged`, and needs no `deficiencySep`) or COVERAGE ((MC-79)'s
        `δ`). SPLITOFF (`δ ≥ 5`) was listed here too; its design recon (2026-09-28) found it
        consumes none of them (the SPLITOFF entry below).
    - **CHAIN's note is answered:** the `k ≤ 3` ears never need (MC-134)(b) at the actual flag pair.
      - `k = 3, 4` never use `λ_k` alone.
      - `k = 2` uses a flat witness, as CHAIN's hexagon did (the flag pair is in orbit (iv) at it).
      - `k = 1`'s `λ₁ = 2` ((MC-169)) is automatic at an admissible picture.
    - [ ] **Tracked cleanup-round items, from 40h's close (2026-09-27; not close gates, and none
      blocks ORBIT).**
      - **File sizes.** `Short.lean` is at 1 366 lines (134 under the ~1500-line tripwire) and
        `Bricks.lean` at 1 458 (42 under). The commit that would take `Bricks.lean` past splits its
        vertex-2-cut layer (section `TwoCutCarriers`, lines 803–1454) into its own file first (40g's
        plan). ORBIT and SPLITOFF leave both files untouched (their steps go in new `Orbit.lean`
        and `SplitOff.lean`, 2026-09-28).
        The commit that would take `Short.lean` past first splits its antecedent and base-data layer
        into its own file, imported by `Short.lean`: the three sections from `## The antecedent G″`
        through `## The base data of the three- and four-body steps` (lines 221–635:
        `splitOff_ear_four`/`_three`, `induce_splitOff_ear`, `Graph.isLink_update_splitOff`,
        `linearIndependent_tetra_witness`, `Graph.exists_earBase_splitOff`). The near-copies item
        below would take about 300 lines off first. (`Pinning.lean`, 1 978 lines, was past the
        tripwire before 40h, at 1 964; outside Phase 40's plan.)
      - **The B2 dedupe.** `Graph.splitOff_deficiency_le_of_eq_left`
        (`Induction/SplitOffDeficiency.lean`, lines 177–309) re-runs about 110 lines of the landed `Graph.splitOff_deficiency_le`'s proof
        (lines 53–176). The two differ only in why the new label does not cross in `G` under the
        extended partition: it is fresh (`e₀ ∉ E(G)`), or it is `eₐ`, internal to that partition. A
        shared core over any `e₀` with `e₀ ∉ E(G) ∨ e₀ = eₐ` would make both corollaries, as 40g made
        B5/B6 corollaries of B5′/B6′; no statement or pin moves.
      - **The three-body step's near-copies** (the open FRICTION entry *The three-body step repeats
        the four-body step*). About 90 lines of `exists_insertion_three` (`Lines.lean`) repeat
        `exists_insertion_four`; `splitOff_ear_three` (63 lines) repeats `splitOff_ear_four` (72);
        and about 200 lines of `Graph.X0Attains.of_openEar_three`'s assembly (`Short.lean`, lines
        998–1365) repeat `…_four`'s (lines 636–997). The proposed fix is in the entry.
      - **The pin budget of `lem:pencil-ear-data`** (found at the close's re-read). It carries nine
        pins (`blueprint/AUTHORING.md` D: four or more bundle results). Split it along its three
        clauses, with the ear data as a definition node, or leave helpers unpinned. `EarGen.lean`'s
        docstrings cite the label by clause, so repoint them in the same commit (40g's fixup
        `75df1aac` is the precedent for a moved pin).
  - **SPLITOFF = 40j, ✓ closed** (`notes/Phase40j.md`): (MC-28)–(MC-31), the split-off step at a
    body `x` of degree two whose neighbours `a ≁ b`, at `δ ≥ 5`. No new mathematics: the design
    recon (opus, 2026-09-28, compiler-checked) returned one sorry-free spike, and 40j opened
    directly, with no workbook commit and no second reading (the coordinator's call, the
    40f/40g/40i precedent, checked against Step MC11 and (MC-79)). Estimated 3–5 builds before the
    recon and two, possibly three, after it; it landed as two (`0fdf5d5a`, `2fc2c02c`). The route is
    in *SPLITOFF done* above.
    - **Pins** (PI decision 4(b), first consumer; the recon's §6 table): **SPLITOFF paid none of the
      D5 debt**, refuting the expectation that it would. Its spike uses none of `jointMotions`,
      `weldedRank`, `relScrews`, `pairDelta`, `weldPair` or `deficiencySep` (the coordinator's
      grep); its only uses from the debt list are `deficiencyMerged` and the merged split-off
      bound, pinned at 40i. The rest of the debt passes to COVERAGE (§7).
    - [ ] **Tracked cleanup-round item (the coordinator's call; not a close gate):**
      `span_supportExtensor_ofNormals_eq` could replace the orientation split inlined in
      `PanelHingeFramework.finrank_span_rigidityRows_ofNormals_congr` (`Cut.lean`).
  - **CONTRACT-A = 40k, open** (`notes/Phase40k.md`; design recon 2026-09-28, opus,
    compiler-checked, one sorry-free spike; the coordinator's calls the same day are in the work
    log): (MC-71), the contraction step at a rigid core whose planar deficiency adds, with
    (MC-69)(a)(b). **No new mathematics**: 40k opened directly, with no workbook commit and no
    second reading (the coordinator's call 1, the 40f/40g/40i/40j precedent).
    - **The statement** (compiled; the nodes are `main-component.tex`
      §`sec:main-component-contract-additive`). `Graph.X0Attains.of_additiveContract` takes
      CONTRACT-R's core data (`hr`, `hWss : W ⊂ V(G)`, `hW2`, `hatt`), `hdef3 : def₃(G[W]) = 0`,
      `hadd : def₂(G[W]) + def₂(G/H) ≤ def₂(G)`, and attainment at `H = G[W]` and at
      `G/H = G.rigidContract (G.induce W) r`, in a 2EC `G` satisfying (H). `hadd` is the `≤` half of
      (MC-71)'s count, the form (MC-87)(i)'s proof produces (call 2); `hdef3` is (MC-71)'s rigid
      core (call 3); `hatt` is kept for parity with CONTRACT-R (call 4).
    - **The route** (the recon's verdict):
      - one picture `q` generic for `X₀` and Jackson–Jordán at `H` and `G/H`, and main for `G`;
      - **the lower bound** `dim ker M(0) ≥ 3 + def₂(G)`, from the semicontinuity conjunct of
        Cramer's section at the zero vector, which CONTRACT-R discards;
      - **the upper bound** (MC-69)(a), `dim ker M(0) + 3 ≤ dim ρ(ker M(0)) + dim L_{G/H}(q)`, with
        `ρ` the core heights and `ρ(ker M(t)) ⊆ L_H(q)` at every `t`;
      - with Jackson–Jordán at `H` and `G/H` and `hadd`, the two force `ρ(ker M(0)) = L_H(q)`,
        (MC-69)(b)'s by-product `S ⊆ T`;
      - **two open conditions in `ker M(0)`**, as the `HoldsGenerally` item below predicted:
        `X₀(H)`'s height polynomial on `ρ`, and the degenerate-rank polynomial at `t = 0`, witnessed
        by the flat-core extension K4; `exists_mem_eval_ne_zero₂` gives a common point;
      - Cramer's section through it does not jump:
        `dim ker M(0) ≤ 3 + def₂(G) ≤ dim L_G(q(t)) ≤ dim ker M(t)`;
      - **the core's rank** is `H`'s at `(q, ρ x(t))`, by a collineation of `K⁴` (G1, G2), and that
        is the target by `X₀(H)` at the fixed picture `q`;
      - the degenerate rank, the block coupling and `x0Attains_of_exists` finish, as in CONTRACT-R.
    - **The proof-level departure from (MC-71)'s proof text** (call 1; in the theorem's blueprint
      proof and the remark after it, not a workbook claim): `S ⊆ T`, two open conditions in
      `ker M(0)` and a collineation, in place of (MC-68)(d)'s core-freeness and (MC-38)'s dominance.
    - **The recon's names for the new pieces:** G1 the collineation lemma, G2 the core's rank along
      the curve, G4 the kernel bound through the core heights, G5 the rigid-core standing lemma
      (Lean names and nodes in `notes/Phase40k.md`'s checklist).
    - **The factoring** (PI decision 4, 2026-09-26, as the recon found it). Shared with CONTRACT-R,
      unchanged: the curve, `M(t)`, K1, K2, K4 (already general in Lean), the degenerate rank, the
      coupling, the curve polynomials and the `G/H` standing facts; the two unpinned
      `contractLimitMap` helpers generalize in place to a plane hypothesis. Specific to the flat
      core: `exists_core_plane`, the flat K3 (successor G4), the flat core rank (successor G2), the
      `def₂` standing lemma (successor G5) and CONTRACT-R's assembly.
    - **Placement: option A**, the line above (call 5). The general pieces move to a new
      `MainComponent/ContractCurve.lean`, importing `Cut.lean` (about 1 040 lines moved, 170 new);
      `Contract.lean`, importing it, keeps the flat pieces and CONTRACT-R untouched (1 496 → about
      430); the step goes in a new `ContractAdditive.lean` (about 360). G1 goes in
      `Configuration.lean`, beside `pointJoinFramework_comp_eq_mapSupport` (call 6: a reading of PI
      decision 5's convention, the 40j placement precedent, which the PI may reverse). No fragile-zone
      file is touched. **Alternatives the PI may prefer:** option B, the compiled
      `of_rigidContract_viaAdditive`, re-proves CONTRACT-R in about 20 lines through CONTRACT-A and
      FLAT and removes about 140 lines of duplicated setup, but leaves three pinned flat nodes
      (`lem:pencil-contract-core-plane`, `lem:pencil-contract-limit` (1),
      `lem:pencil-contract-core-rank`) without a consumer; the cheaper-diff sub-option of A keeps
      the general part in `Contract.lean` and moves the flat part out.
    - **Pins** (PI decision 4(b), first consumer; call 7): **CONTRACT-A pays none of the D5 debt**.
      The recon's grep of the spike finds no `jointMotions`, `weldedRank`, `relScrews`, `pairDelta`,
      `weldPair`, `deficiencySep` or `deficiencyMerged`; the debt passes to COVERAGE (§7).
    - **Re-homed** (call 8): (MC-67), (MC-68) and (MC-70) to §2's *Not needed*, with the
      (MC-119)/(MC-120) caveat there; COVERAGE's MC15 row corrected; the `hadd` supplier a COVERAGE
      tracked item.
    - **Not adopted** (call 3): the compiled `of_additiveContract_weak`, which needs no core
      rigidity (`def₃`-additivity in its place, and `h3` at `H` from `X₀(H)`, no `hW2`).
    - [ ] **Tracked cleanup-round items (call 12; not close gates):** the flat K3 as a corollary of
      G4; the `def₂` standing lemma as a corollary of G5; `exists_core_plane`'s middle step via the
      new core-heights lemma; `Graph.finrank_span_rigidityRows_ofNormals_smul_add_affineLifts` via
      G1.
    - **Build commits: three, possibly two** (estimated 4–7 before the recon) — B1 the split, B2 the
      general pieces and the four lemma nodes, B3 `ContractAdditive.lean` and the theorem. The nodes
      of each build are in `notes/Phase40k.md`'s checklist.
  - **ORBIT = 40i, ✓ closed** (`notes/Phase40i.md`): the `k = 1` cell ((MC-54) at `k = 1`, folded
    in from SHORT by PI decision 2) and the `k = 2`, `a ≁ b`, `δ₂ ≥ 2` cell ((MC-176)), with
    (MC-173)–(MC-175). A tail group right after SHORT (PI D2, 2026-09-26), although this list prints
    it last. No new mathematics: the design recon (opus, 2026-09-28, compiler-checked) returned one
    sorry-free spike, and 40i opened directly, with no workbook commit and no second reading (the
    coordinator's call, the 40f/40g precedent). Estimated three builds; it landed as three
    (`5ba25337`, `b733f5fe`, `b3dac673`) and a coordinator fixup of one `\leanok` (`6b266906`). The
    route is in *ORBIT done* above. The name is historical: the orbit table (MC-138) and (MC-46)'s
    count are off the route, and no orbit is computed.
    - [x] **Tracked (the coordinator's flag, 2026-09-27): trace the supply of `hδ₂`. Settled by
      ORBIT's design recon (2026-09-28).** Both cells take the `deficiencyMerged` form, (MC-176)'s
      and (MC-175)(iii)'s `δ₂ ≥ 2` over Layer A's carrier, which COVERAGE computes from (S), by
      (MC-79)(ii) at `k = 1` and by (MC-79)(iii) with (vi) at `k = 2`, `a ≁ b`, `δ ≥ 1`. It fails
      exactly at chains with `δ₂ ≤ 1`, which violate (S) and are covered before (MC-89)'s step 5,
      by CUT/BRIDGE, BASE, FLAT (`K_{2,3}` and `K₄` with one edge subdivided once,
      `def₂ = def₃ = 0`, measured, script not retained) or CONTRACT; θ-graphs go through THETA's
      assembly, which uses no `k = 1` ear. The compiled split-off form would be a double split-off
      at `k = 2` (about three lines per call site to switch); `dim U ≥ 2` in Lean form is rejected
      (COVERAGE would re-run U2). The supplier is COVERAGE's, tracked in its section.
    - **Pins** (PI decision 4(b), first consumer): ORBIT pinned only A2's `Graph.deficiencyMerged`
      and `Graph.partitionDef_le_deficiencyMerged`, on `def:deficiency-merged` (40g's
      `def:relative-screws` precedent). The rest of A2/A3, `jointMotions` and `weldedRank` stay
      unpinned for COVERAGE; SPLITOFF consumes none of them (40j's design recon, 2026-09-28; §7).

  **Order** (PI, 2026-09-26): 40e's open and build first, then a read-only ORBIT recon (opus)
  before the next group opens. Both are done; the ORBIT verdict is in §4. The read-only fresh
  second reading of (MC-173)–(MC-176) (PI D1) is done too (2026-09-26): no refutation and no gap,
  repairs applied in place, (MC-177) and (MC-178) added. **40f opened design-first as
  CONTRACT-R** (2026-09-26), from a compiler-checked design recon, and closed the same day after
  one build commit. **CHAIN opened as 40g** (2026-09-27), design-first from a compiler-checked
  recon, and closed the same day after two build commits. **SHORT opened as 40h** (2026-09-27),
  design-first from a compiler-checked recon, after the fresh read-only second reading of its new
  claims (MC-179)–(MC-182) (PI decision 1) confirmed them, with repairs in place, and closed the same
  day after six build commits and the `Carrier.lean` split. **ORBIT opened as 40i** (2026-09-28),
  right after SHORT as the PI's D2 (2026-09-26, verbatim in `notes/pencil/adjudications.md`)
  placed it, with SHORT's `k = 1` cell (PI decision 2): design-first from a compiler-checked recon
  whose sorry-free spike needs no new mathematics, and which settled the tracked `hδ₂` trace; it
  closed the same day after three build commits. **SPLITOFF opened as 40j** (2026-09-28), the
  next group in the list's order: design-first from a compiler-checked recon (opus) of
  (MC-28)–(MC-31) whose sorry-free spike needs no new mathematics; it closed the same day after
  two build commits. **CONTRACT-A opened as 40k** (2026-09-28), the list's next group and the last
  of STEPS: design-first from a compiler-checked recon (opus) of (MC-67)–(MC-71) whose sorry-free
  spike needs no new mathematics; B1, the `Contract.lean` split (its entry above), is next.
- [x] **Tracked for CHAIN's design pass (the second reading of (MC-173)–(MC-176), 2026-09-26):
  settled by CHAIN's design recon (2026-09-27).**
  - **(MC-177) is built in CHAIN, forced**: BASE and the open ear both go through the ear rank law.
    ORBIT (`k = 1, 2`, `a ≁ b`) and SHORT (`k = 3, 4`) then consume the same law. It is built with
    equalities, since SHORT's (MC-24) needs the `≤` direction.
  - **B6 at `pointJoinFramework` or a transport lemma: CHAIN needs neither.** It applies B6′ and the
    ear law, which hold at any framework, directly at `(ofNormals G ends p).toBodyHinge`, the
    framework `X0Attains` reads; the polarity enters only per hinge. ORBIT's recommended route
    stays available (the ear law at `pointJoinFramework`, the rank moved by the landed `mapSupport`
    lemmas), and no `relScrews`/`mapSupport` transport lemma is needed by anyone yet. *(ORBIT's
    design recon, 2026-09-28, takes the direct route too.)*
- [x] **Tracked for SHORT's pre-build recon (the ORBIT recon, 2026-09-26): re-check (MC-44) in
  SHORT's list. Settled by SHORT's design recon (2026-09-27): no consumer on the route, dropped to
  §2's *Not needed* (PI decision 4(b)).** (MC-44) is not in (MC-89)'s tree (Step MC20, Part I). Step MC14's claim that
  (MC-46) uses it was a mis-citation, repaired 2026-09-26. Its other users are off the route:
  (MC-49), (MC-88)'s corollary, the ear cells of Steps MC17–MC18, Step MC21 and Step MC19's
  informal *Consequence*. The new `k = 2` cell (MC-176) does not use it either. So confirm a
  consumer on the route, or drop it from SHORT.
- **Tracked from CARRIER's close and BRIDGE's recon (2026-09-26): settled by the STEPS pre-build
  recon (2026-09-26).** Each verdict below is compiled where it is a Lean question (the pieces the
  later groups reuse are verbatim in the appendix *the STEPS recon's tracked spike*), and lands
  with the group that consumes it.
  - [x] **The SPLITOFF curve-limit lemma** (landed in 40j's B1, `0fdf5d5a`). Its shape is
    `PanelHingeFramework.finite_setOf_finrank_lt_of_curve`, compiled: along a polynomial curve of
    normals whose hinges are nonzero at `t = 0`, the rank is at least its value at `t = 0` for all
    but finitely many `t`. It is the landed rank device composed with the curve. (MC-30)(ii)'s
    rational curve is cleared by rescaling every body by its denominator
    (`finrank_span_rigidityRows_ofNormals_smul`). Main-ness and membership along the curve stay
    SPLITOFF's own obligations. The compiled lemma, with its helper `polynomial_eval_aeval`, is
    verbatim in the appendix *the STEPS recon's tracked spike*. *(40j's design recon, 2026-09-28:
    no rescaling is needed, since the curve is a polynomial line, (MC-30)(ii)'s `P(t)` times a
    scalar nonzero at `t = 0`, and main-ness along it is `G`'s main-picture polynomial restricted
    to the picture line. The lemma re-compiled verbatim at `52706564` and landed in 40j's B1, in
    `Bridge.lean`, its helper as the mirror `MvPolynomial.polynomial_eval_aeval`.)*
  - [x] **The CONTRACT rank-device open point: dissolved** (landed in 40f). The `G/H`
    framework with the actual boundary hinges is never formed. Its rank is the rank of the rows of
    `ofNormals (G.deleteEdges E(H)) endsG`, projected by `(extProj W).dualMap`, and that framework
    is in `ofNormals` form. The value at `t = 0` is Phase 22i's composition (`degeneratePlacement`,
    `panelRow_collapseTo_comp_extProj_dualMap`, `exists_independent_panelRow_subfamily_of_le_finrank_proj`),
    as in `exists_rankPolynomial_of_IH_relabel_linking_set_proj`. One sibling is new: the projected
    rank polynomial must return `eval q₀ Qc ≠ 0`, which its proof already has. The coupling
    `rank_G ≥ rank_H + finrank (S.map D)` is rank-nullity.
  - [x] **`HoldsGenerally`: not built.** Its three consumers need no bundle-level genericity. (MC-44)
    works at one picture inside `L_{G′}(q) ⊇ L_{G′+ab}(q)`. (MC-38) at a `def₂`-rigid core follows
    from the flat limit core being rigid (FLAT and Jackson–Jordán at `H`) and lower semicontinuity
    along the curve; at an additive core it is two open conditions in `ker M₀` at one picture.
    (MC-30)(iv) uses one picture, one fibre point and one curve. `exists_mem_eval_ne_zero₂`
    suffices throughout. Build it only if a later recon finds a witness over a picture that no
    product of polynomials can align. *(40k's design recon, 2026-09-28, confirmed the additive core:
    two open conditions in `ker M(0)`, met by `exists_mem_eval_ne_zero₂`; the CONTRACT-A entry.)*
  - [x] **The slice `q′ = (q_O, Q)`: collapse at `p(r)`, with the magnified core `δ := q|_W`**
    (landed in 40f). With `q_c(t) = q_r + t·q_c` for `c ∈ W`, `H` is read at `q|_W` and `G/H` at
    `q|_{V(G/H)}`, both at one generic ambient picture, so no slice arises. Translation invariance
    was re-derived and is true, but it is not needed and the translation lemmas stay unlanded. The
    remaining question, `H`'s rank under the core rescaling `A_t ∈ GL₄` by the collineation action,
    is **resolved** by CONTRACT-R's recon (2026-09-26): no `A_t` lemma is needed. The core rows of
    `M(t)` do not depend on `t`, so with `L_H(q) = Aff(q)` every kernel vector puts the core on one
    plane. At `t ≠ 0` the core heights are then affine in `q(t)`, and `H`'s rank is its flat rank,
    `6(|W| − 1)`. That uses (MC-3)'s shift `finrank_span_rigidityRows_ofNormals_smul_add_affineLifts`
    (itself a collineation of `K⁴`) and `dim L_H(q(t)) = 3`, from Jackson–Jordán at `H` along the
    curve. *(At an additive core the core heights are not affine, so CONTRACT-A does need the
    `A_t` lemma: G1, a collineation of the normals keeps the rank, and G2, its `A_t` instance
    (40k's design recon, 2026-09-28; the CONTRACT-A entry).)*
  - [x] **`(G.rigidContract (G.induce W) r).Simple`**, compiled as
    `Graph.rigidContract_induce_simple (hS : G.Simple) (hr : r ∈ W) (hatt : ∀ u ∉ W, ∀ c₁ ∈ W,
    ∀ c₂ ∈ W, G.Adj u c₁ → G.Adj u c₂ → c₁ = c₂)`, from the landed `rigidContract_simple` (landed
    in 40f, in `Contract.lean`; the recon's compiled proof is verbatim in the appendix *the STEPS
    recon's tracked spike*).
  - [x] **`h3` from (H)**, compiled as `Graph.three_le_ncard_closedNbhd (hS : G.Simple)
    (hdeg : 2 ≤ G.degree v)`, from the vendored `Graph.degree_eq_ncard_adj` (landed in 40e build 1,
    beside `Graph.closedNbhd` in `Motive.lean`).
- [ ] **Tracked todo, carried past 40e's close (PI, 2026-09-26; not a 40e close gate): the "only
  if" halves of (MC-52)(iv) and (MC-53)(iv).** 40e formalized the "if" halves, the only ones the
  induction consumes; `thm:pencil-x0-cut` and `thm:pencil-x0-bridge` name this item in their remarks. The informal
  proof: at a generic point of `B(G)` the ranks add and each is at most its target, so an attaining
  height of `G` restricts to attaining heights of both pieces, and the restrictions are onto.

### COVERAGE — the structural half and the assembly (pure combinatorics on `def₂`, `def₃`)

| labels | step | 2nd |
|---|---|---|
| (MC-62), (MC-63) *(since 40k's open, 2026-09-28: (MC-69)(a)(b) and (MC-71) moved to STEPS' CONTRACT-A row, and (MC-67), (MC-68)(d) and (MC-70) to §2's* Not needed*. (MC-62) and (MC-63) stay: (MC-62) is cited on this side by (MC-79)(vi) and (MC-89)'s step 5, and (MC-63)(a)'s structure of `δ₂` by (MC-88) and (MC-102); whether COVERAGE's Lean route consumes either is its own recon's question)* | MC15 | ✓ 09-25 (one merge step supplied) |
| (MC-75)(iii), (MC-76), (MC-77), (MC-78), (MC-79)(i)–(iv) → (MC-80); (MC-87) → (MC-89) | MC16 | ✓ (two readers) |
| coverage ⟹ attainment: (MC-56), (MC-55)(i), (MC-2); strong induction | MC14, MC2 | ✓ |
| the statement proved, (MC-10)(a): `X₀(G)`'s generic point attains `6(|V| − 1) − def₃(G)` (moved from CARRIER at its close; `thm:pencil-x0-generic-attains`'s first sentence) | census | — |

**THETA dissolves here** (PI decision 3, 2026-09-27). (MC-139) is an assembly of step theorems:
- BASE, then `of_openEar` (`k ≥ 5`);
- SHORT's `of_openEar_four` and `…_three`, whose antecedent `θ(p₁, p₂, p₃ − 1)` comes from the strong
  induction;
- `of_openEar_two`, with `def₃(C_s) = 0` for `s ≤ 6`;
- FLAT at `K₄ − e` and `K_{2,3}`.

So COVERAGE's strong induction covers θ-graphs, and a remark records it, as with (MC-21)(a)'s class
theorem in 40g. COVERAGE also supplies SHORT's `hdef` from `δ = 0`, through
`Graph.deficiency_induce_le_of_ear_of_merge`, and the split-off antecedents satisfying (H): SHORT's
`G.splitOff (x 1) (x 0) (x 2) (e 1)`, ORBIT's `G₁ = G.splitOff (x 1) (x 0) b (e 1)` and SPLITOFF's
`G″ = G.splitOff (x 0) a b (e 0)`. One lemma, "(H) holds after splitting off at non-adjacent
ends", serves all three (40j's design recon, 2026-09-28); none is landed.
- [ ] **Tracked (from 40i's open, 2026-09-28): ORBIT's `hδ₂` supplier.** Both ORBIT steps ask
  `(G.induce V₁).deficiencyMerged 2 a b + 2 ≤ (G.induce V₁).deficiency 2` at a chain of `G ∈ 𝒮`.
  COVERAGE builds it as a Layer-A lemma, "(S) at `G` ⟹ `deficiencyMerged₂(G′; a, b) + 2 ≤
  def₂(G′)`", at a one-body chain by (MC-79)(ii)'s computation, and at a two-body chain with
  `a ≁ b`, `δ ≥ 1` by (MC-79)(iii) with (vi). It uses Layer A only. The trace is the ORBIT entry's
  settled item (§3 STEPS).
- [ ] **Tracked (from 40j's open, 2026-09-28): SPLITOFF's `hδ` supplier.** `of_splitOff` asks
  `(G.induce V₁).deficiencyMerged 3 a b + 5 ≤ (G.induce V₁).deficiency 3` at a one-body chain
  `a − x − b` of `G ∈ 𝒮`, at (MC-89)'s step 5. COVERAGE builds it as a Layer-A lemma at `n = 3`,
  "`x` in no rigid subgraph of `G` ⟹ `δ ≥ 5`", from (MC-79)(ii)'s first bullet, in the same form as
  ORBIT's `hδ₂` supplier above.
- [ ] **Tracked (from 40k's open, 2026-09-28): CONTRACT-A's `hadd` supplier.** `of_additiveContract`
  asks `(G.induce W).deficiency 2 + (G.rigidContract (G.induce W) r).deficiency 2 ≤ G.deficiency 2`,
  with `hatt`, at a core `W` of (MC-80) in `G ∈ 𝒮`, at (MC-89)'s step 5. COVERAGE builds it as a
  Layer-A lemma from (MC-87)(i)'s "if" direction at the (MC-80) cores ((MC-87)(ii)), in the `≤`
  form: (MC-87)(i)'s proof bounds every partition value of `G/H` by the singleton value
  `s′(V) − s′(W) = def₂(G) − def₂(H)`. `hatt` at those cores comes with it ((MC-87)'s "`G/G[W]`
  simple", by a maximality argument, the recon's observation; the PI-decision-2 todo, §3 STEPS).
  The (MC-80) cores are rigid, which is `hdef3`, and `lem:pencil-contract-standing-rigid` at `n = 3`
  then gives (H) at `H` for the induction hypothesis. The same form as the ORBIT and SPLITOFF
  supplier items above.

**Lean reuse.** `exists_maximal_induced_isProperRigidSubgraph`, `triangle_isProperRigidSubgraph`,
`c4_isProperRigidSubgraph`. The proof uses all of (H), because CUT and BRIDGE pass through
non-2EC graphs, while the consumer uses only the 2EC form (§4).

### MOTIVES — `X0Dist` and `X0Gen` (closes the phase)

| labels | step | 2nd |
|---|---|---|
| (MC-157) from (MC-89) | MC19 | ✓ 09-25 |
| (MC-133)(ii) ← (MC-123), the hub-plane chart (MC-124)–(MC-129), the reduction (MC-130); nondegeneracy on `X₀` (MC-13)(a), (b) and (MC-14)'s union lemma | MC19, MC8 | ✓ 09-25 ((MC-130)'s cycle citation repaired) |

**Lean reuse.** `pencilChartFramework`/`PencilSeed`, `exists_pencilSeed_of_nondeg`, L6b
(`pencilNondegFeasible_of_ncard_closedHubNbhd_le_three_of_triangleFree`), and
`hasGenericPencilRealization_of_independent_pencilRow_target`. Landing both discharges L0's
carried hypotheses and closes the phase. At the close, re-decide the held kernels (§6).

**Consumes `Graph.X0Attains`** (CARRIER C1a, `notes/Phase40b.md` *Decisions*): `X0Dist` takes one
attaining `(q, z)` through the landed `Graph.X0Attains.hasDistinctPencilRealization` (CARRIER C4);
`X0Gen` intersects the fibre-open attaining set with a nondegenerate open set inside one fibre
`L(q)`, through the landed fibre-intersection lemma `MvPolynomial.exists_mem_eval_ne_zero₂`
(CARRIER C5′, `lem:pencil-x0-fibre-intersection`) and C3's polynomial plane normal
`pencilNormalOfPicturePoly`.

**The blueprint node.** `thm:pencil-x0-generic-attains` (red) sits in the chapter's final stub
subsection `sec:main-component-statements`. Its first sentence is COVERAGE's conclusion
((MC-10)(a), by (MC-56)'s induction via (MC-89)); its "granting this" clause is MOTIVES.

**β-headroom (CARRIER's design recon, `notes/Phase40b.md` *Architectural choices*).** Needed; the
fix is an additive-successor `_of_card` triple (`x0Dist_of_card`, `x0Gen_of_card`,
`pencil_conjecture_of_card`) concluding the unchanged L0 `X0Dist`/`X0Gen` and reusing
`pencil_conjecture_of_X0` verbatim. **Two questions for the MOTIVES pre-build recon**, moved here
from `notes/Phase40b.md` at CARRIER's close (the opus and fable recons disagreed; settle against
the landed SPINE2 threading):
- **(a) The exact `hcard` constant.** Opus read `bodyBarDim 3 · (|α|−1)` (= `6·`, matching
  `molecular_conjecture_multigraph` and `freshEdgeSupply_of_card_lt_of_noRigid_of_degree_two`,
  `Molecule/Pencil/Escape.lean`); fable read `3 · (|α|−1)`. Pin it against the SPINE2 producer's
  actual `hfresh`/`hcard` threading.
- **(b) The headroom's root cause.** Opus: the split-off's `e₀ ∉ E(G)` (the `hK`/`hbareSplit`
  slots in `Escape.lean`). Fable (reading `splitOff`, `Induction/Operations.lean`): split-off can
  reuse a freed label, and the real source is BRIDGE consuming SPINE2's `hfresh`. Sub-gap: the
  landed fresh-edge supply lemma keys on sparsity (no proper rigid subgraph), while the split-off
  step runs at `δ ≥ 5`; settle which supply lemma discharges `e₀ ∉ E(G)`.
- **STEPS forces no headroom either** (the STEPS pre-build recon, 2026-09-26): every consumed
  graph reuses labels (§3 STEPS, the step contract).
- **BRIDGE forces no headroom** (the 40d design recon, 2026-09-26). Its Jackson–Jordán forms
  carry no hypothesis on `β`: they relabel the edges into a larger label type (`Graph.embedEdges`,
  §3 BRIDGE), so SPINE2's `hfresh` never reaches a consumer. Questions (a) and (b) stay open for
  the MOTIVES recon, including the two label-reuse sources that recon named. The split-off
  `G.splitOff x a b e₀` can take for `e₀` a freed label of the split vertex. `G′ + ab` at a chain
  can reuse an ear-edge label.

### The blueprint chapter

The main-component argument gets **one new forward-mode chapter** (`main-component.tex`), one
subsection per layer from CARRIER to MOTIVES. The CARRIER, FLAT and BRIDGE subsections are all
green, and so are STEPS' first six, `sec:main-component-cut` (40e),
`sec:main-component-contract` (40f), `sec:main-component-chain` (40g), `sec:main-component-short`
(40h), `sec:main-component-orbit` (40i) and `sec:main-component-splitoff` (40j); the seventh,
`sec:main-component-contract-additive` (40k), is open and red. MOTIVES's stub subsection
`sec:main-component-statements` is the last, and each later layer inserts its subsection before
it. It is opened as red nodes transcribed from the proof map
above, with statements from `ledger.py --brief`, never retyped. Transcribe a layer's section when
that layer opens, not all at once, and run a **pre-build recon of each transcribed section** before
the first build against it (the `/coordinate-phase` transcription guard: a red node's statement is
checked by no gate). The Phase 39 nodes `def:pencil-main-component-statements` and
`thm:pencil-conditional-realization-main-component` (`pencil.tex`) are the chapter's consumer
end.

## 4. Where formalization may expose mathematics

- **Genericity.** The induction argues about generic points throughout; (MC-157) alone needs
  only one. The delicate places are:
  - dominance, (MC-18)(b);
  - the two-scale and flat limits in contraction, (MC-37), (MC-66), (MC-69);
  - semicontinuity at chord points.

  Each must become an explicit nonzero-polynomial or rational-parametrization statement.
- **Fresh edge labels.** `G′ + ab` and split-off add edges inside a fixed `β`. That calls for
  either a `β`-headroom hypothesis like `hcard` or a type-changing induction; the informal proof
  never meets the issue. **If MOTIVES' proof needs headroom**, `X0Dist`/`X0Gen` as L0 pins them
  (no headroom) are stronger than what is proved. The fix is then an additive successor headline
  carrying `hcard`, not an edit of L0's declarations. CARRIER's design recon decided it: headroom is
  needed, and the fix is the `_of_card` triple (§3 MOTIVES).
- **Non-spanning uses** of the rank theorem at `H` and `G/H`. The landed
  `rankHypothesis_of_theorem_55_gen` is stated for spanning `G` with `hcard` headroom; SPINE2's
  non-spanning form is the fix.
- **(H) versus 2EC.** CUT and BRIDGE pass through non-2EC graphs, so the proof needs all of (H);
  the consumer uses only the 2EC form.
- [x] **ORBIT's dimension counting: resolved by the ORBIT recon (opus, 2026-09-26; PI D1/D2,
  `notes/pencil/adjudications.md`).** (MC-46)'s proof, with (MC-138)'s table, counts dimensions
  of incidence varieties and orbits, which has no polynomial-level form. The verdict is option
  (A), in a stronger form than posed. On the route the flag pair is in orbit (i) ((MC-48)(ii)'s
  argument under `δ₂ ≥ 2`), and there a sharper (MC-26) link, the refined link (MC-173), gives
  `(P₁) ⟹ (P₂)` by two curve families. It picks the limit direction outside `ρ + Λ₁(y)`, with no
  description of `B₂(r)`. The cell's step (MC-176) then counts ranks against the antecedent
  directly. (MC-18)(b)'s dominance needs no divisibility: it is (MC-174), which retires SHORT's
  medium-risk item. All of this is in
  Step MC13, second-read 2026-09-26; the grouping effect is in §3 STEPS. Recorded so they are not
  re-asked:
  - **(B), rerouting in COVERAGE, is refuted** (`w4/orbitlink.py --witness`). `K₄` with every
    edge subdivided twice is in 𝒮, with `def₂ = 9 > def₃ = 0`. It is rigid, it has no (MC-80)
    core, and all six chains have `k = 2`, `a ≁ b` and `δ = δ₂ = 3`, so its only covering step
    is this cell. Splitting off a chain vertex gives the cell's own antecedent. The consumers are
    Step MC16's *usable* list, (MC-79)(v), (MC-80), (MC-81), (MC-82)(iii) and (MC-89)'s step 5.
  - **(C), building dimension theory, is not feasible at any sensible cost** (well over 20
    builds). The claims below were checked by compiler witnesses and bare-name searches across
    `.lake/packages`.
    - Mathlib **has** `ringKrullDim`, `MvPolynomial.ringKrullDim_of_isNoetherianRing`,
      `Algebra.trdeg`, Noether normalization (`exists_finite_inj_algHom_of_fg`), Chevalley
      (`PrimeSpectrum.isConstructible_comap_image`) and the topological `UpperSemicontinuous`.
    - It **lacks** a fibre-dimension theorem, algebraic group actions, orbit–stabilizer
      dimensions, a tangent-rank orbit bound, a trdeg–Krull-dimension bridge
      (`Algebra.trdeg_eq_ringKrullDim` and `ringKrullDim_eq_trdeg` are unknown identifiers), and
      any dimension for K-points over a non-closed field.
- `supportExtensor e ≠ 0` must hold for **every** `e : β`, not only the edges of `G`. This is
  trivial, but it is easy to miss.

### Duality: field generality and what it buys (recon 2026-09-26)

**Verdict, landed as DUAL-K** (`notes/Phase40b.md`). A read-only opus recon commissioned by the PI
(witnesses: `lake env lean` scratch files at `[Field K]`, exit 0, no `sorry`; the coordinator re-ran
the main one). The polarity preserves rank, motion space, rigidity and genuine hinges over **every
field, of every characteristic**, as a transport of frameworks and of pencil realizations; it needs
only a nondegenerate dot product. The landed ℝ duality cluster and all of
`ProjectiveInvariance.lean` restated over `K` with the ℝ proofs verbatim (the ℝ scope was Phase
33's `Molecule/` line; only the molecular dictionary is ℝ³-bound; this settles `K-clos.md` (AC-1)).
There is no field obstruction on the `X₀` route: characteristic 2 (`ω ∧ ω = 2·Pf`) and isotropic
vectors are never used, and genuine field dependence concerns only the self-dual configurations of
route σ and kernel (K), the held kernels (`fmlnote:pencil-conditional-realization-pair-field`). The
polarity never preserves adjacent-distinctness, `IsNondegPencilRealization` or `X₀` (the dual's
"points" are the plane normals, which coincide on triangle edges, (MC-13)(c)), so self-duality is
not a route to `X0Dist`; `hasPencilPanelRealization_mapExtensor_screwComplementIso` has zero Lean
consumers. What it bought: C4's polar/primal rank equality.
- **Rejected, so they are not re-asked:**
  - Deriving one of X0Gen's two nondegeneracy halves from the other. Duality maps realizations,
    not conditions; conjunct 4 is automatic on `B` by (MC-1), while conjunct 3 is all of
    (MC-12)/(MC-14).
  - Dual STEPS moves. Duality moves off `X₀`, and the (MC-138) orbit table is not duality-closed.
  - Replacing (MC-4)'s `Φ` by the 3D polarity. `Φ` sends motions to heights; it does not
    transport a framework.
  - Building Klein self-duality S7(v). That is motion/wrench duality, which no route label uses.
- **Still open (hypotheses and cleanup items).**
  - *Hypothesis:* with the Euclidean form, duality's fixed points need `char ≠ 2` and `−1` a sum of
    three squares; the second condition is an artefact of the choice of form.
  - `X₀` (points free) and its dual `X₀*` (planes free) differ whenever a def₂-rigid subgraph has
    an edge. *Hypothesis:* they coincide otherwise.
  - Collineations over `K` (`Arms.lean`) plus the polarity give the whole projective group
    (Crapo–Whiteley 1982 §3.6, p. 68, read in `.refs`). The polarity is a correlation, not `Λ²g`.
  - Duplication for a cleanup round: `mapExtensor` and `mapSupport` are one definition, and
    `thm:projective-invariance`'s rank half restates `lem:screw-map-rows`.
- **Citations** (FLAT used them; verdict in §3 FLAT). Crapo–Whiteley Ex. 4.4 (pp. 72–73) is
  verified as the flat-tetrahedron instance of (MC-4)'s `Φ`, with Whiteley 1996 §8.3 for liftings.
  Whiteley 1984 (*Discrete Appl. Math.* 9(3) 269–295) is verified by Crossref metadata only; it is
  not cited until read.

## 5. Standing constraints

- **Landing a mathematical repair** found by formalization (a gap, a wrong citation, a missing
  case): the repair goes in place in the owning `K-main*.md` step, marked with its date and
  finder. New claims get the next free `MC-` labels, with a `notes/pencil/labels.md` row in the
  same commit. New drivers are ported to `notes/scripts/w4/` with a `README.md` row
  (`HARNESS.md` *Reproducibility*). Run `python3 notes/ledger.py --lint` before committing. The
  reusable second-reader brief is the Appendix.
- **Files.** Never touch `notes/attacks/smark/` or `notes/pencil/workbook/attack-smark.md`; a
  resumed smark runs in its own worktree. `notes/Phase39-design.md` is a frozen archive: append
  only.
- **Do not:** edit `hK`, `hbareSplit`, `pencilPair_of_splitOff_of_habitat` or the landed
  headline; launch `kres` or a contraction attack; or treat `workbook/W4.md`'s (K-res) statement
  or cost estimates as current.

## 6. Held fallback

The split/contract architecture and its three kernels are recorded in `notes/pencil/W4-reopen.md`
(held record) and `W4-reopen-archive.md`: (K-res)/`kres`, (K-c), and (K-bare-c) with (α).
Phase 39's held checklist items are the grid route for `hK`, tree-triples, and the rest of the
W4 build. smark's O7e programme is paused; its status surface is `notes/attacks/smark/state.md`.
All of these are held until MOTIVES lands (PI, 2026-09-25), then re-decided. On a HIT on a held
kernel, the phase-boundary consequences are the PI's call (`PHASE-BOUNDARIES.md`), surfaced with an
estimate.

**Phase 39's held checklist items, moved here at its close (2026-09-25):**
- **`hK` on the tight stratum from grid vanishing**, the colouring statement as hypothesis:
  decoupling, rank formula, Vandermonde, chart step, descent. It decides whether the independence
  proviso is a hypothesis of the crux (`notes/attacks/gr10/brief.md` §2 *Proviso (P)*). The chart
  machinery exists (`IsFin3SelectorOf`, `cross₃`, `pencilRow`); the grid geometry does not.
- **Tree-triple ⇒ `dim Z = 0`**, and the circular-ladder family (GUNIZERO's uniform instance) as a
  formal witness.
- **The rest of the W4 build** (`notes/pencil/W4-reopen.md`, held record): T1, the W4 wrapper
  carrying (K-res); W4-L4b (`exists_degree_two_of_co1_rigid`, pinned and spike-elaborated);
  W4-L2/L3′/L5; the residual carry `hnoGood'`. W4-L1 (W4-A) landed as Phase 39's L0b.
- **The reverse arms of the W0 transport** (a `complementIso` involution lemma), off every critical
  path (the workbook's §(K-σ) *Step σ6*, via `python3 notes/ledger.py`).

## 7. Deferred from Phase 39

Moved here at Phase 39's close (2026-09-25). None is on SPINE2's path; each names the layer or
round that lands it.

- **A6 — C3, the welded pendant law** `g(H) = max(g(H−u), f_sep(H−u) − (D−1))` and
  `δ(H) = min(δ′+1, D)` (S6(ii)'s remaining clauses; both need `w ≠ v`). Deferred by the PI's D2
  call (2026-09-16): off the consumed path — S6 is the side-degree-1 reduction, S14's `H′` has
  side-degree ≥ 2 at both ends (S10(iii)) — and it is the only law needing `deficiencySep`. Site
  `Induction/SplitOffDeficiency.lean`. Build only if STEPS consumes S6's reduction.
- **The shared hub normalization — a factoring item.** C2ℓ's merged hub
  `screwDim_mul_compl_add_deficiencyMerged_le_finrank_jointMotions` (`Molecule/Pencil/TwoCut.lean`)
  duplicates ~85 lines of `screwDim_mul_compl_add_deficiency_le_finrank_infinitesimalMotions`
  (`AlgebraicInduction/PanelLayer.lean`); only the attaining labeling's subtype, one `g u = g v`
  step and the final monotonicity differ. Extract the `ι₀` normalization as one private lemma — for
  any `f`, some `g` with (i) `g '' V(G) ⊆ V(G)`, (ii) `numParts g = numParts f`,
  (iii) `crossingEdges g = crossingEdges f`, (iv) `|range g| = numParts f + |V(G)ᶜ|`,
  (v) `g x = g y ↔ f x = f y` on `V(G)` — and rebuild both hub sites on it. It edits
  `PanelLayer.lean`, in the defeq-fragile zone, so it gets its own pass with its own verification
  (Phase 38 is the precedent); a cleanup round or a STEPS slice that touches the hub.
- **Item 6's other deferred laws** (all cheap on Layer B): the general-`U` joint count (S7(iii))
  and `finrank_jointMotions_eq` (S7(i)) — motion-side, hence `|α|`-laden; S7(ii) (the bar reading),
  S7(v) (Klein self-duality), S9 (the `ear1` criterion). Build when a STEPS step consumes one.
- **The D5 blueprint debt.** Item 6's leaves landed with **no blueprint nodes** (PI, D5: a chapter
  without a complete informal proof would pin a shape likely to be reworked), and `checkdecls`
  cannot see a decl with no node. STEPS pins each law when it consumes it (§3's *There is no
  landed cut-vertex deficiency law* note), or a cleanup round pins the set if the PI reverses D5.
  The debt, `private` helpers exempt: `deficiency_removeVertex_of_degree_eq_one` (A1);
  `deficiencyMerged`, `deficiencySep`, `weldPair`, `pairDelta`, `partitionDef_map`,
  `deficiency_weldPair_eq_deficiencyMerged`, `bddAbove_range_partitionDef_merged`,
  `partitionDef_le_deficiencyMerged` (A2); `pairDelta_le_bodyBarDim`, `deficiency_eq_max` (A3);
  `partitionDef_split_of_vertexTwoCut`, `deficiency_eq_of_vertexTwoCut`, `deficiency_eq_of_vertexTwoCut'`
  (A4/A5); `relScrews`, `jointRows`, `jointMotions`, `weldedRank`,
  `span_jointRows_eq_map_dualAnnihilator`, `finrank_span_jointRows` (B1/B2);
  `inf_span_rigidityRows_span_jointRows_top`, `weldedRank_eq`, `map_screwDiff_comm`,
  `span_jointRows_bot` (B3/B4); `inf_span_rigidityRows_of_vertexTwoCut`,
  `finrank_span_rigidityRows_vertexTwoCut_eq` (B5/B6); `weldedRank_add_finrank_jointMotions_bot`,
  `partitionMotions_le_jointMotions_bot`,
  `screwDim_mul_compl_add_deficiencyMerged_le_finrank_jointMotions` (B7); `pencilLoss`,
  `weldedLoss`, `pencilLoss_nonneg`, `finrank_relScrews_eq`, `weldedLoss_nonneg`,
  `finrank_relScrews_le`, `pencilLoss_vertexTwoCut` (C1ℓ–C4ℓ). **Paid so far:**
  `partitionDef_split_of_vertexTwoCut` (40e build 1, on `lem:deficiency-cut-vertex`); `relScrews`,
  `jointRows` (40g's open, on the green `def:relative-screws`); `inf_span_rigidityRows_of_vertexTwoCut`,
  `finrank_span_rigidityRows_vertexTwoCut_eq` (40g's open; green since 40g build 1, and since 40g's
  close on their own node `cor:block-rank-vertex-two-cut`, the induced corollary of
  `lem:block-rank-two-cut`); `deficiencyMerged`, `partitionDef_le_deficiencyMerged` (40i's open, on
  the green `def:deficiency-merged`). `jointMotions`, `weldedRank` and the rest of the A2/A3 set go to
  their first consumer, COVERAGE, or have none; not SHORT, ORBIT, SPLITOFF or CONTRACT-A (PI
  decision 4(b), 2026-09-27; the design recons of 40j and 40k, 2026-09-28, found that neither
  SPLITOFF's spike nor CONTRACT-A's uses any of them; §3 STEPS).
- **Two `[pending]` entries of `notes/BlueprintExposition.md`** (its `pencil.tex` section), Phase
  40's to write or close: **`thm:pencil-conditional-realization-main-component`** — the fuller
  exposition (the main component as a vector bundle over planar pictures, the flat rank, the
  ear/split-off/contraction/cut steps) is written at Phase 40's close, in Phase 40's chapter; and
  **`thm:pencil-conditional-realization-pair`** (the held kernels) — closes as superseded when
  MOTIVES lands, or is written if a kernel is proved.

## Appendix — the reusable second-reader brief (as used 2026-09-25)

Dispatch a `recon-opus` agent, read-only. The brief says:
- **The role.** A fresh second reader, adversarial: try to refute. A located gap beats a
  confirmation.
- **Hygiene.** Leave `git status` clean. Cite by label, never by line number, since other commits
  land meanwhile. Every foreground command gets an explicit timeout.
- **The return.** The harness refuses subagent report files, so the report is the final message.
  Scratch holds scripts and raw outputs only.
- **Reading.** Read K-main's header, which ends with the standing hypotheses (H). Retrieve claims
  with `ledger.py --label` / `--brief`, not grep. Obey `HARNESS.md` § *Evidence*.
- **Scope.** The claims, in priority order. For Lean-facing claims, open the definition bodies,
  not the docstrings.
- **Method.** Re-derive each proof, and check every citation's hypotheses. Re-run every cited
  driver command. Any new script must be seeded and exact.
- **Deliverable.**
  - a verdict per claim: CONFIRMED / CONFIRMED-WITH-REPAIR / GAP / REFUTED;
  - each repair as exact replacement text keyed by label;
  - new claims under placeholder labels, which the coordinator mints as `MC-` labels;
  - the commands re-run, with timings.

## Appendix — the STEPS recon's tracked spike (verbatim, 2026-09-26)

The STEPS pre-build recon's scratch file `S40eTracked.lean`, kept verbatim because two of its three
pieces land with later groups (§3 STEPS, the settled *Tracked* items):
- (2) `Graph.rigidContract_induce_simple`, with **CONTRACT-R** (landed in 40f's build,
  `Molecule/Pencil/MainComponent/Contract.lean`);
- (3) `polynomial_eval_aeval` and `PanelHingeFramework.finite_setOf_finrank_lt_of_curve`, the
  curve-limit lemma, with **SPLITOFF** (re-compiled verbatim against `52706564` by 40j's design
  recon, importing `…MainComponent.Orbit`; it landed in 40j's B1, `Bridge.lean`, the helper as the
  mirror `MvPolynomial.polynomial_eval_aeval`).

Piece (1), `Graph.three_le_ncard_closedNbhd`, landed in 40e build 1 (`Molecule/Pencil/Motive.lean`).

**Provenance.** It compiled sorry-free against HEAD `c8319ce0` (the 40e opening commit; toolchain
`leanprover/lean4:v4.34.0-rc2`); the coordinator re-ran it there: exit 0, no warnings. **To re-run:**
save it as a `.lean` file and run `lake env lean <file>` from the repository root on a built tree.
Against a tree after 40e build 1, delete piece (1) first, since it then duplicates the landed
declaration (the only error). Re-checked at 40e's close, at HEAD `d57672c0`: the file as written
fails on that duplicate alone, and without piece (1) it exits 0 with no output. Re-checked at 40f's
close, at HEAD `e267d5fc`: without piece (1) it still exits 0 with no output. Piece (2) does not
clash with the landed copy, because the file imports `…MainComponent.Bridge`, not `…Contract`.

```lean
import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.Bridge

/-!
# Phase 40 STEPS pre-build recon — the tracked Lean items (scratch spike)

(1) `h3` from the Lean form of (H);
(2) the simplicity of `G / G[W]` from "no outside vertex has two neighbours in `W`";
(3) the curve-limit lemma: the row rank of an `ofNormals` framework is lower semicontinuous
    along a polynomial curve of normals (the univariate specialization of the landed rank device).
-/

open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K] {α β : Type*}

/-! ## (1) `h3` from (H) -/

/-- A body of degree at least two in a simple graph has at least three members in its closed
neighbourhood. -/
theorem _root_.Graph.three_le_ncard_closedNbhd [Finite α] {G : Graph α β} (hS : G.Simple)
    {v : α} (hdeg : 2 ≤ G.degree v) : 3 ≤ (G.closedNbhd v).ncard := by
  have hnot : v ∉ N(G, v) := fun h => by
    obtain ⟨e, he⟩ := h
    exact hS.toLoopless.not_isLoopAt e v he
  have heq : G.closedNbhd v = insert v (N(G, v)) := rfl
  rw [heq, Set.ncard_insert_of_notMem hnot (Set.toFinite _), ← Graph.degree_eq_ncard_adj]
  omega

/-! ## (2) The simplicity of the contraction at an induced core -/

theorem _root_.Graph.rigidContract_induce_simple {G : Graph α β} (hS : G.Simple) {W : Set α}
    {r : α} (hr : r ∈ W)
    (hatt : ∀ u ∉ W, ∀ c₁ ∈ W, ∀ c₂ ∈ W, G.Adj u c₁ → G.Adj u c₂ → c₁ = c₂) :
    (G.rigidContract (G.induce W) r).Simple := by
  classical
  have hV : V(G.induce W) = W := rfl
  -- a surviving edge never has both ends in `W`
  have hsurv : ∀ e x y, (G.deleteEdges E(G.induce W)).IsLink e x y →
      G.IsLink e x y ∧ ¬ (x ∈ W ∧ y ∈ W) := by
    intro e x y h
    rw [Graph.deleteEdges_isLink] at h
    refine ⟨h.1, fun ⟨hx, hy⟩ => h.2 ?_⟩
    exact (show (G.induce W).IsLink e x y from ⟨h.1, hx, hy⟩).edge_mem
  have hcol : ∀ x, Graph.collapseTo r W x = if x ∈ W then r else x := fun _ => rfl
  -- the collapse is the identity off `W` and sends `W` to `r ∈ W`
  have hout : ∀ {a b : α}, b ∉ W → Graph.collapseTo r W a = b → a ∉ W ∧ a = b := by
    intro a b hb h
    rw [hcol] at h
    by_cases ha : a ∈ W
    · rw [ite_eq_left ha] at h; exact absurd (h ▸ hr) hb
    · rw [ite_eq_right ha] at h; exact ⟨ha, h⟩
  have hin : ∀ {a : α}, Graph.collapseTo r W a = r → a ∈ W := by
    intro a h
    rw [hcol] at h
    by_cases ha : a ∈ W
    · exact ha
    · rw [ite_eq_right ha] at h; exact h ▸ hr
  have hcolW : ∀ {a : α}, a ∈ W → Graph.collapseTo r W a = r := by
    intro a ha; rw [hcol, ite_eq_left ha]
  have hcolO : ∀ {a : α}, a ∉ W → Graph.collapseTo r W a = a := by
    intro a ha; rw [hcol, ite_eq_right ha]
  refine Graph.rigidContract_simple (fun e x y h hxy => ?_)
    (fun e₁ e₂ x₁ y₁ x₂ y₂ h₁ h₂ hx hy => ?_)
  · obtain ⟨hl, hnW⟩ := hsurv e x y h
    rw [hV] at hxy
    by_cases hx : x ∈ W <;> by_cases hy : y ∈ W
    · exact hnW ⟨hx, hy⟩
    · rw [hcolW hx, hcolO hy] at hxy; exact hy (hxy ▸ hr)
    · rw [hcolO hx, hcolW hy] at hxy; exact hx (hxy ▸ hr)
    · rw [hcolO hx, hcolO hy] at hxy
      subst hxy
      exact hS.toLoopless.not_isLoopAt e x hl
  · obtain ⟨hl₁, hn₁⟩ := hsurv e₁ x₁ y₁ h₁
    obtain ⟨hl₂, hn₂⟩ := hsurv e₂ x₂ y₂ h₂
    rw [hV] at hx hy
    -- one end outside `W` pins the other edge's end there too
    have key : ∀ {a b c : α}, a ∈ W → b ∉ W → c ∈ W → G.IsLink e₁ a b → G.IsLink e₂ c b →
        e₁ = e₂ := by
      intro a b c ha hb hc h1 h2
      have := hatt b hb a ha c hc ⟨e₁, h1.symm⟩ ⟨e₂, h2.symm⟩
      subst this
      exact hS.eq_of_isLink h1 h2
    by_cases hx₁ : x₁ ∈ W
    · have hy₁ : y₁ ∉ W := fun h => hn₁ ⟨hx₁, h⟩
      rw [hcolW hx₁] at hx
      rw [hcolO hy₁] at hy
      have hx₂ := hin hx.symm
      obtain ⟨-, rfl⟩ := hout hy₁ hy.symm
      exact key hx₁ hy₁ hx₂ hl₁ hl₂
    · rw [hcolO hx₁] at hx
      obtain ⟨hx₂, rfl⟩ := hout hx₁ hx.symm
      by_cases hy₁ : y₁ ∈ W
      · rw [hcolW hy₁] at hy
        have hy₂ := hin hy.symm
        exact key hy₁ hx₁ hy₂ hl₁.symm hl₂.symm
      · rw [hcolO hy₁] at hy
        obtain ⟨-, rfl⟩ := hout hy₁ hy.symm
        exact hS.eq_of_isLink hl₁ hl₂

/-! ## (3) The curve-limit lemma -/

/-- Evaluating a polynomial substitution of univariate polynomials. -/
theorem polynomial_eval_aeval {σ : Type*} (c : σ → Polynomial K) (Q : MvPolynomial σ K) (t : K) :
    (MvPolynomial.aeval c Q).eval t = MvPolynomial.eval (fun i => (c i).eval t) Q := by
  rw [MvPolynomial.aeval_def, ← Polynomial.coe_evalRingHom, MvPolynomial.hom_eval₂]
  congr 1
  ext a
  simp [Polynomial.coe_evalRingHom]

/-- **The curve-limit lemma**: along a polynomial curve `t ↦ c(t)` of normals, the row rank of
`ofNormals G ends (c t)` is at least its value at `t = 0` for all but finitely many `t`, provided
every recorded hinge is nonzero at `t = 0`. The univariate specialization of
`PanelHingeFramework.exists_rankPolynomial_of_le_finrank_linking`. -/
theorem PanelHingeFramework.finite_setOf_finrank_lt_of_curve {k : ℕ} [Finite α] [Finite β]
    (G : Graph α β) (ends : β → α × α)
    (hends : ∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2)
    (c : α × Fin (k + 2) → Polynomial K)
    (hne : ∀ e, G.IsLink e (ends e).1 (ends e).2 →
      (PanelHingeFramework.ofNormals G ends (fun p => (c p).eval 0)).toBodyHinge.supportExtensor e
        ≠ 0)
    {N : ℕ} (hN : N ≤ Module.finrank K (Submodule.span K
      (PanelHingeFramework.ofNormals G ends (fun p => (c p).eval 0)).toBodyHinge.rigidityRows)) :
    {t : K | Module.finrank K (Submodule.span K
      (PanelHingeFramework.ofNormals G ends (fun p => (c p).eval t)).toBodyHinge.rigidityRows)
        < N}.Finite := by
  classical
  obtain ⟨Q, hQ₀, hQ⟩ :=
    PanelHingeFramework.exists_rankPolynomial_of_le_finrank_linking G ends hends hne hN
  set P : Polynomial K := MvPolynomial.aeval c Q with hP
  have hPt : ∀ t, P.eval t = MvPolynomial.eval (fun p => (c p).eval t) Q :=
    fun t => polynomial_eval_aeval c Q t
  have hP0 : P ≠ 0 := fun h => hQ₀ (by rw [← hPt 0, h, Polynomial.eval_zero])
  refine (P.roots.toFinset.finite_toSet).subset fun t ht => ?_
  simp only [Set.mem_ofPred_eq] at ht
  simp only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hP0,
    Polynomial.IsRoot.def]
  by_contra h
  exact absurd (hQ _ (by rwa [← hPt])) (not_le.mpr ht)

end CombinatorialRigidity.Molecular
```
