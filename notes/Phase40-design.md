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
opened 2026-09-27** (`notes/Phase40h.md`), design-first from a compiler-checked recon whose new
claims (MC-179)–(MC-182) were second-read first, with B1 next; the three later groups are
provisional. The ORBIT recon is done (2026-09-26, §4), and so is the second reading of its new
claims (MC-173)–(MC-176). This doc replaces the planning note
`notes/pencil/X0-formalization.md` (2026-09-25), whose content moved here and which is now a
pointer. The PI's calls behind the plan are verbatim in `notes/pencil/adjudications.md`
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
and (MC-26)'s links are superseded on the route too; they all stay proved.

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

**Done.** (MC-1)–(MC-3) are formalized in `Molecule/Pencil/MainComponent/Carrier.lean`: admissible
pictures, `L(q)` and `Aff(q)`, `U` (nonempty and Zariski-open, `Graph.exists_mvPolynomial_isMainPicture`),
the `cross₃` picture→normal map, `Graph.X0Attains` and its one-witness upgrade
`Graph.x0Attains_of_exists`, the configuration as a pencil realization with the `X0Dist` leg
`Graph.X0Attains.hasDistinctPencilRealization`, (MC-3)'s scale-and-shift rank invariance, and the
fibre-intersection lemma `MvPolynomial.exists_mem_eval_ne_zero₂`; DUAL-K made the polarity
field-general (§4). (MC-2)'s vector bundle and its irreducible closure are never formed:
`thm:pencil-x0-main-component` is green at its formalized content, with the geometry in
`rem:pencil-x0-main-component`; (MC-3)'s augmented-matrix rank split has no Lean object and is the
remark `rem:pencil-hinge-affine`. (MC-10)(a) moved to COVERAGE. The accepted design (uncurried
pictures, a single `X0Attains`, the β-headroom `_of_card` triple) and every decision are in
`notes/Phase40b.md`. **`Carrier.lean` is at 1 496 lines** (40f's build added the lifting system with
weights), at the ~1500-line tripwire. Its split waited for a commit that would grow it, since a
split rebuilds every Phase-40 module downstream. **That commit is now scheduled: the split lands as
its own commit before 40h's B3** (PI decision 5, 2026-09-27; §3 STEPS, the SHORT entry), along its
section headers: the picture-to-normal API, its polynomial mirror, the configuration as a pencil
framework, the scale-and-shift invariance and the linear pencil condition (CARRIER's C3–C5′) to a
second file, the rest (C1–C2) left behind. B3's locality lemmas then go in the part left behind,
beside `liftingSpace` and `IsAdmissiblePicture`.

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

### STEPS — the local steps of the induction → by group; **CUT/BRIDGE = sub-phase 40e, ✓ closed 2026-09-26** (`notes/Phase40e.md`); **CONTRACT-R = sub-phase 40f, ✓ closed 2026-09-26** (`notes/Phase40f.md`); **CHAIN = sub-phase 40g, ✓ closed 2026-09-27** (`notes/Phase40g.md`); **SHORT = sub-phase 40h, open** (`notes/Phase40h.md`)

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
step-contract prerequisite was built (the step contract, below). `Bricks.lean` is at 1 443 lines:
the commit that would take it past the ~1500-line tripwire splits its vertex-2-cut layer (section
`TwoCutCarriers`) into its own file first. Every decision is in `notes/Phase40g.md`.

| step of (MC-89) | labels, in proof order | 2nd |
|---|---|---|
| CUT / BRIDGE | (MC-52), (MC-53), (MC-55)(ii), (MC-56) | ✓ (MC14) |
| BASE `C_n` | (MC-16) (closed chain), (MC-17), (MC-19)(a) → (MC-21)(a); certificate (MC-134)(a) | ✓ (MC10, MC20) |
| chains `k ≥ 5` | (MC-18)(a), (MC-16), (MC-17), (MC-19)(b) → (MC-20); cert. (MC-134)(b) | ✓ |
| chain `k = 4` | (MC-180) ← the antecedent `G′ + ear₃` (`G.splitOff (x 1) …`), (MC-179)(a), (d), (MC-182), (MC-16) in rank form, (MC-18)(a), (MC-17)'s separated count *(since 2026-09-27; (MC-24)/(MC-25) with (MC-136) off the route)* | ✓ (MC13, 2026-09-27; found by formalization the same day) |
| chain `k = 3` | (MC-181) ← the antecedent `G′ + ear₂`, (MC-179)(b)–(d) ((c) = (MC-135)(ii)'s `k = 2` step with (MC-47)(i)'s span identity), (MC-182), (MC-16) in rank form, (MC-18)(a), (MC-17)'s separated count *(since 2026-09-27; (MC-45)'s `r`-split off the route)* | ✓ (as `k = 4`) |
| chain `k = 2`, `a ≁ b`, `δ₂ ≥ 2` | (MC-176) ← the refined link (MC-173), the parametrized incidence (MC-174) (SHORT's (MC-18)(b)), (MC-175)(i)(ii), (MC-16) at `k = 1, 2`, (MC-18)(a)/(b)'s fibre identifications, (MC-169); orbit (i) and `dim U ≥ 2` by (MC-48)(ii)'s argument under `δ₂ ≥ 2` ((MC-175)(iii), (MC-4)(b), Jackson–Jordán at `G′ + ab` = (MC-172)). (MC-46)/(MC-138) superseded on route (2026-09-26); (MC-177) is (MC-16)'s rank form | ✓ (MC13, 2026-09-26; found by formalization the same day) |
| chain `k ≤ 2`, `δ = 0` | (MC-54) ← (MC-19)(b), (MC-18)(a)/(b), (MC-16); the Lean hypothesis is `def₃(G′) ≤ def₃(G)` (PI decision 4(a), 2026-09-27); `k = 1` with (MC-174) and (MC-48)(ii) goes to ORBIT | ✓ (MC14) |
| SPLITOFF (`k = 1`, `δ ≥ 5`) | (MC-28), (MC-29), (MC-30)(iv) → (MC-31); Jackson–Jordán at `G″` | ✓ (MC11) |
| CONTRACT | (MC-34)–(MC-38) → (MC-39); (MC-59)(b), (c1)–(c3) → (MC-59)(d) | ✓ (MC12, MC14) |
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
    Neither is built. **SHORT (40h) builds the two locality lemmas at B3**, beside their
    definitions after `Carrier.lean`'s split (PI decision 5; `lem:pencil-picture-local`); main-picture
    propagation is not in its plan. For whichever later group needs them, the compiled signatures (proofs in
    `scratch/40g/S40gPrereq.lean`, local to the recon's checkout; propagation is five lines from
    FLAT's `three_add_deficiency_le_finrank_liftingSpace`, no Jackson–Jordán):
    - `Graph.liftingSpace_congr {G : Graph α β} {q q' : α × Fin 2 → K}
      (hq : ∀ w ∈ V(G), ∀ i, q (w, i) = q' (w, i)) : G.liftingSpace q = G.liftingSpace q'`;
    - `Graph.isAdmissiblePicture_congr` (same hypothesis) `: G.IsAdmissiblePicture q ↔
      G.IsAdmissiblePicture q'`;
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
    lines).
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
  - **SHORT = 40h, open** (`notes/Phase40h.md`; design recon done 2026-09-27, opus, compiler-checked;
    PI decisions 1–5 the same day, `notes/pencil/adjudications.md`): the open ears with `k = 2, 3, 4`.
    After CHAIN. The fresh read-only second reading of the new claims (MC-179)–(MC-182) is done
    (2026-09-27; Step MC13, found by formalization; PI decision 1, the ORBIT precedent): confirmed, with
    repairs in place. **40h opened 2026-09-27**, design-first, from the recon's verdict and the PI's
    decisions, with fourteen red nodes (`main-component.tex` §`sec:main-component-short`, and one node
    each in `molecular-induction.tex` and `deficiency.tex`): **7 builds (B1–B7) and the `Carrier.lean`
    split + open + close**. B1 is next.
    - **The route** (the recon's verdict). By the landed ear rank law, `G` attains at a
      configuration where `G[V₁]` attains iff `dim(ρ ⊔ Λ_k) ≥ k + 1 + def₃(G[V₁]) − def₃(G)`.
      - `k = 3, 4` ((MC-181), (MC-180)): the antecedent is `G″ := G.splitOff (x 1) (x 0) (x 2) (e 1)`
        (`G` with its second interior body suppressed, the freed label reused; ORBIT's own
        construction). Re-inserting `x 1` along `x 0 + t u` or `x 2 + t u` ((MC-179)(d)) gains one
        dimension unless `star(x 0) ⊔ star(x 2) ≤ ρ ⊔ Λ_{k−1}`. At `k = 4` that forces the span of the
        tetrahedron `x 0, x 2, x 3, p_b` ((MC-179)(a)), so it cannot happen short of everything. At
        `k = 3` it is excluded by the bilinear lemma ((MC-179)(c), (MC-135)(ii)'s `k = 2` step).
      - The count needs only (MC-182) (`def₃(G″) ≤ def₃(G)`) and the landed lower half
        `Graph.deficiency_induce_add_le_of_ear`. **No `δ`, no exact (MC-17), no (MC-22), (MC-24) or
        (MC-44), no `a ≁ b`, no orbit.** (MC-24)/(MC-136) (the four-orbit collision) and (MC-45)'s
        `r`-split with (MC-26)'s links are off the route.
      - **The genericity order is new** (the EARGEN device, (MC-180)'s Steps 1–2). Fix the `V₁`
        data `(q|V₁, z|V₁)` first, from one configuration where `G″` and `G[V₁]` both attain. Then
        choose the ear pictures and middle heights generically: `G`'s main polynomial with the `V₁`
        coordinates substituted, the antecedent's joint rank polynomial composed with the ear map,
        the tetrahedron determinant, and (`k = 3`) `κ(c, x 0 ∧ x 2)`.
      - `k = 2` ((MC-54), PI decision 4(a)): the hypothesis is `def₃(G[V₁]) ≤ def₃(G)`, plus a
        bridge lemma from a tight partition of `G[V₁]` merging `a, b` (COVERAGE's `δ = 0`). The
        proof is CHAIN-style, one picture: a flat certificate at heights `0` for `λ₂ = 3`.
    - **The step statements** (compiled by the recon, proofs `sorry`), in 40e/40g's explicit-path
      format with (H) = `Graph.IsX0Graph` at `G` and `h₁ : (G.induce V₁).X0Attains K`:
      `Graph.X0Attains.of_openEar_four` and `…_three`, with
      `h₂ : (G.splitOff (x 1) (x 0) (x 2) (e 1)).X0Attains K`; and `Graph.X0Attains.of_openEar_two`,
      with `hdef : (G.induce V₁).deficiency 3 ≤ G.deficiency 3`. Also
      `Graph.splitOff_deficiency_le_of_eq_left` (the reused-label successor of the landed
      `splitOff_deficiency_le`, no call site moved; PI decision 4(c)) and
      `Graph.deficiency_induce_le_of_ear_of_merge` (the `δ = 0` bridge). Kernel-checked
      satisfiability: `θ(1,2,4)` meets the `k = 3` hypotheses, and its antecedent is `θ(1,2,3)` in the
      `k = 2` format.
    - **The line geometry is compiled sorry-free** (standard axioms): the Klein pairing in flat
      coordinates with `κ(p ∧ q, r ∧ s) = det`, the tetrahedron basis, the two-star bound
      `dim(star y ⊔ star y′) ≥ 5` with `star y ⊔ star y′ ≤ ker κ(·, y ∧ y′)`, the bilinear lemma, the plane
      lines (at most 3-dimensional), and the affine-curve independence. The insertion lemma had one
      elementary residual (a basis of `R` extended by two vectors outside it is independent). The
      second reader filled it and proved the insertion lemma's "at least `dim W`" half, which the
      recon's spike did not state and B6's `W = ⊤` branch needs.
    - **The plan for 40h's open** (the recon's build table, with PI decision 5's split and placement):

      | build | content | file | risk |
      |---|---|---|---|
      | B1 | the line geometry, (MC-179); also `linearIndependent_basis_sumElim_two`, `linearIndependent_basis_sumElim_one` and `exists_insertion_ge`, from the second reader's compiled file (`scratch/40h-read/S40hReadGeom.lean`, local to this checkout: a builder pointer, not evidence) | new `MainComponent/Lines.lean`; `pointJoin_add_smul_left` and `pointJoin_self` in `Flat.lean`, beside `pointJoin` (PI decision 5) | low |
      | B2 | (MC-182) as `splitOff_deficiency_le_of_eq_left`; the `δ = 0` bridge; the module docstring's "KT 4.3(ii)" corrected to 4.3(i) | `Induction/SplitOffDeficiency.lean`; `MainComponent/Ear.lean` (990 → ~1060) | low |
      | split | `Carrier.lean` (1 496 lines) split along its section headers, its own commit (PI decision 5; the plan is §3 CARRIER's): C3–C5′ to a second file, C1–C2 left in `Carrier.lean`; the downstream Phase-40 modules rebuild once, and no statement changes | `Carrier.lean` and one new file | low |
      | B3–B4 | EARGEN: picture locality (`liftingSpace_congr`, `isAdmissiblePicture_congr`, the step contract's compiled signatures) beside their definitions, in the part of the split that keeps `liftingSpace` and `IsAdmissiblePicture` (PI decision 5); the ear configuration as a polynomial map over fixed `V₁` data, main-ness and the antecedent's rank polynomial in the ear data | `Carrier.lean` (the locality lemmas); new `MainComponent/EarGen.lean` | high |
      | B5 | `of_openEar_two` | new `MainComponent/Short.lean` | low |
      | B6 | `of_openEar_four` (the tetrahedron; its `W = ⊤` branch uses `exists_insertion_ge`); its docstring cites (MC-180), not (MC-25) | `Short.lean` | medium |
      | B7 | `of_openEar_three` (the bilinear lemma); its docstring cites (MC-181), not (MC-45) | `Short.lean` | medium |

      `Bricks.lean`, `Chain.lean` and `Contract.lean` are untouched, so there is no `TwoCutCarriers`
      split; `Carrier.lean` is split first, as §3 CARRIER planned (PI decision 5, 2026-09-27). Two
      pieces of the step proofs have no compiled form, and the recon's own table put both in B1:
      the affine witness of a nonzero bilinear form (`k = 3`, Case A; B7), and the
      transport of `ρ ⊔ Λ` from meets to joins (B6, B7), unless the ear law is applied at the join
      framework as ORBIT's route does. The blueprint node of each build is in `notes/Phase40h.md`'s
      checklist.
    - **Re-homed and dropped** (PI decisions 2–4):
      - the `k = 1` cell (B8–B9) and (MC-175)(iii) go to **ORBIT** (below);
      - THETA ((MC-139)) dissolves into **COVERAGE**'s strong induction, with a remark and no named
        theorem;
      - (MC-44), (MC-136), (MC-24), the exact (MC-17) and (MC-134)(b) at `k = 3, 4` go to §2's *Not
        needed*;
      - the pins of `jointMotions`, `weldedRank` and A2/A3 go to their first consumer, which is not
        SHORT: SPLITOFF (`δ ≥ 5`), ORBIT ((MC-175)(iii) on `deficiencySep`/`deficiencyMerged`) or
        COVERAGE ((MC-79)'s `δ`).
    - **CHAIN's note is answered:** the `k ≤ 3` ears never need (MC-134)(b) at the actual flag pair.
      - `k = 3, 4` never use `λ_k` alone.
      - `k = 2` uses a flat witness, as CHAIN's hexagon did (the flag pair is in orbit (iv) at it).
      - `k = 1`'s `λ₁ = 2` ((MC-169)) is automatic at an admissible picture.
  - **SPLITOFF**: (MC-28)–(MC-31). 3–5. The compiled curve-limit lemma is in the same appendix.
  - **CONTRACT-A**, the additive core: (MC-67)–(MC-71). After CONTRACT-R. 4–7. It factors out
    the shared part of CONTRACT-R's assembly (PI decision 4, 2026-09-26): `M(t)`, K1, K2, K4, the
    degenerate rank and the coupling are general; the core-plane, K3 and core-rank lemmas are
    specific to the flat core. **It also splits `Contract.lean`** (1 496 lines at 40f's close, at
    the ~1500-line tripwire) along that line: the general pieces to a shared file, the flat-core
    pieces and CONTRACT-R's assembly left behind. The split waits for CONTRACT-A because the
    factoring decides the cut, and the file has no other consumer.
  - **ORBIT**, the `k = 2`, `a ≁ b`, `δ₂ ≥ 2` cell: the refined link (MC-173) and the cell's step
    (MC-176), with (MC-175)(i)(ii). A 2–3-build tail group after SHORT, and so after CHAIN (PI D2,
    2026-09-26). The name is historical: the orbit table (MC-138) and (MC-46)'s count are off the
    route, and no orbit is computed.
    - **Consumes:** CHAIN's (MC-16) at `k = 1, 2` in rank form,
      `rank R_{G′+ear_k} = rank R_{G′} + 5k − 1 + dim(ρ + Λ_k)`. This is
      `BodyHingeFramework.finrank_span_rigidityRows_vertexTwoCut_eq` at `{a, b}`, plus the path
      side's rank `5(k + 1)` and the fact that its `relScrews` is the span of the hinges.
      Both landed in 40g build 1 (`MainComponent/Ear.lean`), as the path brick and the ear rank law
      `BodyHingeFramework.finrank_span_rigidityRows_ear_eq`, which holds at every adjacency (CHAIN
      applies it directly at `(ofNormals G ends p).toBodyHinge`, the polarity entering only per
      hinge through `screwComplementIso_mk_extensor`; ORBIT may do the same). The second side's induced graph is the path because
      `a ≁ b`. Instantiate the lemma at `pointJoinFramework G ends (pencilConfigPoint q z)`, whose
      `relScrews` are the workbook's `ρ`, `Λ_k` in `⋀²K⁴` as written, and move each rank to
      `X0Attains`'s `ofNormals` form by `ofNormals_toBodyHinge_eq_mapSupport_pointJoinFramework`
      and `BodyHingeFramework.finrank_span_rigidityRows_mapSupport`; the `G′` side's rank is
      `X0Attains(G′)`'s by `PanelHingeFramework.finrank_span_rigidityRows_ofNormals_congr` once
      `G[V(G′)] = G′`.
      It also consumes SHORT's (MC-174) and (MC-48)(ii), and (MC-18)'s two fibre identifications.
    - **The antecedent** is `G₁ = G.splitOff x₂ x₁ b e`, with `e` a freed label.
    - **(MC-173)'s curve** goes through `Matrix.finite_setOf_not_linearIndependent_rows_of_polynomial`
      and `exists_polynomial_ne_zero_of_linearIndependent_at`. Its frame basis of `Λ²` is
      `exteriorPower.ιMulti_family_linearIndependent_field` (in the join model no carrier lemma is
      needed; `panelSupportExtensor_linearIndependent_iff` covers only pure panel-hinge families,
      and (MC-173)'s family is a basis of `ρ` plus hinges).
    - **The step** does not have the STEPS contract's one-picture shape: `G₁`'s picture puts `x₁`
      on the zero line of `h_a − h_b`, which depends on the `G′` heights. The order is `q` on
      `V(G′)` (each graph's polynomial reduced to a nonzero coefficient in those coordinates); then
      `(z′, q_x)` by (MC-174); then a common point in `L_{G₁}` by
      `MvPolynomial.exists_mem_eval_ne_zero₂`; then `(q_{x₁}, q_{x₂})` off (MC-173)'s chart
      polynomial and `Graph.exists_mvPolynomial_isMainPicture` at `G`. `G`'s heights come from
      `z′` by (MC-18)(a). It ends at `Graph.x0Attains_of_exists`, and needs no `δ`, (MC-17),
      (MC-22) or (MC-44).
    - *(The Consumes, curve and step bullets were repaired at the second reading of
      (MC-173)–(MC-176), 2026-09-26.)*
    - **The `k = 1` cell, folded in from SHORT** (PI decision 2, 2026-09-27; the SHORT recon's B8–B9).
      This is (MC-54) at `k = 1`: `Graph.X0Attains.of_openEar_one` (compiled statement, proof `sorry`).
      It has SHORT's explicit-path format at `k = 1` with `hnadj : ¬ G.Adj a b`, `h₁`, `hdef` as in
      `of_openEar_two`, and `hδ₂ : (G.splitOff (x 0) a b (e 0)).deficiency 2 + 2 ≤
      (G.induce V₁).deficiency 2`. The proof chooses the ear body's picture jointly with the `V₁`
      heights by (MC-174), since `L_G(q)` is a hyperplane section of `L_{G′}(q)` there. `rank D ≥ 2`
      comes from **U2**, (MC-48)(ii)'s argument: BRIDGE's JJ at the split-off `G.splitOff (x 0) a b
      (e 0)` (= `G′ + ab`, simple as `a ≁ b`), FLAT's (MC-4)(b) at `G[V₁]`, and `hδ₂`. `λ₁ = 2` is
      automatic at an admissible picture. It needs SHORT's EARGEN device (40h's B3–B4). Builds: (MC-174)
      and U2 about 1; `of_openEar_one` about 1.
    - **(MC-175)(iii)** (`δ₂ ≥ 2 ⟹ def₂(G′ + ab) ≤ def₂(G′) − 2`, on Layer A's `deficiencySep` and
      `deficiencyMerged`) is ORBIT's too (PI decision 4(b)). Both the `k = 2` cell and COVERAGE's
      `k = 1` use feed it into U2.
    - [ ] **Tracked (the coordinator's flag, 2026-09-27): trace the supply of `of_openEar_one`'s
      `hδ₂` at ORBIT's recon.** At COVERAGE's `k = 1`, `δ = 0` use, the theorem's
      `hδ₂ : def₂(G.splitOff (x 0) a b (e 0)) + 2 ≤ def₂(G[V₁])` must be supplied. It fails at
      `K_{2,3}` (`def₂(C₄) = 1`), which FLAT covers instead.
    - **Build commits:** (MC-173) about 1, the step 1–2, and the `k = 1` cell about 2 (so 4–5 in
      all).

  **Order** (PI, 2026-09-26): 40e's open and build first, then a read-only ORBIT recon (opus)
  before the next group opens. Both are done; the ORBIT verdict is in §4. The read-only fresh
  second reading of (MC-173)–(MC-176) (PI D1) is done too (2026-09-26): no refutation and no gap,
  repairs applied in place, (MC-177) and (MC-178) added. **40f opened design-first as
  CONTRACT-R** (2026-09-26), from a compiler-checked design recon, and closed the same day after
  one build commit. **CHAIN opened as 40g** (2026-09-27), design-first from a compiler-checked
  recon, and closed the same day after two build commits. **SHORT opened as 40h** (2026-09-27),
  design-first from a compiler-checked recon, after the fresh read-only second reading of its new
  claims (MC-179)–(MC-182) (PI decision 1) confirmed them, with repairs in place; B1 is next.
  ORBIT's dependencies do not touch CONTRACT-R.
- [x] **Tracked for CHAIN's design pass (the second reading of (MC-173)–(MC-176), 2026-09-26):
  settled by CHAIN's design recon (2026-09-27).**
  - **(MC-177) is built in CHAIN, forced**: BASE and the open ear both go through the ear rank law.
    ORBIT (`k = 1, 2`, `a ≁ b`) and SHORT (`k = 3, 4`) then consume the same law. It is built with
    equalities, since SHORT's (MC-24) needs the `≤` direction.
  - **B6 at `pointJoinFramework` or a transport lemma: CHAIN needs neither.** It applies B6′ and the
    ear law, which hold at any framework, directly at `(ofNormals G ends p).toBodyHinge`, the
    framework `X0Attains` reads; the polarity enters only per hinge. ORBIT's recommended route
    stays available (the ear law at `pointJoinFramework`, the rank moved by the landed `mapSupport`
    lemmas), and no `relScrews`/`mapSupport` transport lemma is needed by anyone yet.
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
  - [x] **The SPLITOFF curve-limit lemma** (lands with SPLITOFF). Its shape is
    `PanelHingeFramework.finite_setOf_finrank_lt_of_curve`, compiled: along a polynomial curve of
    normals whose hinges are nonzero at `t = 0`, the rank is at least its value at `t = 0` for all
    but finitely many `t`. It is the landed rank device composed with the curve. (MC-30)(ii)'s
    rational curve is cleared by rescaling every body by its denominator
    (`finrank_span_rigidityRows_ofNormals_smul`). Main-ness and membership along the curve stay
    SPLITOFF's own obligations. The compiled lemma, with its helper `polynomial_eval_aeval`, is
    verbatim in the appendix *the STEPS recon's tracked spike*.
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
    product of polynomials can align.
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
    curve.
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
| (MC-62), (MC-63), (MC-67), (MC-68)(d), (MC-69)(a) → (MC-69)(b), (MC-70), (MC-71) | MC15 | ✓ 09-25 (one merge step supplied) |
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
`Graph.deficiency_induce_le_of_ear_of_merge`, and the antecedent `G.splitOff (x 1) (x 0) (x 2) (e 1)`
satisfying (H).

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
green, and so are STEPS' first three, `sec:main-component-cut` (40e),
`sec:main-component-contract` (40f) and `sec:main-component-chain` (40g); the fourth,
`sec:main-component-short` (40h), is open and red; MOTIVES's stub subsection
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
  `lem:block-rank-two-cut`). `jointMotions`, `weldedRank` and the A2/A3 set go to their first consumer: SPLITOFF, ORBIT or COVERAGE, not SHORT (PI decision 4(b), 2026-09-27; §3 STEPS).
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
  curve-limit lemma, with **SPLITOFF**.

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
