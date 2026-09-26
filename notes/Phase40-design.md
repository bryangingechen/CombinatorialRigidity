# Phase 40 — PENCIL-X0: the `X₀` formalization of the pencil conjecture (design doc)

**Status: LIVE** (opened 2026-09-25). This is the cross-phase plan for Phase 40, the
sub-lettered home in the `notes/PhaseN-design.md` pattern (`notes/CLAUDE.md`): the target, the
index of work already done, the layer plan by **stable codes**, the proof map, the risks, and the
standing constraints. Sub-phases get a letter and a work log `notes/Phase40x.md` only when they
open. **40a = SPINE2 closed 2026-09-25** (`notes/Phase40a.md`); **40b = CARRIER closed 2026-09-26**
(`notes/Phase40b.md`); **40c = FLAT closed 2026-09-26** (`notes/Phase40c.md`); **40d = BRIDGE
closed 2026-09-26** (`notes/Phase40d.md`); **STEPS runs by group: 40e = CUT/BRIDGE opened
2026-09-26** (`notes/Phase40e.md`), the six later groups provisional (§3 STEPS). This doc replaces the
planning note `notes/pencil/X0-formalization.md` (2026-09-25), whose content moved here and which
is now a pointer. The PI's calls behind the plan are verbatim in `notes/pencil/adjudications.md`
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
| the informal mathematics, (MC-1)–(MC-171) | `notes/pencil/workbook/K-main.md` §(K-main). Steps MC1–MC9 are in that file; MC10–MC21 are one file each, `K-main-MCnn.md` (the index is in `K-main.md`). Query with `python3 notes/ledger.py --label '(MC-89)'`, `--brief …` | written; second-read (§3's proof map, column *2nd*) |
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
sanity check.

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
`notes/Phase40b.md`.

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

### STEPS — the local steps of the induction → by group; **CUT/BRIDGE = sub-phase 40e, opened 2026-09-26** (`notes/Phase40e.md`)

| step of (MC-89) | labels, in proof order | 2nd |
|---|---|---|
| CUT / BRIDGE | (MC-52), (MC-53), (MC-55)(ii), (MC-56) | ✓ (MC14) |
| BASE `C_n` | (MC-16) (closed chain), (MC-17), (MC-19)(a) → (MC-21)(a); certificate (MC-134)(a) | ✓ (MC10, MC20) |
| chains `k ≥ 5` | (MC-18)(a), (MC-16), (MC-17), (MC-19)(b) → (MC-20); cert. (MC-134)(b) | ✓ |
| chain `k = 4` | (MC-22), (MC-19)(b) `k = 2, 4` → (MC-24), (MC-25); `⋂Λ₄ = 0` (MC-136) | ✓ |
| chain `k = 3` | (MC-22), (MC-19)(b) `k = 2, 3` → (MC-45); `r = 1` via (MC-26) and (MC-135); `r = 2` via (MC-47)(i)'s span identity; `r ≥ 3` via (MC-26)'s link | ✓ (MC13, MC20) |
| chain `k = 2`, `a ≁ b`, `δ₂ ≥ 2` | (MC-46) ← orbit table (MC-138), (MC-26)'s link, (MC-18)(b), (MC-19)(b) `k = 1`, (MC-22); `dim U ≥ 2` by (MC-48)(ii); Jackson–Jordán at `G′ + ab` | ✓ |
| chain `k ≤ 2`, `δ = 0` | (MC-54) ← (MC-19)(b), (MC-18)(a)/(b), (MC-16) | ✓ (MC14) |
| SPLITOFF (`k = 1`, `δ ≥ 5`) | (MC-28), (MC-29), (MC-30)(iv) → (MC-31); Jackson–Jordán at `G″` | ✓ (MC11) |
| CONTRACT | (MC-34)–(MC-38) → (MC-39); (MC-59)(b), (c1)–(c3) → (MC-59)(d) | ✓ (MC12, MC14) |
| THETA | (MC-21)(b) ← (MC-21)(a), (MC-20), and (MC-139) | ✓ (MC20) |

- **Lean reuse.** The deficiency laws `rigidContract_deficiency_eq`,
  `deficiency_eq_of_cutEdges_ncard_le_one`, `removeVertex_deficiency_ge`,
  `deficiency_le_deficiency_of_le_vertexSet_eq`, and Phase 39 item 6's Layers A–C: the vertex
  2-cut law `deficiency_eq_of_vertexTwoCut`, the gluing identity
  `finrank_span_rigidityRows_vertexTwoCut_eq`, and the loss carriers in
  `Molecule/Pencil/TwoCut.lean`.
- **There is no landed cut-vertex deficiency law.** 40e lands one (`lem:deficiency-cut-vertex`,
  in `Deficiency.lean`), and its proof consumes item 6's A4 split
  `partitionDef_split_of_vertexTwoCut` at a repeated vertex, so 40e pins it. Item 6's leaves have no
  blueprint nodes (Phase 39's D5 debt); STEPS pins each when it consumes it.
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
  - The ear steps also need picture locality (`L`, admissibility, main-ness and rank read the
    picture only on `V(Γ)`; the rank half is 40e's `finrank_span_rigidityRows_ofNormals_congr`) and
    main-picture propagation (admissible with `dim L ≤ 3 + def₂` is main).
- **The provisional grouping** (PI, 2026-09-26, "Accept"; codes until each opens, letters minted
  only then; `notes/pencil/adjudications.md`). In dependency order, with build-commit estimates:
  - **CUTBRIDGE = 40e**: (MC-52), (MC-53). 3–4.
  - **CONTRACT-R**, the `def₂`-rigid core: (MC-34)–(MC-39), (MC-59). Reuses Phase 22i's projected
    Case-I machinery, FLAT, Jackson–Jordán, `rigidContract_deficiency_eq`, and the Cramer section.
    The rescaled lifting system `M(t)` and its kernel at `t = 0` are new. 6–9.
  - **CHAIN**: (MC-16)–(MC-19), (MC-134)(a)(b), (MC-169), BASE (MC-21)(a), chains `k ≥ 5` (MC-20).
    Pins Layer B (`relScrews`, `jointMotions`) and A2/A3 (D5 debt); `CycleData` fits BASE.
    `ChainData` does not fit: it forces `d = n` and a fresh label. 6–10.
  - **SHORT**: (MC-22), (MC-24), (MC-44), (MC-25)/(MC-136), (MC-45)/(MC-135)/(MC-26)/(MC-47)(i),
    (MC-54), THETA (MC-139). After CHAIN. 8–12.
  - **SPLITOFF**: (MC-28)–(MC-31). 3–5.
  - **CONTRACT-A**, the additive core: (MC-67)–(MC-71). After CONTRACT-R. 4–7.
  - **ORBIT**: (MC-46), (MC-138), (MC-48)(ii). After CHAIN and SHORT. Size unknown (§4).

  **Order** (PI, 2026-09-26): 40e's open and build first, then a read-only ORBIT recon (opus)
  before the next group opens.
- **Tracked from CARRIER's close and BRIDGE's recon (2026-09-26): settled by the STEPS pre-build
  recon (2026-09-26).** Each verdict below is compiled where it is a Lean question (the spike files
  are kept for the build, `notes/Phase40e.md`), and lands with the group that consumes it.
  - [x] **The SPLITOFF curve-limit lemma** (lands with SPLITOFF). Its shape is
    `PanelHingeFramework.finite_setOf_finrank_lt_of_curve`, compiled: along a polynomial curve of
    normals whose hinges are nonzero at `t = 0`, the rank is at least its value at `t = 0` for all
    but finitely many `t`. It is the landed rank device composed with the curve. (MC-30)(ii)'s
    rational curve is cleared by rescaling every body by its denominator
    (`finrank_span_rigidityRows_ofNormals_smul`). Main-ness and membership along the curve stay
    SPLITOFF's own obligations.
  - [x] **The CONTRACT rank-device open point: dissolved** (lands with CONTRACT-R). The `G/H`
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
  - [x] **The slice `q′ = (q_O, Q)`: collapse at `p(r)`, with the magnified core `δ := q|_W`** (lands
    with CONTRACT-R). With `q_c(t) = q_r + t·q_c` for `c ∈ W`, `H` is read at `q|_W` and `G/H` at
    `q|_{V(G/H)}`, both at one generic ambient picture, so no slice arises. Translation invariance
    was re-derived and is true, but it is not needed and the translation lemmas stay unlanded. What
    remains is `H`'s rank under the core rescaling `A_t ∈ GL₄`, by the collineation action (to
    confirm at CONTRACT-R's recon).
  - [x] **`(G.rigidContract (G.induce W) r).Simple`**, compiled as
    `Graph.rigidContract_induce_simple (hS : G.Simple) (hr : r ∈ W) (hatt : ∀ u ∉ W, ∀ c₁ ∈ W,
    ∀ c₂ ∈ W, G.Adj u c₁ → G.Adj u c₂ → c₁ = c₂)`, from the landed `rigidContract_simple` (lands
    with CONTRACT-R).
  - [x] **`h3` from (H)**, compiled as `Graph.three_le_ncard_closedNbhd (hS : G.Simple)
    (hdeg : 2 ≤ G.degree v)`, from the vendored `Graph.degree_eq_ncard_adj` (landed in 40e build 1,
    beside `Graph.closedNbhd` in `Motive.lean`).
- [ ] **Tracked todo, not a 40e close gate (PI, 2026-09-26): the "only if" halves of (MC-52)(iv)
  and (MC-53)(iv).** 40e formalizes the "if" halves, the only ones the induction consumes;
  `thm:pencil-x0-cut` and `thm:pencil-x0-bridge` name this item in their remarks. The informal
  proof: at a generic point of `B(G)` the ranks add and each is at most its target, so an attaining
  height of `G` restricts to attaining heights of both pieces, and the restrictions are onto.

### COVERAGE — the structural half and the assembly (pure combinatorics on `def₂`, `def₃`)

| labels | step | 2nd |
|---|---|---|
| (MC-62), (MC-63), (MC-67), (MC-68)(d), (MC-69)(a) → (MC-69)(b), (MC-70), (MC-71) | MC15 | ✓ 09-25 (one merge step supplied) |
| (MC-75)(iii), (MC-76), (MC-77), (MC-78), (MC-79)(i)–(iv) → (MC-80); (MC-87) → (MC-89) | MC16 | ✓ (two readers) |
| coverage ⟹ attainment: (MC-56), (MC-55)(i), (MC-2); strong induction | MC14, MC2 | ✓ |
| the statement proved, (MC-10)(a): `X₀(G)`'s generic point attains `6(|V| − 1) − def₃(G)` (moved from CARRIER at its close; `thm:pencil-x0-generic-attains`'s first sentence) | census | — |

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
green; MOTIVES's stub subsection `sec:main-component-statements` is the last, and each later
layer inserts its subsection before it. It is opened as red nodes transcribed from the proof map
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
- **ORBIT's dimension counting** (the STEPS pre-build recon, 2026-09-26). (MC-46)'s proof, with
  (MC-138)'s table, counts dimensions of incidence varieties and orbits: `dim I ≥ dim S`, fibre
  dimensions, orbit dimensions from Lie-algebra tangent vectors. It has no polynomial-level form,
  and Mathlib lacks the dimension theory, so it will not transcribe as written. The options are a
  new polynomial-level proof of `(P₂)` outside the three families, routing that cell
  (`k = 2`, `a ≁ b`, `δ₂ ≥ 2`) another way in COVERAGE, or building dimension theory. The read-only
  ORBIT recon after 40e's build decides which (PI, 2026-09-26). (MC-18)(b)'s "the zero set of a
  bilinear form of rank `≥ 2` is irreducible and dominates" needs a polynomial-divisibility
  reformulation (medium risk, SHORT).
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
  `partitionDef_split_of_vertexTwoCut` (40e build 1, on `lem:deficiency-cut-vertex`).
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
