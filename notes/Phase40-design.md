# Phase 40 — PENCIL-X0: the `X₀` formalization of the pencil conjecture (design doc)

**Status: CLOSED 2026-09-29** (opened 2026-09-25). Phase 40 proved the pencil conjecture outright
over every infinite field: `pencil_conjecture` and `pencilPair_of_nonempty`
(`MainComponent/Statements.lean`), the standard three axioms. This was the cross-phase plan, the
sub-lettered home in the `notes/PhaseN-design.md` pattern (`notes/CLAUDE.md`): the target, the
index of work already done, the layer plan by **stable codes**, the proof map, the risks and the
standing constraints. It is now the phase's closed record, under the ~1500-line tripwire, with 9
live Lean anchors (into §1, §3 and the appendix, and one to the file); cleanup round 5 compressed
its §3 to cited verdicts (`notes/Phase40-docs.md`, task 8). The sixteen sub-phases, each with
its work log `notes/Phase40x.md`: **SPINE2** = 40a; **CARRIER** = 40b; **FLAT** = 40c; **BRIDGE**
= 40d; **STEPS** by group, CUT/BRIDGE = 40e, CONTRACT-R = 40f, CHAIN = 40g, SHORT = 40h, ORBIT =
40i, SPLITOFF = 40j, CONTRACT-A = 40k; **COVERAGE** as REDUCE = 40l and CHAINS + THEOREM-S = 40m;
**MOTIVES** as DIST+BASE = 40n, EARS = 40o and REDUCE+CLOSE = 40p (§3). Route B ((MC-183)–(MC-193),
`notes/pencil/workbook/K-main-MC19.md`) replaced the planned fibre route to the generic statement
(§3 MOTIVES). The held fallback of §6 was **retired** at the close (PI, 2026-09-29). This doc
replaced the planning note `notes/pencil/X0-formalization.md` (2026-09-25), now a pointer; the PI's
calls behind the plan are verbatim in `notes/pencil/adjudications.md`. **Carried past the close:**
the tracked cleanup-round items, indexed in §7.

**§2 indexes the written, second-read mathematics the route consumed**; the job was transcription
and formalization, not re-derivation.

## 1. Target and decided calls

- **The headline.** `pencil_conjecture_of_X0` (Phase 39's closing item L0, `notes/Phase39.md`
  item 0) carries two consumer-shape hypotheses. Phase 40 discharges them.
  - `X0Dist K α β` says every simple 2EC `G` with `3 ≤ |V(G)|` has
    `HasDistinctPencilRealization K 3 G`. This is (MC-157) restricted to 2EC graphs.
  - `X0Gen K α β` says the same graphs, when `PencilNondegFeasible K G` holds, have
    `HasGenericPencilRealization K 3 G`. This is (MC-133)(ii) restricted likewise.

  **Phase 40 closes** when both are theorems and a headline carrying neither has landed. The
  headlines are both (PI, 2026-09-28): `pencil_conjecture`, L0's spanning shape
  (`pencil_conjecture_of_X0 x0Dist x0Gen`), and the stronger `pencilPair_of_nonempty` it rests on
  (every nonempty `G`; no `[Nonempty α]`, `[DecidableEq β]` or spanning hypothesis).
- **Field: every infinite field** (PI, 2026-09-25): `[Infinite K]`, no `CharZero`. The informal
  proof is written in characteristic 0 modulo Jackson–Jordán, and over any infinite field modulo
  (MC-33)(i) (the (MC-166) audit). SPINE2 removes the Jackson–Jordán dependence field-generally.
- **Architecture.** The simpler `pencil_conjecture_of_arms_pair` route. The landed `hK`,
  `hbareSplit`, `pencilPair_of_splitOff_of_habitat` and
  `pencil_conjecture_of_hcontract_hK_hbareSplit_of_card` are protected: not edited and not
  consumed.
- **Held until MOTIVES landed, then retired** (PI, 2026-09-25 and 2026-09-29): the kernels
  (K-res)/`kres`, (K-c) and (K-bare-c) with (α), and smark's O7e programme, with the rest of §6.
  smark is closed.
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
| the superseded split/contract route | `notes/pencil/W4-reopen.md` (retired record), `W4-reopen-archive.md`, `workbook/W4.md` | retired 2026-09-29 (§6) |

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

By COVERAGE's design recon (2026-09-28; the PI's call at 40l's open), the Step MC15–MC16 claims its
Lean route does not consume join the list:
- (MC-62) and (MC-63), the orbit dimensions and the structure of `δ₂` (the ORBIT steps and COVERAGE
  take `δ₂` as a deficiency inequality);
- (MC-75)(ii), (MC-77), (MC-78), and (MC-79)(i)'s formula, (iv) and (vi): the partition into maximal
  rigid sets, its quotient and Lemma T, which the departures D1–D3 replace (§3 COVERAGE);
- (MC-81)–(MC-85), (MC-88) and (MC-119)–(MC-121).

Caveat: they are not consumed **by this route**. All stay proved, and they return if a re-route takes
the workbook's argument through the partition into maximal rigid sets (and (MC-67) with
(MC-119)/(MC-120)).

By MOTIVES' design recon (2026-09-28; route B, (MC-183), the PI's calls at 40n's open), the Step
MC19 claims its Lean route does not consume:
- (MC-123)(⇐): feasibility of the smaller graph comes by restriction ((MC-186)(b));
- (MC-124), (MC-125) and (MC-128): no hub-plane chart `Z(G)` is formed, and no class theorem is used;
- (MC-126)(iii)–(v), and (MC-126)(i)–(ii) as stated ((MC-185), (MC-186) are the forms consumed);
- (MC-127)(c), the lollipop: route B meets only 2-edge-connected graphs;
- (MC-130)'s own induction, (MC-131) and (MC-132);
- (MC-13)(c)'s "if" direction and (MC-14)'s "only if".

The same caveat applies: all stay proved (or measured), and they return if a re-route runs the generic
motive by (MC-130)'s induction.

## 3. Layer plan (stable codes) and the proof map

Layers are listed in dependency order; a letter was minted when a layer opened as a sub-phase. Every
layer is closed, so each entry is its verdict: what landed and where, the calls that shaped it,
the commits. The *labels* tables are the proof map (claims in proof order, their step, their
second-reading state; `python3 notes/ledger.py --brief <labels>` briefs a layer). Cleanup round 5
compressed the recons' arcs, plan tables and tracked-item lists to these verdicts
(`notes/Phase40-docs.md`, task 8); the blow-by-blow is in git and in each sub-phase's work log.
"PI decision N" numbers that sub-phase's entries in `notes/pencil/adjudications.md`, where every
PI call below is verbatim. Lean that round 4 (`40-simplify`) deleted or restated is marked where
it is named.

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

**Done.** (MC-1)–(MC-3) are formalized in `Molecule/Pencil/MainComponent/Carrier.lean` and
`Configuration.lean` (`sec:main-component-carrier`): admissible pictures, `L(q)` and `Aff(q)`, the
main pictures `U` (`Graph.IsMainPicture`, nonempty and Zariski-open,
`Graph.exists_mvPolynomial_isMainPicture`), `Graph.X0Attains` and its one-witness upgrade
`Graph.x0Attains_of_exists`, the configuration as a pencil realization with the `X0Dist` leg
`Graph.X0Attains.hasDistinctPencilRealization`, (MC-3)'s scale-and-shift rank invariance and the
fibre-intersection lemma `MvPolynomial.exists_mem_eval_ne_zero₂`; DUAL-K made the polarity
field-general (§4). (MC-2)'s vector bundle is never formed: `thm:pencil-x0-main-component` is green
at its formalized content, the geometry in `rem:pencil-x0-main-component`. (MC-3)'s augmented-matrix
rank split has no Lean object (its remark `rem:pencil-hinge-affine` was cut by round 3, task 10,
`a5f782a5`). (MC-10)(a) moved to COVERAGE. The design (uncurried pictures, one `X0Attains`
carrying a Zariski-open set of attaining heights, the slices C1a, C1b and C2–C5′) and every
decision are in `notes/Phase40b.md`; the β-headroom `_of_card` triple it planned was never built,
retired by MOTIVES' recon. **`Carrier.lean` split 2026-09-27** (`3f7f272d`, before 40h's B3, at
1 496 lines; PI decision 5 of 40h, "Convention, split Carrier"): C3–C5′ moved to the new
`Configuration.lean`, and C1–C2 stayed, joined by 40h's locality lemmas.

### FLAT — the flat rank → **sub-phase 40c, ✓ closed 2026-09-26** (`notes/Phase40c.md`)

**Done.** (MC-4)(a)–(c) and (MC-5)(i)–(iii) are formalized in
`Molecule/Pencil/MainComponent/Flat.lean` and `Molecular/Deficiency.lean`
(`sec:main-component-flat`, and `lem:deficiency-antitone`). The compiler-checked recon's route: the
flat (primal) side through C4's rewrites, the split as the linear equivalence `flatScrewEquiv`,
(MC-4)(a) as an exact identity, (MC-4)(b) as the grade-1 relative bound at the normals
`(x_v, y_v, 1)`, (MC-5)(i) in antitone form, and the flat witness
`Graph.x0Attains_of_finrank_liftingSpace_le` (CARRIER's old C5 item). 40a's pin debt was paid on
the new node `lem:relative-deficiency-rank-bound`. The citations for `Φ` are Crapo–Whiteley 1982
Example 4.4 (pp. 72–73) and Whiteley 1996 §8.3, with no identity attributed (§4 *Citations*); the
codim bound `dim L(q) ≥ 3|V| − 2|E|` stays dropped (no consumer; a corollary of (MC-4)(b)).
Decisions: `notes/Phase40c.md`.
- [x] **Cleanup-round item: the wider stand-in audit** of the other `lem:trivial-motions-rank-bound`
  sites, repointing each that means the relative bound. Paid by round 1, `40-cleanup` tasks
  23a–23b (`36aa7e10`, `2d3d3818`).

### BRIDGE — Jackson–Jordán's equality, as it is consumed → **sub-phase 40d, ✓ closed 2026-09-26** (`notes/Phase40d.md`)

**Done.** The equality `dim L(q) = 3 + def₂(G)` at the generic picture is formalized in
`Molecule/Pencil/MainComponent/Bridge.lean` (`sec:main-component-jj`) for every simple `G` with a
body and `|N[v]| ≥ 3` at every body, anywhere in `α`, `β`, over every infinite field, with no
hypothesis on `β` and no connectivity. SPINE2 supplies the form of (MC-33) the proof uses, so
Jackson–Jordán's theorem itself is not used (its field-general write-up stays a fallback, §2); the
informal record is (MC-172) (Step MC11). The consumer forms: the generic form
`Graph.exists_mvPolynomial_finrank_liftingSpace_eq` (one nonzero polynomial in the picture
coordinates whose non-roots are main pictures at `3 + def₂`), the `ℓ₀` form
`Graph.IsMainPicture.finrank_liftingSpace_eq`, the existential form, and with FLAT
`Graph.x0Attains_of_deficiency_two_eq_three` (`cor:pencil-jj-flat`, (MC-89)'s step 3). The recon's
chart route: per-body rescaling moves a common non-root of SPINE2's rank polynomial, the
general-position polynomial and `∏ n(a, 2)` into the chart `(x_v, y_v, 1)`, where FLAT reads the
rank; the edges are first relabelled into `β ⊕ Fin (3|α| + 1)` (`Graph.embedEdges`), where
`Graph.freshEdgeSupply_of_card_lt (n := 2)` supplies SPINE2's `hfresh`. The route never forms
`IsGenericNormals`, so the total-selector open point (40a's Slice 4) dissolved. Decisions:
`notes/Phase40d.md`.
- **The consumer map, for STEPS** (the recon's). At `G`: the existential form, through
  `cor:pencil-jj-flat`. At a core `H = G[W]` (both kinds of CONTRACT): the generic form, and FLAT
  through the corollary. At `G/H = G.rigidContract (G.induce W) r`: the `ℓ₀` form; `rigidContract`
  keeps parallel edges, as the informal `G/H` does, so its simplicity needs `H` induced, and
  `|N[v]| ≥ 3` at the contracted vertex needs `|δ(W)| ≥ 2`, from 2EC. At `G′ + ab` and at
  `G.splitOff x a b e₀` (`a ≁ b`): the generic or `ℓ₀` form. `H`, `G/H` and `G′ + ab` do not span
  `α`, which is why the equality holds anywhere in `α`, on SPINE2's non-spanning row rank. These
  uses' questions became STEPS' settled *Tracked* items; the label-reuse sources are MOTIVES'
  β-headroom bullet.
- [ ] **Cleanup-round item: the edge-restricted, non-spanning generic-normals row rank**, with the
  optional re-base routed here from 40a's Slice 4. The recon compiled three declarations, never
  landed, generalizing `finrank_span_rigidityRows_ofNormals_of_isGenericNormals` (no
  `[Nonempty α]`, no spanning hypothesis, a selector restricted to links); the re-base would derive
  the spanning `PanelHingeFramework.rankHypothesis_genuine_recordsLinks_of_theorem_55_gen` from
  SPINE2's form. Neither is on a consumer path. **Left**, unbuilt with no node: round 3's item 4
  (`notes/Phase40-exposition.md`, which found that `HingeGeneric.lean` and `Steer.lean`, listed by
  the recon as call sites, name it only in docstrings), sanctioned at round 4's Stop 2 (`r4`).

### STEPS — the local steps of the induction → **✓ done 2026-09-28**, by group; **CUT/BRIDGE = sub-phase 40e, ✓ closed 2026-09-26** (`notes/Phase40e.md`); **CONTRACT-R = sub-phase 40f, ✓ closed 2026-09-26** (`notes/Phase40f.md`); **CHAIN = sub-phase 40g, ✓ closed 2026-09-27** (`notes/Phase40g.md`); **SHORT = sub-phase 40h, ✓ closed 2026-09-27** (`notes/Phase40h.md`); **ORBIT = sub-phase 40i, ✓ closed 2026-09-28** (`notes/Phase40i.md`); **SPLITOFF = sub-phase 40j, ✓ closed 2026-09-28** (`notes/Phase40j.md`); **CONTRACT-A = sub-phase 40k, ✓ closed 2026-09-28** (`notes/Phase40k.md`)

Seven groups, each opened design-first from an opus recon. Each group's verdict, then the proof
map, the contract every step shares, the grouping and order, and the tracked items.

**CUT/BRIDGE done** (40e). The "if" halves of (MC-52) and (MC-53), in
`Molecule/Pencil/MainComponent/Cut.lean` (`sec:main-component-cut`): `Graph.X0Attains.of_cutVertex`
and `Graph.X0Attains.of_bridgePath` (a chain of `k + 1` bridges, any `k ≥ 0`, by explicit path
hypotheses), over (H) as `Graph.IsX0Graph`. The cut-vertex laws are
`Graph.deficiency_add_le_of_cutVertex` / `_eq_add_of_cutVertex` (`Deficiency.lean`) and
`BodyHingeFramework.finrank_span_rigidityRows_cutVertex_eq` (`Bricks.lean`), placed by PI decision
3 ("Deficiency/Bricks"). BRIDGE counts along the path with the pendant-body rank law
`BodyHingeFramework.add_le_finrank_span_rigidityRows_induce_union_singleton` and Phase 39's
`Graph.deficiency_induce_union_singleton`; a peeled body has no admissible picture, so BRIDGE cuts
once at the last bridge and telescopes. Decisions: `notes/Phase40e.md`.

**CONTRACT-R done** (40f; restated by round 4). (MC-59)(d) with (MC-39) and its side claims (PI
decision 3): `Graph.X0Attains.of_rigidContract`, at an induced core `H = G[W]` with `def₂(H) = 0`
and no outside body adjacent to two core bodies (`hatt`), in a 2EC `G` satisfying (H), from
`X₀(G/H)` attaining. 40f's one build (`e267d5fc`) moved the picture along the curve `q(t)` that
shrinks the core to `r`'s picture point, with heights in the rescaled lifting system `M(t)`, whose
kernel does not jump at `t = 0`, and read the core's rank as its flat rank. Its general pieces went
beside their definitions (PI decision 1, "Convention everywhere"): `Graph.weightedLiftingMatrix`
(`Carrier.lean`), `Graph.connected_of_isKDof_zero` (`Deficiency.lean`), the projected
rank-polynomial sibling (`CaseI.lean`) and the block coupling (`Coupling.lean`). **Round 4
restated it** as an 18-line corollary of CONTRACT-A (10p `993b9e74`: `cor:pencil-x0-contract-rigid`
in one contraction section, `sec:main-component-contract`; 10q `91755996`: `Contract.lean`) and
deleted the flat-core curve proof. Decisions: `notes/Phase40f.md`.

**CHAIN done** (40g). BASE and (MC-20), open and closed, in
`Molecule/Pencil/MainComponent/Chain.lean` (`sec:main-component-chain`):
`Graph.X0Attains.of_cycle` (the edge `ab` plus the path `a…b`, no (H); PI decision 3),
`Graph.X0Attains.of_openEar` (`k ≥ 5`, `a ∼ b` allowed) and
`Graph.X0Attains.of_closedEar` (`k ≥ 2`; a named theorem although off the route, PI decision 2), in
40e's explicit-path format, with (H) at `G` only and attainment at `G[V₁]`. The rank side is B5′/B6′
over any two link-partitioning graphs (`Bricks.lean`; B5/B6 their induced corollaries, PI decision
1), the path's rank and relative screws (MC-177)(i)(ii) and the ear rank law
`BodyHingeFramework.finrank_span_rigidityRows_ear_eq`, at every adjacency (`Ear.lean`); the
deficiency side is (MC-17)'s lower half, `Graph.deficiency_induce_add_le_of_ear`. (MC-19)(b)'s "for
any flag pair" is replaced by a witness inside the fibre: the height `1` at two middle bodies and
`0` elsewhere lies in `L_G(q)` at every admissible picture, and the hexagon of (MC-134)(a) at a
collapsed picture (`p_a = p_b`) makes six ear joins independent (`k ≥ 4` for the witness, `k ≥ 5`
for six edges). The closed ear is `of_cutVertex` plus `of_cycle`; (MC-21)(a)'s class theorem stays
unstated (`rem:pencil-x0-ear-class`). Decisions: `notes/Phase40g.md`.

**SHORT done** (40h). The open ears with two, three and four interior bodies, the ends possibly
adjacent, in `Molecule/Pencil/MainComponent/Short.lean` (`sec:main-component-short`), over the line
geometry (MC-179) in `Lines.lean` and the ear data over fixed base data in `EarGen.lean`.
`Graph.X0Attains.of_openEar_two` is (MC-54) at `k = 2`, under `def₃(G[V₁]) ≤ def₃(G)` (PI decision
4(a)); `…_four` and `…_three` are (MC-180) and (MC-181), from attainment at `G[V₁]` and at
`G″ = G.splitOff (x 1) (x 0) (x 2) (e 1)`; (H) at `G` only. The count is (MC-182)
(`Graph.splitOff_deficiency_le_of_eq_left`, an additive successor, PI decision 4(c)) with
`Graph.deficiency_induce_add_le_of_ear`. The route: `k = 2` is CHAIN's one-picture route at the
hexagon witness; `k = 3, 4` fix base data first (`Graph.exists_earBase_splitOff`), take two rounds
of genericity, certify the `k = 4` span `Λ²K⁴` at one exhibited ear datum
(`linearIndependent_tetra_witness`) through EARGEN's span transfer, and put `x₂` back at `x₁`'s
point (a vanishing hinge) in place of (MC-179)(d)'s "at least `dim W`" half. (MC-179)–(MC-182) were
found by formalization and second-read before the open (PI decision 1). Placement (PI decision 5):
the locality lemmas `Graph.liftingSpace_congr` and `Graph.isAdmissiblePicture_congr` in
`Carrier.lean`, after its split; the `pointJoin` lemmas in `Flat.lean`. Decisions:
`notes/Phase40h.md`.

**ORBIT done** (40i). The open ears with one interior body, and with two at no bound on the
deficiency, both at non-adjacent ends and under `deficiencyMerged₂(G[V₁]; a, b) + 2 ≤ def₂(G[V₁])`,
in `Molecule/Pencil/MainComponent/Orbit.lean` (`sec:main-component-orbit`):
`Graph.X0Attains.of_openEar_one` ((MC-54) at `k = 1`, under `def₃(G[V₁]) ≤ def₃(G)`) and
`Graph.X0Attains.of_openEar_two_of_splitOff` ((MC-176)), from attainment at `G[V₁]` and at
`G₁ = G.splitOff (x 1) (x 0) b (e 1)`; (H) at `G` only. The merged deficiency is Phase 39's A2
carrier on `def:deficiency-merged`; (MC-175)(iii)'s `≤` half is
`Graph.splitOff_deficiency_add_le_of_deficiencyMerged`. The route: U2 (rank–nullity,
`Graph.two_le_finrank_map_planeDiff`) and (MC-174) (`exists_incidence`) on the lifting system's
kernel; one base for both cells, `Graph.exists_oneEar_base`, choosing the ear body's picture
jointly with a kernel point of `G′`; at `k = 2`, (MC-173) in existence form
(`exists_insertion_two`, `Lines.lean`) with EARGEN's span transfer. Off the route: (MC-173)'s chart
polynomial, (MC-48)(i)/(iii), and the `pointJoinFramework` instantiation of the ear law, which is
applied at `(ofNormals …).toBodyHinge`. The name is historical: no orbit is computed, (MC-138)'s
table and (MC-46)'s count being off the route. Decisions: `notes/Phase40i.md`.

**SPLITOFF done** (40j). The split-off step at a body `x 0` of degree two whose neighbours `a ≁ b`
(the one-body ear `a − x 0 − b` on `V₁`), under `deficiencyMerged₃(G[V₁]; a, b) + 5 ≤ def₃(G[V₁])`,
Step MC11's `δ ≥ 5`, in `Molecule/Pencil/MainComponent/SplitOff.lean`
(`sec:main-component-splitoff`): `Graph.X0Attains.of_splitOff`, (MC-31)'s `δ ≥ 5` conclusion, from
attainment at `G″ = G.splitOff (x 0) a b (e 0)`, with no `ℓ₀(G″)` hypothesis (BRIDGE discharges it)
and (H) at `G` only. The route: (MC-28) as a count of motion spaces
(`Graph.finrank_span_rigidityRows_splitOff_special`, through
`BodyHingeFramework.finrank_span_rigidityRows_eq_add_of_motions`); (MC-29) as one inequality,
`def₃(G″) + 1 ≤ def₃(G)`; (MC-30)(i) on the lifting system's kernel
(`Graph.planeDiff_eq_zero_of_splitOff`; `G′` may have bodies of degree 1); (MC-30)(ii), (iv) and
(MC-31) along one polynomial line of flexes and pictures (`exists_mem_forall_add_smul_eq_zero`)
from the non-admissible special point to the general picture, with the curve-limit lemma
`PanelHingeFramework.finite_setOf_finrank_lt_of_curve` (`Bridge.lean`) for the semicontinuity. Off
the route: (MC-30)(iii), and (MC-31)'s bound within one for `δ ≤ 4`, a remark in
`thm:pencil-x0-splitoff`. Decisions: `notes/Phase40j.md`.

**CONTRACT-A done** (40k). (MC-71), with (MC-69)(a) as an inequality and (MC-69)(b), in
`Molecule/Pencil/MainComponent/ContractAdditive.lean` (`thm:pencil-x0-contract-additive`; since
round 4's 10p in `sec:main-component-contract`, CONTRACT-R its corollary).
`Graph.X0Attains.of_additiveContract` takes CONTRACT-R's core data (`hr`, `hWss`, `hW2`, `hatt`),
`hdef3 : def₃(G[W]) = 0` and `hadd : def₂(G[W]) + def₂(G/H) ≤ def₂(G)`, the form (MC-87)(i)'s
proof produces, and concludes from attainment at `H = G[W]` and at `G/H`, (H) at `G` only. The
route: two bounds on `ker M(0)` (`3 + def₂(G)` below, by semicontinuity; (MC-69)(a) above,
`Graph.finrank_ker_contractLiftingMatrix_zero_add_three_le`), with Jackson–Jordán at `H` and `G/H`
and `hadd`, force its core heights onto `L_H(q)`, (MC-69)(b)'s `S ⊆ T`; two open conditions in
`ker M(0)` meet by `exists_mem_eval_ne_zero₂`; and the core's rank is read by a collineation at the
fixed picture `q`, where `X₀(H)` attains (G1,
`PanelHingeFramework.finrank_span_rigidityRows_ofNormals_linearEquiv`, in `Configuration.lean`, and
its instance G2, `Graph.finrank_span_rigidityRows_induce_contractHeight_eq`). These replace
(MC-68)(d)'s core-freeness and (MC-38)'s dominance: a proof-level departure, in the blueprint
proof, not a workbook claim; (MC-67), (MC-68) and (MC-70) are off the route (§2). Placement, option
A (the coordinator's call 5): `Contract.lean` split first, the curve, `M(t)`, the degenerate rank
and the `G/H` standing facts into the new `ContractCurve.lean`. Decisions: `notes/Phase40k.md`.

| step of (MC-89) | labels, in proof order | 2nd |
|---|---|---|
| CUT / BRIDGE | (MC-52), (MC-53), (MC-55)(ii), (MC-56) | ✓ (MC14) |
| BASE `C_n` | (MC-16) (closed chain), (MC-17), (MC-19)(a) → (MC-21)(a); certificate (MC-134)(a) | ✓ (MC10, MC20) |
| chains `k ≥ 5` | (MC-18)(a), (MC-16), (MC-17), (MC-19)(b) → (MC-20); cert. (MC-134)(b) | ✓ |
| chain `k = 4` | (MC-180) ← the antecedent `G′ + ear₃` (`G.splitOff (x 1) …`), (MC-179)(a), (d), (MC-182), (MC-16) in rank form, (MC-18)(a), (MC-17)'s separated count; (MC-24)/(MC-25) with (MC-136) off the route | ✓ (MC13, 2026-09-27; found by formalization the same day) |
| chain `k = 3` | (MC-181) ← the antecedent `G′ + ear₂`, (MC-179)(b)–(d) ((c) = (MC-135)(ii)'s `k = 2` step with (MC-47)(i)'s span identity), (MC-182), (MC-16) in rank form, (MC-18)(a), (MC-17)'s separated count; (MC-45)'s `r`-split off the route | ✓ (as `k = 4`) |
| chain `k = 2`, `a ≁ b`, `δ₂ ≥ 2` | (MC-176) ← the refined link (MC-173) in existence form (`lem:pencil-insertion-two`; its chart polynomial off the route), the parametrized incidence (MC-174) ((MC-18)(b)'s form), (MC-175)(i)(ii), (MC-16) at `k = 1, 2`, (MC-18)(a)/(b)'s fibre identifications, (MC-169); `dim U ≥ 2` by (MC-48)(ii)'s argument under `δ₂ ≥ 2` ((MC-175)(iii), (MC-4)(b), Jackson–Jordán at `G′ + ab` = (MC-172)); (MC-46)/(MC-138) off the route; (MC-177) is (MC-16)'s rank form | ✓ (MC13, 2026-09-26; found by formalization the same day) |
| chain `k ≤ 2`, `δ = 0` | (MC-54) ← (MC-19)(b), (MC-18)(a)/(b), (MC-16); the Lean hypothesis is `def₃(G′) ≤ def₃(G)` (PI decision 4(a), 2026-09-27); `k = 1` with (MC-174) and (MC-48)(ii) in ORBIT | ✓ (MC14) |
| SPLITOFF (`k = 1`, `δ ≥ 5`) | (MC-28), (MC-29), (MC-30)(iv) → (MC-31); Jackson–Jordán at `G″`; (MC-30)(i) on the lifting system's kernel, (MC-30)(ii) a polynomial line; only (MC-31)'s `δ ≥ 5` conclusion on the route | ✓ (MC11) |
| CONTRACT | (MC-34)–(MC-38) → (MC-39); (MC-59)(b), (c1)–(c3) → (MC-59)(d) | ✓ (MC12, MC14) |
| CONTRACT-A (additive core) | (MC-35), (MC-36), (MC-37) steps 2–3, (MC-69)(a) as an inequality, (MC-69)(b) → (MC-71); Jackson–Jordán at `H` and `G/H`; (MC-67), (MC-68) and (MC-70) off the route | ✓ (MC15, MC12) |
| THETA | (MC-21)(b) ← (MC-21)(a), (MC-20), and (MC-139); **dissolves into COVERAGE** (PI decision 3, 2026-09-27): no named theorem, a remark | ✓ (MC20) |

- **Lean reuse.** The deficiency laws `rigidContract_deficiency_eq`,
  `deficiency_eq_of_cutEdges_ncard_le_one`, `removeVertex_deficiency_ge` and
  `deficiency_le_deficiency_of_le_vertexSet_eq`, and Phase 39 item 6's vertex-2-cut gluing
  `finrank_span_rigidityRows_vertexTwoCut_eq`. The plan also listed item 6's 2-cut deficiency law
  `deficiency_eq_of_vertexTwoCut` and the loss carriers of `Molecule/Pencil/TwoCut.lean`; no step
  consumed them, and round 4 deleted both (10b, `c48d323e`).
- **The cut-vertex deficiency law landed in 40e** (`lem:deficiency-cut-vertex`, in
  `Deficiency.lean`), consuming item 6's A4 split `partitionDef_split_of_vertexTwoCut`, which 40e
  pinned. Item 6's other leaves had no blueprint nodes (Phase 39's D5 debt), and STEPS pinned each
  when it consumed it: 40g `relScrews`, `jointRows` and B5/B6, 40i `deficiencyMerged` and
  `partitionDef_le_deficiencyMerged`. The rest of the debt is §7's.
- **The step contract** (the STEPS pre-build recon, 2026-09-26). Every step concludes
  `G.X0Attains K` from `Gᵢ.X0Attains K` at smaller graphs `Gᵢ : Graph α β` (same `α`, same `β`),
  with (H) at `G` (`Graph.IsX0Graph`: simple, connected, degree `≥ 2`) and structural hypotheses.
  It picks one picture generic for every `Gᵢ` and main for `G`, chooses heights inside the one
  fibre `L_G(q)` (`MvPolynomial.exists_mem_eval_ne_zero₂`) and ends at `Graph.x0Attains_of_exists`;
  CONTRACT-R, SPLITOFF and CONTRACT-A move the picture along a curve instead, and ORBIT chooses it
  jointly with a kernel point. No step consumes more than attainment at smaller graphs satisfying
  (H), Jackson–Jordán at named graphs and structural facts, so COVERAGE is a plain strong induction
  on `V(G).ncard`, with no `Covered` predicate; 2EC is not carried but is CONTRACT's step
  hypothesis (for `h3` at `G/H`), which COVERAGE supplies. Every consumed graph reuses labels
  (`splitOff` with a freed label, `G′ + ab` by relinking a chain edge, `G/H` keeping its own), so
  **STEPS forces no `β`-headroom** (§3 MOTIVES). Picture locality was built by SHORT
  (`lem:pencil-picture-local`); main-picture propagation (admissible with `dim L ≤ 3 + def₂` is
  main), compiled by CHAIN's recon, was never built: no layer needed it.
- **The provisional grouping** (PI, 2026-09-26, "Accept"; codes until each opens, letters minted
  only then), each group's route being its *… done* paragraph above:
  - **CUTBRIDGE = 40e, ✓ closed**: (MC-52), (MC-53); three builds and a recon.
  - **CONTRACT-R = 40f, ✓ closed**, the `def₂`-rigid core: (MC-34)–(MC-39), (MC-59); one build
    commit (`e267d5fc`) from the recon's sorry-free spike.
  - [x] **Tracked todo, carried past 40f's close (PI decision 2, 2026-09-26; not a 40f close gate):
    revisit the shape of CONTRACT-R's simplicity hypothesis for readability. Closed at 40l's open
    (PI, 2026-09-28): `hatt` kept**, COVERAGE's producers at both core kinds deriving it from
    maximality. The alternative, `(G/H).Simple`, needs the converse of
    `Graph.rigidContract_induce_simple`. CONTRACT-A keeps `hatt` too (the coordinator's call 4).
  - **CHAIN = 40g, ✓ closed**: BASE, (MC-20) open (`k ≥ 5`) and closed; two build commits
    (`80bcd3bb`, `1cf5b60f`) from one sorry-free spike. It pinned `relScrews`, `jointRows` and
    B5/B6. What it did not consume went to its first consumer (PI decision 4, 2026-09-27), and
    SHORT's recon re-homed it again; (MC-19)(c) and (MC-134)(c) have no consumer (§2).
  - **SHORT = 40h, ✓ closed**: the open ears with `k = 2, 3, 4`; six build commits (`89a9c446` to
    `a3ec5a8d`) and the `Carrier.lean` split, after the second reading of (MC-179)–(MC-182) (PI
    decision 1, the ORBIT precedent). Re-homed and dropped (PI decisions 2–4): the `k = 1` cell and
    (MC-175)(iii) to ORBIT; THETA into COVERAGE; (MC-44), (MC-136), (MC-24), the exact (MC-17) and
    (MC-134)(b) at `k = 3, 4` to §2's *Not needed*; the pins of `jointMotions`, `weldedRank` and
    A2/A3 to their first consumer (ORBIT and COVERAGE paid four A2/A3 names; round 4 deleted
    `jointMotions`, `weldedRank` and most of the unpaid rest, 10b `c48d323e`; §7). No `k ≤ 3` ear
    needs (MC-134)(b) at the actual flag pair, which answers CHAIN's note.
    - [x] **Tracked cleanup-round items, from 40h's close (2026-09-27): paid by round 1**
      (`40-cleanup`; commits in §7's index): the B2 dedupe of
      `Graph.splitOff_deficiency_le_of_eq_left` against `Graph.splitOff_deficiency_le`; the
      three-body step's near-copies (FRICTION *The three-body step repeats the four-body step*,
      resolved in round 1, now in `notes/FRICTION-archive.md`); the pin budget of
      `lem:pencil-ear-data`. The standing **file-size rule** (40h's plan: before `Bricks.lean`
      passes ~1500 lines, split out its vertex-2-cut section `TwoCutCarriers`; before `Short.lean`
      does, its antecedent and base-data layer) never fired: at round 4's close `Short.lean` has
      1 063 lines and `Bricks.lean` 1 251.
  - **ORBIT = 40i, ✓ closed**: the `k = 1` cell (folded in from SHORT, its PI decision 2) and the
    `k = 2`, `a ≁ b`, `δ₂ ≥ 2` cell ((MC-176)), with (MC-173)–(MC-175); a tail group right after
    SHORT (PI D2, 2026-09-26). Three builds (`5ba25337`, `b733f5fe`, `b3dac673`) and a coordinator
    fixup (`6b266906`). It pinned `Graph.deficiencyMerged` and
    `Graph.partitionDef_le_deficiencyMerged` on `def:deficiency-merged`.
    - [x] **Tracked (the coordinator's flag, 2026-09-27): trace the supply of `hδ₂`. Settled by
      ORBIT's design recon (2026-09-28):** both cells take the `deficiencyMerged` form, which
      COVERAGE computes from (S) by (MC-79)(ii)–(iii); chains with `δ₂ ≤ 1` violate (S) and are
      covered before (MC-89)'s step 5. COVERAGE's supplier items settle it.
  - **SPLITOFF = 40j, ✓ closed**: (MC-28)–(MC-31) at `δ ≥ 5`; two builds (`0fdf5d5a`, `2fc2c02c`).
    It paid none of the D5 debt (the coordinator's grep of the spike).
    - [x] **Tracked cleanup-round item (the coordinator's call):**
      `span_supportExtensor_ofNormals_eq` in place of the orientation split inlined in
      `PanelHingeFramework.finrank_span_rigidityRows_ofNormals_congr` (`Cut.lean`). Paid by round 1,
      task 13 (`a0dda000`).
  - **CONTRACT-A = 40k, ✓ closed**: (MC-71) with (MC-69)(a)(b); three commits (`b7e9a778`, the
    split; `8499bb79`; `b394aac3`), factoring out CONTRACT-R's shared assembly (PI decision 4 of
    40f). The recon's G1, G2, G4 and G5 are mapped to Lean names and nodes in `notes/Phase40k.md`'s
    checklist. Option B of call 5, CONTRACT-R re-proved through CONTRACT-A and FLAT, was not adopted
    then; round 4's 10p–10q later restated CONTRACT-R that way. Call 3 rejected the compiled
    `of_additiveContract_weak` (no core rigidity); call 7 found no D5 pin paid; call 8 sent (MC-67),
    (MC-68) and (MC-70) to §2's *Not needed* and the `hadd` supplier to COVERAGE.
    - [x] **Tracked cleanup-round items (call 12):** four corollary rebases onto CONTRACT-A's
      general pieces (via G4, G5, the core-heights lemma and G1). Paid by round 1, tasks 14a–14b
      (`58c4fa28`, blueprint fixup `388e5a18`; `ab2253e1`).

  ORBIT, SPLITOFF and CONTRACT-A had no new mathematics: each opened directly, with no workbook
  commit and no second reading (the coordinator's calls, the 40f/40g precedent). **Order** (PI,
  2026-09-26): 40e's open and build first, then the read-only ORBIT recon (§4, *ORBIT's dimension
  counting*) and the fresh second reading of (MC-173)–(MC-176) that PI D1 asked for (no refutation,
  no gap; (MC-177) and (MC-178) added). Then **40f opened design-first as CONTRACT-R**
  (2026-09-26), **CHAIN opened as 40g** (2026-09-27), **SHORT opened as 40h** (2026-09-27), **ORBIT
  opened as 40i** (2026-09-28, where PI D2 placed it), **SPLITOFF opened as 40j** and **CONTRACT-A
  as 40k** (2026-09-28), each closing the day it opened. **STEPS is done**; COVERAGE followed.
- [x] **Tracked for CHAIN's design pass (the second reading of (MC-173)–(MC-176), 2026-09-26):
  settled by CHAIN's design recon (2026-09-27).** (MC-177) is built in CHAIN, forced: BASE and the
  open ear both go through the ear rank law, built with equalities. No `pointJoinFramework`
  transport is needed: B6′ and the ear law apply directly at `(ofNormals G ends p).toBodyHinge`, the
  framework `X0Attains` reads (ORBIT's recon took the same route).
- [x] **Tracked for SHORT's pre-build recon: re-check (MC-44). Settled by SHORT's design recon
  (2026-09-27):** not in (MC-89)'s tree, so dropped to §2's *Not needed* (PI decision 4(b)); Step
  MC14's claim that (MC-46) uses it was a mis-citation, repaired 2026-09-26.
- **Tracked from CARRIER's close and BRIDGE's recon (2026-09-26): settled by the STEPS pre-build
  recon (2026-09-26)**, each compiled where it was a Lean question (the appendix *the STEPS recon's
  tracked spike*):
  - [x] **The SPLITOFF curve-limit lemma**: `PanelHingeFramework.finite_setOf_finrank_lt_of_curve`,
    landed in 40j's B1 (`0fdf5d5a`, `Bridge.lean`), its helper the mirror
    `MvPolynomial.polynomial_eval_aeval`.
  - [x] **The CONTRACT rank-device open point: dissolved** (40f). The `G/H` framework with the
    actual boundary hinges is never formed: its rank is that of the rows of
    `ofNormals (G.deleteEdges E(H)) endsG`, projected by `(extProj W).dualMap`.
  - [x] **`HoldsGenerally`: not built.** No consumer needs bundle-level genericity;
    `exists_mem_eval_ne_zero₂` suffices throughout, CONTRACT-A's two open conditions included.
  - [x] **The slice `q′ = (q_O, Q)`: collapse at `p(r)`, with the magnified core `δ := q|_W`**
    (40f). `H` is read at `q|_W` and `G/H` at `q|_{V(G/H)}`, both at one generic ambient picture,
    which collapses at `r`'s own picture point: no slice arises, and translation invariance is not
    needed. At a `def₂`-rigid core 40f needed no `A_t` lemma, the core's rank being its flat rank;
    at an additive core CONTRACT-A's G1–G2 are that lemma, and since round 4 CONTRACT-R takes that
    route too.
  - [x] **`(G.rigidContract (G.induce W) r).Simple`**: `Graph.rigidContract_induce_simple` under
    `hatt`, from the landed `rigidContract_simple` (40f; in `ContractCurve.lean` since 40k's split).
  - [x] **`h3` from (H)**: `Graph.three_le_ncard_closedNbhd` (40e build 1, beside
    `Graph.closedNbhd` in `Motive.lean`).
- [ ] **Tracked todo, carried past 40e's close (PI, 2026-09-26; not a 40e close gate): the "only
  if" halves of (MC-52)(iv) and (MC-53)(iv).** 40e formalized the "if" halves, the only ones the
  induction consumes. **Left**, unbuilt with no node: round 3's item 3 (with only `G` under (H) they
  are false; with both sides, a corollary no proof needs), sanctioned at round 4's Stop 2 (`r3`).
  Round 3's task 13 (`9c931242`) cut the remarks after `thm:pencil-x0-cut` and
  `thm:pencil-x0-bridge` that stated them informally.

### COVERAGE — the structural half and the assembly (pure combinatorics on `def₂`, `def₃`) → **two sub-phases (PI, 2026-09-28): REDUCE = sub-phase 40l, ✓ closed 2026-09-28** (`notes/Phase40l.md`); **CHAINS + THEOREM-S = sub-phase 40m, ✓ closed 2026-09-28** (`notes/Phase40m.md`); **COVERAGE done**

| labels | step | 2nd |
|---|---|---|
| (MC-75)(i), (iii); (MC-76), the direction "no `def₂`-rigid set ⟹ (S)" and the count of bodies of degree two; (MC-79)(i) "⇐", (ii), (iii); (MC-80) in the Lean form below; (MC-87)(i) "if", in the `≤` form; (MC-87)(ii) → (MC-89) | MC16 | ✓ (two readers); the Lean proofs of (MC-79)(ii)'s first bullet, (MC-79)(iii) and (MC-87)(ii) are new (D1–D3 below), recorded in the blueprint and not second-read (PI, 2026-09-28) |
| coverage ⟹ attainment: (MC-56), (MC-55)(i), (ii), (MC-2); strong induction | MC14, MC2 | ✓ |
| the statement proved, (MC-10)(a): `X₀(G)`'s generic point attains `6(|V| − 1) − def₃(G)` (`thm:pencil-x0-generic-attains`'s first sentence) | census | — |

(MC-62), (MC-63) and the other unconsumed Step MC15–MC16 claims moved to §2's *Not needed*, with
the caveat there (the PI's call at 40l's open).

**The design recon's verdict** (opus, 2026-09-28, compiler-checked; spikes S1, S4, S5 and S6 in
`scratch/40l/`, gitignored and local to the recon's checkout). The target is
`Graph.IsX0Graph.x0Attains` (every `G` satisfying (H) attains), with MOTIVES' form
`Graph.X0Attains.of_twoEdgeConnected`; no small-`|V|` base, no `β`-headroom. `Graph.IsOpenEar`
bundles the ear format, and `Graph.X0Reduces P G`, a non-recursive inductive with thirteen
constructors (one per landed step, its hypotheses verbatim, `P` at every consumed graph), is one
step; `Graph.X0Reduces.x0Attains` dispatches, and `Graph.X0Attains.of_isX0Graph_of_x0Reduces` is
the plain strong induction (PI, 2026-09-28: not the ruled-out `Covered`). The case analysis
(`Graph.IsX0Graph.x0Reduces`): not 2EC → BRIDGE; a cut vertex → CUT; all degrees two → the cycle;
`def₂ = def₃` → FLAT; a `def₂`-rigid set → CONTRACT-R at a maximal one; otherwise (S), and a usable
chain, or Theorem S's core → CONTRACT-A.

**The sub-phases and their interfaces** (PI, 2026-09-28: three sub-phases with named interfaces; a
second call the same day, after CHAINS' recon, folded THEOREM-S into CHAINS as 40m; both verbatim in
`notes/pencil/adjudications.md`). Each landed, in its own files, against the statements the next
consumes:
1. **REDUCE = 40l, ✓ done 2026-09-28** (B1 `42352cea`, B2 `e6fb3fbf`, B3 `776daad5`;
   `notes/Phase40l.md`): `MainComponent/Coverage.lean` (the thirteen `X0Reduces` constructors,
   `X0Below`, the induction's `hcov`) and `Molecular/Induction/SparseDeficiency.lean` (the
   deficiency kit, (MC-75)(i), (MC-76), (MC-79)(ii)(iii), (MC-87)(i) and D1–D3, in S4's exact form
   but for one dropped hypothesis); all eleven REDUCE nodes green.
2. **CHAINS = 40m, B1–B3, ✓ done 2026-09-28** (B1 `059fbd25`, B2 `13a3d4e1`, B3 `8858f01d`, with
   the coordinator fixup `eb085494`; `notes/Phase40m.md`): `MainComponent/CoverageChain.lean` and
   `MainComponent/CoverageCut.lean`, not the planned `Chains.lean`/`Cuts.lean`, one letter from the
   step files. Interface: `Graph.IsChain`, `IsX0Graph.exists_isChain`, `IsChain.isX0Graph_induce`,
   `IsX0Graph.splitOff` with its four `IsOpenEar` instances, and the cases where every degree is
   two, or `G` is not 2EC or not connected. **The route:** one core, the maximal ear
   `IsOpenEar.exists_maximal`, serves chain extraction and the cycle; BRIDGE runs the same
   extension on a bridge ear with its two sides tracked; the cut arguments go through one gate,
   `Graph.Connected.induce_of_gate`.
3. **THEOREM-S = 40m, B4–B5, ✓ done 2026-09-28** (B4 `a394309a`, B5 `36e66c7a`, with the
   coordinator fixup `61d97b06`): `MainComponent/CoverageTheoremS.lean`, not the planned
   `Cover.lean`. Interface: `Graph.ChainUsable`, `IsChain.x0Reduces_of_chainUsable`,
   `exists_additiveCore_of_rigid` and `exists_additiveCore` ((MC-80) with (MC-87)),
   `x0Reduces_of_sparse`, `x0Reduces`, and **MOTIVES' interface** `Graph.IsX0Graph.x0Attains` and
   `Graph.X0Attains.of_twoEdgeConnected`. All sixteen 40m pins and the eighteen headline results
   were at the standard axioms at 40m's close. **COVERAGE is done.**
- [x] **Tracked cleanup-round item (40m's open): CHAINS' `pathVertex` helpers to `Cut.lean`, their
  definition's file** (left in `CoverageChain.lean` by the 40l precedent). Paid by round 1, task 20
  (`473a4a11`).

**Proof-level departures** (kernel-checked in S4/S5; recorded in the node proofs, not second-read:
PI, 2026-09-28, the 40k precedent; no workbook label added):
- **D1, (MC-87)(ii):** a maximal rigid set avoiding `X₀` (empty, or one body of degree at most two
  with at most one edge into the set) bounds every singleton value above it, by a minimal
  counterexample (`partitionDef_induce_id_le_of_maximal`), in place of the partition into maximal
  rigid sets and its rigid-free quotient ((MC-77)) or (MC-119)'s finest optimal partition.
- **D2, (MC-79)(ii)'s first bullet:** by refining the part of `a, b` in an optimal merged partition
  (`deficiencyMerged_three_add_five_le`), in place of (MC-79)(i)'s formula over the quotient.
- **D3, (MC-79)(iii):** "a tight set of three or more bodies in an (S)-graph is rigid"
  (`deficiency_three_induce_eq_zero_of_tight`), in place of Lemma T (MC-78).
- **D4, THETA:** no θ branch; θ-graphs reach FLAT, CONTRACT-R or a usable chain (measured at
  sixteen), and Theorem S's proof does not exclude them.

**THETA: settled** (PI decision 3, 2026-09-27, with D4). No named theorem and no θ branch;
`rem:pencil-x0-theta` records that the coverage needs no separate case, and keeps (MC-139)'s
covering along the longest path as one covering by the steps alone.

**The tracked supplier items: settled by the design recon**, each landed as named:
- [x] ORBIT's `hδ₂`: at `k = 1`, `Graph.not_adj_and_deficiencyMerged_two_add_two_le` (through
  THEOREM-S' adapter `IsOpenEar.not_adj_and_two_le_pairDelta_two`); at `k = 2`,
  `Graph.deficiencyMerged_two_add_two_le`, consumed in Theorem S. SPLITOFF's `hδ`:
  `Graph.deficiencyMerged_three_add_five_le`, consumed in Theorem S. All three 40l B3.
- [x] CONTRACT-A's `hadd` with `hatt`: `partitionDef_induce_id_le_of_maximal` and
  `deficiency_induce_add_deficiency_rigidContract_le` (40l B3), `hatt` from
  `deficiency_induce_insert_eq_zero` (40l B2) and maximality, assembled in
  `exists_additiveCore_of_rigid`.
- [x] (H) after splitting off at non-adjacent ends: `Graph.IsX0Graph.splitOff` and its four
  instances (CHAINS). SHORT's `hdef` from `δ = 0`: `IsOpenEar.deficiency_induce_le` (THEOREM-S).
- PI decision 2's `hatt` todo: closed, `hatt` kept (§3 STEPS). The "only if" halves of
  (MC-52)/(MC-53): not consumed, the dispatch calling only the "if" halves (§3 STEPS).

**Pins.** COVERAGE paid `partitionDef_map` and `deficiencyMerged_le_deficiency` of the D5 debt (§7)
at 40l. **Lean reuse.** The route uses neither `exists_maximal_induced_isProperRigidSubgraph` nor
`triangle_isProperRigidSubgraph`: the kit has its own maximal rigid superset, and the 4-cycle is
rigid as a tight set (D3). CHAINS reuses the landed `Graph.isLink_eq_of_degree_eq_two` (Phase 23g,
in place of S5's duplicate), `Cut.lean`'s `pathVertex` API and the Matroid package's
`connected_iff_forall_exists_adj` and `exists_of_not_connected`. **Not adopted: Phase 39's
`Induction/ForestSurgery/MaximalChain.lean`** (M1–M3b; the file was deleted by round 4, 10i
`1e7d78a9`), checked by CHAINS' recon at the consumers' slots: its lemmas take `TwoEdgeConnected`,
which BRIDGE's graph lacks, and return `WList` paths, closed walks or `Nonempty G.CycleData` where
the slots take `IsOpenEar`'s `Fin k → α` along `pathVertex`, so every use needed an adapter. Nor
`chainData_of_isPath` (`ChainExtraction.lean`; KT's `ChainData n`, the wrong shape), nor the
Matroid package's `Graph/Connected/Ear.lean` (Whitney's ear decomposition, a different notion).

### MOTIVES — `X0Dist` and `X0Gen` (closes the phase) → **three sub-phases (PI, 2026-09-28): DIST+BASE = sub-phase 40n, ✓ closed 2026-09-28** (`notes/Phase40n.md`); **EARS = sub-phase 40o, ✓ closed 2026-09-29** (`notes/Phase40o.md`); **REDUCE+CLOSE = sub-phase 40p, ✓ closed 2026-09-29** (`notes/Phase40p.md`); **MOTIVES done, and with it Phase 40**

| labels | step | 2nd |
|---|---|---|
| (MC-157) from (MC-89), at the 2EC graphs (`X0Dist`) | MC19 | ✓ 09-25 |
| (MC-183), route B: the generic motive inside the pencil reduction's induction | MC19 | ✓ 09-28 |
| the base, at rigid-free graphs: (MC-184) (`G_e`, (MC-13)(a)–(b), (MC-172)), (MC-12) in the form (MC-189), with (MC-89) and the fibre intersection | MC19, MC8 | (MC-12) ✓; (MC-184) ✓ 09-28; (MC-189) added 09-28 |
| (MC-129) at 2EC graphs (the good ear or a pendant triangle; no lollipop) | MC19 | ✓ 09-25 |
| (MC-186) the formal hubs by steering; (MC-185) the one-ear extension; (MC-127)(b) the pendant triangle; (MC-188) the witness of (MC-186)(a) | MC19 | (MC-127) ✓; (MC-185), (MC-186) ✓ 09-28; (MC-188) added 09-28 |
| (MC-187), the obstruction to the fibre route | MC19 | ✓ 09-28 |
| EARS' forms: (MC-190) the formal hubs at any subgraph; (MC-191) the steering's scope; (MC-192) the pendant triangle's rank at the cut vertex | MC19 | ✓ 09-29 (after the builds); (MC-193) added 09-29, off the route |
| (MC-129) at 2EC graphs by a shorter count (N1–N4: no cycle, no chain walk, the tight-set lemma at step 4) | MC19 | a proof-level departure, recorded in the blueprint and not second-read (the 40l precedent), 09-29 |

**The recon's verdict (opus, read-only, compiler-checked, 2026-09-28; spikes in `scratch/40n/`,
gitignored and local to the recon's checkout).**
- **`X0Dist`** is two lines over landed pieces:
  `(Graph.X0Attains.of_twoEdgeConnected hS hV htec).hasDistinctPencilRealization`.
- **No β-headroom anywhere.** STEPS reuse labels, BRIDGE relabels its edges internally, every EARS
  and REDUCE step removes bodies (`G.induce V₁`), and BASE's auxiliary graph `G_e` is a vertex-type
  change: the Matroid package's `G.apex ↾ (inl '' E(G) ∪ {inr u, inr w}) : Graph (Option α) (β ⊕ α)`
  (the PI's call; import `Matroid.Graph.Constructions.Sum`). CARRIER's `_of_card` triple and the two
  questions this section carried (the `hcard` constant, the headroom's root cause) are retired.
- **The planned fibre route to `X0Gen` fails** at two hubs with three common neighbours, `K_{2,3}`
  the smallest ((MC-187), kernel-checked): `X0Gen` does not follow from `X0Attains` by intersecting
  sets inside one fibre `L(q)`; that argument is sound only at the base.
- **Route B** ((MC-183)). The generic conjunct at a simple 2EC feasible `G` is proved inside
  `Graph.pencil_reduction`'s induction, from `PencilPair` at every smaller graph; the landed cut arm
  covers the non-2EC graphs, so the lollipop (MC-127)(c) never arises. `X0Gen` is a corollary of
  `pencilPair_of_nonempty`, and `pencil_conjecture` consumes `pencil_conjecture_of_X0` verbatim.
  The recon's composition compiled with four new-mathematics leaves as `sorry`: BASE, (MC-129) at
  2EC graphs, (MC-127)(a) and (MC-127)(b).

**The split** (PI, 2026-09-28): **DIST+BASE = 40n** (M0, B1–B3); **EARS** (the chart toolkit
T1–T3, the one-ear step, the pendant triangle); **REDUCE+CLOSE** ((MC-129), the route-B assembly,
both headlines, the phase close).

**DIST+BASE — ✓ done (sub-phase 40n, closed 2026-09-28).** M0 (`8a0752d7`): `x0Dist` in the new
`MainComponent/Statements.lean`, `PencilNondegFeasible.hub_conditions`, the three-body lemma
`Graph.noRigid_of_simple_of_ncard_eq_three` (deleted by round 4, 10j `8f297c7d`) and the two-hubs
obstruction, verbatim from the recon's spikes. The second read of (MC-183)–(MC-187) (`3d1d463f`;
no gap, repairs in place, (MC-188) and (MC-189) added) compiled BASE sorry-free, so B1–B3 landed as
one build (`2f126b5f`): the new `MainComponent/GenericBase.lean`, with `Graph.addTwoEar` there
rather than in `Bridge.lean` (the coordinator's call, keeping the `Sum` import out of
`Bridge.lean`'s downstream cone), and the base
`Graph.IsX0Graph.hasGenericPencilRealization_of_forall_deficiency_two_ne_zero`. Detail in
`notes/Phase40n.md`.

**EARS — ✓ done (sub-phase 40o, closed 2026-09-29).** B1 `e7c80bba` (T1, into
`Pencil/Reseed.lean`), B2 `45d49861` (T2 + T3, the new `MainComponent/GenericSteer.lean`), B3
`f62cfd3c` (Z1, the new `MainComponent/GenericEar.lean`), B4 `306dcf15` (Z2, the new
`MainComponent/GenericTriangle.lean`), the coordinator's fixup `7f782d79`; its pre-build recon
closed every leaf sorry-free (`scratch/ears/`, gitignored). The leaves: T1
`exists_pencilSeed_of_nondeg_of_selectors`, two realizations as chart points of one chart; T2
`exists_isNondegPencilRealization_restrict_of_demoted` ((MC-190)), any subgraph, the demoted hubs
losing only non-hubs; T3 `exists_isNondegPencilRealization_steer` ((MC-191)), needed because the
induction hypothesis says nothing at the demoted ends' closed hub-neighbourhoods; Z1
`Graph.IsOpenEar.hasGenericPencilRealization_of_one`, without `¬ G.Adj a b` (the coordinator's
call: (F2) excludes it at a feasible `G`); Z2 `hasGenericPencilRealization_of_closedEar_two`
((MC-192)), the triangle rigid since its three hinge lines are independent (Crapo–Whiteley 1982,
Proposition 3.4, the calculation KT cite for their Lemma 5.4; `theorem_55_cycle`). The second read
(2026-09-29, opus, fresh, read-only, after the builds) confirmed (MC-190)–(MC-192) against the
landed Lean with no gap, repaired (MC-191) and (MC-192) in place (KT Lemma 5.4's attribution among
the repairs), and added (MC-193), off the route: the count is the Lean chart's (`PencilSeed.ofCoord`
has no free non-hub fills). Detail in `notes/Phase40o.md`.

**REDUCE+CLOSE — ✓ done (sub-phase 40p, closed 2026-09-29).** One build, B1 (`5829cc74`),
transcribed the pre-build recon's complete sorry-free spike (opus, read-only, compiler-checked at
`23f31681`): R, (MC-129) at 2EC graphs, in the new `MainComponent/GoodEar.lean`, by a shorter count
than Step MC19's (N1–N4: the all-hub case at one edge, no chain walk, step 4's rigidity by
`lem:deficiency-tight-rigid`, minimality only through (S)), recorded in the blueprint proof and not
second-read (the 40l precedent; the PI did not overturn it at the close); F1 and both headlines in
`MainComponent/Statements.lean`. (MC-15)(i) step 2's bridgeless form is not landed and not needed.
Detail in `notes/Phase40p.md`.

**Lean reuse.** Used: Phase 39's chart (`PencilSeed`, `pencilChartPoint`, `PencilChartWF`,
`pencilChartFramework`, `exists_pencilSeed_of_nondeg`) and its steering engine
(`exists_common_seed_pencilRow_and_polynomials`, `exists_fillNbr_pencilChartWF_of_standing`,
`finrank_span_rigidityRows_pencilChartFramework_eq_of_independent_pencilRow`);
`IsNondegPencilRealization.mono`; the ear and cut-vertex rank laws; BRIDGE's equality at `G` and
`G_e`; `MvPolynomial.exists_mem_eval_ne_zero₂` (BASE's fibre intersection, the one place the fibre
argument is sound); the landed cut arm `pencilPair_of_not_twoEdgeConnected`. **Not used**, since
the smaller graph's feasibility comes by restriction and route B builds the generic realizations
directly: L6b (`pencilNondegFeasible_of_ncard_closedHubNbhd_le_three_of_triangleFree`), whose
triangle-freeness excludes (F2)'s pendant triangles, and
`hasGenericPencilRealization_of_independent_pencilRow_target` (`|closedHubNbhd| ≤ 3`,
triangle-free); round 4 deleted both (10i, `1e7d78a9`).

**The interface consumed** (landed at 40m, `CoverageTheoremS.lean`): `Graph.IsX0Graph.x0Attains` and
`Graph.X0Attains.of_twoEdgeConnected`, exactly `X0Dist`'s graphs. **The blueprint nodes**: the
fourteen new nodes of `sec:main-component-statements`, the rewritten
`thm:pencil-x0-generic-attains`, and `thm:pencil-conjecture` (`pencil.tex`), red at 40n's open;
40n greened eight of the fourteen, 40o three (EARS') and 40p the rest with both headlines.
`thm:pencil-x0-generic-attains`'s first sentence is COVERAGE's conclusion; its proof runs route B.

### The blueprint chapter

The main-component argument has **one forward-mode chapter**, `main-component.tex`, one subsection
per layer from CARRIER to MOTIVES, all green since 40p: CARRIER's, FLAT's and BRIDGE's; STEPS'
`sec:main-component-cut`, `-contract`, `-chain`, `-short`, `-orbit` and `-splitoff` (CONTRACT-A's
`sec:main-component-contract-additive` merged into `sec:main-component-contract` by round 4's 10p,
`993b9e74`); COVERAGE's `sec:main-component-sparse` and `sec:main-component-coverage`; MOTIVES'
`sec:main-component-statements`. Each layer's section was transcribed when that layer opened, its
statements from `ledger.py --brief` and the recons' compiled spikes, never retyped, and a
**pre-build recon of each transcribed section** ran before the first build against it (the
`/coordinate-phase` transcription guard: a red node's statement is checked by no gate). The Phase
39 nodes `def:pencil-main-component-statements` and
`thm:pencil-conditional-realization-main-component` (`pencil.tex`) are the chapter's consumer end.

## 4. Where formalization may expose mathematics

- **Genericity.** The induction argues about generic points throughout; (MC-157) alone needs
  only one. The delicate places are:
  - dominance, (MC-18)(b);
  - the two-scale and flat limits in contraction, (MC-37), (MC-66), (MC-69);
  - semicontinuity at chord points.

  Each must become an explicit nonzero-polynomial or rational-parametrization statement.
  *Promoted to `DESIGN.md`* *Genericity without dimension theory* (the rule, why, and how it
  landed).
- **Fresh edge labels.** `G′ + ab` and split-off add edges inside a fixed `β`. That calls for
  either a `β`-headroom hypothesis like `hcard` or a type-changing induction; the informal proof
  never meets the issue. **If MOTIVES' proof needs headroom**, `X0Dist`/`X0Gen` as L0 pins them
  (no headroom) are stronger than what is proved. The fix is then an additive successor headline
  carrying `hcard`, not an edit of L0's declarations. **Settled by MOTIVES' recon (2026-09-28): no
  headroom is needed**, and CARRIER's `_of_card` triple is retired. STEPS reuse freed labels, BRIDGE
  relabels its edges internally, MOTIVES' steps only remove bodies, and BASE's `G_e` changes the
  vertex type (`Graph.apex`, §3 MOTIVES), as BRIDGE's `embedEdges` changes the edge type.
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
    builds). What mathlib has and lacks (compiler witnesses and bare-name searches across
    `.lake/packages`, 2026-09-26): *Promoted to `DESIGN.md`* *Genericity without dimension
    theory*.
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
route σ and kernel (K), the kernels retired at the close (`fmlnote:pencil-conditional-realization-pair-field`). The
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
  - *Settled by `40-cleanup` task 22:* the duplicate `mapSupport` is deleted, and `mapExtensor`
    moved up to `RigidityMatrix/Basic.lean` for both consumers. The rank half is not a restatement:
    it is the motion-space finrank, `lem:screw-map-rows` the row-span one, and bridging needs
    `[Finite α]`.
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
  reusable second-reader brief is the Appendix. Why new claims are second-read before a build,
  and the four instances: *Promoted to `DESIGN.md`* *New mathematics found by formalization is
  second-read before it is built on*.
- **Files.** smark is closed (PI, 2026-09-29): `notes/attacks/smark/` and
  `notes/pencil/workbook/attack-smark.md` are its record, not edited. `notes/Phase39-design.md` is
  a frozen archive: append only.
- **Do not:** edit `hK`, `hbareSplit`, `pencilPair_of_splitOff_of_habitat` or the landed Phase 39
  headlines, which stay as conditional theorems; or treat `workbook/W4.md`'s (K-res) statement or
  cost estimates as current.

## 6. Retired fallback (held 2026-09-25, retired 2026-09-29)

**Retired on the PI's word at Phase 40's close** (2026-09-29, verbatim in
`notes/pencil/adjudications.md`, the Phase 40 close entry): "All of design §6". Held until MOTIVES
landed (PI, 2026-09-25), then re-decided; MOTIVES landed, the pencil conjecture is proved by the
main-component route, and nothing below is pursued. The landed Lean on that route stays as
conditional theorems carrying the kernels as hypotheses (`pencilPair_of_splitOff_of_habitat`,
`pencil_conjecture_of_arms_pair`, `pencil_conjecture_of_hcontract_hK_hbareSplit` and its `_of_card`
form); reopening any item is the PI's call. **Round 4 (`40-simplify`, task 10i) retired most of
this Lean** at the PI's 2026-10-04 Stop-2 sanction (`notes/pencil/adjudications.md`):
`pencilPair_of_splitOff_of_habitat` and `pencil_conjecture_of_hcontract_hK_hbareSplit` (and its
`_of_card` form) deleted with `_of_card`'s cluster, the kernel route's two roots, and the girth
chain; `pencil_conjecture_of_arms_pair` stays, generalized to every nonempty graph (`c3`). The
record:
- **The split/contract architecture and its three kernels**, (K-res)/`kres`, (K-c), and
  (K-bare-c) with (α): `notes/pencil/W4-reopen.md` (retired record) and `W4-reopen-archive.md`.
- **smark's O7e programme** on `hK`/`hbareSplit`: smark is CLOSED (the header line of
  `notes/attacks/smark/state.md`; nothing else in the track edited).
- **gr10's Part B fallback** (the grid recipe on the tight stratum, `notes/attacks/gr10/brief.md`
  Part B): retired; gr10 was already closed (2026-09-23).
- **Phase 39's four held checklist items**, moved here at its close (2026-09-25):
  - `hK` on the tight stratum from grid vanishing, the colouring statement as hypothesis
    (decoupling, rank formula, Vandermonde, chart step, descent; the proviso question of
    `notes/attacks/gr10/brief.md` §2 *Proviso (P)*);
  - tree-triple ⇒ `dim Z = 0`, with the circular-ladder family (GUNIZERO's uniform instance) as a
    formal witness;
  - the rest of the W4 build (`notes/pencil/W4-reopen.md`): T1, the W4 wrapper carrying (K-res);
    W4-L4b (`exists_degree_two_of_co1_rigid`, pinned and spike-elaborated); W4-L2/L3′/L5; the
    residual carry `hnoGood'` (W4-L1, W4-A, landed as Phase 39's L0b);
  - the reverse arms of the W0 transport (a `complementIso` involution lemma; the workbook's
    §(K-σ) *Step σ6*).

## 7. Deferred from Phase 39, and carried past Phase 40's close

Moved here at Phase 39's close (2026-09-25). None was on Phase 40's route; each names the layer or
round that lands it, and at Phase 40's close (2026-09-29) every one not paid below is carried to a
post-Phase-40 cleanup round, with the tracked cleanup-round items of §3 (indexed at the end of this
section).

- **A6 — C3, the welded pendant law** `g(H) = max(g(H−u), f_sep(H−u) − (D−1))` and
  `δ(H) = min(δ′+1, D)` (S6(ii)'s remaining clauses; both need `w ≠ v`). Deferred by the PI's D2
  call (2026-09-16): off the consumed path — S6 is the side-degree-1 reduction, S14's `H′` has
  side-degree ≥ 2 at both ends (S10(iii)) — and it is the only law needing `deficiencySep`. Site
  `Induction/SplitOffDeficiency.lean`. Build only if STEPS consumes S6's reduction. **Left at
  round 4's close** (2026-10-04): the condition never fired, and round 3's leave (its item 2) was
  sanctioned at round 4's Stop 2.
- [x] **The shared hub normalization — a factoring item. Paid by cleanup round 2, `40-factor`**
  (`notes/Phase40-factor.md`, tasks 1 and 2: `080be6a4` and `0b260626`; the round closed
  2026-09-30). The extraction landed as the public `Graph.exists_normalized_labeling`
  (`Molecular/Deficiency.lean`), not as a private lemma, because the two hubs are in different
  files (that log's *Decisions*). It has properties (i)–(v) below, and both hubs are rebuilt on it
  with their statements unchanged. The item as specified: C2ℓ's merged hub
  `screwDim_mul_compl_add_deficiencyMerged_le_finrank_jointMotions` (`Molecule/Pencil/TwoCut.lean`)
  duplicated ~85 lines of `screwDim_mul_compl_add_deficiency_le_finrank_infinitesimalMotions`
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
  **Left at round 4's close** (2026-10-04): none was consumed, and round 3's leave (its item 2)
  was sanctioned at round 4's Stop 2.
- **The D5 blueprint debt.** Item 6's leaves landed with **no blueprint nodes** (PI, D5: a chapter
  without a complete informal proof would pin a shape likely to be reworked), and `checkdecls`
  cannot see a decl with no node. STEPS pins each law when it consumes it (§3's *There is no
  landed cut-vertex deficiency law* note), or a cleanup round pins the set if the PI reverses D5.
  The debt, `private` helpers exempt: `deficiency_removeVertex_of_degree_eq_one` (A1);
  `deficiencyMerged`, `deficiencySep`, `weldPair`, `pairDelta`, `partitionDef_map`,
  `deficiency_weldPair_eq_deficiencyMerged`, `bddAbove_range_partitionDef_merged`,
  `partitionDef_le_deficiencyMerged` (A2); `pairDelta_le_bodyBarDim`, `bddAbove_range_partitionDef_sep`,
  `partitionDef_le_deficiencySep`, `deficiencyMerged_le_deficiency`, `deficiencySep_le_deficiency`,
  `deficiency_eq_max` (A3; the four middle names added at 40l's open, checked against
  `Deficiency.lean`'s module docstring);
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
  the green `def:deficiency-merged`); `partitionDef_map` and `deficiencyMerged_le_deficiency`
  (COVERAGE, at 40l's B3 and B2, on `lem:deficiency-additive-core` and
  `lem:deficiency-merge-rigid`). No other name of the debt is consumed by COVERAGE (the grep of
  its design recon's spikes, 2026-09-28), nor by SHORT, ORBIT, SPLITOFF or CONTRACT-A (PI decision
  4(b), 2026-09-27; the design recons of 40j and 40k); the rest, `jointMotions`, `weldedRank` and
  the remaining A2/A3 names included, has no consumer on Phase 40's route through COVERAGE, and a
  cleanup round pins or leaves it (PI, D5). **Round 4 (`40-simplify`, task 10b, `r1`) deleted the
  unpaid debt** — A1, A2, A3, A4/A5, B1/B2, B3/B4, B7 and all of C1ℓ–C4ℓ (`Molecule/Pencil/TwoCut.lean`
  whole) — keeping the paid names above, the two B5/B6 pins and four live helpers
  (`bddAbove_range_partitionDef_merged`, `span_jointRows_eq_map_dualAnnihilator`,
  `finrank_span_jointRows`, `map_screwDiff_comm`).
- [x] **Two `[pending]` entries of `notes/BlueprintExposition.md`** (its `pencil.tex` section):
  **both settled at Phase 40's close.** `thm:pencil-conditional-realization-main-component`'s
  fuller exposition (the main component as a vector bundle over planar pictures, the flat rank,
  the induction's cut, ear, split-off and contraction steps, the coverage and route B) is written,
  as `main-component.tex`'s section introduction; `thm:pencil-conditional-realization-pair` (the
  kernels) closes as superseded, the kernels retired (§6).

**Carried past Phase 40's close — the tracked cleanup-round items** (none is a close gate, none has
a consumer on the route; a post-Phase-40 cleanup round takes them, or leaves them by a recorded
call). At round 4's close (2026-10-04), the last round that edits Lean, each is paid or left:
- the wider stand-in audit of `lem:trivial-motions-rank-bound` (§3 FLAT): paid by round 1,
  `40-cleanup`, tasks 23a–23b (`36aa7e10`, `2d3d3818`);
- the edge-restricted non-spanning generic-normals row rank (§3 BRIDGE): left, unbuilt with no
  node (round 3's item 4, from its task 12; sanctioned at round 4's Stop 2);
- the "only if" halves of (MC-52)/(MC-53) (§3 STEPS, CUT/BRIDGE): left, unbuilt with no node
  (round 3's item 3; sanctioned at Stop 2). Round 3's task 13 (`9c931242`) cut the remarks after
  `thm:pencil-x0-cut` and `thm:pencil-x0-bridge` that stated them informally;
- the 40h file-size and readability items (§3 STEPS): paid by round 1. The B2 dedupe is task 15
  (`289f96c3`), the three-body near-copies tasks 16 and 18 (`d7fea229`, `b8b24c9a`; task 17's
  general split-off ear, `1080f59c`, netted no shorter and did not land), and `lem:pencil-ear-data`'s
  pin budget task 19 (`d9acaee8`). The file-size rule never fired: at round 4's close `Short.lean`
  has 1 063 lines and `Bricks.lean` 1 251;
- `span_supportExtensor_ofNormals_eq` in `Cut.lean` (§3 STEPS): paid by round 1, task 13
  (`a0dda000`);
- call 12's corollary rebases (§3 STEPS): paid by round 1, tasks 14a–14b (`58c4fa28`, blueprint
  fixup `388e5a18`; `ab2253e1`);
- CHAINS' `pathVertex` helpers to their definition's file (§3 COVERAGE): paid by round 1, task 20
  (`473a4a11`);
- the §4 duplication note (`mapExtensor`/`mapSupport`): paid by round 1, task 22 (`0b5fcd46`);
- the §7 items above. A6 and item 6's other laws: left, as their build-when-consumed conditions
  never fired (round 3's item 2; sanctioned at Stop 2). The shared hub normalization: paid by
  round 2, `40-factor` (`080be6a4`, `0b260626`); its merged-hub caller went with `TwoCut.lean` at
  round 4's 10b. The rest of the D5 debt: paid by round 4's deletion, 10b (`c48d323e`).

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
  `Molecule/Pencil/MainComponent/ContractCurve.lean`, moved from `Contract.lean` at the Phase 40k
  split);
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
