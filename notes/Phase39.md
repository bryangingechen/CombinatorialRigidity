# Phase 39 — PENCIL: the hinge-pencil molecular conjecture (work log)

**Status:** in progress (opened 2026-07-23, recon-first; W0-core landed
2026-07-23; W0 blueprint chapter opened 2026-07-23).

## Current state

**Adjudication (user, 2026-07-23, verbatim): "Build W0–W2, then reassess."**
The phase proceeds on the design doc's W0, W1, W2 only; the three open
cores W3–W5 are **not** sanctioned by this decision; after W2 lands the
coordinator re-adjudicates (proceed on the open cores vs close).

**W0 Lean core landed** (`Molecular/Molecule/Pencil.lean`): the statement
layer (`ExtensorThroughPoint`, `HasPencilPanelRealization`), the extensor-
level polarity bridge (`screwComplementIso_mk_extensor`), the two forward
predicate-transport implications, and the stratum self-duality
(`hasPencilPanelRealization_mapExtensor_screwComplementIso`).

**W0 blueprint chapter opened** (`blueprint/src/chapter/pencil.tex`, wired
into `chapter/main.tex` before `\appendix`): five green forward-mode nodes
— `def:extensor-through-point`, `def:pencil-panel-realization`,
`lem:pencil-transport-through-to-in`, `lem:pencil-transport-in-to-through`,
`lem:pencil-self-dual` — `\uses`-wired to `def:coplanar-panel-realization`,
`lem:panel-hinge-dual-molecular`, `def:panel-support-extensor`, and
`lem:case-III-claim612-line-in-panel-union` per the prior hand-off.
`screwComplementIso_mk_extensor` itself got no new label (its own
doc-comment already pins the existing `lem:panel-hinge-dual-molecular`):
extended that node's `\lean{...}` list in `molecule-modelling.tex` plus one
sentence generalizing the extensor-level identity to arbitrary homogeneous
points, in the same commit. No W1/W2 red target nodes added — W1/W2 have
no typechecked statement spike yet (unlike W0's), so stating them risked
the plausible-"corrected"-statement failure mode; add them alongside their
own Lean when W1/W2 land. `intro.tex`'s *Organization* enumerate got its
one-paragraph "fifth continuation (phase~39)" entry (README/home_page/
formalization.yaml already synced at phase-open, `4314eabe`).

**W1 base case landed** (`Molecular/Molecule/Pencil.lean`, two nodes in
`pencil.tex`): (1) `exists_linearIndependent_extensor_pair_through_point`
(`lem:extensor-pair-through-point`) — the coincident-panel pencil pair (KT
Lemma 5.3's geometric core): for any normal `n`, a nonzero point `q₀ ∈ n^⊥`
and two screw elements each `ExtensorInPanel n` *and* `ExtensorThroughPoint q₀`,
with LI extensors; the pencil analogue of
`exists_linearIndependent_extensor_pair_perp`, reusing
`linearIndependent_pair_extensor_of_li3` (its two shared-vector wedges `q₀∨a`,
`q₀∨b` supply the pencil pin for free). (2)
`exists_pencilPanelRealization_parallel_pair`
(`lem:pencil-base-parallel-pair`) — the two-body coincident-panel pencil
realization: the parallel-pair graph carries a `HasPencilPanelRealization`
rigid on `V(G) = {x,y}` (via `theorem_55_base` on the pair's two LI hinges),
the `def=0` rank-`D` content. Stopped at the `V(G)`-relative rigidity, not the
global `RankHypothesis` (which needs a spanning graph — a W3 concern).

**W1 pencil-cycles geometric core landed** (`Molecular/Molecule/Pencil.lean`,
node `lem:coplanar-hinges-concurrent`):
`exists_concurrency_point_of_extensorInPanel_pair` — two nonzero coplanar
hinges (`ExtensorInPanel n`, `n ≠ 0`) automatically share a nonzero
concurrency point `q ∈ n^⊥` through which both pass, so a degree-`≤2` body's
pencil pin is met for free. Proof: two 2-planes in the 3-dim panel `n^⊥` meet
in dim `≥ 1` (modular law `finrank_sup_add_finrank_inf_eq` + the single-vector
panel-dim helper `finrank_toDualPerp_single_eq`, mirroring `Meet.lean`'s
`finrank_toDualPerp_pair_eq`). This is the "degree-2 is automatically pencil"
*check*; the framework-level *wrap* of `cycle_realization` remains (see
Hand-off). Gates all green; `#print axioms` = propext/Classical.choice/
Quot.sound.

**W1 nonvacuity witness landed** (`Molecular/Molecule/Pencil.lean`,
`exists_hasPencilPanelRealization_witness`): `HasPencilPanelRealization` is
inhabited at a concrete `d=3` instance — the two-vertex double edge
`(Graph.singleEdge 0 1 0).addEdge 1 0 1 : Graph (Fin 2) (Fin 7)` — with a
framework rigid on its two bodies. Immediate from
`exists_pencilPanelRealization_parallel_pair`; mirrors
`molecular_conjecture_witness`. No blueprint node (a Lean-only certificate,
as with `molecular_conjecture_witness` — re-flagged, not silently skipped),
so no `.tex` touched this commit. Gates green; `#print axioms` =
propext/Classical.choice/Quot.sound. Next concrete step: **the
cycle-realization wrap** (the last open W1 item) — see Hand-off.

The opening recon ran 2026-07-23 (full record + grounding:
`notes/Phase39-design.md`). Verdicts: **R1** — statement pinned
(containment model + per-body homogeneous concurrency point;
typechecked candidate shapes in the design doc), stratum satisfiable,
projectively self-dual on-stratum modulo one new transport lemma.
**R2** — no refutation: exact-rational rank experiments attain the
full target on every graph tested (incl. four deg-3 bodies at the
tight minimal-0-dof count and five deg-4 bodies); negative data is
confined to the deep all-coplanar locus of *sparse* graphs. **R3** —
KT's route does **not** survive verbatim: Lemma 6.2 / Case II survive,
but the outer Theorem-5.6 strip-extend layer, the Case-I connecting
glue, and Claim 6.12's span (6 → 5, a quantified 1-dim shortfall) all
consume freedom the pencil pin removes — three open cores, so the
phase is **not** the queued "warmup".

## The question

KT's theorem (formalized: `molecular_conjecture`, Phases 17–26; the
multigraph/coplanar-model strengthening, Phase 35) says the generic
body-hinge rank in `ℝ³` is already achieved on the *panel* stratum —
each body's hinges coplanar — and, by projective duality (Phase 25),
on the *molecular* stratum — each body's hinges concurrent. PENCIL
asks about the **intersection stratum**: each body's hinges both
concurrent *and* coplanar, i.e. a **pencil** of lines through a point
in a plane. Does a pencil realization generic in that stratum still
achieve the generic body-hinge rank (Tay's tree-packing count;
`5G` ⊇ 6 edge-disjoint spanning trees at `d = 3` via KT Cor. 5.7)?

In the `G²` molecular reading (Phase 25/26 modelling), the hinges at
the body of atom `v` are the bond lines through `p(v)` — concurrency
is automatic — so the pencil condition says **`v`'s bond-star is
coplanar** (its neighbors lie in a plane through `p(v)`). Chemically:
sp²/planar-bonded atoms. So PENCIL reads: *does the molecular count
stay valid for molecules with planar-bonded atoms?* The condition
only bites at bodies of degree ≥ 3 (two coplanar lines are
automatically projectively concurrent).

Trivial direction: pencil ⇒ panel per body, so pencil rank ≤ generic
(KT). The content is the lower bound. The all-bodies statement is the
strongest form: any mixed version (pencil on a subset of bodies,
generic elsewhere) follows by rank lower-semicontinuity, since the
all-pencil stratum sits inside every mixed stratum.

The queue entry hoped for a warmup (no new carrier material); the
opening recon **refuted the warmup premise** — the carrier material is
indeed all in-tree, but three KT proof steps consume panel-only
freedom the pencil pin removes (see *Opening recon verdicts*). As of
2026-07-23 no literature result on this stratum was found (searched;
Jordán 2016 and the KT paper are silent) — **this is new mathematics**.

## Opening recon verdicts (R1–R3, landed 2026-07-23)

Full record, grounding, and the W0–W5 decomposition:
**`notes/Phase39-design.md`**. One-line verdicts:

- **R1** — panel-side statement pinned in the Phase-35 containment
  model + per-body homogeneous concurrency point (`ExtensorThroughPoint`
  dual of `ExtensorInPanel`; typechecked shapes in the design doc);
  satisfiable for every graph; self-dual on-stratum via the landed
  `screwComplementIso` modulo one new transport lemma. Surprise: for
  dense graphs (K4, K3,3, theta(2,2,2)) the stratum *collapses* to the
  all-coplanar locus.
- **R2** — conjecture survives all exact-rational rank tests
  (pencil-generic = full target rank everywhere tested, incl. the
  collapsed dense strata); the deep all-coplanar locus is deficient
  exactly when `2|E| < 3|V| − 3` (deficit = the spline count) — the
  queued "all-coplanar is rank-deficient" claim is a *bar-joint-side*
  fact, false for body-hinge on dense graphs.
- **R3** — KT Lemma 6.2 / Case II survive with pinned choices; the
  outer Thm-5.6 strip-extend, the Case-I glue (Claim 6.4), and Case
  III's Claim 6.12 span (6 → 5, exactly 1-dim short when both chain
  ends have deg ≥ 3) break — three open cores.

## Blockers / open questions

- **Adjudication resolved** (2026-07-23): build W0–W2, then reassess.
  Nothing blocks; prerequisites are all in-tree (Phases 17–26, 35).
- The full biconditional transport `ExtensorThroughPoint C q ↔
  ExtensorInPanel (screwComplementIso C) q` (design doc's W0 pin) is
  landed only as its **two forward implications** (which is all the
  self-duality consumes). The reverse arms need a `complementIso`
  involution lemma (`screwComplementIso` applied twice = a scalar),
  not in tree — a separate result, deferred; not on the W0–W2 critical
  path. Land it only if a later node needs the `↔`.

## Hand-off / next phase

**W0 complete + W1 base case + pencil-cycles concurrency + nonvacuity
witness landed** (the pencil pair, the two-body realization, the degree-2
concurrency lemma, and the concrete-instance witness
`exists_hasPencilPanelRealization_witness`; see *Current state*). **The one
open W1 item is the cycle-realization wrap; after it, W2.**

- **the cycle-realization wrap** (the last open W1 item): turn KT's Lemma-5.4
  cycle realization into a `HasPencilPanelRealization` (+ rigidity). At `d=3`
  (`k=2`) the constraint `cy.m ≤ n = k+1 = 3` forces `cy.m = 3` — **the only
  cycle is the triangle** (`CycleData.ofCardThree`), a 3-cycle with every body
  degree 2. The degree-2 concurrency *check* is done
  (`exists_concurrency_point_of_extensorInPanel_pair`); what remains is the
  framework-level assembly. **Route (assessed, not yet built):** build on the
  *meet* framework (as `cycle_realization` does internally, via
  `exists_cycle_normals` + `PanelHingeFramework.ofNormals`), NOT a fresh free
  placement — because each edge's hinge must lie in *both* endpoint panels AND
  through *both* endpoint points, which the meet structure gives for free (a
  fresh placement would need W2's two-pencil compatibility first). Steps: (1)
  reproduce the `nrm`/`ofNormals` setup; (2) each edge `i` hinge =
  `panelSupportExtensor (nrm i) (nrm (i+1))`, which is `ExtensorInPanel` both
  endpoints via `extensorInPanel_panelSupportExtensor` (LI of consecutive
  normals from `hjoin`/`normalsJoin_ne_zero_iff`); handle total-over-β
  (non-cycle labels get a nonzero fallback); (3) `point (cy.vtx i)` := the
  concurrency point of body `i`'s two incident hinges `edge (i-1)`, `edge i`
  (both `ExtensorInPanel (nrm i)`) via the concurrency lemma, `choose`n across
  `Fin cy.m` then `Function.extend`ed off `vtx`; (4) per-link through-point:
  `edge i` passes through `point (vtx i)` (it is body `i`'s *second* hinge) and
  `point (vtx (i+1))` (body `i+1`'s *first* hinge); (5) rigidity via
  `theorem_55_cycle`. This is a large fragile assembly (~100+ lines, `ofNormals`
  / `CycleData` / choice internals) — **decompose** if it wedges: land a
  `HasCoplanarPanelRealization` wrap of the meet triangle first, then add the
  `point` layer as a second commit. Blueprint: green node(s) once the statement
  is pinned (`lem:cycle-realization`-adjacent).

Add each remaining W1 red-then-green node to `blueprint/src/chapter/pencil.tex`
in the same commit as its Lean (no typechecked spike existed yet for these at
W0-open time, so no red nodes were pre-authored — author them once a
concrete statement is pinned, per the plausible-"corrected"-statement
caution). Then **W2** (the two-pencil extension lemma — the honest
replacement for `exists_extensor_in_two_panels_grade`, stated with its
true hypotheses `pt(u) ∈ Π(v) ∧ pt(v) ∈ Π(u)`). Gates:
`blueprint/verify.sh` + `blueprint/lint.sh` (the vocabulary gate bans
"stratum"/"strata" — use "stage" or rephrase) whenever `.tex` is touched;
`lake build` (warning-clean) + `lake lint` whenever `.lean` is touched.

After **W2** lands, the coordinator re-adjudicates (open cores vs close);
if it closes without them, the phase-close records statement pinned +
numerically supported + route obstruction mapped, conjecture open, per
`PHASE-BOUNDARIES.md`.

## Adjacent directions (orientation only, not this phase)

ORIGAMI (`notes/Origami.md`, next queued) is the bar-joint-side
analog; the wider unqueued survey — incl. IDENT-PANEL, the nearest
neighbor — is `notes/IdeaBacklog.md`.

## Decisions made during this phase

- **W1 nonvacuity witness landed** (2026-07-24, `Molecular/Molecule/Pencil.lean`,
  `exists_hasPencilPanelRealization_witness`): `HasPencilPanelRealization`
  inhabited at a concrete two-vertex double edge
  `(Graph.singleEdge 0 1 0).addEdge 1 0 1`, rigid on its bodies — immediate from
  the two-body producer. No blueprint node (Lean-only certificate, per
  `molecular_conjecture_witness` precedent; re-flagged). Landed as the sanctioned
  "smaller honest slice": the cycle-realization wrap (coordinator's primary next
  item) is a large fragile meet-framework assembly (see *Hand-off* for the
  assessed route + decompose plan), so the bounded witness went first.
- **W1 pencil-cycles geometric core landed** (2026-07-23,
  `Molecular/Molecule/Pencil.lean`, node `lem:coplanar-hinges-concurrent`):
  `exists_concurrency_point_of_extensorInPanel_pair` — two coplanar hinges
  automatically share a concurrency point (degree-2 pencil pin free), via a
  two-2-planes-in-a-3-space modular-law argument (`finrank_sup_add_finrank_inf_eq`
  + the new single-vector panel-dim helper `finrank_toDualPerp_single_eq`
  mirroring `Meet.lean`'s pair version). Scoped to the geometric *check*, not
  the framework *wrap* of `cycle_realization` — the per-body edge-incidence
  extraction from `CycleData` is the fiddly remainder, handed off. Low ScrewSpace
  fragility (pure `Fin 4 → K` subspace linear algebra).
- **W1 base case landed** (2026-07-23, `Molecular/Molecule/Pencil.lean`, two
  green nodes): (1) `exists_linearIndependent_extensor_pair_through_point`
  (`lem:extensor-pair-through-point`) — the coincident-panel pencil pair (KT
  Lemma 5.3 core), reusing `linearIndependent_pair_extensor_of_li3` (its two
  shared-vector wedges give the pencil point free), LI transported to
  `ScrewSpace K 2` via `LinearMap.linearIndependent_iff`. (2)
  `exists_pencilPanelRealization_parallel_pair` (`lem:pencil-base-parallel-pair`)
  — the two-body realization: parallel-pair graph carries a
  `HasPencilPanelRealization` rigid on `V(G)` via `theorem_55_base`. Scoped the
  rank to `IsInfinitesimallyRigidOn V(G)` (the `def=0`, `V(G)`-relative rank-`D`
  form), *not* the global `RankHypothesis`/prop11 chain — that needs a spanning
  graph and is a W3 concern; B1 bridges the two if a later node needs it.
- **W0 Lean core landed** (2026-07-23, `Molecular/Molecule/Pencil.lean`):
  statement layer + polarity bridge + two forward transport implications
  + self-duality (`#print axioms` clean: propext/Classical.choice/Quot.sound).
  The transport is delivered as the two forward arms, not the pinned `↔`:
  the self-duality (W0's operational core) consumes only the forward arms,
  and the reverse arms need a `complementIso` involution not in tree (see
  *Blockers*). Self-duality's meet→through arm rides a dimension-count
  helper (`mem_span_of_dotProduct_perp_pair`, via `finrank_toDualPerp_pair_eq`);
  the through→meet arm is pure linearity. Blueprint chapter deferred to a
  follow-up commit (kept the fragile ScrewSpace Lean commit off the
  blueprint toolchain surface) — landed the same day, next entry.
- **W0 blueprint chapter opened** (2026-07-23, `blueprint/src/chapter/pencil.tex`):
  five green nodes per *Current state* above. `screwComplementIso_mk_extensor`
  reused the existing `lem:panel-hinge-dual-molecular` label (its own
  doc-comment already pinned it as the arbitrary-point generalization of
  `screwComplementIso_lineExtensor`) rather than minting a new one — the
  additive-successor discipline (`CLAUDE.md` *Working*): extended that
  node's `\lean{...}` list + one generalizing sentence in
  `molecule-modelling.tex`, same commit. No W1/W2 red nodes: neither has a
  typechecked statement spike yet, unlike W0's.
- **Opening recon landed** (2026-07-23): R1–R3 verdicts as above;
  canonical record `notes/Phase39-design.md`. Method: KT primary
  source (page pointers re-verified), landed definition bodies, a
  typechecked `lake env lean` statement spike (scratch, not
  committed), exact-rational rank experiments (configurations +
  results tabulated in the design doc).
- **Negative-data correction** (2026-07-23, recon): the queued
  "all-atoms-coplanar is rank-deficient" is a bar-joint/`G²` fact
  (via the general-position-gated dictionary); in the body-hinge
  model the coplanar locus attains full target rank whenever
  `2|E| ≥ 3|V| − 3` (numerics), and is deficient by exactly the
  spline count otherwise. PENCIL carries no `G²` corollary without
  new dictionary work at degenerate placements.
- **Recon-first; no pinned statement at open** (2026-07-23, per the
  queue entry + `notes/Pencil.md`): R1's statement/satisfiability
  questions are genuinely open, so the open commit pins no Lean
  signature and no blueprint node.
- **Blueprint chapter deferred to the R1 verdict** (2026-07-23):
  `notes/Pencil.md` planned the forward-mode chapter opening with the
  phase, but with R1 unsettled a chapter-open red node risks the
  known plausible-"corrected"-statement failure mode (dispatch-log
  2026-07-11); the Phase-32/34/35 precedent — chapter opens on the
  recon verdicts — applies instead. Re-flagged here rather than
  silently dropped.
- **Higher-`d` flag discharged** (2026-07-23, recon): the stratum is
  self-dual and the chain analysis carries over at every `d` (only
  chain *ends* get pinned); nothing about `d > 3` looks easier — see
  `notes/Phase39-design.md` *Higher-`d` note*. The between-strata
  hierarchy stays in `notes/IdeaBacklog.md` Tier A.

## Citations (transcribed, project-canonical sources)

- Katoh–Tanigawa, *A proof of the molecular conjecture*, Discrete
  Comput. Geom. **45** (2011) — the KT pointers in this note
  (Cor. 5.7, Thm 4.9, Thm 5.5, Lemma 6.13, the Case I/II/III split)
  are transcribed from `notes/Pencil.md`'s 2026-07-23 survey against
  the project-canonical source (ROADMAP *References*); KT pointer
  verification history: `notes/Phase35.md` *Citations*,
  `notes/Phase23-cleanup.md`.
- Jordán 2016 (MSJ Memoirs 34) — checked silent on the pencil stratum
  in the 2026-07-23 survey (the no-literature-result finding).
