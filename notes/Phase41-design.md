# Phase 41 — RECONCILE-FORMAL: design (cross-phase plan and recon)

**Status:** opened 2026-10-24 with the PI. Sub-phase **41a** (CARRIER) closed 2026-10-24, work log
`notes/Phase41a.md`: the field `isLink_ends` is on `PanelHingeFramework`, and no main result's
statement changed. Sub-phase **41b** (RESTATE) opened 2026-10-24 with the PI's decisions in §1b,
work log `notes/Phase41b.md`. MULTIGRAPH and UNSTATED are tracked by code (§3) and get letters when
they open. Item 1's recon on KT's nonparallel panels is §2's last arc; item 2 dropped
`HasGenericFullRankRealization`'s last conjunct (§2, *RESTATE's open recon*, Q3). Next concrete
task: 41b's item 3, `F-324`, `theorem_55_minimalKDof_gen`'s derivable `hD`.

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
  `exists_rankHypothesis_isGeneralPosition4` is untouched: it reads
  `rankHypothesis_genuine_of_theorem_55_gen`, which states nothing of the normals, and re-chooses
  them; a third polynomial factor would add nonparallel to it, a change §1b does not sanction
  (§4).
- **Order.** Item 4 after items 2 and 3 (the new predicate is born without the link conjunct, and
  both 3 and 4c edit `theorem_55_minimalKDof_gen`) and before item 5, whose Theorem 5.6 then states
  `IsNonparallel` off the strip realization, whose normals `reaimSubLink` keeps; else
  `thm:theorem-55-6` is restated twice. The commits are 41b's items 4a–4c.

## 3. Sub-phases, by code

| Code | Letter | Contents | Commits |
|---|---|---|---|
| **CARRIER** | 41a (closed 2026-10-24) | done: `reaimSub` retired; the link predicate, its lemmas and the fill-in tactic; the four R statements; the spike; the switch (the field, 123 declarations in 27 files) and the footprint's docstrings; `withGraph` restricted; `reaim` deleted with `hC` on links; the two genuine forms merged (`notes/Phase41a.md`) | 9, besides the build-time detour P1–P5 |
| **RESTATE** | 41b (opened 2026-10-24) | S2's main results and nodes (with `F-323`, §1.2–1.4); `cor:theorem-55-d3-spanning`; S1's panel and body-hinge theorems (with S13 and `F-324`); G6's row; round 1's scope sentences on the degenerate hinges removed (`formalization.yaml`, README, home page, `intro.tex`, ROADMAP; their selector half went in 41a's item 5b); non-vacuity witnesses at minimal graphs for these rows; S18 (the conditional statement or a repin on the generic forms, after S1; its `hC` moved to links in 41a's item 6); the remaining footprint docstrings; the link conjuncts the field makes redundant (the coordinator's call at 41a's close): the rows form `finrank_span_rigidityRows_genuine_recordsLinks_of_theorem_55_gen` and `exists_rankHypothesis_isGeneralPosition4_of_two_le` (`Theorem56.lean`), and `exists_independent_normalRow_of_le_finrank`'s `hQends` (`PanelGeneric.lean`), with the d = 3 wrapper `exists_rankHypothesis_isGeneralPosition4`; from the PI's decisions at its open (§1b): Theorem 5.6 with general position, G6's row as the rank formula, `HasGenericFullRankRealization`'s last conjunct, and KT's nonparallel in Theorem 5.5's conclusion | 13–16 (`notes/Phase41b.md`) |
| **MULTIGRAPH** | — | M1: the multigraph generic body-hinge theorem (JJ 2010 Theorem 6.1) | 3–5 |
| **UNSTATED** | — | the claims no declaration states, the report's estimates: S22 1–2, S23 1, S24 2–3, S25 1, S31 2–3, S3 0–2, S16 1, S19 0–3, G5 3–5, `F-061` 1–2; after CARRIER, since S3 and S19 touch carrier code (`case_II_placement_eq612`) | 13–23 |

**Why the switch was one commit** (CARRIER): under the lint gate a field cannot be staged file by
file without a temporary twin structure, as an unused proof argument fails `unusedArguments`;
Phase 22l's lesson, API first and switch last (`notes/Phase22l.md` *Architectural choices*).

The program closes with the phase: ROADMAP's RECONCILE bullet compressed, and the ledger's last
`reported` entries given dispositions (`notes/Reconcile.md` §3).

## 4. Open questions

- **KT's nonparallel** (§1b.4): settled by §2's *KT's nonparallel recon* (route B, 41b's items
  4a–4c). Two options stay with the PI, neither in the plan: KT's eq. (6.1) motive at full strength
  (route A, about a dozen internal producers gain `1 ≤ k`), and nonparallel in the conclusion of the
  d = 3 wrapper `exists_rankHypothesis_isGeneralPosition4` (one more polynomial factor).
- **M1 and loops**: assume `G.Loopless`, or relax the upper bound's `hC` to non-loop links (a loop's
  constraint is vacuous, and a loop never crosses a partition). MULTIGRAPH's open decides. JJ 2010
  Theorem 6.1 (EJC 31, p. 582) is a maximum-rank statement for 2-edge-coloured multigraphs; the
  row's "every generic realization" is the project's strengthening.
