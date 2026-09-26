# Phase 40 — PENCIL-X0: the `X₀` formalization of the pencil conjecture (design doc)

**Status: LIVE** (opened 2026-09-25). This is the cross-phase plan for Phase 40, the
sub-lettered home in the `notes/PhaseN-design.md` pattern (`notes/CLAUDE.md`): the target, the
index of work already done, the layer plan by **stable codes**, the proof map, the risks, and the
standing constraints. Sub-phases get a letter and a work log `notes/Phase40x.md` only when they
open. **40a = SPINE2 closed 2026-09-25** (`notes/Phase40a.md`); **next: CARRIER** (§3), not yet
opened. This doc replaces the planning note
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

### CARRIER — planar pictures, `L(q)`, `X₀` and "the generic point attains" → **sub-phase 40b, ◐ opened design-first 2026-09-26** (`notes/Phase40b.md`)

| label | step | 2nd | content |
|---|---|---|---|
| (MC-1) | MC1 | ✓ 09-25 | the pencil condition is linear in the heights over an admissible picture |
| (MC-2) | MC2 | ✓ 09-25 | `X₀` is the main component; `ℓ₀`, the open set `U` |
| (MC-3) | MC3 | ✓ 09-25 | the hinges are affine in the heights |
| (MC-10)(a) | census | — | the statement proved: `X₀(G)`'s generic point attains `6(|V| − 1) − def₃(G)` |

- **Lean reuse.** `MvPolynomial.exists_eval_ne_zero` and its variants
  (`Mathlib/Algebra/MvPolynomial/Funext.lean`); the `PanelHingeFramework.exists_rankPolynomial_of_*`
  family (`GenericityDevice.lean`, `CaseI.lean`); the pencil statement layer
  (`Molecule/Pencil/Statement.lean`).
- **Design settled (opened 2026-09-26; accepted design + leaf plan → `notes/Phase40b.md`).** The
  compiler-checked recon (opus, adopted as session rung; a parallel fable pass too) fixed the four new
  mirror defs — uncurried picture `q : α × Fin 2 → K` + admissibility, the lifting space `L(q)`, the
  `cross₃` picture→normal map (polynomial, denominator-free), and a **single** `X0Attains` carrying a
  nonzero `MvPolynomial (α × Fin 2) K` (semicontinuity once, in a mirror lemma `x0Attains_of_exists`).
  β-headroom (§4): **needed**; fix is an additive-successor `_of_card` triple concluding the unchanged
  L0 `X0Dist`/`X0Gen` and reusing `pencil_conjecture_of_X0` verbatim (a MOTIVES leaf). Two questions
  deferred to the MOTIVES pre-build recon: the exact `hcard` constant, and the headroom root-cause
  (`notes/Phase40b.md` *Blockers*).

### FLAT — the flat rank

| label | step | 2nd | content |
|---|---|---|---|
| (MC-4) | MC4 | ✓ 09-25 (Plücker by hand) | the flat rank is an identity in `dim L(q)`: `6|V| − 3 − dim L(q)`, with `dim L(q) ≥ 3 + def₂` |
| (MC-5)(ii) | MC5 | ✓ 09-25 | `X₀` flat ⇒ `def₂ = def₃ = 0`, without Jackson–Jordán |

- **Lean reuse.** The inequality is landed at grade 1:
  `screwDim_mul_compl_add_deficiency_le_finrank_infinitesimalMotions` (`PanelLayer.lean`). The
  upper bound `BodyHingeFramework.finrank_span_rigidityRows_add_deficiency_le` is general.
- **Pin debt, routed here from 40a (Slice 4).** That upper bound has **no `\lean{}` pin** anywhere
  in the blueprint; `thm:theorem-55-6-rows` (`panel-layer.tex`) points at
  `lem:trivial-motions-rank-bound` as a stand-in for it. FLAT consumes the bound, so the FLAT
  commit that first uses it pins it on its own node and repoints that stand-in `\uses`, in the same
  commit. (If a cleanup round reaches it first, it lands there instead.)
- **New.** `F(q) ≅ L(q)`, and the split `Λ²K⁴ = W_Π ⊕ W′` against the opaque `ScrewSpace`
  carrier. Treat anything touching the carrier as fragility zone (opus minimum for producers).

### BRIDGE — Jackson–Jordán's equality, as it is consumed

The equality is consumed at FLAT (`G`), CONTRACT (`H`, `G/H`), `G′ + ab` and SPLITOFF (`G″`).
Every use is at a simple graph ((MC-141)'s list). (MC-33) is the informal statement; SPINE2
supplies it. BRIDGE builds two things on top of SPINE2:
- the map from (MC-4)'s `F(q)` to the motion space of `PanelHingeFramework.ofNormals G ends q`
  at normals `(x_v, y_v, 1)`, with generic normals moved into the chart by per-body rescaling and
  open admissibility;
- the non-spanning forms at `H`, `G/H` and `G′ + ab`, each carrying a `hfresh`-type hypothesis.
  SPINE2 lands the row-rank core.
- **Open point (40a Slice 4 spike, 2026-09-25).** The landed generic-normals row rank
  `PanelHingeFramework.finrank_span_rigidityRows_ofNormals_of_isGenericNormals`
  (`GenericLift/PanelGeneric.lean:400`) takes a *total* selector
  `hends : ∀ e, G.IsLink e (ends e).1 (ends e).2`, which forces `E(G) = β`. At `H`, `G/H` or
  `G′ + ab` inside a fixed `β` that cannot hold, so BRIDGE needs an edge-restricted-selector,
  non-spanning variant of the generic-normals form. A read-only spike compiler-checked a variant
  that drops `[Nonempty α]`/`hspan` by swapping in the new SPINE2 row-rank producer
  (`PanelHingeFramework.finrank_span_rigidityRows_genuine_recordsLinks_of_theorem_55_gen`); the
  total `hends` remained, and that is the open point BRIDGE still needs to close.
- **Optional re-base, routed here from 40a (Slice 4).** The spanning
  `PanelHingeFramework.rankHypothesis_genuine_recordsLinks_of_theorem_55_gen` is now a ~10-line
  corollary of the SPINE2 row-rank form (fable-spike-checked, not landed), and its `[Nonempty α]`
  is unnecessary. Its consumers are the generic-normals and generic-hinge row ranks
  (`GenericLift/{PanelGeneric,HingeGeneric}.lean`) and `Molecule/Theorem56.lean`; the first is
  the declaration the open point above generalizes. Take it in the BRIDGE slice that builds the edge-restricted
  variant, if that slice finds it cheaper; otherwise it is a post-Phase-40 cleanup-round item.

### STEPS — the local steps of the induction

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
- **There is no landed cut-vertex deficiency law.** Item 6's leaves have no blueprint nodes
  (Phase 39's D5 debt). STEPS pins them when it consumes them.

### COVERAGE — the structural half and the assembly (pure combinatorics on `def₂`, `def₃`)

| labels | step | 2nd |
|---|---|---|
| (MC-62), (MC-63), (MC-67), (MC-68)(d), (MC-69)(a) → (MC-69)(b), (MC-70), (MC-71) | MC15 | ✓ 09-25 (one merge step supplied) |
| (MC-75)(iii), (MC-76), (MC-77), (MC-78), (MC-79)(i)–(iv) → (MC-80); (MC-87) → (MC-89) | MC16 | ✓ (two readers) |
| coverage ⟹ attainment: (MC-56), (MC-55)(i), (MC-2); strong induction | MC14, MC2 | ✓ |

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
attaining `(q, z)` and CARRIER C4's point-join rank equality; `X0Gen` intersects the fibre-open
attaining set with a nondegenerate open set inside one fibre `L(q)`, which needs a new
fibre-intersection lemma (two polynomials each nonvanishing somewhere on a subspace are jointly
nonvanishing somewhere on it, `K` infinite) and C3's polynomial plane normal.

### The blueprint chapter

The main-component argument gets **one new forward-mode chapter**, one section per layer from
CARRIER to MOTIVES. It is opened as red nodes transcribed from the proof map above, with
statements from `ledger.py --brief`, never retyped. Transcribe a layer's section when that layer
opens, not all at once, and run a **pre-build recon of each transcribed section** before the
first build against it (the `/coordinate-phase` transcription guard: a red node's statement is
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
  carrying `hcard`, not an edit of L0's declarations. CARRIER's design recon decides this.
- **Non-spanning uses** of the rank theorem at `H` and `G/H`. The landed
  `rankHypothesis_of_theorem_55_gen` is stated for spanning `G` with `hcard` headroom; SPINE2's
  non-spanning form is the fix.
- **(H) versus 2EC.** CUT and BRIDGE pass through non-2EC graphs, so the proof needs all of (H);
  the consumer uses only the 2EC form.
- `supportExtensor e ≠ 0` must hold for **every** `e : β`, not only the edges of `G`. This is
  trivial, but it is easy to miss.

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
  `finrank_relScrews_le`, `pencilLoss_vertexTwoCut` (C1ℓ–C4ℓ).
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
