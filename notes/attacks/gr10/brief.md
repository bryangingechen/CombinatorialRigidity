> **Brief — reviewed by the PI 2026-09-15; RE-SCOPED by the user 2026-09-16 (verbatim: `notes/pencil/adjudications.md` § *2026-09-16 — (GR-10)'s scope*); restructured 2026-09-17 in a PI-directed docs session against the tree at `084ee4ff`, after the Phase 39 Lean round (checklist items 4–6) closed.** Written by an agent from owning sections, driver code, the Lean statements and the KT paper; rewritten only at milestones (`/review-attack`) or by PI direction. Its claims are the writer's readings of the sections cited in §B8 — an attack re-derives what it builds on. **Part A is the live item: the characteristic-2 probe. Session 1 runs Part A, not Part B.** Part B is the grid/colouring route, kept in substance as a **documented fallback** (its §B3 restated against the landed `hK`), to be reopened only if S-mark's S14(iii)/(vii) or O7 stall (user, 2026-09-16). Edits marked *[formalization 2026-09-15]* carry the corrections of that day's Lean design pass (`notes/Phase39-design.md` § *Field-hypothesis recon*); *[Lean 2026-09-17]* marks what this restructuring changed.

# (GR-10): the characteristic-2 probe (live), and the grid recipe on the tight stratum (fallback)

## Part A — the live item: does characteristic 2 limit the method or the conjecture?

### A1. The consumer, quoted verbatim

Kernel (K) is the hypothesis `hK` of `pencilPair_of_splitOff_of_habitat` (`Molecule/Pencil/Escape.lean:354`; carried unchanged by `pencil_conjecture_of_hcontract_hK_hbareSplit` (`:455`) and `pencil_conjecture_of_hcontract_hK_hbareSplit_of_card` (`:558`)). Its **landed** form since 2026-09-16 (Phase 39 checklist item 5) — never the older chart-form pin:

```lean
-- Escape.lean:360–366
(hK : ∀ (G : Graph α β) (v a b : α) (eₐ e_b e₀ : β),
  G.Simple →
  5 ≤ V(G).ncard →
  G.TwoEdgeConnected →
  (∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G 3) →
  G.degree v = 2 →
  eₐ ≠ e_b →
  G.IsLink eₐ v a →
  G.IsLink e_b v b →
  (¬ G.PencilHub a ∨ ¬ G.PencilHub b) →
  e₀ ∉ E(G) →
  (∀ G' : Graph α β, V(G').Nonempty → V(G').ncard < V(G).ncard → PencilPair K 3 G') →
  HasGenericPencilRealization K 3 (G.splitOff v a b e₀) →
  HasGenericPencilRealization K 3 G)
```

Operators, glossed from their definition bodies (never from a docstring): `HasGenericPencilRealization K 3 G` (`Motive.lean:141`) is `∃ F normal point, IsNondegPencilRealization G F normal point ∧ rank = 6(|V|−1) − def₃(G)` — a *single* nondegenerate configuration at the deficiency-rank target, over the *given* field `K`. `IsNondegPencilRealization` (`Motive.lean:111–116`) is four conjuncts: a pencil panel realization; adjacent points projectively distinct; closed-hub-neighbourhood normals linearly independent; closed-neighbourhood points linearly independent at every non-hub. `PencilPair` (`Motive.lean:178`) is `(Simple → Feasible → Generic) ∧ (Simple → Distinct) ∧ Bare`. `G.splitOff v a b e₀` (`Molecular/Induction/Operations.lean:770`) deletes `v` and adds one fresh edge `e₀` joining `a` and `b`. `K` is any **infinite** field (`[Infinite K]`; option C, checklist item 3): the reduction uses no characteristic, and whatever field hypothesis a *proof* of `hK` needs lives on that proof.

Under route R2 (S-mark, `notes/attacks/smark/brief.md` §2; workbook S14(iii), (vii)) the induction hypothesis plus the split-off antecedent are expected to discharge `hK` on its whole domain with **no chart and no colouring** — which is why the uniform-colouring statement of Part B is not being attacked. What Part B would have supplied at def = 0 is now a fallback; what survives as live is the one question about `hK` that R2 does not answer: **its field range.**

### A2. The statement to settle

**Probe statement (P).** For every tight class shape `G` in the 907-shape census (Part B §B4; the `kslidecomb` sweep of `grid.md` §(K-grid)), `HasGenericPencilRealization K 3 G` holds over every infinite field `K` of characteristic 2 — i.e. `hK`'s *conclusion* at def = 0 does not depend on `char K ≠ 2`.

(P) is decided **per shape** by an exact certificate. Let `M(q)` be the **chart matrix**: the `pencilRow` family (`Engine.lean:318` — the row at `(e, t₁, t₂)` is `hingeRow` of the annihilator of the point-join of the two chart points `pencilChartPoint (PencilSeed.ofCoord q) hubSel (ends e)`) at a seed `q`, with `hubSel` a `Fin 3`-selector of each closed hub neighbourhood (`IsFin3SelectorOf`, `Chart.lean:378`). Every entry of `M(q)` is a ℤ-polynomial in the seed coordinates (*[formalization 2026-09-15]* the field recon's G7 check: no denominators). A `6(|V|−1) × 6(|V|−1)` minor `Δ(q)` that is **nonzero at one seed over `F_{2^k}`** is nonzero as a polynomial mod 2, hence nonzero at some seed over *every* infinite field `K` of characteristic 2 (a nonzero polynomial over an infinite field has a non-root); at that seed `hasGenericPencilRealization_of_independent_pencilRow_target` (`Escape.lean:201`, the landed W5-L7b bridge, consumer-free since item 5 and retained for exactly this use) turns the independent rows into `HasGenericPencilRealization K 3 G`. **A hit is a proof of (P) at that shape.** The bridge's hypotheses, to be read at session 1 (this is the reading check): `G.Simple`; `V(G).Nonempty`; `∀ v, |closedHubNbhd v| ≤ 3` (`closedHubNbhd`, `Motive.lean:83`); triangle-freeness; a hub selector for every closed hub neighbourhood; an index set of *genuine edges* of size exactly `6(|V|−1) − def₃(G)`; the `pencilRow`s at that index set linearly independent at the seed. On the census shapes the first four hold by construction (simple; girth ≥ 7; every hub with ≤ 2 hub neighbours) — confirm against Part B §B1 before trusting it.

A **miss** at a shape (rank deficit at every seed tried) is probabilistic, not a proof: by Schwartz–Zippel a uniformly random seed over `F_{2^k}` fails to witness a nonzero `Δ` with probability ≤ deg Δ / 2^k, so every reported miss carries `k`, the number of seeds, and a bound on deg Δ (row degree × minor size). **Systematic** misses across shapes are evidence that `hK`'s conclusion itself fails in characteristic 2 — the chart reproduces every nondegenerate realization projectively (the design doc's W5-L4 contract; `grid.py --chart` is the machine check of chart-image membership, (GR-5)), so a chart-rank deficit at every seed says no nondegenerate realization attains there — and they are a **re-pin trigger for the headline typeclass** (`[NeZero (2 : K)]` on the reduction, not only on kernel (K)). That decision is the PI's; the probe reports.

**Why hits are expected.** Nothing in the pencil *statement* involves a quadratic form; characteristic 2 enters Part B's method only through the quadric `x·x = 0` and the polarity's eigen-splitting (recorded as (AC-8); `closure.py --char2` shows the quadric is a double plane over `F₂⁴` and `Λ²` does not split — a statement about the *grid* matrix at one seed, not about `Δ`). If every census shape hits, the `[NeZero (2 : K)]` expectation on kernel (K) (checklist item 3) is a limitation of the grid *method* only, and a proof of `hK` by R2 may be stated over every infinite field.

### A3. The route (session 1 writes `state.md` from this)

Obligations, in order; each is one leg of one committed driver under `notes/attacks/gr10/drivers/` (seeded, exact, an explicit timeout on every run; `HARNESS.md` *Reproducibility*):

- **O1 — the chart matrix, faithfully.** Implement `M(q)` over `F_{2^k}` (and over ℚ and a few odd `F_p` as controls) from the *Lean definitions* of `pencilChartPoint`, `pencilRow`, `hingeRow`, `annihRow` — **not** from the branch-system matrix `dim_W_branch` that Part B's drivers rank (that is the *grid* recipe's matrix, whose char-2 behaviour is the known-bad (AC-8)). `grid.py --chart` (`chart_reproduce`, `notes/scripts/w4/grid.py:766`) already builds chart points over ℚ(i) and checks them against grid points; `closure.py` carries the harness's own `⋆` (`repin.hodge_star`), rigidity rows (`hybrid_gates.build_rigidity_extensors`) and nondegeneracy checker (`flanks.nondeg_conjuncts`). Reuse them read-only; write only under `notes/attacks/gr10/`. Control: at one census shape over ℚ, `rank M(q)` at a random seed must equal the landed exact-point rank `6(|V|−1)` (Part B §B4) — a mismatch is a bug in O1, not a finding.
- **O2 — the seed and the field.** `F_{2^k}` with `k` chosen so that `deg Δ / 2^k` is small (state the bound; `k ≥ 20` is likely ample); seeds from a named PRNG seed; hub selectors chosen once per shape and recorded. Name the population: which shapes, how many seeds each, which `k`, which odd `p`.
- **O3 — the transfer, written out.** One paragraph in the workbook: nonzero mod-2 minor ⟹ nonzero over every infinite char-2 field ⟹ the bridge's hypotheses ⟹ `HasGenericPencilRealization K 3 G`; each hypothesis discharged by name, the one needing the shape's structure (`|closedHubNbhd| ≤ 3`) checked per shape by the driver.
- **O4 — the sweep.** All 907 shapes; hits/misses per shape and per characteristic; for a miss, the observed rank deficit and the seed count. If the 907 are cheap, the 40 742 cubic shapes at ≤ 6 hubs (Part B §B4) are a second population — a separate figure with its own cap.
- **O5 — the report to the PI** (the deliverable). One page in the workbook file: the population, the caps, the hit/miss table, the certificate for one hit (seed, hub selectors, the minor's row-index set — reproducible from the committed driver), and one of two verdicts — "characteristic 2 limits the *method* only" or "characteristic 2 limits the *target* at shapes X; re-pin recommended".

Workbook file: `notes/pencil/workbook/attack-gr10.md` (create it; number results P1, P2, … as S-mark numbers S1, S2, …; no label prefix is registered — the PI has not assigned one). Retrieve corpus claims through `python3 notes/ledger.py --label`, never by reading `notes/pencil/workbook/*.md` directly. The Lean you may read is under `Molecule/Pencil/` (`Escape.lean`, `Engine.lean`, `Chart.lean`, `Motive.lean` cover everything A1–A2 names).

### A4. What a probe result does and does not settle

- A hit at a shape settles `hK`'s **conclusion** there, in characteristic 2 — not `hK` (the implication), and not Part B's weak form (a statement about *colourings*, one specific way to reach a hit). It moves no gap-map row.
- Misses at a few shapes with hits at the rest are a result about those shapes' char-2 geometry — exhibit which minors vanish identically mod 2 — but not a re-pin trigger on their own; the trigger is *systematic* misses.
- Nothing here touches `hbareSplit` or the def > 0 stratum of `hK`.

## Part B — the grid recipe on the tight stratum (documented fallback; reopen only on the PI's call)

*[Lean 2026-09-17]* §§B1–B8 are the 2026-09-15 brief's §§1–8 in substance. §B3 is restated against the landed `hK` (no chart-form conclusion; the chart step is internal to this route and ends at the bridge lemma named in A2). Nothing below has been re-verified since 2026-09-15 except the pointers in §B8.

### B1. Objects

Fields are infinite of characteristic ≠ 2 (*[formalization 2026-09-15]* the quadric `x·x = 0` and the polarity's eigen-splitting collapse in characteristic 2, recorded as (AC-8); nothing else in the route uses the characteristic — "characteristic 0" was inherited from the ℚ(i) computations); computations live over ℚ(i). A **tight** graph G is simple, 2-edge-connected, with 5|E| = 6(|V|−1) and no proper rigid subgraph (body-hinge deficiency 0, Katoh–Tanigawa). Writing f(W) = 5e(W) − 6(|W|−1), this forces f(W) ≤ −1 on proper W with |W| ≥ 2, hence def(G) = 0 and girth ≥ 7 unless G is a cycle. Hubs are vertices of degree ≥ 3; each has ≤ 2 hub neighbours, so G is a subdivision of a **hub multigraph** G° whose branches have lengths ℓ_β ∈ [1,5]. A **tight class shape** is such a (G°, ℓ). Counting gives Σ_β(ℓ_β − 2) = 2Σ_v(deg v − 3) + 6, so large shapes are cubic with almost all branches of length 2.

Geometry: body-hinge frameworks whose hinges at each body pass through a point p_v of its panel, placed on the quadric Q = {x·x = 0} ⊂ P³ with p_v its own normal. Points of Q ≅ P¹×P¹ are conjugate iff they share a ruling parameter, so a **grid configuration** is a map V → P¹×P¹ with adjacent bodies agreeing in one coordinate; edges are labelled A or B by their hinge's ruling. An **admissible colouring** alternates at every degree-2 body (one free bit per branch), makes both colour classes forests, is balanced, has no monochromatic hub, and separates bodies. Its **classes** are the components of one colour; each class X has a single hinge line, a conic point with free parameter t_X.

The polarity of Q splits the screw space into two 3-spaces and the rigidity matrix into two **blocks**. In the + block, B-edges force equal unknowns m_v ∈ K³ and A-edges of class X force m_u − m_w ∥ (1, t_X, t_X²); contracting the forest E_B leaves a direction network on H₊ = G/E_B (n_c nodes, m = |E_A| edges) of rank 3n_c − 3 − dim Z₊,

  Z₊ = { c ∈ K^{E_A} : c, s·c, s²·c ∈ cut(H₊) }, s_e := t_{X(e)},

i.e. C¹ quadratic splines on H₊ with moduli (t − t_X)² modulo constants. dim Z₊ = 0 means the + block is isostatic; Z₋ is the mirror. At balance 2m = 3n_c − 3, and the Tay target 6(|V|−1) is reached iff Z₊ = Z₋ = 0. dim Z is a matrix corank, polynomial in the t_X, so one exact rational zero proves generic vanishing.

A **tree-triple** in a block partitions its classes into F₁, F₂, F₃ with each F_i ∪ F_j a spanning tree of H₊ (equivalently every H₊ ∖ F_j connected): a class-respecting decomposition of 2H₊ into three spanning trees.

### B2. The statement (of the fallback)

**Weak form.** Every tight class shape admits an admissible colouring with generic dim Z₊ = dim Z₋ = 0.

**Strong form.** Every tight class shape admits an admissible colouring carrying a tree-triple in both blocks.

Strong ⟹ weak (proved): set t_X := a_j on F_j; the Vandermonde in the a_j puts each c|F_j into cut(H₊); a nonzero cut vector inside F_j contains a bond, contradicting connectivity of H₊ ∖ F_j; semicontinuity finishes. Not conversely: blocks with dim Z = 0 and no tree-triple exist; tree-triple existence per block is NP-complete.

**Proviso (P), internal to this route.** The chart step needs each hub's closed hub-neighbourhood points (≤ 3) independent; on the grid this fails exactly when a hub meets two hub-neighbours through same-coloured edges (collinear points). So each same-colour hub–hub subgraph must be a matching. Without (P) the grid lies only in the closure of the chart image; no closure argument is written. *[Lean 2026-09-17]* Since `hK` no longer concludes in chart form, (P) is a hypothesis of *this route's* chart step only, not of `hK`'s statement.

### B3. Why it would suffice (against the landed `hK`)

From the weak form with (P): take an exact point with both blocks at rank; decoupling and the rank formula give 6(|V|−1). Chart step: let each hub's seed normal be its point; all inputs to the chart's cross product at v lie in p_v^⊥, so the chart point is ∝ p_v and the chart rows have the configuration's rank — a hub selector, a seed and 6(|V|−1) independent `pencilRow`s. *[Lean 2026-09-17]* That is no longer `hK`'s conclusion: since checklist item 5 `hK` concludes `HasGenericPencilRealization K 3 G` directly (A1), and the chart-form witness reaches it through the retained bridge `hasGenericPencilRealization_of_independent_pencilRow_target` (`Escape.lean:201`; hypotheses listed in A2). So this route, if reopened, discharges `hK` at def = 0 as: weak form ⟹ exact grid point ⟹ chart witness ⟹ bridge ⟹ `HasGenericPencilRealization K 3 G`, **ignoring the induction hypothesis and the split-off antecedent that `hK` now carries** — both unused by this route, which is its weakness against R2, not a gap in it. Descent: the certifying minor is a ℤ-polynomial in the seed, so it stays nonzero over every infinite characteristic-0 field. *[formalization 2026-09-15]* In characteristic `p` it needs only the minor `≢ 0 mod p`, a per-shape condition (Part A's O3 is exactly this transfer, run at `p = 2`): if the weak form closes, it closes `hK` at def = 0 over every infinite field of characteristic ≠ 2 (the transfer run over `\bar{F_p}` instead of ℚ(i)). Kernel (K) via this route is expected with `[Infinite K] [NeZero (2 : K)]`; the reduction stays `[Infinite K]` (PI, option C; blueprint `fmlnote:pencil-conditional-realization-pair-field`).

Judgment: decoupling, rank formula, Vandermonde, descent — proved (*[formalization 2026-09-15]* descent in characteristic 0; in characteristic `p ≠ 2` conditional on the per-shape mod-`p` non-vanishing). Chart step — correct from the definitions, needs (P). Weak form — open.

**Not covered.** *[Lean 2026-09-17]* Under R2 the whole of `hK`'s arm — def = 0 and def > 0 alike — is S-mark's (workbook S14(iii), (vii); the latter still a sketch), so this route covers strictly less than R2 claims. If reopened it would still cover only 5|E| = 6(|V|−1); for def > 0 the corpus used the escape argument (sweep the two hinges at the split vertex; a wrench-nonparallelism criterion), open uniformly. The over-counted corner (e.g. θ(3,4,4)) exists; the corpus calls escape automatic there, unverified. The hubless tight C₆ is in the habitat, outside "class shape", and trivial.

### B4. What is known

- Infinite family (proved; machine-verified at 35 values of m, one connectivity case checked by hand): circular ladders C_m × K₂, six length-3 rungs at columns 0,2,…,10, other branches length 2, even m ≥ 12 — closed-form colouring and tree-triple (fixed window, periodic tail), so the strong form. Rungs spread evenly: exact points to m = 60, no uniform certificate.
- Per-shape proofs by exact points: the 907-shape census (strong form 907/907; (P) holds, hits requiring all nondegeneracy conjuncts); 40 742 cubic shapes at ≤ 6 hubs (complete without hub–hub edges; with them, complete at ≤ 4 hubs) and 166 088 labelled shapes with ≥ 2 hub–hub edges at 6 hubs, (P) unchecked.
- Packing half (proved; Nash-Williams/Tutte, Edmonds): def = 0 makes the hub multigraph with multiplicities 6 − ℓ_β a union of six spanning trees, and a length-legal 3+3 split always exists; a tree-triple is such a split plus a consistent hub labelling.
- Structure: the whole graph is exactly critical and every proper chunk has slack 1; no single obstruction set binds at every colouring.

### B5. What has failed

- Per-block min-max for the strong form: NP-complete; kills a good characterisation, not existence.
- Uniform defect cap ≤ 1: false from 8 hubs. Bounded-deviation selection: refuted by an unbounded parity floor.
- First-moment / union-bound / local lemma: refuted on ladders; a proof must correlate hub choices.
- Hub-local propagation, degree profiles: blind at 6 hubs. Matroid union on the hub side: head-independence fails exchange.
- "Counting saturation": its argument (tightness pins the escape route's slack at 1) concerns the escape kernel, not colouring existence; the ladder proof is itself a tree-packing count. It excludes only shape-only invariants.

### B6. Live ideas (of the fallback)

1. Generalise the ladder template (fixed window, periodic tail) to periodic cubic hub graphs, or find a local move on G° transporting tree-triples (ladders resist bounded moves).
2. Reformulate Z₊ = 0 as "class subspaces H_X ⊗ ℓ_X fill H₁ ⊗ K³": Edmonds' union proves it for ≤ 3 classes or singleton classes; treat repeated moduli as a gain graph, try Dilworth truncation. Untried.
3. Z₊ ≅ H⁰ of an elementary modification of O(2) ⊗ H₁* along the cographic arrangement; generic-splitting arguments might give the weak form directly. Untried.
4. *[Lean 2026-09-17]* The characteristic-2 probe — **promoted to Part A**; it is the live item, not a fallback idea. Spec history: `notes/Phase39-design.md` § *Field-hypothesis recon*, last subsection.

### B7. A counterexample

A cubic hub graph on ≥ 8 hubs, six units of excess on ≤ 6 branches, girth ≥ 7 after subdivision, every one of whose 2^M bit patterns has a block with dim Z > 0, through varying obstruction sets. Test by GF(p) rank per pattern, confirm over ℚ. Same-colour hub–hub paths of length 2 probe whether (P) is essential.

### B8. Pointers

- `grid.md`: (GR-15) G17; (GR-10) G11; (GR-9) G10; (GR-1) G1; (GR-5) G6; (GR-7) G8; (GR-16)–(GR-18), (GR-21), (GR-25), (GR-30)–(GR-32); (GR-26) sweeps, GISLAND; (GR-129)–(GR-143) packing/CSP; GUNIZERO (GR-257)–(GR-265), (GR-175), (GR-238), (GR-256); §(K-res) (RS-1), (RS-6). Retrieve with `python3 notes/ledger.py --label`.
- `K-clos.md` (AC-2)–(AC-8); `K-tight.md` Step 5; `strategy.md` §2.5; (GR-141)(iii).
- *[formalization 2026-09-15]* Field: `notes/Phase39-design.md` § *Field-hypothesis recon* ((i) the grid route's uses of the field; the last subsection is the char-2 probe's original hand-off); blueprint `fmlnote:pencil-conditional-realization-pair-field`.
- *[Lean 2026-09-17]* Lean *(line numbers at `084ee4ff`; cite by declaration name, lines drift)*: `Molecule/Pencil/Escape.lean:354` `pencilPair_of_splitOff_of_habitat` (`hK` at `:360–366`), `:201` `hasGenericPencilRealization_of_independent_pencilRow_target`; `Engine.lean:318` `pencilRow`; `Chart.lean:84` `cross₃`, `:378` `IsFin3SelectorOf`; `Motive.lean:83` `closedHubNbhd`, `:111` `IsNondegPencilRealization`, `:141` `HasGenericPencilRealization`, `:178` `PencilPair`. The kernels' current form: `notes/Phase39-design.md` § *Kernel restatement (2026-09-16)*. Route R2 and S-mark: `notes/attacks/smark/brief.md`.
- Drivers (read-only from this attack; new code goes under `notes/attacks/gr10/drivers/`): `notes/scripts/w4/grid.py` (`--chart`), `cflank.py`, `gpack.py`, `gunizero.py`, `closure.py` (`--char2`); their index `notes/scripts/w4/README.md`.
