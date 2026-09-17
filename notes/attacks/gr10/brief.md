> **Brief — reviewed by the PI 2026-09-15.** Written by an agent from owning sections, driver code, the Lean statements and the KT paper; rewritten only at milestones (`/review-attack`). Its claims are the writer's readings of the sections cited in §8; an attack re-derives what it builds on. Edits carrying the corrections the Lean formalization found (PI-directed, 2026-09-15; `notes/Phase39-design.md` § *Field-hypothesis recon*) are marked *[formalization 2026-09-15]*. **PI pointer (2026-09-16, after S-mark review 2; `notes/Phase39.md` *Blockers*):** (1) before any work, diff §3 against `hK`'s declaration in `Escape.lean` (`pencilPair_of_splitOff_of_habitat`) hypothesis by hypothesis, *both sides of the implication* — the S-mark brief paraphrased its consumer wrong twice (the dropped `¬ PencilHub` disjunct; the antecedent `HasGenericPencilRealization K 3 (G.splitOff v a b e₀)`, which this brief does not mention) — and `hK`'s statement is being changed (Phase 39 checklist item 5: an induction hypothesis on smaller graphs, possibly a weaker conclusion). (2) **DECIDED 2026-09-16 (user), after the item-4 recon: this attack is RE-SCOPED.** The recon confirmed that S-mark's route R2 covers `hK`'s arm as well as `hbareSplit`'s (`notes/attacks/smark/state.md` *Statement*; workbook S14(iii), (vii)), and its (d) — adopted in Phase 39 checklist item 5 — weakens `hK`'s conclusion to `HasGenericPencilRealization K 3 G`, so **`hK` needs no chart at all** and *Proviso (P)* of §2 drops out of the target, surviving only inside the grid route itself. Consequences, binding on any session that starts from this brief: **the uniform-colouring statement of §2 (weak or strong form) is NOT being attacked, and session 1 does not run as briefed.** The grid/colouring route is retained as a **documented fallback**, to be reopened only if S14(iii)/(vii) or O7 stall. **The one live item is §6 idea 4, the characteristic-2 probe** — it is about the conjecture's field range rather than the route, and a systematic `F_{2^k}` miss is a re-pin trigger for the headline typeclass, so it reports to the PI. Verbatim: `notes/pencil/adjudications.md`; §§1–8 below are unrewritten and describe the fallback route as it stood.

# Uniform vanishing for the grid recipe on the tight stratum

## 1. Objects

Fields are infinite of characteristic ≠ 2 (*[formalization 2026-09-15]* the quadric `x·x = 0` and the polarity's eigen-splitting collapse in characteristic 2, recorded as (AC-8); nothing else in the route uses the characteristic — "characteristic 0" was inherited from the ℚ(i) computations); computations live over ℚ(i). A **tight** graph G is simple, 2-edge-connected, with 5|E| = 6(|V|−1) and no proper rigid subgraph (body-hinge deficiency 0, Katoh–Tanigawa). Writing f(W) = 5e(W) − 6(|W|−1), this forces f(W) ≤ −1 on proper W with |W| ≥ 2, hence def(G) = 0 and girth ≥ 7 unless G is a cycle. Hubs are vertices of degree ≥ 3; each has ≤ 2 hub neighbours, so G is a subdivision of a **hub multigraph** G° whose branches have lengths ℓ_β ∈ [1,5]. A **tight class shape** is such a (G°, ℓ). Counting gives Σ_β(ℓ_β − 2) = 2Σ_v(deg v − 3) + 6, so large shapes are cubic with almost all branches of length 2.

Geometry: body-hinge frameworks whose hinges at each body pass through a point p_v of its panel, placed on the quadric Q = {x·x = 0} ⊂ P³ with p_v its own normal. Points of Q ≅ P¹×P¹ are conjugate iff they share a ruling parameter, so a **grid configuration** is a map V → P¹×P¹ with adjacent bodies agreeing in one coordinate; edges are labelled A or B by their hinge's ruling. An **admissible colouring** alternates at every degree-2 body (one free bit per branch), makes both colour classes forests, is balanced, has no monochromatic hub, and separates bodies. Its **classes** are the components of one colour; each class X has a single hinge line, a conic point with free parameter t_X.

The polarity of Q splits the screw space into two 3-spaces and the rigidity matrix into two **blocks**. In the + block, B-edges force equal unknowns m_v ∈ K³ and A-edges of class X force m_u − m_w ∥ (1, t_X, t_X²); contracting the forest E_B leaves a direction network on H₊ = G/E_B (n_c nodes, m = |E_A| edges) of rank 3n_c − 3 − dim Z₊,

  Z₊ = { c ∈ K^{E_A} : c, s·c, s²·c ∈ cut(H₊) }, s_e := t_{X(e)},

i.e. C¹ quadratic splines on H₊ with moduli (t − t_X)² modulo constants. dim Z₊ = 0 means the + block is isostatic; Z₋ is the mirror. At balance 2m = 3n_c − 3, and the Tay target 6(|V|−1) is reached iff Z₊ = Z₋ = 0. dim Z is a matrix corank, polynomial in the t_X, so one exact rational zero proves generic vanishing.

A **tree-triple** in a block partitions its classes into F₁, F₂, F₃ with each F_i ∪ F_j a spanning tree of H₊ (equivalently every H₊ ∖ F_j connected): a class-respecting decomposition of 2H₊ into three spanning trees.

## 2. The statement

**Weak form.** Every tight class shape admits an admissible colouring with generic dim Z₊ = dim Z₋ = 0.

**Strong form.** Every tight class shape admits an admissible colouring carrying a tree-triple in both blocks.

Strong ⟹ weak (proved): set t_X := a_j on F_j; the Vandermonde in the a_j puts each c|F_j into cut(H₊); a nonzero cut vector inside F_j contains a bond, contradicting connectivity of H₊ ∖ F_j; semicontinuity finishes. Not conversely: blocks with dim Z = 0 and no tree-triple exist; tree-triple existence per block is NP-complete.

**Proviso (P), absent from both.** The chart step needs each hub's closed hub-neighbourhood points (≤ 3) independent; on the grid this fails exactly when a hub meets two hub-neighbours through same-coloured edges (collinear points). So each same-colour hub–hub subgraph must be a matching. Without (P) the grid lies only in the closure of the chart image; no closure argument is written.

## 3. Why it suffices

From the weak form with (P): take an exact point with both blocks at rank; decoupling and the rank formula give 6(|V|−1). Chart step: let each hub's seed normal be its point; all inputs to the chart's cross product at v lie in p_v^⊥, so the chart point is ∝ p_v and the chart rows have the configuration's rank. That is the carried hypothesis `hK` of `pencil_conjecture_of_hcontract_hK_hbareSplit_of_card` at def = 0: a hub selector, a seed, 6(|V|−1) independent rows. Descent: the certifying minor is a ℤ-polynomial in the seed, so it stays nonzero over every infinite characteristic-0 field. *[formalization 2026-09-15]* In characteristic `p` it needs only the minor `≢ 0 mod p`, a per-shape condition, so the descent is characteristic-0 as written, not essentially: if the weak form closes, it closes `hK` over every infinite field of characteristic ≠ 2 (the transfer run over `\bar{F_p}` instead of ℚ(i)). Kernel (K)'s Lean lemma is expected with `[Infinite K] [NeZero (2 : K)]`; the reduction stays `[Infinite K]` (PI, option C; blueprint `fmlnote:pencil-conditional-realization-pair-field`).

Judgment: decoupling, rank formula, Vandermonde, descent — proved (*[formalization 2026-09-15]* descent in characteristic 0; in characteristic `p ≠ 2` conditional on the per-shape mod-`p` non-vanishing). Chart step — correct from the definitions, needs (P). Weak form — open.

**Not covered.** `hK` also ranges over 5|E| ≠ 6(|V|−1). For def > 0 the corpus uses the escape argument (sweep the two hinges at the split vertex; a wrench-nonparallelism criterion), open uniformly. The over-counted corner (e.g. θ(3,4,4)) exists; the corpus calls escape automatic there, unverified. The hubless tight C₆ is in the habitat, outside "class shape", and trivial.

## 4. What is known

- Infinite family (proved; machine-verified at 35 values of m, one connectivity case checked by hand): circular ladders C_m × K₂, six length-3 rungs at columns 0,2,…,10, other branches length 2, even m ≥ 12 — closed-form colouring and tree-triple (fixed window, periodic tail), so the strong form. Rungs spread evenly: exact points to m = 60, no uniform certificate.
- Per-shape proofs by exact points: the 907-shape census (strong form 907/907; (P) holds, hits requiring all nondegeneracy conjuncts); 40 742 cubic shapes at ≤ 6 hubs (complete without hub–hub edges; with them, complete at ≤ 4 hubs) and 166 088 labelled shapes with ≥ 2 hub–hub edges at 6 hubs, (P) unchecked.
- Packing half (proved; Nash-Williams/Tutte, Edmonds): def = 0 makes the hub multigraph with multiplicities 6 − ℓ_β a union of six spanning trees, and a length-legal 3+3 split always exists; a tree-triple is such a split plus a consistent hub labelling.
- Structure: the whole graph is exactly critical and every proper chunk has slack 1; no single obstruction set binds at every colouring.

## 5. What has failed

- Per-block min-max for the strong form: NP-complete; kills a good characterisation, not existence.
- Uniform defect cap ≤ 1: false from 8 hubs. Bounded-deviation selection: refuted by an unbounded parity floor.
- First-moment / union-bound / local lemma: refuted on ladders; a proof must correlate hub choices.
- Hub-local propagation, degree profiles: blind at 6 hubs. Matroid union on the hub side: head-independence fails exchange.
- "Counting saturation": its argument (tightness pins the escape route's slack at 1) concerns the escape kernel, not colouring existence; the ladder proof is itself a tree-packing count. It excludes only shape-only invariants.

## 6. Live ideas

1. Generalise the ladder template (fixed window, periodic tail) to periodic cubic hub graphs, or find a local move on G° transporting tree-triples (ladders resist bounded moves).
2. Reformulate Z₊ = 0 as "class subspaces H_X ⊗ ℓ_X fill H₁ ⊗ K³": Edmonds' union proves it for ≤ 3 classes or singleton classes; treat repeated moduli as a gain graph, try Dilworth truncation. Untried.
3. Z₊ ≅ H⁰ of an elementary modification of O(2) ⊗ H₁* along the cographic arrangement; generic-splitting arguments might give the weak form directly. Untried.
4. *[formalization 2026-09-15]* **The characteristic-2 probe** (PI 2026-09-15, deferred to this attack; session 1's backlog, the attack decides when): evaluate the census shapes' *chart* matrix (`pencilRow` at a random seed — not the branch-system matrix the drivers rank) over `F_{2^k}`, `k` large enough that a random seed is generic with high probability, and over a few odd `F_p`. A full-rank hit at a shape is a proof of `hK`'s conclusion at that shape over every infinite field of that characteristic (the ℤ-minor is nonzero mod `p`, then the descent transfer); systematic `F_{2^k}` misses are evidence that the target itself fails in characteristic 2 — the chart reproduces every nondegenerate realization projectively, so a rank deficit at every seed says no nondegenerate realization attains there — and a re-pin trigger for the headline typeclass. A miss is probabilistic (Schwartz–Zippel), a hit exact. Nothing in the pencil statement involves a quadratic form, so hits are expected; the value is deciding whether characteristic 2 limits the method or the conjecture. Cost: one driver leg beside `closure.py --char2`, which tested one seed, not the polynomial. Spec: `notes/Phase39-design.md` § *Field-hypothesis recon*, last subsection.

## 7. A counterexample

A cubic hub graph on ≥ 8 hubs, six units of excess on ≤ 6 branches, girth ≥ 7 after subdivision, every one of whose 2^M bit patterns has a block with dim Z > 0, through varying obstruction sets. Test by GF(p) rank per pattern, confirm over ℚ. Same-colour hub–hub paths of length 2 probe whether (P) is essential.

## 8. Pointers

- `grid.md`: (GR-15) G17; (GR-10) G11; (GR-9) G10; (GR-1) G1; (GR-5) G6; (GR-7) G8; (GR-16)–(GR-18), (GR-21), (GR-25), (GR-30)–(GR-32); (GR-26) sweeps, GISLAND; (GR-129)–(GR-143) packing/CSP; GUNIZERO (GR-257)–(GR-265), (GR-175), (GR-238), (GR-256); §(K-res) (RS-1), (RS-6).
- `K-clos.md` (AC-2)–(AC-7); `K-tight.md` Step 5; `strategy.md` §2.5; (GR-141)(iii).
- *[formalization 2026-09-15]* Field: `notes/Phase39-design.md` § *Field-hypothesis recon* ((i) the grid route's uses of the field, and the char-2 probe hand-off); blueprint `fmlnote:pencil-conditional-realization-pair-field`.
- Lean `Pencil/Escape.lean:555`. Drivers `w4/grid.py`, `cflank.py`, `gpack.py`, `gunizero.py`.
