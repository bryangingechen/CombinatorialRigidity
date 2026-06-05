# Phase 22 — realization-layer design (decision-support doc)

**Status:** design pass, not a build plan. Produced 2026-06-04 after the
constructibility recon (FRICTION dead-end #5; `notes/Phase22a.md` *Blockers*)
found the Case-I coupling has two real gaps **(G1)/(G2)** the type-level plan
was blind to. The user paused per-commit Lean work to decide the **motive
question** — should `PanelHingeFramework.HasFullRankRealization` carry general
position (KT's "nonparallel"). The motive decision landed (the **two-motive
split**, §1.4, green); §**1.5** (2026-06-04) is the follow-on **generic-motive
recon** settling the N6-composer IH-shape gap as a **hybrid route** and cutting
it into the buildable N6-G1/G2/G3 nodes (the live to-do is `notes/Phase22a.md`
*Lemma checklist*). No Lean / `\leanok` / blueprint edits accompany this doc.

Primary sources read for this pass: KT 2011 §5–§6.4 (`.refs/`, printed pp.
669–697); `Molecular/{AlgebraicInduction,Extensor,Deficiency,Induction}.lean`;
`blueprint/src/chapter/algebraic-induction.tex` Case I/II/III + `thm:theorem-55`;
`notes/Phase21b.md` *Finding A/B*; the cross-cutting `DESIGN.md` sections
(*Realization motive must be V(G)-relative*, *Constructibility recon …*,
*Phase Case-naming …*).

---

## 0. The crux, in one paragraph

KT Theorem 5.5 (printed p. 669) reads: *"there exists a **(nonparallel, if G is
simple)** panel-hinge realization `(G,p)` satisfying `rank R(G,p) =
D(|V|−1)−k`."* The induction is on `|V|`; **every inductive case invokes the IH
(KT's eq. (6.1)) in this same `∃ nonparallel realization` form** and builds a
new nonparallel realization from it. Three places consume the nonparallel-ness
of the *incoming* legs: (i) KT Claim 6.4's "each entry of the rigidity matrix of
a **nonparallel** realization is a polynomial in the panel coefficients"
(printed p. 674) — exactly the project's `panelRow`/B0 coordinatization, which
needs `supportExtensor e ≠ 0`, i.e. transversal hinges; (ii) Lemma 6.3/6.5's
boundary-panel intersection `Π_{G/E',p2}(u) ∩ Π_{G',p1}(v)` (eq. 6.6) is a
genuine `(d−2)`-flat **only when the two panels are transversal**; (iii) the
simple cases additionally require the two legs' panel coefficients to be
*jointly algebraically independent over ℚ* (printed pp. 673, 675), so they can
be placed on one shared generic point. The project's motive currently asks for a
**bare** rigid realization (`∃ Q, Q.graph = G ∧ Q rigid on V(G)`), with no
general-position promise. That mismatch **is** gap (G1); the joint-genericity in
(iii) **is** gap (G2). Both are intrinsic to KT's argument, not artefacts of the
Lean encoding.

---

## 1. Motive decision

### 1.1 What KT Theorem 5.5 actually guarantees

`Molecular/AlgebraicInduction.lean:2445`:
```
def HasFullRankRealization (k : ℕ) (G : Graph α β) : Prop :=
  ∃ Q : PanelHingeFramework k α β, Q.graph = G ∧
    Q.toBodyHinge.IsInfinitesimallyRigidOn V(G)
```
KT's conclusion is strictly stronger when `G` is simple: `∃ Q, Q.graph = G ∧
Q.IsGeneralPosition ∧ Q.toBodyHinge.IsInfinitesimallyRigidOn V(G)`, where
`IsGeneralPosition P := ∀ a b, a ≠ b → LinearIndependent ℝ ![P.normal a,
P.normal b]` (`AlgebraicInduction.lean:1762`). General position is a property of
the **normals `q` alone** (pairwise independence) — independent of the graph,
the endpoint selector, and `withGraph`. (`withGraph_normal` is `rfl`:
`(P.withGraph G').normal = P.normal`.) This is the single most important
structural fact for the whole decision: **a general-position seed `q₀` for the
parent is automatically general-position for every leg `withGraph GH/Gc`.**

KT's "if `G` is simple" caveat: general position can genuinely **fail** in the
non-simple base/Lemma-6.2 cases — two parallel edges, or the K₂-with-double-edge
base, want `ΠG,p1(a) = ΠG,p1(b)` (equal panels, printed pp. 670, 672). So a
motive that *unconditionally* demands general position is **too strong** — it is
false for the two-vertex double-edge base case. The honest strengthened motive
is general-position **conditioned on `G.Simple`** (or carried as a separate
conjunct only where the producers consume it). See §1.4.

### 1.2 What each producer NEEDS from / SUPPLIES to the motive

The table reads "for the recursion `theorem_55 = minimal_kdof_reduction hbase
hsplit hcontract`":

| Producer | NEEDS from IH | SUPPLIES (its conclusion) | Notes |
|---|---|---|---|
| **base** (`hbase`, `theorem_55_base`, `AlgebraicInduction.lean:831`) | nothing (leaf) | bare rigid on `{u,v}`; **already takes `hgen : LinearIndependent ![C(e₁),C(e₂)]`** as a hypothesis = general position of the *two hinges* | The base already *consumes* a general-position witness; it can *supply* `IsGeneralPosition` of `Q` for free when the two bodies' normals are independent. K₂-double-edge (parallel) is the one non-general-position leaf. |
| **Case II** (`hsplit`, **= KT Case III**, k=0, RED) | KT Lemma 6.8/6.10: a **nonparallel** realization of the smaller split `G_v^{ab}` | nonparallel realization of `G` | The eq. (6.12) degenerate placement explicitly sets `p1(vb)=q(ab)` — uses the incoming nonparallel `q` to reproduce the `e₀` row. Claim 6.4 (polynomial-in-normals) applied here needs the incoming leg nonparallel. |
| **Case I** (`hcontract`, KT §6.2, RED) | **nonparallel** realizations `(G',p1)`, `(G/E',p2)` of the two legs, **jointly generic** (algebraically independent panel coefficients, eq. 6.6) | nonparallel realization of `G` (Lemma 6.3/6.5); bare for non-simple (Lemma 6.2) | (G1) = "needs nonparallel legs"; (G2) = "needs them jointly generic on one seed". |
| **`theorem_55` statement** | — | — | the motive type only — flips with the producers |
| **device feed** (`exists_rankPolynomial_of_rigidOn`, `AlgebraicInduction.lean:3226`; `hasFullRankRealization_of_splice_ofNormals:3064`) | `hne : ∀ e, supportExtensor e ≠ 0` (transversal hinges) **and** `hgp : IsGeneralPosition` at the seed | the generic full-rank realization | This is where (G1)/(G2) bite in the *green* infra. Both the polynomial-producer and the splice already demand general position; the only thing missing is an IH that *delivers* it. |

The decisive observation: **the green producer infra already requires general
position** (`hne`/`hgp` are hypotheses of `exists_rankPolynomial_of_rigidOn` and
`hasFullRankRealization_of_splice_ofNormals`). The gap is purely that the IH
motive does not *carry* general position to discharge them. KT closes this by
making the IH itself nonparallel. The project currently does not.

### 1.3 What breaks / must change if the motive is strengthened

Enumerated green nodes touched (all in `AlgebraicInduction.lean` unless noted):

1. **`HasFullRankRealization` def (`:2445`)** — add the `IsGeneralPosition`
   conjunct (conditioned, see §1.4). One-line def edit; **no proof**, but every
   consumer/producer of the def re-types.
2. **`theorem_55` statement (`:2471`)** — purely transitive: it is
   `Graph.minimal_kdof_reduction hbase hsplit hcontract`, so its type follows
   the motive. The *body* is unchanged (one-line `exact`). The three IH
   hypotheses `hbase`/`hsplit`/`hcontract` re-type to the stronger motive.
3. **base case `theorem_55_base` / its `PanelHingeFramework` lift (`:2013–2028`)
   + `hbase` wiring** — must now *also conclude* `IsGeneralPosition`. The two-
   body case with independent normals supplies it directly from `hgen`; the
   **non-general-position parallel base** (K₂ double-edge) is the obstruction
   that forces the *conditioned* motive (§1.4). The base proof grows by the
   general-position conclusion (small, but real — it is where the "if simple"
   caveat has to be discharged).
4. **Case II accounting iff `lem:case-II` and Case I accounting iff `lem:case-I`
   (green, `:733`/the `isInfinitesimallyRigidOn_iff_pinnedMotionsOn_le` family)**
   — these are *rank-side* iffs about rigidity-on-`V(G)`; they do **not** mention
   the motive type, so they are **untouched**. (Confirmed: they take general
   position implicitly via the device hypotheses, not via the motive.)
5. **The device feed (`exists_rankPolynomial_of_rigidOn`,
   `hasFullRankRealization_of_splice_ofNormals`,
   `hasFullRankRealization_of_rigidOn_seed`,
   `exists_rigidOn_ofNormals_of_hasFullRankRealization`)** — these *already* take
   `hne`/`hgp` as explicit hypotheses, so the strengthened motive lets a producer
   *discharge* them rather than re-prove them. **They do not break; they get
   easier to feed.** `exists_rigidOn_ofNormals_of_hasFullRankRealization`
   (`:3192`) grows by one conjunct (carry the general-position witness out of the
   repackaged `Q`), still a ~5-line `rfl`/`subst` proof.
6. **`rigidityMatrix_prop11` (`:2525`), `lem:cycle-realization`** — consume the
   motive only through `theorem_55` as a *cited* `hgen`; the *statements* do not
   carry `HasFullRankRealization`, so they are untouched at the type level.

**Ripple cost: bounded and front-loaded.** The def edit + the `theorem_55`
re-type + the base-case general-position conclusion are a single small commit
(no new mathematics — general position of the base is read off `hgen`). The
*producers* (`hsplit`/`hcontract`) are red regardless; strengthening the motive
**reduces** their remaining obligation (they no longer have to manufacture
general position from a bare rigid IH — gap (G1) is dissolved at the source).
The one genuine new burden is handling the **non-general-position base** so the
motive stays *satisfiable* for the parallel K₂ leaf — see §1.4.

### 1.4 Recommendation

**Strengthen the motive — but condition the general-position conjunct on
`G.Simple`, matching KT's "(nonparallel, if `G` is simple)" exactly.** Concretely
the recommended shape is one of:

> (A) `HasFullRankRealization k G := ∃ Q, Q.graph = G ∧
>     Q.toBodyHinge.IsInfinitesimallyRigidOn V(G) ∧ (G.Simple → Q.IsGeneralPosition)`

or, if the `Simple` predicate proves awkward to thread through the reduction
(`minimal_kdof_reduction` does not currently track simplicity), the equivalent
**two-motive** split KT effectively uses: keep the bare `HasFullRankRealization`
for the non-simple/base legs, and add a *separate* `HasGenericFullRankRealization
k G` (general position unconditional) carried only through the simple-graph
cases, with a one-line `HasGenericFullRankRealization → HasFullRankRealization`
forgetful map.

Rationale for "strengthen", against the alternative (b) "keep the motive bare,
prove a perturbation lemma 'a bare rigid realization has a nearby transversal-
rigid sibling'":

- **(b) is circular / heavier.** The perturbation argument (rigidity is
  Zariski-open, so a generic nearby normal is still rigid) is *itself* the rank
  polynomial — you would need `exists_rankPolynomial_of_rigidOn`, which already
  needs `hne` (transversal). So (b) cannot bootstrap general position from a
  genuinely-degenerate rigid IH without first having general position. This is
  the (G1) circularity the recon flagged.
- **(A) matches the source.** KT's induction is *designed* so the IH is
  nonparallel; the project diverged by relativizing to a bare motive (a correct
  fix for the `V(G)`-relative trap, `DESIGN.md`, but it dropped the nonparallel
  conjunct that the relativization did not require it to drop). (A) re-adds only
  the dropped conjunct.
- **(A) dissolves (G1) at the source** and makes the splice feed direct: a
  general-position parent seed gives general-position legs (`withGraph_normal`
  is `rfl`), so `hgp`/`hne` are discharged for free.

**Caveat the user should weigh before committing to (A) vs the two-motive
split:** a `Graph.Simple` predicate *does* exist (the vendored
`Matroid/Graph/Simple.lean:183`, `class Simple … extends G.Loopless`), so (A) is
feasible — but `Graph.minimal_kdof_reduction` (`Induction.lean:3529`, Phase 20,
green) does **not** currently expose graph-simplicity to its case dispatch, and
the inductive subgraphs (`splitOff`, `rigidContract`) would need a simplicity-
preservation side-fact (KT Lemma 6.7(ii): `G_v^{ab}` is simple when `G` is
simple). KT spends Lemma 6.7 on exactly this. If threading `Simple` through the
reduction proves costly, the **two-motive split** localizes the general-position
bookkeeping to the simple cases and avoids re-opening Phase 20's reduction
principle. **I lean to the two-motive split** as the lower-ripple option: it
touches no Phase-20 node, the forgetful map is one line, and it mirrors KT's own
bifurcation (Lemma 6.2 bare vs. 6.3/6.5 nonparallel). The single-conjunct form
(A) is cleaner if and only if `Simple` threads cheaply through
`minimal_kdof_reduction` — that is a Lean-feasibility question worth a 1-commit
spike before the full producer build.

### 1.5 Generic-motive recon — the route is a hybrid (2026-06-04)

The two-motive split (§1.4) landed green, and so did all the Case-I bricks (N4,
N5, N6a, the (G2) factor, the N6b/N6c coupling, the leg-transport
`hasGenericRealization_transport_ends`). The **one remaining red node** is the
N6 composer, whose IH-shape gap the hand-off named for a math-first recon. This
section settles it. The two candidate routes from the §1.4 hand-off:

- **Route 1** — re-run `Graph.minimal_kdof_reduction` against
  `HasGenericFullRankRealization` (make the *IH* generic).
- **Route 2** — strengthen the simple-case coupling to conclude GP at the
  realizing point (make the *producer* generic).

**Decision: a hybrid — Route 2 *and* Route 1 are the two halves, not
alternatives.** The composer's per-leg adapter
`hasGenericRealization_transport_ends` (green, `AlgebraicInduction.lean:4109`)
*consumes* each leg in `HasGenericFullRankRealization` (its `hQgp` hypothesis)
and the coupling `…_couple_ofNormals` *produces* only the bare motive. So:

1. **Route 2 is needed to make the producer generic. GREEN (2026-06-04, one
   commit).** The coupling already *derives* `IsGeneralPosition` at its seed `q₀`
   (`:4036`, `hgp := hQgp_pos q₀ hq₀gp`), but the bare device closure realizes at
   a **different**, existentially-hidden `q` returned by
   `exists_good_realization_ofParam` (`:2938`, conclusion `∃ q, finrank ≤ …` — no
   GP conjunct). **N6-G1a spike correction:** the original plan asserted that `q`
   *is* general position ("the device varies over `ofParam` moment-curve points");
   **this was a false premise.** Tracing the device output —
   `exists_good_realization_ofParam` → `exists_relative_full_count_ofParam` →
   `exists_good_realization` → `exists_finrank_dualCoannihilator_polynomial` — shows
   `q` is an *arbitrary* non-root of a Gram-determinant `MvPolynomial`, **not** an
   `ofParam` moment-curve point, so `isGeneralPosition_ofParam` (`:2048`) does not
   apply and there is *no* dropped GP witness to re-expose. The correct, cheaper
   route realizes at the GP *seed* `q₀` directly: the splice glue
   `isInfinitesimallyRigidOn_of_splice` (`:1550`) is *genericity-free* (it does not
   invoke the device) and already proves `(ofNormals G ends q₀).toBodyHinge` rigid
   on all of `V(G)`, and `q₀` is GP by hypothesis. So N6-G1 is the single lemma
   `hasGenericFullRankRealization_of_splice_ofNormals` =
   `⟨ofNormals G ends q₀, rfl, hgp, glue⟩`, bypassing the device entirely (the
   device certifies the witnessed corank only for the *bare* motive). One commit,
   axiom-clean, no Phase-20 touch.

2. **Route 1 is still needed to make the IH generic.** Route 2 produces
   `HasGenericFullRankRealization` for the simple-case *output*, but the
   composer's *input* legs come from `minimal_kdof_reduction`'s IH, which is the
   bare motive. Closing the simple branch therefore *also* needs the induction
   to thread the GP motive. This is genuinely Phase-20-touching and
   multi-commit (`N6-G2`, **needs-further-recon**): the honest motive is the
   *conditioned* `(G.Simple → GP) ∧ bare` (unconditional GP is false at the
   parallel-K₂ base, §1.1).

**KT Lemma 6.7(ii), verified against the source (KT 2011 printed p.676 = pdf
p.31).** For `G` 2-edge-connected minimal `k`-dof, `|V|≥3`, **and no proper
rigid subgraph**: (i) `|V|=3 ⟹ k=0` and `G` (a triangle) has a nonparallel
full-rank realization; (ii) `|V|≥4 ⟹ G_v^{ab}` is simple for any degree-2 `v`.
The standing *no-proper-rigid-subgraph* hypothesis means **6.7(ii) is the
Case-II/III (splitting-off) simplicity fact — it does NOT cover the Case-I
contraction.** No `splitOff`/`rigidContract` simplicity lemma exists in the
project. For the Case-I legs specifically: `Graph.Simple.mono`
(`Matroid/Graph/Simple.lean:202`, `H ≤ G → G.Simple → H.Simple`) gives the
rigid block `H` simple **for free** (it is a subgraph); the *contraction*
`G/E(H)` simplicity is exactly KT's Lemma 6.3-vs-6.5 split (printed pp. 673,
675), not a single fact. So `N6-G2` needs Lemma 6.7(ii) *for the split-off
branch* **plus** a Case-I contraction-simplicity dichotomy — both new, each its
own decomposition pass (re-recon at G2-open).

**Why the hybrid and not Route 1 alone.** Route 1 alone (a fully generic
reduction) would force *every* case — including the parallel-K₂ base and the
non-simple Lemma-6.2 branch — to conclude GP, which they cannot (§1.1). The
conditioned motive `(G.Simple → GP) ∧ bare` avoids that, but the GP conjunct of
its conclusion still has to be *produced* somewhere for the simple cases — which
is exactly Route 2's `_generic` producer. So Route 2 is a prerequisite of Route
1's simple-case discharge regardless; doing Route 2 first (it is the buildable,
motive-independent half) also de-risks G2's recon.

**Why the hybrid and not Route 2 alone.** Route 2 alone makes the simple-case
producer generic, but the composer still needs *generic legs in* — and those
come from the IH, which only Route 1 upgrades. A producer that concludes the
strong motive from strong-motive inputs is inert until the induction supplies
strong-motive inputs.

**Build order (N6):** `N6-G1` ✓ (`hasGenericFullRankRealization_of_splice_ofNormals`,
GREEN — collapsed from the planned G1a-spike + G1b once the spike found the
device-GP route false; see Route 2 above) → **`N6-G2`** (Route 1, the
generic-motive reduction, multi-commit + Phase-20-touch; **re-reconned in §1.6**
into G2a/G2b/G2c) →
`N6-G3` (composer assembly: dispatch on `G.Simple`, feed N4 + the two transported
generic IHs into `hasGenericFullRankRealization_of_splice_ofNormals`, forget down
for non-simple via `hasFullRankRealization_of_generic`). The node list and
statuses are in `notes/Phase22a.md` *Lemma checklist*.

### 1.6 N6-G2 re-recon — the generic-motive reduction, decomposed (2026-06-04)

The §1.5 hand-off named N6-G2 as the remaining red half and flagged it
**NEEDS-FURTHER-RECON, do-not-dispatch-whole**. This section is that recon: it
fixes the *shape* of the generic-motive reduction and cuts it into the three
named decomposition passes (G2a/G2b/G2c), each its own future commit, with the
honesty gate (`DESIGN.md` *Constructibility recon …*) applied per pass. **No
Lean / `\leanok` / blueprint edits accompany it** — like §1.4/§1.5 it is
decision-support. The structural facts were read off the live source
(`Induction.lean:3529` `minimal_kdof_reduction`, `AlgebraicInduction.lean:2737`
`theorem_55`, `:2699` `HasGenericFullRankRealization`, `:4151`
`hasGenericRealization_transport_ends`) and verified against KT 2011 §6.2
(printed pp. 673–676, pdf pp. 27–30).

**The target, precisely.** N6-G3's per-leg adapter
`hasGenericRealization_transport_ends` consumes each leg in
`HasGenericFullRankRealization` (its `hQgp`). The legs come from `theorem_55`'s
`hcontract` IH `∀ G', G'.IsMinimalKDof n 0 → … → V(G') < V(G) →
HasFullRankRealization k G'` — **bare**. So N6-G2's job is to supply a parallel
induction whose IH delivers the *generic* motive to the simple-Case-I legs.
`theorem_55` is *literally* `minimal_kdof_reduction … hbase hsplit hcontract`
instantiated at `P := HasFullRankRealization k` (`:2755`), so the motive is a
free `P`-parameter — a generic reduction is `minimal_kdof_reduction` instantiated
at a *different* `P`. The only question is **which `P`**, and that is where the
two prior blockers live.

**The two structural obstructions, restated.**
1. **Unconditional GP (`P := HasGenericFullRankRealization k`) is false at two
   leaves** — the parallel-K₂ base (`hbase`, two parallel edges want *equal*
   panels, KT Lemma 5.3 / 6.2, §1.1) and the non-simple Lemma-6.2 branch. So a
   bare `minimal_kdof_reduction` at the generic motive cannot discharge `hbase`
   or the non-simple `hsplit`/`hcontract`.
2. **The conditioned motive `Pc G := (G.Simple → GP G) ∧ bare G` re-opens
   `Simple`-threading**, and `splitOff` does *not* preserve simplicity (verified
   against the live def `Induction.lean:572`: `splitOff v a b e₀` adds `e₀`
   linking `a`-`b` *unconditionally*, so a simple parent with a pre-existing
   `a`-`b` edge `e ≠ e₀` recurses on a non-simple child). Hence at `hsplit` a
   simple parent's `Pc`-IH on the split-off child delivers *nothing* (the child's
   `Simple → GP` premise is unmet) — the §1.5 dead-end.

**The new finding (KT §6.2 verified, sharpens the decomposition).** KT's Case I
is **not a uniform contraction recursion**; it trifurcates by simplicity (KT
p.673): Lemma 6.2 (`G` not simple, bare), Lemma 6.3 (`G` simple **and** some
proper rigid `G′` has `G/E′` simple → generic), Lemma 6.5 (`G` simple but **no**
such `G′` → generic). Crucially, **Lemma 6.5's proof (Claim 6.6, p.676) shows
that case is a degree-2 vertex *removal* `Gv`, not a contraction**, and `Gv` is
simple *because it is a vertex removal* ("Gv is simple since G is simple", p.676
— vertex deletion `-` has a `Simple` instance in the fork; `splitOff` does not).
So the simple-Case-I legs that genuinely need a *generic* IH are exactly the
**Lemma-6.3 legs**: the rigid block `G′` (= the project's `H`) and the
contraction `G/E′` (= `G.rigidContract H r`). For those two:
- **`H` simple is free** — `H ≤ G` and `Graph.Simple.mono`
  (`Matroid/Graph/Simple.lean:202`). No new fact.
- **`G/E′` simple is the genuine new combinatorial obligation** — it is exactly
  KT's Lemma-6.3-vs-6.5 dichotomy (does a contraction stay simple?), *not* a
  single fact, and the project has *no* `Simple` lemma for `map`/`collapseTo`
  (`rigidContract = (G ＼ E(H)).map (collapseTo r V(H))`, `Induction.lean:1855`;
  the fork's `Simple` instances cover `↾`/`＼`/`-`/induce/`noEdge`/`singleEdge`,
  **not** `map`).

**Decision: condition the motive on `G.Simple` (form (A) `Pc`), and route the
`Simple`-failure cases to the *bare* conjunct — do NOT attempt unconditional
GP.** The conditioned motive `Pc` is satisfiable everywhere (the bare conjunct is
`theorem_55` itself, already green-modulo-21b; the `Simple → GP` conjunct is
vacuous wherever `G` is non-simple — incl. the parallel-K₂ base and Lemma-6.2).
The §1.5 split-off dead-end (obstruction 2) is *not* fatal under this routing:
N6-G2 only needs the `Simple → GP` conjunct discharged at the *contraction*
(`hcontract`) branch for Lemma-6.3 legs, and the contraction branch's IH is
applied to `H` and `G/E(H)` whose simplicity is governed by `Simple.mono` +
the new `map`-simplicity fact — **not** by `splitOff`. At `hsplit` and `hbase`
the parent is allowed to be non-simple (or the conjunct discharged trivially),
so `splitOff`-non-preservation is harmless: a simple parent reaching `hsplit` is
KT's Lemma-6.5 case (degree-2 removal), where KT itself recurses on the
vertex-removal `Gv` (simple) — *not* on the project's edge-adding `splitOff`.
**Open sub-question for G2a — RESOLVED at G2a-build (2026-06-04):** the project's
`minimal_kdof_reduction` routes *all* no-proper-rigid-subgraph cases — including
KT's Lemma-6.5 simple case — through `hsplit`/`splitOff`, whereas KT's Lemma 6.5
uses vertex-removal `Gv`. The flag asked whether `Pc`'s `hsplit` premise is
dischargeable for a *simple* parent under the project's `splitOff` routing. **The
resolution is by *scope*, not routing:** the `Simple → GP` conjunct of the
splitting-off branch is itself the Case-III generic *producer* (Track B,
`theorem_55.hsplit`, one rigidity row short), which is out of 22a's Case-I scope
and entirely red — so regardless of whether `splitOff` preserves simplicity, that
conjunct cannot be discharged *within* 22a. The honest in-scope shape (taken in
`theorem_55_generic`) carries it as the explicit hypothesis `hsplitGP` — escalation
(ii) above, the Phase-21b green-modulo `h…` idiom — keeping the node green-modulo and
honest, with **no** Phase-20 `removeVertex` re-parameterization (escalation (i)) needed.

**The three decomposition passes (each its own future commit; re-recon each at
open).**
- **G2a — the conditioned-motive reduction skeleton (Phase-20-touching). GREEN
  (`theorem_55_generic`, 2026-06-04, axiom-clean).** `Graph.minimal_kdof_reduction`
  at `Pc G := (G.Simple → GP G) ∧ bare G`; each branch's bare conjunct from the
  `theorem_55`-shaped hypotheses, each branch's `Simple → GP` conjunct from a
  carried hypothesis (`hbaseGP`/`hsplitGP`/`hcontractGP`, the latter fed the *full
  conditioned IH*). **The flagged sub-question is SETTLED by scope, not routing:**
  the splitting-off branch's `Simple → GP` conjunct *is* KT Case III (Track B, out
  of 22a scope, red), so it is carried as `hsplitGP` (green-modulo `h…`) — no
  Phase-20 `removeVertex` re-route, no internalizing the `splitOff`-non-simplicity
  question. Pure structural composition (the motive plumbing is the only new
  content, and it is one `minimal_kdof_reduction` application).
- **G2b — `map`/`collapseTo` simplicity (the new combinatorial fact). GREEN
  (`rigidContract_simple` + `map_simple`, 2026-06-04, project-side in
  `Induction.lean`).** The math-first pass found the clean primitive is a
  *positive* `map`-simplicity criterion — `map_simple` (`(f ''ᴳ G).Simple` from
  no-self-collapse `hloop` + no-pair-collapse `hpar`), specialized to
  `rigidContract`. The expected "Lemma-6.3-vs-6.5 dichotomy as a decidable case
  split" turned out to be *downstream*: `map_simple` is the faithful statement of
  Lemma 6.3's `G/E′`-simple *hypothesis*, and the dichotomy (which of `hloop`/`hpar`
  holds at the realized contraction) is what G2c decides. `map` is the one op that
  breaks `Simple` (it can make loops and parallel edges), absent any `map`-simplicity
  instance in the fork — project-side route taken (no fork edit). Axiom-clean.
- **G2c — wire G2a+G2b into the simple-Case-I `hcontract` discharge.** With the
  conditioned IH (G2a) giving `GP` on the two Lemma-6.3 legs (`H` via
  `Simple.mono`, `G/E(H)` via G2b), feed them through
  `hasGenericRealization_transport_ends` into N6-G1 (the generic producer), then
  `hasFullRankRealization_of_generic` to land the bare conjunct of `Pc`.
  `buildable` once G2a/G2b are green (it is the same assembly N6-G3 does, at the
  conditioned-motive layer). This pass and N6-G3 may merge.

**Net.** N6-G2's hard kernel was **G2b** (the `map`-simplicity / Lemma-6.3-vs-6.5
fact) and the **G2a flagged sub-question** (does `Pc`'s `hsplit` survive the
project's `splitOff` routing for a simple parent, or is a Phase-20 re-route
onto vertex-removal needed). **Both are now GREEN.** G2a (`theorem_55_generic`,
2026-06-04; the flagged sub-question resolved by *scope*, above) and G2b
(`rigidContract_simple` + `map_simple`, 2026-06-04; the dichotomy collapsed to a
clean positive criterion, the dichotomy itself deferred downstream to G2c). **The
next commit is G2c** — wire G2a+G2b into the simple-Case-I `hcontract` discharge
(`theorem_55_generic`'s `hcontractGP`); may merge with N6-G3. The one open
question for G2c is discharging `rigidContract_simple`'s `hloop`/`hpar` from KT
Lemma 6.3's standing setup — re-recon at G2c-open (escalation-eligible to the
"carry `(G/E(H)).Simple` as `h…`" idiom if the failure cases need the dichotomy).

---

## 2. Shared-infra map (green vs. missing across the layer)

Built once, reused by all cases. **Green** unless marked.

| Brick | Lean name (`AlgebraicInduction.lean` unless noted) | Status | Reused by |
|---|---|---|---|
| Genericity device (Claim 6.4/6.9) | `exists_good_realization`, `_const`, `_ofParam` (`:2604`,`:3388`,`:2672`) | GREEN | Case I, Case II/III, Prop 1.1 |
| B0 row coordinatization (polynomial-in-normals) | `exists_good_realization_ofParam` (`:2672`) | GREEN | Case I, Case II/III |
| Device→motive closure (N7a) | `hasFullRankRealization_of_independent_panelRow` (`:2808`) | GREEN | all producers |
| N7b-0 (rigid-on-V ⟹ full-size independent panel-row subfamily) | `BodyHingeFramework.exists_independent_panelRow_subfamily_of_rigidOn` (`:2929`) | GREEN | Case I, Case II/III |
| N7b-1/2/3 (per-edge new-block rows; transport; pin-a-body column split) | `exists_independent_panelRow_subfamily_of_edge`, `…_transport`, `linearIndependent_sum_pinned_block` | GREEN | Case II/III (eq. 6.12) |
| Case-I splice glue (block-triangular gluing, genericity-free) | `BodyHingeFramework.isInfinitesimallyRigidOn_of_splice` (`lem:case-I-splice-seed`), `isInfinitesimallyRigidOn_union_of_inter` | GREEN | Case I |
| Splice producer (composes glue→N7b-0→device) | `hasFullRankRealization_of_splice` / `…_ofNormals` / `…_ofParam` | GREEN | Case I |
| Splice producer, general-position-free (N6a) | `hasFullRankRealization_of_splice_of_supportExtensor` / `…_of_supportExtensor_ofNormals` | GREEN — takes `hsupp` not `hgp`; non-simple Lemma 6.2 | Case I (non-simple) |
| Single-leg seed→realization bridge | `hasFullRankRealization_of_rigidOn_seed` (`:3151`) | GREEN | Case I, Case II/III |
| IH repackage (motive ⟹ rigid `ofNormals` locus) | `exists_rigidOn_ofNormals_of_hasFullRankRealization` (`:3192`) | GREEN (re-types under §1.3.5) | Case I |
| Per-leg rank polynomial (rigid leg ⟹ nonzero Gram-det `MvPolynomial`) | `exists_rankPolynomial_of_rigidOn` (`:3226`) | GREEN — **but needs `hne` (G1)** | Case I |
| Rank-polynomial consumer (non-root ⟹ rigid at that point) | `isInfinitesimallyRigidOn_ofNormals_of_rankPolynomial_ne_zero` (`:3315`) | GREEN | Case I |
| Constructive rank-witnessing mirror | `exists_polynomial_ne_zero_of_linearIndependent_at` (`Mathlib/LinearAlgebra/Matrix/Rank.lean`) | GREEN | Case I |
| General-position witnesses (moment curve) | `momentCurve`, `withMomentNormals`, `ofParam`, `isGeneralPosition_ofParam` (`:1785`–`:1933`) | GREEN | all (seed) |
| transversal hinge ⟹ nonzero extensor | `supportExtensor_ne_zero_of_isGeneralPosition` (`:1773`) | GREEN | all |
| N4 graph↔matroid contraction-minimality | `Graph.rigidContract_isMinimalKDof` (`Induction.lean`) | GREEN | Case I (`hcontract` recursion) |
| Count bridges (`V(G)`-relative N1–N3) | `finrank_pinnedMotionsOn_vertexSet`, `exists_relative_full_count_ofParam`, `isInfinitesimallyRigidOn_vertexSet_of_finrank_le` | GREEN | all |
| **Lemma 2.1 (extensor independence)** | `omitTwoExtensor_linearIndependent` (`Extensor.lean:493`) | GREEN — **hyp `AffineIndependent ℝ p`** | Case III (the missing row) |
| **(G2) general-position factor** | `exists_generalPosition_polynomial` (+ `pairLeadingMinorPoly`, `pair_linearIndependent_of_leading_minor_ne_zero`) | **GREEN** (2026-06-04; off-diagonal product of leading `2×2` minor polynomials) | Case I coupling |
| **`prop:rigidity-matrix-prop11` `hub`** | carried as hypothesis (`:2527`) | RED (multi-commit, Phase-19 partition count) | Prop 1.1 only |

**Reading:** the entire device + witness-transfer + splice + count + N4
substrate is GREEN; **(G2) is now GREEN too** (2026-06-04,
`exists_generalPosition_polynomial`). The *only remaining missing analytic brick
across the whole layer* is the **Case-III missing row** via Lemma 2.1 (Track B);
the simple Case-I cases N6b/N6c are now an *assembly* of green bricks (no new
analytic content). (G1) was not a missing brick — it was the motive decision of
§1, dissolved by the two-motive split.

---

## 3. Per-case producer structure, node list, build order

Honesty gate applied: each node tagged **buildable** (math settled, arithmetic
closes from green inputs — decompose-then-build) or **research-shaped** (the
math is the hard part — math-first before any node is scheduled), per `DESIGN.md`
*Constructibility recon …*.

### Track A — Case I producer (`hcontract`), KT §6.2

KT splits Case I into three sub-cases by simplicity. The **constructibility
arithmetic closes for all three**: `rank = D(|V'|−1) [rigid block] + D(|V∖V'∪{v*}|−1)−k [contraction] = D(|V|−1)−k` (eqs. 6.3, 6.9), full rank at k=0. No
shortfall — this is the tractable track.

Nodes (composing the green infra of §2):

- **N6a — non-simple Case I (KT Lemma 6.2).** **GREEN** (2026-06-04). Equal-panel
  splice (`ΠG/E',p2(v*) = ΠG',p1(a) = ΠG',p1(b)`); a bare (non-general-position)
  realization suffices, so it consumes the *bare* motive and supplies the bare
  motive. Built as `hasFullRankRealization_of_splice_of_supportExtensor`
  (+ leg-native `…_ofNormals`): the splice producer parameterized by transversal
  hinges (`hsupp`) directly rather than general position (`hgp`) — N7b-0 only ever
  needed `hsupp`. The old `hasFullRankRealization_of_splice` now factors through it
  as a thin GP corollary. Lowest-risk starting node; **does not need the motive
  strengthening** — confirmed in practice (axiom-clean, no Phase-20 touch).
- **N6b/N6c — simple Case I (KT Lemma 6.3/6.5).** **GREEN** (2026-06-04;
  `hasFullRankRealization_of_couple_ofNormals`). The shared-seed coupling: each
  leg's leg-restricted rank polynomial × the (G2) factor → triple-product shared
  non-root → each leg rigid + GP at it → `…_splice_ofNormals`. *Note:* this
  concludes only the **bare** motive — the GP is held at the seed `q₀` but the
  device realizes at a different hidden `q` (see §1.5); upgrading it to conclude
  `HasGenericFullRankRealization` is N6-G1.
- **(G2) general-position factor.** **GREEN** (2026-06-04;
  `exists_generalPosition_polynomial`). Off-diagonal product of leading `2×2`
  minor polynomials, witnessed nonzero at the moment-curve seed (Vandermonde).
- **N6 — Case I composer (`lem:case-I-realization`).** **RED — decomposed in §1.5
  into the hybrid N6-G1/G2/G3; N6-G1 now GREEN.** Not `buildable` as a single
  commit: the composer's adapter needs each leg in `HasGenericFullRankRealization`,
  which (i) the coupling did not produce — **fixed by N6-G1,
  `hasGenericFullRankRealization_of_splice_ofNormals`, GREEN** — and (ii)
  `minimal_kdof_reduction` does not thread (N6-G2, Route 1, multi-commit,
  re-reconned in §1.6 into G2a/G2b/G2c). Remaining: G2a → G2b → G2c → N6-G3.
  See §1.6 + `notes/Phase22a.md`.

**Build order (Track A), updated 2026-06-04 (everything before N6 is green):**
§1 motive decision ✓ → N6a ✓ → (G2) ✓ → N6b/N6c coupling ✓ → **N6 composer
(§1.5 hybrid, §1.6 N6-G2 cut): N6-G1 ✓ → G2a → G2b → G2c → N6-G3.**

### Track B — Case II/III producer (`hsplit`), KT §6.3 (Lemma 6.8) + §6.4.1

**This is KT Case III** at the project's k=0 scope (FRICTION dead-end #3; Finding
B; `DESIGN.md` *Phase Case-naming …*). Constructibility: eq. (6.12) degenerate
placement gives `+(D−1)` ⟹ `rank = D(|V|−1)−1`, **one row short** of the k=0 full
target. The missing row is the Case-III redundant-edge row.

- **eq. (6.12) degenerate placement** (`p1(vb)=q(ab)` reproduces the `e₀`
  row). `buildable` (feeds the green N7b-0/1/2/3 + pin-a-body split). Gives
  `+(D−1)`. **Needs the incoming split-leg nonparallel** (Claim 6.4) — so it too
  consumes the strengthened motive (or the two-motive's generic form).
- **Lemma 6.10 (`d=3`, 3 candidates)** — `research-shaped`. The single largest
  proof in KT (~12 pp.). Two sub-claims:
  - **Claim 6.11 (combinatorial↔linear):** `R(G_v^{ab},q)` has a redundant
    `ab`-row, via Lemma 4.3(ii) + IH. Wires `M(G̃_v^{ab})` to the row matroid of
    `R`. The hardest non-extensor step; `research-shaped`.
  - **Claim 6.12 (extensor-span genericity):** if all `D` candidates fail, a
    nonzero `r ∈ ℝᴰ` is ⟂ all extensors on `d+1` generic panels, which by
    **Lemma 2.1** (`omitTwoExtensor_linearIndependent`, green, hyp
    `AffineIndependent ℝ p`) span `ℝᴰ` — contradiction. The degree-2 condition
    forces all candidates to test the same `r` (eq. 6.44). The extensor half maps
    onto Phase-17's Lemma 2.1 directly; `research-shaped` only in the candidate-
    bookkeeping (consider an abstracted "candidate normal form" lemma to avoid
    repeating the row-ops three times).

**Build order (Track B):** strictly *after* Track A and the motive decision. The
eq. (6.12) placement is the buildable warm-up; Lemma 6.10 is the crux and is the
natural decompose-math-first target for a dedicated sub-session.

### Assembly (may defer to Phase 23)

- **`prop:rigidity-matrix-prop11` `hub` brick** — `research-shaped (multi-commit)`,
  Track-independent (Phase-19 partition count: construct `D(|P|−1)−(D−1)·d_G(P)`
  motions from a deficiency-attaining partition). Decompose math-first before
  scheduling.
- **`thm:theorem-55` / `lem:case-III` flip green** once the producers land
  (one-line, the recursion body is already assembled).

---

## 4. Risk / scope

**Genuinely research-shaped (the math is the hard part):**
- **Lemma 6.10 / Claim 6.11** (Track B) — the largest proof in KT; the
  combinatorial↔linear redundant-`ab`-row identity is the single highest-risk
  node in Phases 22–23. Claim 6.12's extensor half is de-risked (Lemma 2.1 green).
- **`hub` partition-count** — multi-commit but settled math (Phase-19 substrate).
- **(G2) general-position factor** — bounded research-shaped; standard math, new
  Lean mirror.

**Buildable once §1 is decided:** the entire Case-I track (N6a fully motive-
independent; N6b/N6c gated on (G2)+motive), the eq. (6.12) placement, and the
final `theorem_55` flip.

**Axiomatization / deferral candidates, if full formalization of a case proves
out of reach (in escalation order — do not reach for these before the math-first
decomposition is genuinely stuck):**
1. **Lemma 6.10 / Claim 6.11 as an explicit hypothesis on the Case-III node**,
   in the established Phase-21b "carry the analytic crux as `h…` and `\uses` the
   red node" idiom (exactly how Cases I/II carried the device pre-21b). This
   keeps `theorem_55` green-modulo-Lemma-6.10 and honest (the node stays red),
   and is the *recommended* fallback — it isolates the one genuinely-hard kernel
   without blocking the rest of the molecular program (Phases 24–26 depend on
   Thm 5.6, which needs Thm 5.5; a green-modulo capstone unblocks them).
2. **(G2) factor as a hypothesis** on the Case-I composer (same idiom), if the
   Vandermonde brick stalls — lower-risk than (1), since (G2) is bounded.
3. **`theorem_55` itself as `axiom`** — *last resort, not recommended.* It would
   make the whole molecular capstone (Cor 5.7) rest on an axiom; prefer the
   green-modulo decomposition (1)/(2), which keeps every discharged step honest
   and tracks the remaining obligation as a visible red node.

**Scope guard:** the motive decision (§1) is a *prerequisite* to any Case-I
simple-case build or any Track-B build — both consume nonparallel legs. The one
node that needs *nothing* from §1 is N6a (non-simple Case I). A sensible first
commit after the motive decision is N6a (proves out the splice plumbing on the
bare motive), then the (G2) factor, then the simple cases.

---

## 5. One-line recommendation

**Strengthen the motive to carry general position, conditioned on `G.Simple`
(matching KT's "nonparallel, if simple"); prefer the two-motive split if
threading `Simple` through `minimal_kdof_reduction` is costly — this dissolves
gap (G1) at the source, leaves the green producer infra needing only the bounded
(G2) general-position factor for Case I, and isolates the one genuinely
research-shaped kernel (Lemma 6.10 / Claim 6.11, Track B) as a green-modulo
deferral candidate.**
