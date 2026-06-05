# Phase 22 — realization-layer design (decision-support doc)

**Status:** design pass, not a build plan. Produced 2026-06-04 after the
constructibility recon (FRICTION dead-end #5; `notes/Phase22a.md` *Blockers*)
found the Case-I coupling has two real gaps **(G1)/(G2)** the type-level plan
was blind to. The user paused per-commit Lean work to decide the **motive
question** — should `PanelHingeFramework.HasFullRankRealization` carry general
position (KT's "nonparallel"). The motive decision landed (the **two-motive
split**, §1.4, green); §**1.5** (2026-06-04) is the follow-on **generic-motive
recon** settling the N6-composer IH-shape gap as a **hybrid route** and cutting
it into the buildable N6-G1/G2/G3 nodes; §**1.6** (2026-06-04) cuts N6-G2 into
G2a/G2b/G2c (all now green); §**1.7** (2026-06-05) is the **N6-G3 recon**,
settling the `Gc ≤ G` binding obstruction (the splice's contraction leg is
`G ＼ E(H)`, not the relabelled `rigidContract`; the collapse lives on the
placement side as KT's Claim 6.4 transport) and cutting N6-G3 into G3a/G3b/G3c
(the live to-do is `notes/Phase22a.md` *Lemma checklist*). No Lean / `\leanok` /
blueprint edits accompany this doc.

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

### 1.7 N6-G3 re-recon — the `Gc ≤ G` mismatch is KT's Claim 6.4 transport; the splice's contraction leg is `G ＼ E(H)`, not the relabelled `rigidContract` (2026-06-05)

G2c landed green (the *generic coupling producer*
`hasGenericFullRankRealization_of_couple_ofNormals`), so every Case-I *producer*
brick is now green and the one remaining red node is the N6-G3 composer assembly.
The hand-off (`notes/Phase22a.md` *Blockers*/*Hand-off*) flagged the binding
obstruction as "**the `Gc ≤ G` mismatch** — `G.rigidContract H r` collapses
`V(H)` to `r`, so it is *not literally* a subgraph of `G`, yet the coupling
brick's `hGc : Gc ≤ G` demands one — the right thing to recon first." This section
is that recon. **No Lean / `\leanok` / blueprint edits accompany it; it is
decision-support**, like §1.4–§1.6. Verified against KT 2011 §6.2 (printed
pp. 673–675 = pdf pp. 27–29, eqs. (6.3)–(6.9)) and the live splice API
(`AlgebraicInduction.lean` `isInfinitesimallyRigidOn_of_splice:1550`,
`hasGenericFullRankRealization_of_couple_ofNormals:4197`; `Induction.lean`
`rigidContract:1855`, `IsInfinitesimallyRigidOn` is constancy on `s` bodies,
`RigidityMatrix.lean:752`).

**The mismatch is real and not a relabelling artefact — it is structural.** Every
splice brick across the layer (the glue `isInfinitesimallyRigidOn_of_splice`, the
producers `hasFullRankRealization_of_splice*`, both couplings) requires **both**
legs to be *literal subgraphs of the parent* `G` (`hGH : GH ≤ G`, `hGc : Gc ≤ G`),
because the glue transports each leg's rigidity to the parent by
`isInfinitesimallyRigidOn_of_withGraph_of_le` ("re-adding edges only shrinks
motions", which needs `leg ≤ parent`). The rigid block `H` fits (`H ≤ G` from
`IsRigidSubgraph`). The contraction `G.rigidContract H r =
(G ＼ E(H)).map (collapseTo r V(H))` does **not**: `map` relabels `V(H) ↦ r`, so
`V(G.rigidContract H r) = collapseTo r V(H) '' V(G)` is a *quotient* of `V(G)`,
and there is **no** `rigidContract_le` lemma (confirmed: none exists, and none can
— the vertex sets are not even comparable). Feeding `Gc := G.rigidContract H r`
to the coupling's `hGc` is therefore *type-impossible*, not merely missing a proof.

**What KT actually splices (eq. (6.3)) — the contraction leg in the rigidity
matrix is `G ＼ E(H)`, a genuine `≤ G` subgraph.** KT's eq. (6.3) block form is
`R(G,p) = [ R(G',p1)  0 ; *  R(G,p; E∖E′, V∖V′) ]`. The *second block* is
`R(G,p; E∖E′, V∖V′)` — the rigidity matrix of the parent `G` **restricted to the
surviving edges `E∖E′ = E(G) ∖ E(H)`** (over the body columns `V∖V′`). In the
project's encoding that is exactly `(ofNormals G ends q₀).toBodyHinge.withGraph
(G.deleteEdges E(H))` — and `G.deleteEdges E(H) ≤ G` holds (it is a subgraph
operation with a `Simple`/`≤` instance, `edgeSet_rigidContract` already reads its
edge set as `E(G) ∖ E(H)`). **So the contraction leg of the splice is
`Gc' := G.deleteEdges E(H)`, NOT the relabelled `rigidContract`.** The collapse to
`v∗`/`r` lives entirely on the *placement* side, not the graph side: eq. (6.7)'s
`p_{E∖E′}` realizes the contraction's edges on `G ＼ E(H)` (the boundary hinges
`δ_G(V′)` placed by the panel-intersection `Π_{G/E′,p2}(u) ∩ Π_{G′,p1}(v)`), with
`v∗` realized as a *d-dimensional body* rather than a panel (KT p. 675, the
`(G/E′, p_{E∖E′})` body-hinge framework).

**The genuinely-new analytic content is KT Claim 6.4 — the rank-transport
`rank R(G/E′, p_{E∖E′}) ≥ rank R(G/E′, p2)`** (eq. (6.9)). This is *not* a green
brick. The contraction's inductive rigidity is `HasGenericFullRankRealization
(G.rigidContract H r)` — rigidity of the *abstract relabelled* graph at its own
seed. To feed the splice we need rigidity of `withGraph (G ＼ E(H))` on the body
set `(V(G) ∖ V(H)) ∪ {r}` (where `r = v∗`). KT Claim 6.4 supplies exactly this:
because the joint panel coefficients of `p1`, `p2` are algebraically independent
over ℚ (general position — the GP conjunct of the *generic* motive, which is why
the simple Case-I legs need `HasGenericFullRankRealization`), the
`p_{E∖E′}`-realization of `G ＼ E(H)` attains the contraction's rank. In the
project's rank-polynomial language this is a *new* per-leg brick:
**transport the contraction leg's rigidity across the collapse map** — from
`(ofNormals (G.rigidContract H r) ends_c q_c)` rigid on `V(G.rigidContract H r)`
to `(ofNormals (G.deleteEdges E(H)) ends q₀)` rigid on `(V(G) ∖ V(H)) ∪ {r}` at a
shared general-position seed. The lever is that the body-hinge motion space depends
on the graph only through the *linking edges'* support extensors
(`infinitesimalMotions_eq_of_isLink_span_supportExtensor`,
`AlgebraicInduction.lean:1140`), and the surviving edges `E(G) ∖ E(H)` are in
bijection between `G.rigidContract H r` and `G.deleteEdges E(H)` (only the
endpoints are relabelled by `collapseTo`); the relabelling is absorbed by the
endpoint selector / the `ends`-swap brick on the surviving edges, with the
collapsed body `r` carrying the `v∗` panel.

**Decision: N6-G3 is NOT one commit; it needs a new Claim-6.4 transport brick
before the assembly. Cut into G3a/G3b/G3c.** The per-leg recon (DESIGN.md
*Constructibility recon …*) shows the assembly's *second* leg cannot be supplied
by any green brick — the coupling consumes a `≤ G` leg rigid as `ofNormals · ends
·`, and the contraction IH delivers a relabelled-graph rigidity that no existing
lemma converts. That conversion (KT Claim 6.4) is the genuine remaining analytic
content of Case I. The three passes (each its own future commit; re-recon at open):

- **G3a — the Claim-6.4 collapse-transport brick (the new analytic content).**
  `rigidContract_rigidity_transport` (working name): from
  `HasGenericFullRankRealization (G.rigidContract H r)` (the contraction IH) and
  the general-position parent seed, produce a seed `q_c` and the rigidity of
  `(ofNormals (G.deleteEdges E(H)) ends q_c)` on `(V(G) ∖ V(H)) ∪ {r}`. The math
  is KT Claim 6.4 (eq. (6.9)); the Lean lever is the surviving-edge bijection +
  `infinitesimalMotions_eq_of_isLink_span_supportExtensor` (motion space sees only
  linking-edge support extensors) carrying rigidity across the relabel, with `r`
  the collapsed-body representative. **`research-shaped`** (the genuine new
  brick) — math-first decomposition before any dispatch; escalation-eligible to
  carrying Claim 6.4 as an explicit `h…` hypothesis on the composer (the Phase-21b
  green-modulo idiom) if the surviving-edge transport stalls.
  **OUTCOME (2026-06-05): GREEN-MODULO; the proposed lever does NOT close it.** The
  math-first pass found `infinitesimalMotions_eq_of_isLink_span_supportExtensor` is
  *inapplicable*: the surviving-edge "bijection" is endpoint-*relabelling*, and
  `collapseTo r V(H)` sends a surviving edge's endpoints to different bodies, so its
  support extensor `panelSupportExtensor (q u) (q v)` uses *different normals* in
  `rigidContract` vs. `deleteEdges E(H)` — the `hspan` span-equality the brick demands
  fails. Recovering the rank at the un-collapsed endpoints across that relabel *is* the
  algebraic-independence statement of Claim 6.4, irreducibly research-shaped. So the
  escalation fired: `PanelHingeFramework.rigidContract_rigidity_transport` carries
  Claim 6.4 as the narrow explicit hypothesis `htransport` and is the surrounding
  plumbing only (axiom-clean, no `sorry`); `htransport` re-enters at G3c (via
  `lem:case-III` / 22b+).
- **G3b — the cover/shared-body/endpoint-selector geometry.** With both legs now
  `≤ G` (`H` and `G.deleteEdges E(H)`), discharge the coupling's combinatorial
  inputs: `hcH : r ∈ V(H)`, `hcc : r ∈ V(G.deleteEdges E(H))`, the cover
  `V(G) ⊆ V(H) ∪ V(G.deleteEdges E(H))` (in fact `V(G.deleteEdges E(H)) = V(G)`,
  so the cover is trivial), the parent endpoint selector `ends`, and (G2b)
  `rigidContract_simple`'s `hloop`/`hpar` for the simplicity conjunct. **`buildable`**
  once G3a is green (graph-combinatorics from `IsProperRigidSubgraph`).
- **G3c — the composer assembly + `theorem_55`/`theorem_55_generic` flip.**
  Dispatch on `G.Simple`: simple branch feeds the `H`-leg IH (via `Simple.mono` +
  `subgraph_minimality`) and the transported contraction leg (G3a + N4
  `rigidContract_isMinimalKDof`) through `hasGenericRealization_transport_ends`
  into the G2c generic coupling, then `hasFullRankRealization_of_generic` for the
  bare `hcontract`; non-simple branch uses N6a directly. Discharges
  `hcontractGP`/`hcontract` ⟹ `lem:case-I-realization` green. **`buildable`** once
  G3a/G3b are green.

**Net.** The hand-off's blocker #1 (`Gc ≤ G` mismatch) **dissolves at the graph
level** — the splice's contraction leg is `G ＼ E(H)` (`≤ G`), not the relabelled
`rigidContract` — but **relocates to the placement level** as the genuinely-new
KT Claim 6.4 transport (G3a), which is the last research-shaped brick of Case I.
Blocker #2 (`rigidContract_simple`'s `hloop`/`hpar`) is G3b, downstream and
`buildable`. The right next *build* commit is **G3a**, preceded by a math-first
decomposition of the surviving-edge collapse transport (or its green-modulo
`h…`-deferral if that decomposition stalls). N6-G3's apparent "pure leg-data
geometry" framing in the prior hand-off was **too optimistic** — it was blind to
the placement-side Claim 6.4 obligation, exactly the *quantifier-domain / actual-
construction* sharpening the recon rule (DESIGN.md *Constructibility recon …*)
exists to catch.

---

### 1.8 G3c re-recon — the splice coupling hardcodes each leg rigid on its *full* `V(·)`, but the contraction leg is rigid only on `V∖V′ ∪ {v∗}`; G3c is NOT pure green-brick assembly (2026-06-05)

G3a (`rigidContract_rigidity_transport`) and G3b
(`couple_geometry_of_isProperRigidSubgraph`) landed; the §1.7 hand-off scoped G3c
as "the Lean assembly ONLY ... by assembling the green bricks" (`buildable`): feed
the `H`-leg IH and the G3a-transported contraction leg into the G2c coupling
`hasGenericFullRankRealization_of_couple_ofNormals`. **This recon (no Lean /
`\leanok` / blueprint edits; decision-support like §1.4–§1.7, verified vs. the live
brick signatures) finds that assembly is impossible as-is — a body-set mismatch the
"buildable" tag was blind to.**

**The mismatch.** Every Case-I splice *coupling/producer* above the honest base
glue hardcodes each leg infinitesimally rigid on its **full vertex set** `V(GH)` /
`V(Gc)`:
- `hasGenericFullRankRealization_of_couple_ofNormals` (G2c, `:4197`) and its bare
  sibling (`:4112`) take `hrigc : (ofNormals Gc ends qc).toBodyHinge.IsInfinitesimallyRigidOn V(Gc)`;
- the witness-transfer step (i) calls `exists_rankPolynomial_of_rigidOn_linking`
  (`:3874`), whose `hrig` is rigidity on **`V(G)`** and whose count is the full
  relative `D(|V(G)|−1)` (it bottoms on N7b-0
  `exists_independent_panelRow_subfamily_of_rigidOn_linking`, which reads
  `F.graph.vertexSet` rigidity and the full `D(|V|−1)` row count).

But the contraction leg is `Gc := G.deleteEdges E(H)`, and `V(Gc) = V(G)`
(`vertexSet_deleteEdges`, used by G3b's own cover proof). The contraction is **not**
rigid on all of `V(G)`: the surviving edges `E(G)∖E(H)` do not connect the interior
`V(H)∖{r}` (those edges were in `E(H)`, deleted), so those bodies are free — the
framework is rigid only on `(V(G)∖V(H)) ∪ {r}`, exactly the set G3a
(`rigidContract_rigidity_transport`) delivers (= `V(G.rigidContract H r)` as a set,
`rigidContract_vertexSet_ncard`'s `himg`). So `hrigc` on `V(Gc) = V(G)` is
unsatisfiable for the contraction leg; G3a's output does **not** fit the coupling.

**This is KT's own body-set split, collapsed away by the formalization.** KT eq.
(6.3)'s second block is `R(G,p; E∖E′, V∖V′)` — parent restricted to surviving edges
*and* surviving **bodies** `V∖V′`; the rank bookkeeping is
`D(|V′|−1) [block] + D(|V∖V′ ∪ {v∗}|−1) − k [contraction] = D(|V|−1)−k` (§3 Track A,
line ~605), a sum over **two distinct body sets**. The honest base glue
`isInfinitesimallyRigidOn_of_splice` (`:1550`) faithfully takes arbitrary `sH`,
`sc` (`c ∈ sH`, `c ∈ sc`, `V(G) ⊆ sH ∪ sc`) — but the *coupling/rank-polynomial
producers* layered on top specialized `sc := V(Gc)` (sound for the all-of-`V` legs
the earlier nodes consumed, e.g. N6a's `withGraph` legs and the simple
non-contraction couplings). G3a is the first consumer whose leg is rigid on a
**proper subset** of `V(Gc)`, which is what exposes the collapse.

**Decision: G3c needs a body-set-relative coupling first; the `buildable` framing
was over-optimistic. Cut into G3c-i / G3c-ii / G3c-iii.** Two genuinely-new bricks
(not assembly), then the assembly:
- **G3c-i — body-set-relative rank polynomial + N7b-0.** Generalize
  `exists_rankPolynomial_of_rigidOn_linking` (and its N7b-0 dependency
  `exists_independent_panelRow_subfamily_of_rigidOn_linking` +
  `finrank_infinitesimalMotions_of_isInfinitesimallyRigidOn_vertexSet`) from rigidity
  on `V(G)`/count `D(|V(G)|−1)` to rigidity on an arbitrary body set `s ⊆ V(G)` /
  count `D(|s|−1)`. **research-shaped** — the relative-count split (N1/N3,
  `finrank_pinnedMotionsOn_vertexSet`) is stated against the *graph's* vertex set;
  pushing it to a sub-body-set re-opens the relative-screw-split arithmetic. Math-first
  before any dispatch; green-modulo `h…`-deferral eligible if it stalls.
- **G3c-ii — body-set-relative coupling.** A `couple_ofNormals` variant threading
  per-leg body sets `sH`, `sc` (`c ∈ sH`, `c ∈ sc`, `V(G) ⊆ sH ∪ sc`) through the
  witness-transfer (steps (i)–(v)) and finishing on the base glue
  `isInfinitesimallyRigidOn_of_splice` at the shared seed `q₀` directly (the legs
  rigid on `sH`/`sc`, not `V(GH)`/`V(Gc)`). `buildable` once G3c-i is green.
- **G3c-iii — the assembly + flip** (the original G3c). Dispatch on `G.Simple`;
  simple branch feeds the `H`-leg IH (on `sH := V(H)`) and the G3a-transported
  contraction leg (on `sc := (V(G)∖V(H)) ∪ {r}`) into the G3c-ii body-set coupling.
  `buildable` once G3c-i/ii land.

**Net.** The §1.7 recon dissolved the *graph-level* `Gc ≤ G` mismatch (leg is
`G ＼ E(H)`) and relocated the analytic content to G3a (Claim 6.4, green-modulo).
This recon finds a *second*, orthogonal mismatch the §1.7 framing missed: the
**body-set** mismatch (`V(Gc) = V(G)` vs. the contraction's `V∖V′ ∪ {v∗}`), which
makes G3c a multi-brick build, not assembly. The honest base glue already supports
arbitrary body sets; the work is lifting the *witness-transfer producers* (rank
polynomial + coupling) off the hardcoded `V(·)` to a per-leg body set — KT's own
`V∖V′` restriction, collapsed away in the earlier (all-of-`V`-leg) nodes.

### 1.9 G3c-ii re-recon — the body-set N3 consumer needs the complement-isolation equality; route (a) (carry it as `h…`), buildable, mirrors `isInfinitesimallyRigidOn_vertexSet_of_finrank_le` (2026-06-05)

G3c-i landed the four body-set *producer* bricks GREEN (rank polynomial + N7b-0,
on a nonempty body set `s`, count `D(|s|−1)`). The G3c-i finding flagged the
**body-set N3 *consumer*** — re-derive "rigid on `s`" from the row count — as the
genuinely-stuck half, since the N1 *equality* `finrank (pinnedMotionsOn s) = D·|sᶜ|`
is false for `s ⊊ V(G)`. The G3c-ii hand-off offered two routes: **(a)** carry the
leg-specific complement-isolation equality as an honest `h…` (green-modulo), or
**(b)** thread each leg's rigidity straight into the base glue, avoiding the
rank-polynomial round-trip and its N3 re-derivation. **This recon (no Lean edits;
decision-support like §1.4–§1.8) settles it as route (a), and confirms it is
*buildable*, not green-modulo on new analytic content.**

**Why route (b) does not actually avoid the obstruction.** The base glue
`isInfinitesimallyRigidOn_of_splice` needs each leg rigid on its body set `sH`/`sc`
*at the shared seed `q₀`*. The shared seed is found by intersecting the two legs'
rank-polynomial non-root loci (the only mechanism that produces a *common* point).
But each leg's rigidity is supplied at the leg's *own* seed `qH`/`qc` (the form G3a
/ the `H`-leg IH deliver), a *different* point from `q₀`. So a transport from the
own-seed to `q₀` is unavoidable, and the only generic-transport tool in the layer is
the rank polynomial: independence (the row count) is the Zariski-open condition that
transfers across non-roots, *rigidity on `s` is not*. Route (b)'s "feed rigidity
directly" therefore cannot reach `q₀`; it would only re-derive rigidity at the
own-seed, which the splice cannot consume (the two own-seeds differ). The
round-trip is structural, not incidental — so the body-set N3 consumer is required
either way, and it needs the N1 equality.

**Route (a) is buildable and exactly parallels the green N3-on-`V(G)`.** The
all-of-`V(G)` consumer `isInfinitesimallyRigidOn_ofNormals_of_rankPolynomial_ne_zero_linking`
ends by calling N3 `isInfinitesimallyRigidOn_vertexSet_of_finrank_le`, whose proof
is: pick `v₀ ∈ V(G)`, read rigidity off the Case-I bridge
`isInfinitesimallyRigidOn_iff_pinnedMotionsOn_le` at the singleton block `{v₀}`,
reduce to `pinnedMotionsOn s ≤ pinnedMotionsOn {v₀}` (the reverse is `pinnedMotionsOn_mono`),
and match dimensions via `finrank_pinnedMotions_add_screwDim v₀`
(`finrank (pinnedMotionsOn {v₀}) = dim Z − D`) ≤ `D·|sᶜ|` =
`finrank (pinnedMotionsOn s)` — the last `=` being **exactly the N1 equality**. For a
body set `s`, that single rewrite is the only thing missing; supplying it as the
hypothesis `hpin : finrank (pinnedMotionsOn s) = D·|sᶜ|` makes the body-set N3
`isInfinitesimallyRigidOn_of_finrank_le_set` close *verbatim* (`v₀ ∈ s`, the count
`dim Z ≤ D·(|sᶜ|+1)` from the body-set N7b-0 producer, `omega`). The body-set
consumer `isInfinitesimallyRigidOn_ofNormals_of_rankPolynomial_ne_zero_linking_set`
is then the leg-restricted-linking variant carrying `hpin`, and the body-set
coupling `couple_ofNormals_set` threads `sH`/`sc` + the two `hpin`s + `hnesH`/`hnesc`
through the same (i)–(v) witness-transfer, finishing on `isInfinitesimallyRigidOn_of_splice`.

**Honesty status.** `hpin` is *not* a new analytic black box like G3a's `htransport`
(KT Claim 6.4): it is a green *consequence* of the leg being a body-set-isolated
realization, the body-set sibling of the green `finrank_pinnedMotionsOn_vertexSet`,
and it is **discharged at the call site** by the composer (G3c-iii) for each concrete
leg — `sH := V(H)` is the leg's *full* vertex set so `hpin` is literally the green
`finrank_pinnedMotionsOn_vertexSet` (on `withGraph H`); `sc := (V(G)∖V(H)) ∪ {r}` is
the contraction leg's full effective body set, where the interior `V(H)∖{r}` is
isolated in `G ＼ E(H)` so its complement bodies are free — the same N1-equality
proof. So route (a) is a body-set *generalization* that stays green once G3c-iii
supplies the leg-specific isolation; it carries `hpin` as a hypothesis only to keep
G3c-ii leg-agnostic (the coupling does not know which `s` it is handed). This is
*buildable*, the §1.8 tag, not a green-modulo escalation. **Build order:** the
body-set N3 `isInfinitesimallyRigidOn_of_finrank_le_set` → the body-set consumer
`…_rankPolynomial_ne_zero_linking_set` → the body-set coupling `couple_ofNormals_set`.

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
| **Claim 6.4 collapse transport (G3a)** | `PanelHingeFramework.rigidContract_rigidity_transport` | **GREEN-MODULO** (2026-06-05; carries KT Claim 6.4 / eq. (6.9) as the explicit hypothesis `htransport` — the rank-transport across the collapse map, irreducible because the relabel changes the surviving-edge normals; axiom-clean, no `sorry`) | Case I composer (the contraction leg) |
| **`prop:rigidity-matrix-prop11` `hub`** | carried as hypothesis (`:2527`) | RED (multi-commit, Phase-19 partition count) | Prop 1.1 only |

**Reading:** the entire device + witness-transfer + splice + count + N4
substrate is GREEN; **(G2) is now GREEN too** (2026-06-04,
`exists_generalPosition_polynomial`). The Case-I substrate is now also complete:
the **Case-I Claim-6.4 collapse transport** (G3a, `rigidContract_rigidity_transport`)
landed **GREEN-MODULO** 2026-06-05, carrying KT eq. (6.9) as the explicit
hypothesis `htransport` (the relabel-induced normal change makes it irreducible — the
linking-edge lever fails). So the one remaining *missing* analytic brick across the
layer is now **one**: the **Case-III missing row** via Lemma 2.1 (Track B, 22b+).
The N6b/N6c couplings are an assembly of green bricks *given both legs as `≤ G` rigid
`ofNormals`*; G3a supplies the second such leg (modulo `htransport` = KT Claim 6.4,
which itself re-enters via `lem:case-III` / 22b+). (G1) was not a missing brick — it
was the motive decision of §1, dissolved by the two-motive split.

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
  into the hybrid N6-G1/G2/G3; N6-G1/G2 (G2a/G2b/G2c) now GREEN.** Not `buildable`
  as a single commit: the composer's adapter needs each leg in
  `HasGenericFullRankRealization`, which (i) the coupling did not produce — **fixed
  by N6-G1, GREEN** — and (ii) `minimal_kdof_reduction` does not thread (N6-G2,
  Route 1, re-reconned in §1.6 into G2a/G2b/G2c, **all GREEN**). **Remaining: N6-G3's
  G3b/G3c** (re-reconned in §1.7 into G3a/G3b/G3c; **G3a now GREEN-MODULO**, 2026-06-05).
  The composer is NOT pure leg-data geometry: the contraction leg's rigidity is
  transported across the collapse map by G3a `rigidContract_rigidity_transport` (KT
  Claim 6.4, carried as the explicit hypothesis `htransport` — green-modulo, axiom-
  clean); then the cover/simplicity geometry (G3b, buildable) and the assembly/flip
  (G3c, buildable). See §1.7 + `notes/Phase22a.md`.

**Build order (Track A), updated 2026-06-05 (G3a green-modulo; G3b is the next build):**
§1 motive decision ✓ → N6a ✓ → (G2) ✓ → N6b/N6c coupling ✓ → **N6 composer
(§1.5 hybrid, §1.6 N6-G2 cut, §1.7 N6-G3 cut): N6-G1 ✓ → G2a ✓ → G2b ✓ → G2c ✓ →
N6-G3 (G3a ✓ green-modulo → G3b → G3c).**

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
