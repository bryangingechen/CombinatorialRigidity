# Phase 22 — realization-layer design (decision-support doc)

> **File-layout note (pre-Phase-22b structure pass, `notes/Phase22-structure.md`).**
> The single files this doc cites have since been split into subdirectories:
> `AlgebraicInduction.lean` → `Molecular/AlgebraicInduction/`
> (`PanelLayer`/`Pinning`/`PanelHinge`/`GenericityDevice`/`CaseI`) and `Induction.lean` →
> `Molecular/Induction/` (`Operations`/`SplitOffDeficiency`/`ReducibleVertex`/`Contraction`/`ForestSurgery`).
> Inline `….lean:NNNN` line anchors below **predate the split** — find declarations by name in
> the relevant sub-file (the Case-I composer `case_I_realization` and the couple / genericity-device
> producers are in `CaseI` / `GenericityDevice`; `minimal_kdof_reduction` is in `Induction/ForestSurgery`).

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
placement side as KT's Claim 6.4 transport) and cutting N6-G3 into G3a/G3b/G3c;
§**1.8**–§**1.9** (2026-06-05) re-recon G3c (the body-set mismatch; route (a)),
all green; §**1.10** (2026-06-05) lands G3c-iii's GP-conjunct producer bricks and
cuts the residual assembly into G3c-iii-a/b; §**1.11** (2026-06-05) is the
**G3c-iii-a parent-`ends` impedance recon**, settling it as **option (iii)** (the
producers need only an *edge-restricted* `hends`, supplied by a small
`ends`-existence side-lemma — verified buildable) and unblocking G3c-iii-b; §**1.12**
(2026-06-05, coordinator verification pass) is the **G3c-iii-b correctness gap**: the
composer `case_I_realization` (commit c1ef55a) carries a FALSE combinatorial equality
`hpinc` in its "Claim-6.4 bundle" (the contraction leg's complement-isolation is
generically unsatisfiable), making the theorem valid-but-vacuous — §1.12 diagnoses it,
**corrects the §1.9 premise**, and decides the fix (route (b)-corrected: an asymmetric
coupling that removes the contraction leg's rank-polynomial round-trip, so `hpinc`
never arises). The live to-do is the FIX (`notes/Phase22a.md` *Hand-off*). No Lean /
`\leanok` / blueprint edits accompany this doc.

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

**Honesty status — PARTLY WRONG, corrected in §1.12 (2026-06-05).** This paragraph claimed `hpin`
is *not* a new analytic black box but a green *consequence* of the leg being body-set-isolated, and
that the claim holds for **both** call-site legs. The `sH := V(H)` half is **correct** (`hpin` is
literally the green `finrank_pinnedMotionsOn_vertexSet` on the `H`-leg's *full* vertex set). The
`sc := (V(G)∖V(H)) ∪ {r}` half — "the interior `V(H)∖{r}` is isolated in `G ＼ E(H)` so its
complement bodies are free — the same N1-equality proof" — is **FALSE**: the interior bodies are
*not* isolated (surviving boundary edges `δ_G(V(H))` constrain them), so the contraction-leg `hpin`
(= `hpinc`) is generically *unsatisfiable*, the N1 equality genuinely fails off `V(G)`
(`finrank_pinnedMotionsOn_le` proves only the *upper* bound, by design), and the resulting composer
`case_I_realization` (commit c1ef55a) is valid-but-VACUOUS. The deeper error: the contraction leg's
**rank-polynomial round-trip** (which is what forces `hpin` via the body-set N3) must be *removed*
for that leg, not satisfied — the contraction rigidity should be fed to the splice glue directly
from the Claim-6.4 bundle (route (b)-corrected, the asymmetric coupling). Full diagnosis, witness,
KT cross-check, and the corrected fix: **§1.12**. The `sH`-leg round-trip below stays green; the
`sc`-leg one does not.

The (now-superseded for the `sc` leg) build order was: the body-set N3
`isInfinitesimallyRigidOn_of_finrank_le_set` → the body-set consumer
`…_rankPolynomial_ne_zero_linking_set` → the body-set coupling `couple_ofNormals_set`.

### 1.10 G3c-iii re-recon — the GP conjunct needs a body-set *generic* coupling (built); the residual assembly faces the parent-`ends` impedance + Claim-6.4 bundling, not pure green-brick assembly (2026-06-05)

G3c-ii landed the *bare* body-set coupling `hasFullRankRealization_of_couple_ofNormals_set`. The
G3c-iii hand-off framed the remainder as "feed the `H`-leg IH + the G3a-transported contraction leg
into that coupling, then `hasFullRankRealization_of_generic` for the bare `hcontract`" — but that
path discharges **only** the bare `hcontract`. The conditioned-motive reduction `theorem_55_generic`
*also* needs `hcontractGP`, whose conclusion is `HasGenericFullRankRealization k G` off the *same*
body-set legs (the contraction leg rigid only on `sc = (V(G)∖V(H)) ∪ {r}`). **No body-set *generic*
coupling/splice existed:** N6-G1 (`hasGenericFullRankRealization_of_splice_ofNormals`) and G2c
(`hasGenericFullRankRealization_of_couple_ofNormals`) both hardcode each leg rigid on its *full*
`V(·)`. So G3c-ii's "buildable assembly" tag was again incomplete on the GP half.

**Landed this commit (the two missing producer bricks, GREEN, axiom-clean):**
`hasGenericFullRankRealization_of_splice_set_ofNormals` (the body-set generic splice — realize at the
GP seed `q₀` itself, rigidity on `V(G)` from the genericity-free body-set glue, GP from `hgp`; the
common generalization of N6-G1 + G3c-ii's bare body-set splice) and
`hasGenericFullRankRealization_of_couple_ofNormals_set` (the body-set generic coupling — the G2c
witness-transfer (i)–(v) threaded through per-leg body sets `sH`/`sc` + the two `hpin`s, finishing on
the body-set generic splice). These are the GP-conjunct producers the simple Case-I composer feeds.

**Residual obstruction the assembly still faces (the `ends` impedance + Claim-6.4 bundling).** The
composer must build the `hcontractGP`/`hcontract`-shaped *producers* `theorem_55_generic` consumes.
Two unsurfaced obstructions remain, neither pure assembly:

1. **Parent-`ends` impedance.** Every producer above the base glue takes `ends : β → α × α` with
   `hends : ∀ e : β, G.IsLink e (ends e).1 (ends e).2` — quantified over *all* of `β`, the layer's
   standing convention that the label type *is* the edge type. But `theorem_55`/`theorem_55_generic`'s
   premises are stated on the *ends-free* motive `HasFullRankRealization k G` (the framework `Q`
   carries its own `Q.ends`); the parent `ends` the producers need is **not** supplied by the premise
   shape, and is not constructible from `G.Simple` alone for an arbitrary `β` (a non-edge `e₀ : β`
   makes `hends` unsatisfiable). This is *not* G3c-specific — it would block every Case-I/II/III
   producer from discharging a `theorem_55` premise. Resolving it is a motive/`ends`-convention
   question at the `minimal_kdof_reduction` boundary (e.g. carry `ends` in the motive, or restrict the
   development to `β = E(G)`), a recon-level decision, *not* a leaf assembly.
2. **Contraction-leg Claim-6.4 bundling.** G3a's `rigidContract_rigidity_transport` gives the
   contraction leg's *rigidity* on `sc` at a seed `q_c`, but the coupling also needs *transversality*
   `hnec` at `q_c` and the parent selector alignment; both are downstream of the same KT Claim 6.4
   (eq. 6.9) collapse-transport G3a carries as `htransport`. The composer must bundle the full
   contraction-leg-at-parent-selector data as the green-modulo hypothesis, and the producer-scrutiny
   honesty gate (`blueprint/CLAUDE.md`) forbids smuggling the deliverable — so the bundle must be the
   *minimal* Claim-6.4 content, not the whole conclusion.

**Decision: G3c-iii's two GP-conjunct producer bricks land now (this commit); the residual assembly is
re-cut into G3c-iii-a (the parent-`ends` impedance recon/resolution) + G3c-iii-b (the composer
assembly + flip, once `ends` is resolved and the Claim-6.4 bundle is fixed).** The honest move when a
"buildable" node reveals an unsurfaced structural obstruction is a docs-only re-cut, not forcing a
half-baked composer (DESIGN.md *Constructibility recon … → Scale-up*). The two bricks are real,
verified, axiom-clean additions strictly required by the GP conjunct, so they move work forward
independently of the `ends` resolution.

---

### 1.11 G3c-iii-a re-recon — the parent-`ends` impedance dissolves: the producers need only an *edge-restricted* `hends`, which is constructible from `G` alone; resolution is option (iii), verified buildable (2026-06-05)

§1.10 flagged the **parent-`ends` impedance** as the first of the two residual G3c-iii obstructions
and labelled it a layer-wide motive/`ends`-convention recon. This section is that recon. **No Lean /
`\leanok` / blueprint edits accompany it; it is decision-support**, like §1.4–§1.10. Verified against
the live signatures (`AlgebraicInduction.lean` `theorem_55:2843`, `theorem_55_generic:2899`,
`HasFullRankRealization:2780`, the body-set generic coupling
`hasGenericFullRankRealization_of_couple_ofNormals_set:5022`, the linking-set rank polynomial
`exists_rankPolynomial_of_rigidOn_linking_set:4242`; `Induction.lean` `minimal_kdof_reduction:3594`)
and a scratch build of the `ends`-existence construction (compiled green, then removed — this is a
recon commit).

**The impedance, precisely.** Every producer above the base glue takes an *external* endpoint
selector `ends : β → α × α`. The `theorem_55`/`theorem_55_generic` premises (`hcontract`,
`hcontractGP`) conclude the **ends-free** motive `HasFullRankRealization k G` /
`HasGenericFullRankRealization k G` — the realizing framework `Q` carries its own `Q.ends` inside the
existential, but the *parent* `ends` the producers need is not in the premise shape. So the composer
must *manufacture* a parent `ends` from the available data (`G`, `G.Simple`, `G.IsMinimalKDof n 0`).
§1.10 worried `hends : ∀ e : β, G.IsLink e (ends e).1 (ends e).2` (link of **every** `β`-label) is
unsatisfiable, because `hfresh : ∀ G', ∃ e₀, e₀ ∉ E(G')` (the reduction's standing freshness supply)
*guarantees* `β` carries non-edges, and `G.IsLink e₀ x y` is false for a non-edge `e₀`.

**Option (ii) ("restrict to `β = E(G)`") is ruled out at the source.** `minimal_kdof_reduction`
(`Induction.lean:3594`) runs over a **fixed** `β`: the parent `G`, the splitting-off child
`G.splitOff v a b e₀`, and the contraction IH's `G'` all live in `Graph α β` for the *same* `β`, and
`splitOff` consumes a *fresh* label `e₀ : β` drawn from `hfresh`. So `β` is intrinsically a label
*supply* with spare labels — it cannot be the edge type. (i) carrying `ends` in the motive would
re-type `HasFullRankRealization`/`HasGenericFullRankRealization` and all of `theorem_55`/`_generic`
across the whole layer — heavy, and unnecessary (see next).

**The impedance dissolves: the producers never actually need the all-`β` `hends`.** Tracing the
*body-set* producers the composer feeds (not the all-edges `exists_good_realization_ofParam`, which a
proper-subgraph leg never calls): the body-set generic coupling
`hasGenericFullRankRealization_of_couple_ofNormals_set:5022` uses its `hends` argument in **exactly
two places** (lines 5045–5048), both to derive the **edge-restricted** form
`hendsH/hendsc : ∀ e u v, G·.IsLink e u v → G·.IsLink e (ends e).1 (ends e).2` via
`Graph.IsSubgraph.isLink_iff`; everything downstream
(`exists_rankPolynomial_of_rigidOn_linking_set:4242`, the consumer
`isInfinitesimallyRigidOn_ofNormals_of_rankPolynomial_ne_zero_linking_set:4464`,
`exists_generalPosition_polynomial`) takes only the edge-restricted `hends` or the witnessed-index
`hsupp` — *never* the all-`β` form. This is the layer's documented deliberate weakening (the
infra comment at `:688`–`:701`: "the all-edges form's `hends` is weakened to … a link of every
*linking* edge … the form a proper-subgraph leg supplies"). So the all-`β` `hends` in the coupling's
signature is a needless over-strengthening.

**The keystone: an edge-restricted parent `ends` IS constructible from `G` alone** (verified by a
scratch build, compiled green): for `[Nonempty α]`,
```lean
fun e => if h : e ∈ E(G) then ⟨(G.exists_isLink_of_mem_edgeSet h).choose, …⟩
         else ⟨Classical.arbitrary α, Classical.arbitrary α⟩
```
links every edge (`exists_isLink_of_mem_edgeSet` supplies the witness pair per edge; non-edges take a
default) and so satisfies `∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2`. `[Nonempty α]`
holds whenever `2 ≤ |V(G)|` (the reduction's hypothesis), so it is free at the call site.

**Decision: option (iii), in its sharpest form — relax the producers' parent `hends` to
edge-restricted and supply `ends` by a small side-lemma.** Two coordinated G3c-iii-b pieces, both
buildable:
1. **`exists_ends_of_graph`** (working name; project-internal, `AlgebraicInduction.lean`): from
   `[Nonempty α]` (or `2 ≤ |V(G)|`) produce `⟨ends, hends_edge⟩` with the edge-restricted property.
   The scratch above is the proof. (Friction-eligible if `exists_isLink_of_mem_edgeSet.choose`
   plumbing is awkward; it was not in the scratch.)
2. **Relax the body-set generic coupling's parent `hends`** from `∀ e, G.IsLink e (ends e).1
   (ends e).2` to the edge-restricted `∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2`
   (the bare body-set coupling `hasFullRankRealization_of_couple_ofNormals_set` too, for parity). The
   body's only two uses (lines 5045–5048) already *produce* the edge-restricted form — relaxing the
   hypothesis to match deletes the `hends e`/`isLink_iff` step and the proof is unchanged otherwise.

**Net.** The G3c-iii-a impedance is **not** the layer-wide motive re-typing §1.10 feared — it is a
one-lemma + one-signature-relaxation fix, settled by reading the producers' *actual* `hends` usage
(the recurring *quantifier-domain* sharpening of the recon rule, DESIGN.md *Constructibility recon
…*). It is resolved once and unblocks every Case-I/II/III producer's `theorem_55`-premise discharge,
exactly as §1.10 predicted ("resolved once for the whole layer"). G3c-iii-b is now pure (verified)
assembly modulo the Claim-6.4 bundle (`htransport` + the transversality `hnec` at `q_c`, G3a's
green-modulo obligation = KT eq. (6.9)).

> **§1.9 premise CORRECTED — see §1.12.** The "Honesty status" paragraph of §1.9 (and the
> parallel claim in §1.10/§1.11 that the residual is "pure assembly modulo the Claim-6.4 bundle")
> asserted that `hpinc`, the contraction leg's complement-isolation **equality**
> `finrank (pinnedMotionsOn sc) = D·|scᶜ|` for `sc = (V(G)∖V(H)) ∪ {r}`, is a *green consequence*
> ("the interior `V(H)∖{r}` is isolated in `G ＼ E(H)` so its complement bodies are free — the same
> N1-equality proof"). **That premise is FALSE** (the interior bodies are *not* isolated in
> `G ＼ E(H)` — surviving boundary edges constrain them), so `hpinc` is generically *unsatisfiable*
> and `case_I_realization` (commit c1ef55a) is valid-but-vacuous. The diagnosis, the witness, the
> KT cross-check, and the corrected fix are §1.12.

---

### 1.12 G3c-iii-b correctness gap — the contraction leg's complement-isolation `hpinc` is a FALSE combinatorial equality, not Claim 6.4; the round-trip itself must be removed for that leg (2026-06-05, coordinator verification pass)

> **✓ FIX LANDED (2026-06-05).** The route-(b)-corrected fix decided below is now in the tree: the
> asymmetric coupling `hasGenericFullRankRealization_of_couple_asymm_ofNormals_set`
> (`AlgebraicInduction.lean`) runs only the `H`-leg through the rank-polynomial round-trip and feeds
> the contraction leg's rigidity directly from the `∀`-over-GP-seeds conjunct `htransportGP` (KT
> eq. (6.9)). `case_I_realization` re-wired to it; the false `hpinc` (and the now-unneeded `hnec`/
> `∃`-form `htransport`) deleted from `hbundle`; the two false doc-comments corrected. The §1.12 step-1
> open sub-question is settled in favor of the `∀`-over-GP-seeds form. Axiom-clean; build + lint green.

A coordinator verification pass on commit c1ef55a (`case_I_realization`, the G3c-iii-b composer)
found a **correctness gap** in the green-modulo bundle. **No Lean / `\leanok` / blueprint edits
accompany this section; it is decision-support / a Constructibility recon (DESIGN.md), like
§1.4–§1.11.** Verified against the live composer (`AlgebraicInduction.lean` `case_I_realization`,
its `hbundle`), the body-set consumer
(`isInfinitesimallyRigidOn_ofNormals_of_rankPolynomial_ne_zero_linking_set:4464`), the body-set N3
(`isInfinitesimallyRigidOn_of_finrank_le_set:1613`), the body-set N1 upper bound
(`finrank_pinnedMotionsOn_le:1416` + its doc `:1406`), the green
`finrank_pinnedMotionsOn_vertexSet:1348`, `IsProperRigidSubgraph` (`Deficiency.lean:381`), the
generic coupling (`hasGenericFullRankRealization_of_couple_ofNormals_set:5030`), and KT 2011 §6.2
eqs. (6.3)/(6.5)/(6.7)/(6.9) + Claim 6.4 (printed pp. 673–675 = pdf pp. 27–29).

**The bundle is Claim 6.4 ⊕ a FALSE combinatorial fact, not "Claim 6.4 only".** `case_I_realization`
is green-modulo a 5-part bundle `hbundle` (asserted = "the Claim-6.4 bundle"). Four parts are genuine
KT eq. (6.6)/(6.9) content: `hswap`/`hne_ends` (the `H`-leg selector alignment, KT eq. (6.6)
placement), `htransport` (the contraction-leg collapse transport, KT Claim 6.4 / eq. (6.9), the
G3a research-shaped brick), and `hnec` (transversality at the transported seed). The **fifth part
`hpinc` is NOT Claim 6.4**:
```
∀ q, finrank ℝ ((ofNormals (G ＼ E(H)) ends q).toBodyHinge.pinnedMotionsOn ((V(G)∖V(H)) ∪ {r}))
       = screwDim k * ((V(G)∖V(H)) ∪ {r})ᶜ.ncard.
```
It is **placement-independent** (`∀ q` — it holds for *every* normal assignment, or none) and a pure
**graph-combinatorial dimension equality**. Claim 6.4 is a statement about a *transported placement's*
rank (`rank R(G/E′, p_{E∖E′}) ≥ rank R(G/E′, p2)`, eq. (6.9), at a *specific generic* placement); it
**cannot** discharge a `∀ q` equality about a body set's pin dimension. So the bundle is not "Claim
6.4 only" — it is Claim 6.4 ⊕ `hpinc`, and `hpinc` is a separate (false) obligation no analytic
content can supply.

**`hpinc` is generically FALSE.** The equality holds iff the interior bodies `V(H)∖{r}` are *isolated*
in `G ＼ E(H)` (each contributing its full `D = screwDim k` free screws to the pin). They generically
are **not**: a boundary edge of `δ_G(V(H))` (interior body → exterior body) is not in `E(H)`, so it
*survives* `deleteEdges E(H)` and constrains the interior body it touches.
- **Code confirms the equality is false off `V(G)`.** `finrank_pinnedMotionsOn_le:1416` (and its doc,
  `:1406`–`:1415`) state outright: the N1 **equality** `= D·|sᶜ|` holds *only* for `s = V(G)` (where
  the `sᶜ` bodies are genuinely isolated); "for a general `s ⊆ V(G)` the bodies of `V(G) ∖ s` carry
  hinge constraints, so the pin is *smaller* than the free `D·|sᶜ|` — hence the upper bound."
  `pinnedMotionsOn_le_iInf_ker_proj:1394` says the same ("a body in `V(G) ∖ s` still carries hinge
  constraints, so the motion condition is *not* free off `s`"). The producer (body-set N7b-0) needs
  only the upper bound; the *consumer* needs the equality, which is exactly the false half.
- **Witness (D ≥ 3, the molecular regime).** Take `V(G) = {a, b, c, w}`, `H` rigid on `V(H) = {a, b}`,
  `r = a` (so interior `V(H)∖{r} = {b}`), and a boundary edge `e_bd` linking `b`–`w` (not in `E(H)`,
  so it survives `deleteEdges E(H)`). Then `sc = (V(G)∖V(H))∪{r} = {a, c, w}`, and the only complement
  body in `V(G)` is `b`. For `hpinc`, `b` must be *free* (contribute `D`). But `e_bd` is a surviving
  hinge coupling `b` to the pinned `w`, which removes `D−1` of `b`'s relative screw freedoms, leaving
  at most `1`. So `finrank (pinnedMotionsOn sc) ≤ D·(|scᶜ|−1) + 1 < D·|scᶜ|` whenever `D ≥ 2`
  (here `D ≥ 3` by `hD`). The gap is `D−1 ≥ 2`. `hpinc` is false; with `hbundle` unsatisfiable,
  `case_I_realization` is valid-but-VACUOUS.
- **`IsProperRigidSubgraph` does not save it.** `Deficiency.lean:381` is `H ≤ G ∧ H.IsKDof n 0 ∧
  V(H).Nonempty ∧ V(H) ⊂ V(G)` — no constraint forcing `δ_G(V(H))` through `r`. Generic `G` has
  interior-incident boundary edges.

**Root cause (KT cross-check, eqs. (6.3)/(6.5)/(6.7)/(6.9)).** KT's contraction-block rank
bookkeeping lives on the **COLLAPSED** graph `G/E′ = ((V∖V′)∪{v∗}, E∖E′)` — where the interior `V′`
*is gone*, replaced by the single body `v∗`, and there are no interior bodies to be constrained. The
load-bearing step is eq. (6.5)/(6.9): `R(G/E′, p_{E∖E′}; E∖E′, V∖V′)` "is the matrix obtained from
`R(G/E′, p_{E∖E′})` by **deleting the D consecutive columns associated with v∗**", and *deleting those
columns does not change the rank* (`= rank R(G/E′, p_{E∖E′}) ≥ rank R(G/E′, p2)`, Claim 6.4). So the
contraction contributes `rank R(G/E′, p2) = D(|V∖V′∪{v∗}|−1)−k` — a rank statement on the *collapsed*
graph, not a pin-dimension equality on the *un-collapsed* `G ＼ E(H)`. The §1.7 recon correctly moved
the splice's contraction **leg** to `G ＼ E(H)` (to get `≤ G`) and bridged its *rigidity* via Claim 6.4
(G3a, `htransport`). But the §1.9 round-trip then forced that rigidity through the body-set
**rank-polynomial consumer**, which re-derives rigidity-at-the-shared-seed via the body-set N3
(`isInfinitesimallyRigidOn_of_finrank_le_set:1613`), and N3 *needs the N1 equality on `sc`*
(`hpin`, `:1615`, used at `:1628` `Submodule.eq_of_le_of_finrank_le`). On the collapsed graph that
equality is the green `finrank_pinnedMotionsOn_vertexSet`; on the un-collapsed `G ＼ E(H)` it is
`hpinc`, false. **The pin-count does not bridge across the collapse the way the rigidity does** —
that is the precise mistake §1.9 missed.

**Fix-direction evaluation.** Two candidates from the hand-off, plus a third I find decisive:

- **(a) Route the contraction count through the COLLAPSED `G.rigidContract H r`** (where `hpin` IS
  the green `finrank_pinnedMotionsOn_vertexSet`, since the leg is rigid on its *full* vertex set),
  with a Claim-6.4-style count-bridge collapsed → `G ＼ E(H)`. **Rejected: strictly more analytic
  content, and structurally blocked.** The base glue `isInfinitesimallyRigidOn_of_splice:1656`
  requires both legs `≤ F.graph = G`; the collapsed `rigidContract` relabels `V(H)↦r` and is **not**
  `≤ G` (no `rigidContract_le` exists or can — the very obstruction §1.7 dissolved by going to
  `G ＼ E(H)`). So a collapsed leg cannot feed the glue at all; route (a) would need (i) a collapsed
  round-trip producing rigidity-at-`q₀`-on-`V(rigidContract)`, **plus** (ii) a transport of *that*
  back onto `G ＼ E(H)`-rigidity at the *same* `q₀` — and (ii) is Claim 6.4 / eq. (6.9) **again**, on
  top of a second seed-reconciliation. Route (a) adds work, it does not remove `hpinc`'s root cause.

- **(b) Revive route (b): feed the contraction leg's rigidity (from `htransport`) into the splice
  glue directly, without the rank-polynomial round-trip.** This is the correct direction, but **§1.9's
  rejection of it must itself be corrected** (see below). The base glue needs *both* legs rigid at
  *one* common seed; §1.9 argued the only seed-reconciliation tool is the symmetric round-trip, hence
  N3 for both legs, hence `hpinc`. The flaw: the two legs are **not** symmetric. The `H`-leg is rigid
  on its **full** vertex set `sH = V(H)`, so its round-trip uses the *true, green*
  `finrank_pinnedMotionsOn_vertexSet` (`hpinH` is honest — composer line 5223–5229) and is fine. Only
  the **contraction** leg's round-trip needs the false `hpinc`. So the fix is an **asymmetric
  (hybrid) coupling**: the `H`-leg goes through its green round-trip and *produces* the shared seed
  `q₀` (as a non-root of `QH · Qgp`); the contraction leg's rigidity at that `q₀` is then supplied
  **directly** by the Claim-6.4 bundle — *not* re-derived through the body-set N3 consumer. This
  removes `hpinc` entirely (no body-set N3 on `sc`), leaving only the genuine Claim-6.4 content
  (rigidity of the surviving-edge leg at the generic seed) plus transversality.

- **This is exactly what KT does (the decisive cross-check).** KT eq. (6.6) constructs **one**
  placement `p` for all of `G` (it does *not* find a shared point by intersecting two Zariski-open
  rigid loci): `p|E′ = p1` (the block, freely generic — any generic point keeps the rigid block
  rigid), `p|E∖(E′∪δ) = p2`, `p|δ = ΠG/E′,p2 ∩ ΠG′,p1` (boundary, *determined* by `p1`/`p2`). The
  contraction's `p_{E∖E′}` (eq. (6.7)) is then determined, and Claim 6.4 certifies its rank **at that
  one placement**. So the contraction leg's rigidity should be delivered *at the H-leg-determined
  seed*, never re-found by a second round-trip. The honest bundle therefore broadens `htransport`
  from "contraction rigid on `sc` at *some* `q_c`" to a *quantified-over-generic-seed* form
  "contraction rigid on `sc` at the (generic) shared seed" — which is precisely the content of KT's
  algebraic-independence argument (the rank is attained at *generic* placements, eq. (6.9)'s "maximum
  rank over all realizations of `G/E′` determined by (6.7)").

**Decision: route (b), corrected — the asymmetric/hybrid coupling.** The fix is *not* to satisfy
`hpinc` (it is unsatisfiable) but to **remove the contraction leg's rank-polynomial round-trip
entirely**, so `hpinc` never arises. Concretely:

1. **A hybrid body-set coupling** (the new brick): the `H`-leg keeps the green round-trip
   (`exists_rankPolynomial_of_rigidOn_linking_set` + the body-set consumer, with the *honest*
   `hpinH = finrank_pinnedMotionsOn_vertexSet` on `sH = V(H)`), producing the shared seed `q₀`; the
   contraction leg's rigidity at `q₀` on `sc` is taken as a hypothesis (the Claim-6.4 deliverable),
   *not* re-derived via N3. Both `q₀`-rigid legs feed the generic body-set splice
   `hasGenericFullRankRealization_of_splice_set_ofNormals:4990` directly. **No `hpinc`.** This
   replaces `hasGenericFullRankRealization_of_couple_ofNormals_set:5030`'s symmetric (i)–(v)
   witness-transfer with an asymmetric one for the contraction leg.

   *Open Lean-feasibility sub-question (settle at the fix-build's recon):* the H-leg round-trip
   produces `q₀` *inside* the coupling (a non-root of `QH·Qgp`), existentially; the contraction-leg
   hypothesis must therefore be quantified — "contraction rigid on `sc` at **any** `q` with
   `Qgp(q) ≠ 0`" (general position), or "at the produced `q₀`" via a dependent existential. The
   former (a `∀`-over-GP-seeds Claim-6.4 hypothesis, matching KT's "generic placement attains the
   rank") is the cleaner shape; the latter risks the round-trip-ordering tangle. Prefer the
   `∀`-over-GP-seeds form — it is honest (KT eq. (6.9) is a generic statement) and decouples the
   contraction obligation from the H-leg's internal seed search.

2. **The honest `hbundle`.** After the fix, the bundle's contraction part is the *single* Claim-6.4
   conjunct "the surviving-edge leg `G ＼ E(H)` is infinitesimally rigid on `sc = (V(G)∖V(H))∪{r}` at
   every general-position seed" (KT eq. (6.9)) + transversality `hnec`, alongside the `H`-leg's
   `hswap`/`hne_ends` (KT eq. (6.6)). `hpinc` is **deleted**. This makes "green-modulo Claim 6.4"
   *accurate* — the only modulo-content is the one KT-(6.9) transport (already isolated in G3a's
   `htransport`/G3a's brick), with no smuggled false combinatorial fact.

**Cheapness / scope.** Route (b)-corrected is **cheaper than (a)** (one new hybrid coupling brick vs.
two new analytic transports) and **strictly more honest** (it deletes a false hypothesis rather than
carrying it). It **stays within 22a** but requires **re-opening G3c-iii-b** (and adding one brick):
the bare/generic body-set couplings (`…_couple_ofNormals_set`) keep their symmetric form for any
future *both-legs-full-`V`* caller, but Case I needs the new **asymmetric** coupling. The composer
`case_I_realization` re-wires to it and drops `hpinc` from `hbundle`. The body-set N3 + body-set
consumer (G3c-ii) are *not* deleted (the H-leg still uses them on its full `V(H)`, where they are
green); only the contraction leg stops using them.

**Dimension arithmetic (the fix closes).** The base glue's count is unchanged and already correct:
`sH = V(H)` (block, `D(|V(H)|−1)`), `sc = (V(G)∖V(H))∪{r}` (`|sc| = (|V(G)|−|V(H)|)+1`, contraction
`D(|sc|−1)`), sharing body `r`, covering `V(G)`; glued `D(|V(H)|−1) + D(|sc|−1) = D(|V(G)|−1)` since
`|V(H)| + |sc| − 1 = |V(G)|`. (k=0 full rank; this is exactly KT's
`D(|V′|−1) + D(|V∖V′∪{v∗}|−1) − k = D(|V|−1)−k`, eq. after (6.9).) The fix changes *only how the
contraction leg's rigidity-at-`q₀`-on-`sc` is obtained* (Claim-6.4 directly, not N3); the glue
arithmetic that consumes it is untouched, so the fix closes the same count.

**Lean doc-comments the fix commit must correct (do NOT edit in the docs-only recon commit).**
- `case_I_realization`'s narration (`AlgebraicInduction.lean` ~:5119–5132) calls `hpinc` "the body-set
  complement-isolation … part of the same Claim-6.4 bundle" — it is *not* Claim 6.4 and is false; the
  narration must drop `hpinc` and state the asymmetric coupling.
- The body-set consumer's doc (`:4461`, the
  `isInfinitesimallyRigidOn_ofNormals_of_rankPolynomial_ne_zero_linking_set` block) asserts "for the
  contraction leg the surviving edges isolate the interior bodies" — **the unjustified/false claim**;
  the lemma itself stays (the H-leg uses it correctly on `V(H)`), but the doc's contraction-leg
  example is wrong and must be struck.
- §1.9's "Honesty status" paragraph (this doc) is corrected by the box above + this section.

---

### 1.13 Second coordinator verification — the §1.12 asymmetric fix is ALSO undischargeable; the real divergence is motion-space glue vs KT block-triangular; re-architect (2026-06-05)

The §1.12 fix (commit 561a94b) removed the false `hpinc` via an **asymmetric coupling**
(`hasGenericFullRankRealization_of_couple_asymm_ofNormals_set`): the `H`-leg keeps the
rank-polynomial round-trip and produces the shared seed `q₀`; the contraction leg's
rigidity-on-`sc` at `q₀` is supplied by a single `∀`-over-GP-seeds conjunct
`htransportGP`. A coordinator verification pass (reading the coupling body + the motive
defs) found **`htransportGP` is also undischargeable**, for a parallel reason:

- `q₀` is built (coupling lines 5176–5192) as a non-root of `Q_H · Q_gp` — i.e. it is
  known *only* to be **general-position** (and an `H`-leg rank-poly non-root). Nothing
  constrains `q₀` to the contraction leg's rigid locus.
- So discharging `htransportGP` (`∀` GP `q` ⟹ contraction rigid on `sc`) in 22b
  requires **"GP ⟹ rigid"**. That is **false**: `IsGeneralPosition` is *pairwise*
  normal independence (per-edge transversality, `supportExtensor ≠ 0`), strictly weaker
  than the global full-rank/rigidity condition (a higher-order minor/extensor-span
  condition). **The tell:** the `H`-leg — the same kind of object (simple minimal
  0-dof) — does **not** get rigidity from GP; it runs the rank-polynomial round-trip
  precisely because GP ⊊ rank-generic locus. If GP implied rigidity, the entire
  N5/N7b/rank-poly/N3 machinery would be unnecessary for both legs.
- (Note: option (a) "build `Q_c` as a direct rigidity-witnessing minor" does **not**
  rescue it either — rigid-on-`sc` is *null-space-shaped*; turning a row-independence
  polynomial non-root into rigid-on-`sc` routes through the body-set N3 consumer, which
  needs the same false equality. The deep design pass's (c1) recommendation hit this
  wall, which is why it too is rejected.)

So `hcrig` → `hpinc` → `htransportGP` is one unsatisfiability **relocated three times**,
never removed. **The genuine root cause** (sibling-promoted to `DESIGN.md` *Match the
source's argument structure, not just its conclusion*): Phase 21b translated KT's
**block-triangular rank-addition** (eq. 6.3 — `rank R(G,p) = rank R(G′,p₁) + rank
R(G,p;E∖E′,V∖V′)`, each block realized at its *own* leg-wise generic placement, ranks
add by block-triangularity) into the project's motion-space **"overlapping rigid pieces
glue"** `isInfinitesimallyRigidOn_of_splice` (one framework `F` rigid on both `s_H` and
`s_c` ⟹ rigid on the union). The glue intersects one framework's motions, so it demands
a **single common placement on which both legs are simultaneously rigid** — which KT's
block-triangular structure never needs. With the contraction leg on a **proper** body
set `sc`, finding that common seed is the impasse all three bridges failed to cross.

**Decision (owner-directed, 2026-06-05).** Re-architect the Case-I splice to reproduce
KT's block-triangular rank-addition over leg-wise placements (design-first,
owner-reviewed before any Lean — three automated passes have over-claimed). Audit
molecular phases 17–22 for sibling structural divergences. Lesson captured in
`DESIGN.md` + `blueprint/CLAUDE.md` (honesty-gate third check) + `notes/FRICTION.md`
*[process] Phase 22a — motion-space splice glue vs KT block-triangular*.
`case_I_realization` (561a94b) stays in the tree as a valid-but-vacuous theorem until
the reframing rewrites the composer. The block-triangular reframing design lands as a
new section here once produced.

### 1.14 Block-triangular reframing — design (Stage 2, verified; pending owner sign-off to implement) (2026-06-05)

**The reframe.** Replace the common-seed motion-space splice with KT eq. (6.3)'s
block-triangular rank-addition, routed through the **device** `exists_good_realization`
(which certifies `#s + dim Z(F) ≤ D·|α|` from `#s` *independent rows* of one framework
`F` — `exists_good_realization_const`). Exhibit `D(|V(G)|−1)` independent rigidity rows of
the common framework `F = ofNormals G ends q₀`, split block-wise:
- **`s_H`** : `D(|V(H)|−1)` rows of the rigid-block edges `E(H)` — independent, from the
  `H`-leg's rank polynomial (existing green machinery, at the `H`-leg's own generic
  placement transferred to `q₀` across the Zariski-open non-root locus);
- **`s_c`** : `D(|sc|−1)` rows of the surviving edges `E(G)∖E(H)`, `sc = (V(G)∖V(H))∪{r}`.

The device then bounds `dim Z(F)`, and **N3** (`isInfinitesimallyRigidOn_vertexSet_of_finrank_le`)
converts that to rigid-on-`V(G)` — the motive. **This eliminates the common-seed demand by
construction:** the device needs independent *rows* (counts), never *rigidity of `F` on a
leg at a shared seed*. It also re-aligns Case I with how Cases II/III already feed the
device. (Three-trap check: no common-seed rigidity; no GP⟹rigid; no false pin-equality —
the body-set N3 consumer with its `hpin` equality is never invoked on the contraction leg.)

**Piece B — union-independence of `s_H ⊔ s_c` (the block-triangular core; VERIFIED bounded,
~40–60 lines, scratch-compiled axiom-clean).** Project rows onto the **exterior** columns
`V(G)∖V(H)` via `extProj H : (α → ScrewSpace k) →ₗ (α → ScrewSpace k)`,
`S ↦ fun a => if a ∈ V(H) then 0 else S a` (one `LinearMap.mk`); set `D := (extProj H).dualMap`
(precomposition). Then:
- **`H`-rows vanish under `D`** (fact 2): for `u,v ∈ V(H)`, `hingeRow u v r ∘ extProj H = 0`
  (a 3-line `rw` off the row formula `r ∘ (proj u − proj v)`) — the row-side of KT's
  top-right `0`. So `span s_H ⊆ ker D`.
- Given the residual `hsc_proj_indep` (= `D ∘ s_c` independent), `s_c` is independent
  (`LinearIndependent.of_comp`) and `Disjoint (span s_c) (ker D)` (`Submodule.range_ker_disjoint`),
  whence `Disjoint (span s_H) (span s_c)` and `LinearIndependent.sum_type` closes the union.

  **N.B. the projection is to the EXTERIOR columns `V(G)∖V(H)`, not interior** (the original
  Stage-2-draft sketch said "interior", which is backwards — interior columns are touched by
  surviving boundary edges too, so they don't separate the blocks; exterior columns are where
  the `H`-block vanishes). Lemmas (all mathlib, confirmed to fit):
  `LinearMap.dualMap_apply'`, `LinearIndependent.{of_comp,sum_type}`,
  `Submodule.{range_ker_disjoint,disjoint_def,span_le}`, `LinearMap.mem_ker`. The rows are
  the *same functionals* in `ofNormals G ends q₀` (`panelRow ends i` depends only on `ends`/`q`,
  not the graph — `toBodyHinge_supportExtensor`), so membership transport is `rfl`-style
  (`exists_independent_panelRow_transport`). **Piece B is NOT `h…`-deferrable** — it is the
  block-triangular structure itself, cheap to prove; deferring it would smuggle structure.

**The residual honest Claim 6.4** (the single green-modulo hypothesis, replacing the
undischargeable `htransportGP`): **`hsc_proj_indep` — the `s_c` surviving rows are
independent after the exterior-column projection** `D` (= KT's bottom-right block rank
`rank R(G,p;E∖E′,V∖V′) = D(|sc|−1)`, eq. 6.5/6.9 + Lemma 5.1). This is *single-placement*
(one `q₀`), *contraction-leg-local* (only the surviving edges, only their exterior-projected
rows), and a *row-count* (not a ∀-GP-rigid nor a placement-independent pin-equality), so it
is the genuine, dischargeable KT Claim 6.4 (discharged in 22b via the contraction's generic
IH + algebraic independence). State it as exterior-*projected* independence (`D ∘ s_c`),
**not** full-space independence (which is too weak for the union argument).

**Scope.** Piece B (~40–60 new lines) + the composer rewire (~40–60, swap the asymmetric
coupling for the device-row-addition path, reusing IH extraction / N4 / G3b geometry /
`endsOf` / the existing device closure `hasFullRankRealization_of_independent_panelRow`) +
the count arithmetic (`omega`). Bounded rewrite, no new matrix-rank theory. The symmetric /
asymmetric couplings + the `∃`-form transport stay as (now-unused) library bricks. Outcome:
`case_I_realization` honestly green-modulo `hsc_proj_indep` (Claim 6.4), restoring the
coordinator-close path (blueprint flip green-modulo + a red Claim-6.4 node, à la 21→21b).

### 1.15 Stage 3 — molecular 17–22 KT-divergence audit (clean; reframe corroborated) (2026-06-05)

Audited molecular phases 17–22 for *sibling* structural divergences (a locally-sound green
formalization that re-expresses a KT argument as a different shape, risking a downstream
bridge hypothesis KT lacks). **Result: the Case-I splice (§1.13) is the ONLY structural
divergence; no new blocker.**

- **Cases II/III are SAFE (key positive finding).** Their producer (N7a/N7b-0/1/2/3) already
  feeds the device's **independent-row-counting** closure on a *single* framework, making its
  two row-blocks jointly independent via the pin-a-body Lemma-5.1 **block-triangular column
  split** `linearIndependent_sum_pinned_block` (N7b-3) — i.e. they *already* use KT's block
  structure, no common-seed glue. The §1.14 reframing routes Case I onto this same path, and
  N7b-3 is a near-precedent for Piece B's exterior-column separation. Corroborates the reframe.
- **Clean bills:** Phase 17 (Lemma 2.1 / extensor), 21a (meet — modulo the deferred sign,
  flag below), 19 (def=corank / M(G̃)), 20 (Thm 4.9 reduction; the §1.11 `ends` impedance was
  Lean-plumbing, not structural), 21 (Case-I/II accounting iffs faithfully carry the
  rank-addition as `dim Z` inequalities; Case-naming bug fixed, no residue).
- **Phase 18** motion-space carriage of rigidity is the *enabler* of the Case-I divergence but
  benign on its own (the rank lemmas 5.1–5.3 are faithful rank-nullity equivalents; it only
  bit when used to glue two legs). No change needed; the reframe routes Case I to the row side.
- **Forward flags (outside 22a):** (i) item #2 — when 22b opens, the residual Claim 6.4 must be
  the exterior-projected row-independence `hsc_proj_indep` (§1.14), NOT the motion-space
  `∀`-GP-rigid `htransport(GP)` shape (the undischargeable one); (ii) the deferred
  `complementIso` orientation sign (Phase 21a) — verify before **Phase 25** (projective
  invariance) / 26 in case an *oriented* meet is consumed (recorded in `notes/Phase21a.md`).

### 1.16 The §1.14/Stage-4 residual was over-quantified (∀-GP); the dischargeable form is Qc-non-root (verified) (2026-06-05)

The Stage-4 implementation (f504955) landed the block-triangular structure correctly
(Piece B proven green, exterior projection, device-row-addition — all verified) but stated
the residual `hclaim64`/`hsc_proj_indep` as **`∀ q, GP(q) → surviving D-projected-independent`**.
A coordinator scrutiny found this is the **same over-quantification as `htransportGP`**, disguised
as row-independence: it is strictly stronger than KT Claim 6.4 (which gives the surviving rank
only at the *generic* placement, a Zariski-open locus, NOT at *every* GP seed), and discharging
it needs "GP ⟹ surviving max rank", false. The **tell is in the code**: the coupling builds `q₀`
from `QH · Qgp` and gets the `H`-block independent at `q₀` via the `H`-leg's *rank polynomial* `QH`
(not GP) — yet treats the surviving block as `∀`-GP-independent, an unjustified asymmetry.

**The dischargeable form (verified, the fix target): condition on a surviving rank polynomial
`Qc`-non-root, threaded into the seed via the triple product `QH · Qc · Qgp`** (the pattern the
symmetric coupling already uses):
`∃ Qc ≠ 0, ∀ q, eval q Qc ≠ 0 → ∃ rsc, (links in Gc) ∧ |rsc| ≥ D(|sc|−1) ∧ LinearIndependent (D ∘ panelRow rsc)`.
This reduces **exactly** to KT Claim 6.4 and is dischargeable in 22b:
- It IS eq. (6.9): `D = (extProj V(H)).dualMap` is the restriction to `V∖V′ = V(G)∖V(H)` columns,
  and Claim 6.4 gives the surviving block's `V∖V′`-restricted rank `= D(|sc|−1)` (full exterior
  column rank) at the generic placement.
- Packaging machinery exists (no wall): the existing `exists_rankPolynomial_of_rigidOn_linking_set`
  builds its polynomial via the generic mirror `exists_polynomial_ne_zero_of_linearIndependent_at`
  from full-space rows `panelRow`; the variant feeds `D ∘ panelRow` (a fixed linear map ∘ the rows,
  still polynomially coordinatized) + a witness placement. So 22b = (deferred) Claim 6.4 [∃ one
  placement with full exterior-projected surviving rank, from the contraction IH via algebraic
  independence] + (bounded) the `D∘panelRow` producer variant.
- Avoids all four known traps (false `hpinc`; `∀`-GP-rigid; `∀`-GP-independent; consumer/false-
  equality) and restores leg-symmetry (both legs via rank-poly non-roots).

**Meta-lesson (promoted):** a green-modulo residual quantified `∀` over a *genericity class*
(`∀ GP`) is suspect — condition it on the specific Zariski-open locus the construction actually
lands in (a rank-polynomial non-root, intersected into the shared seed), matching the source's
"at the generic placement" (∃/open locus), NOT "at every general-position placement" (∀). This is
the recurring trap (`htransportGP` → `hclaim64`-∀-GP). See `DESIGN.md` *Match the source's
argument structure …* and `notes/FRICTION.md` *[process] Phase 22a …*.

### 1.17 N-22b-1 re-recon — the rank-transport reduces to a single-placement exterior-projected surviving-row witness; the analytic core is `htransport` (KT eq. 6.9), the brick is plumbing (2026-06-05)

N-22b-2 (the bounded `D∘panelRow` producer `exists_rankPolynomial_of_rigidOn_linking_set_proj`)
landed; the remaining red of Claim 6.4 is N-22b-1, the **rank-transport across the collapse map**.
Per `DESIGN.md` *Constructibility recon … → design the LAYER*, this re-recon (decision-support,
verified vs. the live N-22b-2 signature + the composer's `hclaim64` at `CaseI.lean:1187–1198`)
settles its layer before the build.

**What N-22b-1 must produce, traced through to N-22b-2's hypotheses.** N-22b-2 consumes
`(t, q₀, hsupp, hcount, hindep)` and produces the `Qc`-non-root `∃ Qc …` form of `hclaim64`. So
N-22b-1's job is exactly to supply that tuple from the contraction's generic IH `Q` (graph
`= G.rigidContract H r`, GP, rigid on `V(G.rigidContract H r)`): **one** parent seed `q₀`, a
subfamily `t` of surviving-edge (`G ＼ E(H)`) links with `screwDim k * (|sc|−1) ≤ |t|`
(`sc = (V(G)∖V(H)) ∪ {r}`), whose **exterior-projected** rows
`(extProj V(H)).dualMap ∘ panelRow ends` are independent **at `q₀`**. This is the `∃`-one-placement
core (§1.16, the dischargeable Claim-6.4 form), not a `∀`-quantified one.

**The constructibility check: the analytic core is irreducible (§1.7 corroborated against the
projected form).** The contraction IH is rigidity of the *abstract relabelled* graph
`G.rigidContract H r` at its own seed. No green brick converts that into surviving-row independence
on `G ＼ E(H)` at the un-collapsed endpoints, because `collapseTo r V(H)` redirects each surviving
edge's endpoints, so its support extensor uses *different panel normals* in `rigidContract` vs.
`G ＼ E(H)` — the green linking-edge brick
`infinitesimalMotions_eq_of_isLink_span_supportExtensor` demands a support-extensor span-equality
(`hspan`) that fails, and the Phase-21b genericity device addresses a different obligation (it
certifies a corank off independent rows of *one* framework; it does not bridge the collapse-normal
mismatch). Recovering the surviving rank at the un-collapsed endpoints across the relabel **is** the
algebraic-independence statement of KT Claim 6.4 / eq. (6.9) — irreducibly research-shaped. So the
escalation fires (per §1.7's authorization, the Phase-21b green-modulo `h…` idiom): carry the
**projected-independence-at-`q₀` witness** as the explicit hypothesis `htransport`.

**Decision: N-22b-1 = the first buildable sub-brick `rigidContract_exterior_rank_transport`,
carrying `htransport` (LANDED this commit).** It is the faithful exterior-projected analogue of
G3a's superseded motion-space `rigidContract_rigidity_transport` (§1.7): extract the IH
`⟨Q, hQg, hQgp, hQrig⟩`, forward `htransport`'s `(q₀, t, hsupp, hcount, hindep)` in N-22b-2's exact
shape. Axiom-clean (`propext`/`Classical.choice`/`Quot.sound`), no `sorry`. The brick is the
surrounding plumbing only; the irreducible content is one visible hypothesis pinned to KT eq. (6.9).
N-22b-3 (the one-step wire-up) composes `rigidContract_exterior_rank_transport` (witness `q₀`/`t`) →
`exists_rankPolynomial_of_rigidOn_linking_set_proj` (packaging) to discharge the composer's
`hclaim64` and flip `lem:claim-6-4` / `lem:case-I-realization` fully green.

**Why this is the smallest honest first commit (not the whole transport in one shot).** The only
genuinely-new content is the algebraic-independence rank-attainment, and §1.7 already verified it
admits no green-brick reduction; stating it as the narrow `htransport` hypothesis is the established
green-modulo discharge of the layer's research-shaped step, *not* a deferral of routine assembly
(the surrounding plumbing — IH extraction, witness forwarding — is genuinely the only other content,
and it lands green here). A future pass may discharge `htransport` itself (an abstract
algebraic-independence rank-preservation brick + the collapse-normal bookkeeping), but that is a
separate, deeper undertaking; the brick above is honest and complete as the green-modulo node.

**[Sharpened by §1.18 below (2026-06-05 validation pass).]** The "admits no green-brick
reduction" / "separate, deeper undertaking" framing above **overstates** the irreducibility.
A skeptical re-derivation against KT §5.1+§6.2 and the live code found `htransport` decomposes
into a concrete 5-node plan whose analytic crux *re-instantiates the existing genericity
engine*, with 3 of 5 nodes plumbing or green-reuse. The *deferral* (it does not fit a
few-commit 22b finish) stands; the *irreducibility* is softened. See §1.18.

### 1.18 Validation of the `htransport` deferral + the discharge plan (5-node cut; stays Phase 22b, paused) (2026-06-05)

A skeptical validation pass (coordinator-requested; read-only, vs. KT 2011 §5.1/§6.2 + the live
Lean) re-derived §1.17's deferral rather than rubber-stamping it. **Verdict: the deferral is
correct** — the discharge does not fit a few-commit 22b finish, and the single-placement
`∃`-form of `htransport` is the right, sound target (the `∀`-over-GP forms remain false,
§1.13/§1.16) — **but §1.17's "no green-brick reduction / separate, deeper undertaking" is an
overstatement.** The discharge is a tractable dedicated effort with a concrete node cut; 22b
stays open (◷) and **paused** at the reduction checkpoint, with the cut below as its remaining
work.

**The green-infra route §1.17 under-weighted.** §1.7's two load-bearing claims both hold — the
`hspan` mismatch under `collapseTo` is real (boundary edges share one H-side normal `Qcf.normal r`
in the contraction but get distinct generic H-side normals in `ofNormals (deleteEdges E(H)) ends
q₀`; forcing them equal is KT's degenerate lower-bound member `p2` and destroys the GP the engine
needs), and the Phase-21b device sits *downstream* of the gap (it consumes the independent witness
`hindep`, it does not produce it). There is also no analytic `rigidContract`/`map`/`collapseTo`
rigidity-transport in the tree (the only `rigidContract` bridges — `rigidContract_isMinimalKDof`,
`mulTilde_rigidContract` in `Induction/` — are matroidal: minimal-`k`-dof-ness, not matrix rank).
**But** the rigidity→independent-row extraction `htransport`'s *conclusion* needs already exists
green: `BodyHingeFramework.exists_independent_panelRow_subfamily_of_rigidOn_linking_set`
(`GenericityDevice.lean`) — for the *same* framework. So the missing content is *one* analytic
brick (the collapse-map rank transport, KT's family-embedding argument) + bookkeeping, not the
whole obligation.

**KT's actual argument** (Claim 6.4, p. 675 = pdf p. 28, inside Lemma 6.3; grounded on §5.1, p. 668
= pdf p. 21, footnote 4 — verified against `.refs/katoh-tanigawa-2011-…pdf`). Generic-attains-max-
over-a-realization-family: (1) every `R(G,p)` entry is a polynomial in the panel coefficients, so
`rank` is lower-semicontinuous and maximal at coefficients algebraically independent over ℚ; (2)
the body-hinge realization `(G/E′, p_{E∖E′})` (eq. 6.7) gives each boundary edge a *separate*
H-side panel per original endpoint, so the family (6.7) is *larger* than the panel-hinge
realizations, and the canonical collapsed realization `p2` (all H-side panels forced equal to the
`v∗` panel) is one degenerate member; (3) since the generic member attains max rank ≥ the special
member `p2`, `rank R(G,p; E∖E′, V∖V′) ≥ rank R(G/E′, p2) = D(|sc|−1)` — eq. (6.9).

**The discharge cut (T1→T2a→T2b→T3→T4).** `Gc := G.deleteEdges E(H)`, `f := collapseTo r V(H)`,
`sc := (V(G)∖V(H)) ∪ {r}`, `D = screwDim k`.

- **T1 — placement bridge `q₀`** (KT family embedding, eq. 6.7). Construct `q₀` over the original
  vertex set agreeing with `Qcf` on `V(G)∖V(H)` and *generic* on `V(H)` (moment-curve via the
  `ofParam`/`isGeneralPosition_ofParam`/`withMomentNormals` seed infra), so `ofNormals Gc ends q₀`
  is GP. *Bounded/plumbing; low risk (~60–100 LoC).*
- **T2a — degenerate member reproduces `Qcf`'s rows.** The specialized `q₀^deg` (H-side ≡
  `Qcf.normal r`, KT's `p2`) makes the projected surviving rows of `ofNormals Gc ends q₀^deg`
  reproduce `Qcf`'s panel rows over `Gc.map f`: a surviving edge `e=uv` (`u∈V(H)`) has support
  extensor `panelSupportExtensor (Qcf.normal r) (Qcf.normal v)` in both framings. The projection
  `(extProj V(H)).dualMap` is needed because the *interior* H-side columns differ — exactly the
  §1.14 reason the projection is onto the **exterior** columns. New `map_isLink` +
  `panelSupportExtensor`-equality bookkeeping. *Mechanical but defeq-fiddly; medium risk
  (~100–150 LoC) — cf. the `IsInfinitesimallyRigidOn`-defeq-across-graph-swaps caution.*
- **T2b — generic ≥ degenerate** (the analytic crux, KT lower-semicontinuity). The projected
  surviving-row rank at the generic `q₀` ≥ at `q₀^deg`, via the Phase-21b engine
  `exists_polynomial_ne_zero_of_linearIndependent_at` *re-instantiated on the projected family*
  (the independent subfamily at `q₀^deg` from T2a + `exists_independent_panelRow_subfamily_of_
  rigidOn_linking_set` on `Qcf` propagates Zariski-open; the generic `q₀` lands in it). **Re-uses
  the existing engine — no new matrix-rank theory.** *Research-shaped but de-risked; the one node
  that could wall (~100–200 LoC, may sub-cut).*
- **T3 — extract the independent surviving subfamily at `q₀`.**
  `exists_independent_panelRow_subfamily_of_rigidOn_linking_set` reads off the size-`≥ D(|sc|−1)`
  subfamily `t` + `hsupp` + projected `hindep`; T2 supplies its hypothesis. *Pure green-reuse;
  low risk (~30–50 LoC).*
- **T4 — assemble `htransport`, delete it from the composer, flip.** Compose T1–T3 into the
  `htransport` shape, remove `htransport` from `case_I_realization`'s `hbundle` (now provable
  in-proof from the IH `Qcf`), `\leanok` `lem:claim-6-4`, run the phase-close ceremony. *Plumbing
  (mirror of N-22b-3 in reverse); low risk (~30–50 LoC).*

**The one walling risk — T2b's degenerate-placement transversality.** `q₀^deg` is not globally GP
(H-side bodies coincide), so boundary-edge `supportExtensor`s are nonzero only where `Qcf.normal r
≠ Qcf.normal v` — which holds by `Qcf`'s GP for the *surviving* rows; the subtlety is only that the
non-GP `q₀^deg` must still lie in the projected polynomial's domain (the projection `extProj V(H)`
kills the offending interior columns). Expected to close, but this is the verification to gate on.

**Phase-fit: stays Phase 22b, paused; resume gated on a T2b math-first re-recon.** ~350–550 LoC,
4–5 nodes, one research-shaped crux — a dedicated effort, not a few-commit finish, but tractable
(3/5 nodes plumbing/green-reuse; the crux reuses the engine). Per the coordinator decision
(2026-06-05) it stays **Phase 22b** (the phase's headline *is* Claim 6.4; keeping one phase
accountable avoids the receding-goalpost optics, and 22's sub-letters denote *Case* sub-phases — a
new letter would collide). 22b is **paused at the reduction checkpoint** (N-22b-1/2/3 landed);
the resume opens on the T2b math-first decomposition (the
gating/walling node) per `DESIGN.md` *Constructibility recon … → design the LAYER*, then
T1→T2a→T2b→T3→T4. Does **not** fold into 22c+/23 (Case III is independent of `htransport`).

### 1.19 T2b math-first re-recon — the lower-semicontinuity step is already green inside N-22b-2; the walling node is the collapse-relabel row reproduction (was T2a), and the cut shrinks 5→4 nodes (2026-06-05)

The §1.18 *Hand-off* gated the resume on a math-first re-recon of T2b (the planned analytic crux:
"generic projected rank ≥ degenerate projected rank", KT lower-semicontinuity). This re-recon —
decision-support, traced against the *live* signatures of the two landed bricks
(`rigidContract_exterior_rank_transport` / `exists_rankPolynomial_of_rigidOn_linking_set_proj`,
`CaseI.lean:929`/`:794`), the engine `exists_polynomial_ne_zero_of_linearIndependent_at`
(`Mathlib/LinearAlgebra/Matrix/Rank.lean:474`), the green reuse target
`exists_independent_panelRow_subfamily_of_rigidOn_linking_set` (`GenericityDevice.lean:644`), and
the `rigidContract`/`collapseTo`/`hingeRow` defns — finds T2b as stated **is not a node of the
discharge at all**, and re-locates the one walling step. Per `DESIGN.md` *Constructibility recon …
→ design the LAYER* and *trace a producer's actual output point*.

**Finding 1 — `htransport`'s conclusion is single-placement; the lower-semicontinuity step lives
*inside* already-green N-22b-2, not inside `htransport`.** The N-22b-1 brick's `htransport`
hypothesis (and conclusion) is verbatim `∃ q₀, ∃ t, (Gc-links) ∧ D(|sc|−1) ≤ |t| ∧
LinearIndependent (i ↦ (extProj V(H)).dualMap (panelRow ends i)) at q₀)` — a witness at **one**
placement `q₀` (`CaseI.lean:935–942`). The "lift to a Zariski-open generic locus" is done by
N-22b-2 (`exists_rankPolynomial_of_rigidOn_linking_set_proj`), which instantiates the engine at
`p₀ := q₀` and returns the rank polynomial `Qc` whose non-roots carry the independence
(`CaseI.lean:880–883`). So the engine *re-instantiated on the projected family* — the substance
§1.18 assigned to T2b — is **already green and already wired** (N-22b-2, landed). `htransport`
itself only needs the single witness placement. T2b as a separate node dissolves.

**Finding 2 — the witness placement may be the degenerate member `q₀^deg` itself; no generic
placement is required.** Because N-22b-2 builds `Qc` from *any* placement where the projected rows
are independent, KT's degenerate collapsed realization `p2` (`q₀^deg`: H-side bodies ≡ `Qcf.normal
r`) is a valid witness for `htransport` — *provided* its projected surviving rows are independent.
KT's lower-semicontinuity ("generic ≥ degenerate", eq. 6.9) was needed in the paper because KT
states Claim 6.4 about the *generic* `p_{E∖E′}`; the project's `htransport` is existential over the
placement, so it can name the degenerate member directly. This is the §1.5/N6-G1a pattern again
(a seed property need not survive to a generic output — here we never go to a generic output).

**Finding 3 — the irreducible crux is the collapse-relabel row reproduction (was T2a), and it does
*not* dissolve.** With `q₀^deg` as the witness, the remaining content is: the projected surviving
rows of `ofNormals Gc ends q₀^deg` (uncollapsed, columns over `V(G)`) are independent, read off
`Qcf`'s rigid rows (collapsed, columns over `(V(G)∖V(H))∪{r}`). The relabel is genuine: a surviving
edge `e=uv` with `u∈V(H)` carries `hingeRow u v r` (reads `S u − S v`) in the uncollapsed framing
but `hingeRow (f u) (f v) r = hingeRow r (f v) r` (reads `S r − S (f v)`) in `Qcf`; the exterior
projection `extProj V(H)` (which **zeroes the `V(H)` columns**, incl. `u`, `CaseI.lean:720`) is what
reconciles them — `(extProj V(H)).dualMap (hingeRow u v r)` reads only the surviving column `v`,
matching `Qcf`'s `r`-redirected row on the surviving columns. This IS §1.7's irreducibility (the
collapse-normal mismatch) and KT eq. (6.7)'s family embedding; it is research-shaped. So the
walling risk **moves from T2b to the (renamed) collapse-relabel reproduction node** — the
projection is load-bearing here exactly as §1.14 said, but for row-*reproduction*, not for the
block-triangular split.

**Revised cut (4 nodes, was 5).** `Gc := G.deleteEdges E(H)`, `f := collapseTo r V(H)`,
`sc := (V(G)∖V(H))∪{r}`, `D = screwDim k`.

- **U1 — degenerate placement bridge `q₀^deg`** (KT's `p2`, eq. 6.7 with the H-side collapsed).
  Build `q₀^deg : α × Fin(k+2) → ℝ` agreeing with `Qcf`'s normal-coordinates on the surviving bodies
  `V(G)∖V(H)` (via `Qcf.normal ∘ f`) and assigning the single representative normal `Qcf.normal r`
  to every body of `V(H)`. *Plumbing; low risk (~40–80 LoC).* (Cf. T1, but no genericity/moment-curve
  needed — the witness is the degenerate member, not a generic seed.)
- **U2 — collapse-relabel projected-row reproduction** *(the crux; was T2a + the live part of T2b)*.
  For each surviving link `e=uv ∈ Gc` (i.e. `e ∈ E(G)∖E(H)`), the projected uncollapsed row
  `(extProj V(H)).dualMap ((ofNormals Gc ends q₀^deg).panelRow ends e)` **equals** the analogous
  projected row of `Qcf` over `Gc.map f`, via `Graph.IsLink.map` (forward link transport, fork
  `Map.lean:71`, already used at `Contraction.lean:54`) + a `panelSupportExtensor`-equality
  (`panelSupportExtensor (Qcf.normal r) (Qcf.normal v)` in both framings) + `extProj` killing the
  differing interior `V(H)` columns. **Research-shaped; the one node that could wall** — the genuine
  algebraic-independence content of KT Claim 6.4 / eq. (6.9), now isolated to a row-equality across
  the relabel rather than a semicontinuity inequality. *(~120–180 LoC; medium–high risk — the
  `IsInfinitesimallyRigidOn`/`panelRow`-defeq-across-graph-swaps caution applies, FRICTION; **open
  here first on resume, may sub-cut**.)*
- **U3 — extract the independent surviving subfamily from `Qcf`'s rigidity, transport via U2.**
  `exists_independent_panelRow_subfamily_of_rigidOn_linking_set` on `Qcf` (rigid on its full
  `V(Gc.map f)`) yields the size-`≥ D(|sc|−1)` independent subfamily `t` + `hsupp`; U2's row-equality
  carries the independence to the projected uncollapsed rows at `q₀^deg`. *Green-reuse + the U2
  transport; low–medium risk (~50–90 LoC).* (The §1.18 T3.)
- **U4 — assemble `htransport`, delete it from the composer, flip.** Compose U1–U3 into the
  `htransport` shape with `q₀ := q₀^deg`, remove `htransport` from `case_I_realization`'s `hbundle`
  (now in-proof from the IH `Qcf`), `\leanok` `lem:claim-6-4`, run the phase-close ceremony. *Plumbing
  (mirror of N-22b-3 in reverse); low risk (~30–50 LoC).* (The §1.18 T4.)

**Net effect of the re-recon.** The cut shrinks 5→4 nodes and ~350–550 → ~240–400 LoC; the
lower-semicontinuity worry (the §1.18 "one walling risk") is **retired** — it is already green
infrastructure (N-22b-2), and the project's existential `htransport` sidesteps KT's
generic-placement framing by naming the degenerate member. The walling risk re-localizes to **U2**
(the collapse-relabel projected-row reproduction), which is the faithful Lean shape of §1.7's
irreducible collapse-normal mismatch / KT eq. (6.7). The phase stays **Phase 22b, paused**; the resume
**opens on U2** (the one research-shaped node) before scheduling
U1/U3/U4 as builds, then U1 → U2 → U3 → U4. Unchanged: 22b does not fold into 22c+/23.

**[Corrected by §1.20 below (2026-06-05, the U2-opening build): §1.19's "walling node
retired at U2 / U3 is plumbing" is WRONG. The research-shaped crux did not vanish — it
*moved* from U2 to U3. §1.19 correctly retired the *lower-semicontinuity* worry but
conflated "the collapse-relabel ROW reproduction (U2)" with "the only research-shaped
node", missing that the *exterior-projection rank-preservation* (the actual content of KT
Claim 6.4) is a separate crux living in U3. See §1.20.]**

---

### 1.20 The U2 build surfaced the real crux: U3 is NOT plumbing — the exterior-projection drops the `r`-column, so it needs a pin-a-body rank-preservation brick (the genuine KT Claim 6.4) (2026-06-05)

*Provenance.* Reconstructed from the U2-opening work session, which **forked under
backgrounding**: the pre-reset instance did ~33 min of analysis and reached the findings
below, then a context reset wiped it; the post-reset instance found the (sound) U1 + U2-tail
Lean in the tree, committed it (`9098129`), but — lacking the analysis — wrote an
over-optimistic hand-off ("walling retired, U3+U4 plumbing"). This section is the recovered
analysis; the corrected cut supersedes §1.19's.

**What landed (`9098129`, sound).** U1 `degeneratePlacement` (KT's `p2` = the normal field
pulled back through the collapse map `f := collapseTo r V(H)`) + `degeneratePlacement_ofNormals_normal`;
the U2 per-edge tail `panelRow_collapseTo_comp_extProj_dualMap` (the column core
`hingeRow_collapseTo_comp_extProj_eq` lifted to a full per-edge row equality: the
`(extProj V(H)).dualMap`-projected *uncollapsed* surviving row at `q₀^deg` equals the projected
*collapsed* row of `ofNormals (Gc.map f) endsᶠ q₀^deg'`). These are correct, reusable bricks.

**Obstruction O1 — `Qcf.ends` alignment (RESOLVED in principle).** The composer feeds an
*arbitrary* generic realization `Qcf` of the contraction `G.rigidContract H r`; its selector
`Qcf.ends` and normals are **not** tied to `f ∘ (parent ends)`. §1.19's plan implicitly assumed
`Qcf.ends e = (f u, f v)`, which fails. Resolution: state the U2 brick **`Qcf.ends`-free** (as
landed — it talks about the *constructed* framework `Qcf' := ofNormals (Gc.map f) endsᵐ
(Qcf.normal-pullback)`, `endsᵐ e := (f (ends e).1, f (ends e).2)`), and move `Qcf`'s rigidity to
`Qcf'` via the **`ends`-swap brick** `infinitesimalMotions_ofNormals_eq_of_ends_swap` — both
`Qcf.ends e` and `endsᵐ e` record links of `e` in `Gc.map f`, so they agree up to swap, and the
swap cancels (`annihRow` is linear in `C`; `panelSupportExtensor n₂ n₁ = −panelSupportExtensor
n₁ n₂`; `hingeRow u v (−ρ) = hingeRow v u ρ` — the two negations cancel, the standard
`span_panelRow_eq_rigidityRows` cancellation). This is the `hasGenericRealization_transport_ends`
pattern. Bricked, real, but not research-shaped.

**Obstruction O2 — exterior-projection rank-preservation = the genuine KT Claim 6.4 (NOT solved;
missing infra).** The composer (via N-22b-2 `exists_rankPolynomial_of_rigidOn_linking_set_proj`)
needs the **projected** rows `(extProj V(H)).dualMap ∘ panelRow` independent of size `≥ D(|sc|−1)`.
The U3 tool `exists_independent_panelRow_subfamily_of_rigidOn_linking_set` delivers only
**un-projected** independence. **Projection can lower rank**, and `(extProj V(H)).dualMap` drops
*exactly the `r`-column* (`r` is the only vertex of `Qcf'` lying in `V(H)`). That dropping this one
column still preserves rank `D(|sc|−1)` **is precisely KT Claim 6.4 / eq. (6.3)'s bottom-right
block** — a **pin-a-body** fact: rigidity on `sc` means the motions are exactly the `D`-dimensional
trivial screws, which are pinned by fixing the single representative body `r`, so the `r`-column is
rank-redundant. A search confirmed **no green brick** does this projected-subfamily extraction; the
nearest green facts — `linearIndependent_sum_pinned_block` (N7b-3, the pin-a-body column split) and
`finrank_pinnedMotions_add_screwDim` (Lemma 5.1, pin-a-body) — are *related but insufficient*. This
is the research-shaped node, and it lives in **U3**, not U2.

**Corrected U3 cut (U3 splits; U3b is the crux).**
- **U3a — alignment transport** (O1): `Qcf` rigid on `sc = V(Gc.map f) = V(G.rigidContract H r)`
  ⟹ `Qcf'` (the `endsᵐ`-selector framework) rigid on `sc`, via `infinitesimalMotions_ofNormals_eq_of_ends_swap`.
  Bricked; medium (swap bookkeeping). *Not* pure green-reuse, but not a wall.
- **U3b — pin-the-`r`-column projected-rank brick** (O2, the genuine KT Claim 6.4): from `Qcf'`
  rigid on `sc`, the exterior-column projection (drop the `r`-column) preserves independent rank
  `≥ D(|sc|−1)`. **New linear-algebra brick, missing infra, research-shaped.** Reuse candidates:
  `linearIndependent_sum_pinned_block`, `finrank_pinnedMotions_add_screwDim`. *Open this math-first
  before building (design the LAYER).*
- Then **U2 (landed)** carries projected-*collapsed* independence to projected-*uncollapsed* rows at
  `q₀^deg` per edge; **U4** assembles `(q₀^deg, t, …)` into `htransport`, translating the subfamily
  indices from `Gc.map f`-links (at `endsᵐ`) to `Gc`-links (at parent `ends`) via a `Gc`-link
  `hends`, deletes `htransport` from `case_I_realization`, flips `lem:claim-6-4`, then phase-close.

**Net.** §1.19's "4-node cut, 3/4 plumbing, walling retired" is corrected to: U1 ✓, U2 ✓ (the
collapse-relabel reconciliation, genuinely done), **U3a** (alignment, bricked) + **U3b** (the
pin-the-`r`-column rank-preservation — the real Claim 6.4 crux, missing infra), **U4** (assembly).
The honest scope is *one research-shaped node remains* (U3b); it was never retired, only relocated.

---

### 1.21 U3b recon — the crux is bounded: `(extProj V(H)).dualMap` on the contracted framework = pin-at-`r`, so U3b is the projected sibling of the green U3 tool off Lemma 5.1, not a from-scratch research lemma (2026-06-05)

Math-first recon of the U3b node §1.20 flagged, traced against the live bricks
(`finrank_pinnedMotions_add_screwDim` `:995`, `linearIndependent_sum_pinned_block` `:548`,
`exists_independent_panelRow_subfamily_of_rigidOn_linking_set` `GenericityDevice:644`, `extProj`
`CaseI:720`). **Verdict: U3b is one bounded new brick, not a research wall** — §1.20's "missing
infra / research-shaped" is sharpened: the *conceptual crux is already green*; only a *packaging*
lemma is missing.

**Key realization.** `(extProj V(H)).dualMap` applied to the contracted framework `Qcf'` (on
`Gc.map f`, vertices `(V(G)∖V(H)) ∪ {r}`) **= "drop the `r`-column"** — `r` is the *only* vertex of
`Qcf'` in `V(H)` (`f = collapseTo r V(H)` sends all of `V(H)` to `r`; surviving bodies stay outside
`V(H)`). "Dropping one body's columns preserves rank" is exactly **Lemma 5.1**
`finrank_pinnedMotions_add_screwDim`: `finrank(pinnedMotions r) + D = finrank(Z)`. For `Qcf'` rigid
on `sc`, `finrank(Z) = D` ⟹ `finrank(pinnedMotions r) = 0` ⟹ dropping the `r`-column loses **zero**
rank ⟹ the projected rows attain rank `D(|sc|−1)`. That is KT Claim 6.4.

**The layer (3 steps; mirrors the green U3 tool nearly line-for-line):**
1. **`extProj V(H)` on `Qcf'` = pin-at-`r`** — needs `V(Gc.map f) ∩ V(H) = {r}` (collapse fact).
   Bounded.
2. **The one new brick — a *projected* sibling of `exists_independent_panelRow_subfamily_of_rigidOn_linking_set`.**
   Same skeleton (span identity → finrank lower bound → `Submodule.exists_fun_fin_finrank_span_eq`
   extraction), but: (a) the projected `H`-block rows *vanish* (`hingeRow_comp_extProj_eq_zero`,
   GREEN — KT's top-right `0`), so the projected span = projected *surviving* rows; (b) the finrank
   bound comes from **Lemma 5.1** (`pinnedMotions r`) not the full motion space. The genuine content
   is the **finrank bridge** `finrank((extProj V(H)).dualMap '' Φ) ≥ D(|sc|−1)` from
   `finrank(pinnedMotions r) = 0` — standard dual-annihilator LA, possibly a small `Mathlib/` mirror.
3. **Extract `D(|sc|−1)` independent projected rows** — identical machinery to the U3 tool. Plumbing.

**Risk.** Medium on step 2's finrank bridge (the dual-map-image ↔ pinned-motion-space finrank
identity); low elsewhere. The down-grade from §1.20: U3b is *one bounded brick built off green
Lemma 5.1 + a projected re-run of the U3-tool skeleton*, not a from-scratch research lemma. U3a
(alignment, the `ends`-swap brick) feeds `Qcf'`-rigid-on-`sc` in; U4 assembles + flips.

**[Corrected by §1.22 below (2026-06-05, the U3b build-recon traced against the live finrank
machinery): §1.21's "Key realization" — that `Qcf'` rigid on `sc` gives `finrank(Z) = D`, so
`finrank(pinnedMotions r) = 0` and the projection loses zero rank — is WRONG whenever `sc ≠ α`. A
framework rigid on its *vertex set* `sc` has `finrank(Z) = D·(|scᶜ|+1)` (the green
`finrank_infinitesimalMotions_of_isInfinitesimallyRigidOn_vertexSet`), **not** `D`: the free
isolated bodies of `scᶜ` carry `D·|scᶜ|` extra null dimensions, so `finrank(pinnedMotions r) =
D·|scᶜ| ≠ 0`. The clean conclusion `finrank(map D Φ) = D(|sc|−1)` *does* still hold, but via an
**exact cancellation** of the free-isolated-body columns — and the genuine content is a
block-pin count, not a one-line Lemma 5.1 application. See §1.22.]**

---

### 1.22 U3b build-recon — the recon's "finrank Z = D" is false for `sc ≠ α`; the brick closes via `Z ⊔ range(extProj V(H)) = ⊤`, whose real content is the rigid-block pin-count `finrank(pinnedMotionsOn_F V(H)) = D(|scᶜ|−|V(H)|+1)` (2026-06-05)

Build-recon of U3b, traced against the live finrank machinery
(`finrank_infinitesimalMotions_of_isInfinitesimallyRigidOn_vertexSet` `GenericityDevice:386`,
`span_panelRow_linking_eq_rigidityRows` `Pinning:130`, `finrank_pinnedMotionsOn_vertexSet`
`Pinning:775`, `finrank_iInf_ker_proj_eq` `Pinning:800`, `extProj` `CaseI:720`) + the mathlib dual
API. **Verdict: the brick is real linear-algebra content (≈ a product-iso block-pin sub-lemma), not
the one-line Lemma 5.1 corollary §1.21 claimed — but it closes, and the layer is now nailed down.**

**The §1.21 error.** §1.21's "Key realization" reads `Qcf'` rigid on `sc` as `finrank(Z) = D`. That
is the rigid-on-*all-of-α* count. `Qcf'` is rigid on its **vertex set** `sc = (V(G)∖V(H)) ∪ {r}`,
which is generally a *proper* subset of `α`; the green
`finrank_infinitesimalMotions_of_isInfinitesimallyRigidOn_vertexSet` gives
`finrank(Z) = D·(|scᶜ|+1)`, so `finrank(pinnedMotions r) = finrank(Z) − D = D·|scᶜ|`, **nonzero**
when isolated bodies exist. So "drop the `r`-column loses zero rank" does not follow from Lemma 5.1
alone — the `D·|scᶜ|` free-isolated-body dimensions are still present after pinning `r`, and
`(extProj V(H)).dualMap` does **not** drop their columns (it drops only `V(H)`-columns). The clean
`D(|sc|−1)` survives only because those free columns *cancel exactly* between the row-space gain and
the projection's column loss — which has to be proven, not waved through.

**The corrected, verified-closing layer.** Let `Φ := span(F's linking panel rows)`,
`D := (extProj V(H)).dualMap`, `Z := F.infinitesimalMotions`, `W := range(extProj V(H))`. The
projected span is `map D Φ`; rank-nullity on `D|Φ` gives `finrank(map D Φ) = finrank Φ −
finrank(Φ ⊓ ker D)`, and the green `span_panelRow_linking_eq_rigidityRows` + the rigid-block count
give `finrank Φ = D(|sc|−1)`. So **the entire brick reduces to `Φ ⊓ ker D = ⊥`** (i.e. `D` injective
on Φ — projection loses zero rank). Chain (all mathlib facts confirmed present):
1. `ker D = W.dualAnnihilator` — `LinearMap.ker_dualMap_eq_dualAnnihilator_range` (`Dual/Defs`).
2. `Φ = Z.dualAnnihilator` — double-annihilator in finite dim (`Φ = (span rows)`,
   `Z = Φ.dualCoannihilator` by `infinitesimalMotions_eq_dualCoannihilator`, and
   `Subspace.dualAnnihilator_dualCoannihilator_eq` / `…dualCoannihilator_dualAnnihilator…`).
3. `Φ ⊓ ker D = Z.dualAnnihilator ⊓ W.dualAnnihilator = (Z ⊔ W).dualAnnihilator` —
   `Submodule.dualAnnihilator_sup_eq` (`Dual/Defs:427`).
4. So `Φ ⊓ ker D = ⊥` ⟺ `Z ⊔ W = ⊤` (`dualAnnihilator_top = ⊥`).

`Z ⊔ W = ⊤` is the **genuine new content**, proved by the finrank count
`finrank(Z⊔W) + finrank(Z⊓W) = finrank Z + finrank W` (`Submodule.finrank_sup_add_finrank_inf_eq`):
- `finrank Z = D(|scᶜ|+1)` (green, rigid-on-vertexSet).
- `W = range(extProj V(H)) = {S | S = 0 on V(H)} = ⨅ i ∈ V(H), ker(proj i)`, so
  `finrank W = D·|V(H)ᶜ|` (green `finrank_iInf_ker_proj_eq`, modulo the `range extProj = iInf ker
  proj` identity — a small new `extProj_range` lemma).
- `Z ⊓ W = {motions, =0 on V(H)} = F.pinnedMotionsOn V(H)` (defeq to the `pinnedMotionsOn` carrier).

Substituting, `Z ⊔ W = ⊤` ⟺ **`finrank(F.pinnedMotionsOn V(H)) = D(|scᶜ| − |V(H)| + 1)`** — the one
real-content fact. It is the *rigid-block pinned at one representative* count: `V(H) ∩ sc = {r}`, so
`pinnedMotionsOn V(H) = pinnedMotions r ⊓ {vanish on V(H)∖{r}}`, and the `|V(H)|−1` bodies of
`V(H)∖{r} ⊆ scᶜ` are isolated/free inside `pinnedMotions r` (dim `D·|scᶜ|`), so forcing them to 0
removes exactly `D(|V(H)|−1)`: `D·|scᶜ| − D(|V(H)|−1) = D(|scᶜ| − |V(H)| + 1)`. **This is the
sub-lemma to build** — a product-space iso peeling the free isolated columns (the genuine "research
shaped" kernel §1.20 located in U3 and §1.21 under-estimated; the `htransport`-discharge crux).

**Net.** §1.21's "one-line Lemma 5.1 corollary" is corrected to: the U3b brick = the rigid-block
pin-count sub-lemma + the dual-annihilator `Z ⊔ W = ⊤` assembly + the projected-subfamily extraction
(the U3-tool skeleton). All mathlib facts and green project facts are confirmed present; the build
target is the pin-count sub-lemma (needs a small `extProj_range` identity + a free-isolated-body
product iso). Risk: medium on the product iso; the rest is plumbing off confirmed API. **The
build opens on the pin-count sub-lemma** per `DESIGN.md` *Constructibility recon … build the
walling node first*.

The recon-process lesson (rigid-on-`α` vs. rigid-on-vertex-set null-space counts) is lifted to
`DESIGN.md` *Match the source's argument structure …* → *Sharpening: a "rigid" framework's
null-space dimension depends on rigid-on-what*.

**Coordinator verification (2026-06-05).** The arithmetic above was independently re-derived from a
direct motion-space decomposition (not by re-reading §1.22), and **confirmed sound**:
- `finrank Z = D(|scᶜ|+1)`: a motion is *trivial on `sc`* (`D` dims, rigidity) ⊕ *free on `scᶜ`*
  (`D·|scᶜ|`). [So §1.21's `=D` dropped the `D·|scᶜ|` free term — genuinely wrong.]
- `finrank Φ = D|α| − finrank Z = D(|sc|−1)` (full row rank). `Gc.map f` carries *no* H-edges, so
  `Φ` is already the surviving-row span — there are no H-block rows to vanish (the "H-rows die"
  caveat is a composer-level concern, moot for the contracted `Qcf'`).
- Goal ⟺ projection injective on `Φ` ⟺ `Φ ⊓ ker(extProj.dualMap) = ⊥` ⟺ `Z ⊔ range(extProj V(H)) =
  ⊤` (dual annihilators: `Φ° = Z`, `(ker dualMap)° = range extProj`).
- That `⊤` ⟺ (incl–excl) `finrank(Z ⊓ range) = D(|scᶜ|−|V(H)|+1)`, and `Z ⊓ range(extProj V(H)) =
  pinnedMotionsOn V(H)`.
- **Pin-count is true:** pinning `V(H)` forces `S(r)=0` ⟹ (trivial-motion-vanishing-at-a-body `=0`,
  the existing single-body fact) `S|sc = 0`, *plus* `S|(V(H)∖{r})=0` pins the `|V(H)|−1` isolated
  bodies of `V(H)∖{r} ⊆ scᶜ`; residual free = `scᶜ ∖ (V(H)∖{r})`, dim `D(|scᶜ|−|V(H)|+1)`. ✓
So §1.22's layer is mathematically sound; the U3b build is grounded. (This independent check is the
discipline now codified in `DESIGN.md` *Constructibility recon …* → *Verify the recon's load-bearing
claims, don't assert them*.)

**Build progress (2026-06-05).** The §1.22 layer landed exactly as designed, in two commits:
1. **Pin-count walling node** (`0f0e7aa`): `finrank_pinnedMotionsOn_of_isInfinitesimallyRigidOn_vertexSet_inter_eq_singleton`
   (`Pinning.lean`) — `finrank(pinnedMotionsOn t) = D(|Vᶜ|+1−|t|)` for `V ∩ t = {r}`. The
   "free-isolated-body product iso" the recon flagged as the medium-risk kernel turned out *not* to
   need an explicit product iso: pinning `t` forces (rigidity) vanishing on all of `V`, so
   `pinnedMotionsOn t = pinnedMotionsOn (V ∪ t)`, which is the kernel of the `(V∪t)`-projections
   (`pinnedMotionsOn_eq_iInf_ker_proj_of_vertexSet_subset`, a clean `s ⊇ V(G)` generalization of the
   green vertex-set pin), dimension `D·|(V∪t)ᶜ|` straight off `finrank_iInf_ker_proj_eq` + incl–excl.
2. **`Z ⊔ W = ⊤` assembly** (this commit): `infinitesimalMotions_sup_range_extProj_eq_top`
   (`CaseI.lean`), via two supporting bricks — `extProj_range_eq_iInf_ker_proj` (range of the
   idempotent coordinate projection = `⨅ i∈proj, ker(proj i)`) and
   `infinitesimalMotions_inf_range_extProj_eq_pinnedMotionsOn` (`Z ⊓ W = pinnedMotionsOn proj`, the
   defining conjunction) — then `Submodule.finrank_sup_add_finrank_inf_eq` on the three confirmed
   dimensions, closing by `omega` after distributing `D` over the `ncard`-level identity by hand.
   Both axiom-clean, build + lint warning-clean.

3. **Projected-subfamily extraction** (LANDED, this commit): two bricks in `CaseI.lean`. The
   §1.22-injective-form core `injOn_extProj_dualMap_rigidityRows` — for `F` rigid on its vertex set
   and `V(F) ∩ proj = {r}`, `(extProj proj).dualMap` is `Set.InjOn` on `Φ = span rigidityRows`
   (i.e. `Φ ⊓ ker D = ⊥`, the projection loses zero rank), proved by the dual-API chain on the
   landed `Z ⊔ W = ⊤`: `ker D = W.dualAnnihilator` (`ker_dualMap_eq_dualAnnihilator_range`),
   `Φ = Z.dualAnnihilator` (`Z = Φ.dualCoannihilator` + `Subspace.dualCoannihilator_dualAnnihilator_eq`),
   `Φ ⊓ ker D = (Z ⊔ W).dualAnnihilator` (`dualAnnihilator_sup_eq`) `= ⊤.dualAnnihilator = ⊥`,
   then `LinearMap.injOn_of_disjoint_ker` via `disjoint_iff`. Then the extraction proper
   `exists_independent_panelRow_subfamily_of_rigidOn_linking_set_proj`: rather than re-run the
   `exists_fun_fin_finrank_span_eq` skeleton, it calls the **green un-projected tool**
   `exists_independent_panelRow_subfamily_of_rigidOn_linking` for the size-`≥ D(|V(F)|−1)`
   independent subfamily, then maps it through `D` by `LinearIndependent.map_injOn` — the rows live
   in `Φ` (each links ⟹ is a rigidity row, the composer's `hrow_mem` pattern) where `D` is injective,
   so the projected family is independent of the *same* size. Both axiom-clean, build + lint
   warning-clean. **The simplification vs. the recon:** the projected extraction is *not* a re-run of
   the U3-tool span/finrank skeleton — `map_injOn` carries the un-projected independence through
   directly, so the projected count drops out of the un-projected count for free (no projected
   `finrank` bridge needed).

**Remaining U3b — none.** All three §1.22 sub-bricks (pin-count walling node, `Z ⊔ W = ⊤` assembly,
projected-subfamily extraction) are landed. Next: U3a (alignment) → U4 (assemble + flip +
phase-close).

---

### 1.23 U3a build-recon — the §1.20 "alignment RESOLVED in principle" is NOT buildable as scoped: the IH motive `HasGenericFullRankRealization` carries an *arbitrary* `ends` (no link-recording), so `Q`'s rigidity does not transport to the `endsᵐ` selector; the same gap is already an *undischarged* `hbundle` conjunct for the `H`-leg (2026-06-05)

Build-recon of U3a — the one node §1.20 left as "bricked, medium (swap bookkeeping)" — traced against
the live structure defs (`PanelHingeFramework` `PanelHinge:64`, free `ends`/`normal` fields, no
link-recording invariant; `IsInfinitesimalMotion` `RigidityMatrix:331`, the per-edge hinge constraint
`S u − S v ∈ span {supportExtensor e}` quantified over the *graph* links `F.graph.IsLink e u v` but
with `supportExtensor e = panelSupportExtensor (normal (ends e).1) (normal (ends e).2)` reading
`F.ends`), the swap brick `infinitesimalMotions_ofNormals_eq_of_ends_swap` `CaseI:332`, its single
consumer `hasGenericRealization_transport_ends` `CaseI:375`, and the composer's `hbundle`
`case_I_realization` `CaseI:1574`. **Verdict: U3a is NOT a buildable single commit as §1.20 scoped it
— it rests on an assumption the motive does not provide, and the same assumption is already carried,
*undischarged*, as an `hbundle` conjunct for the `H`-leg. The honest next step is a motive-strengthening
recon, not a build.**

**The §1.20 error.** §1.20 O1 reads: "both `Qcf.ends e` and `endsᵐ e` record links of `e` in
`Gc.map f`, so they agree up to swap, and the swap cancels." The second clause holds for `endsᵐ e :=
(f (ends e).1, f (ends e).2)` (it records the contracted link via `IsLink.map` whenever the parent
`ends` records the `Gc`-link). **But the first clause — that `Qcf.ends e` records the link — does
NOT hold.** `Qcf` is an arbitrary witness of `HasGenericFullRankRealization k (G.rigidContract H r)`
(`PanelHinge:938`): `∃ Q, Q.graph = … ∧ Q.IsGeneralPosition ∧ Q.toBodyHinge.IsInfinitesimallyRigidOn …`.
`Q.ends` is a **free field** with no constraint tying it to `Q.graph`'s links, and `IsGeneralPosition`
constrains only the normals (`PanelHinge:84`, pairwise normal independence). So `Q.ends e` may name a
body pair *unrelated* to `e`'s graph endpoints.

**Why the gap is fatal to the transport, not cosmetic.** The motion space genuinely depends on
`F.ends`: `IsInfinitesimalMotion` (`RigidityMatrix:331`) constrains `S u − S v ∈ span {supportExtensor e}`
for graph links `e u v`, and `supportExtensor e` is computed from `F.normal (F.ends e)`. So moving
`Q`'s rigidity (at `Q.ends`) to `Qcf' := ofNormals (Gc.map f) endsᵐ Q.normal` (at `endsᵐ`) via
`infinitesimalMotions_ofNormals_eq_of_ends_swap` requires `Q.ends e =(swap) endsᵐ e` for every link —
i.e. `Q.ends` records `Q.graph`'s links *and* aligns with `f ∘ (parent ends)`. Rigidity alone forces
neither. For a `Q` whose `ends` is pathological (records non-links), `Q` can still be rigid at its own
`ends` while telling us *nothing* about `endsᵐ`; the conclusion of `htransport` (which never mentions
`Q.ends`) must then be manufactured from scratch, and the IH supplies no rigid framework at any
link-recording selector to do it. So `htransport`, **universally quantified over `Q`**, is not
discharge­able from the present motive.

**The same gap is already live for the `H`-leg — and it's an *assumed* `hbundle` conjunct, never
proven.** The composer `case_I_realization` (`CaseI:1574`) takes `hbundle` whose *first* conjunct is
exactly the `H`-leg `hswap`: `∀ Q, Q.graph = H → (∀ e u v, H.IsLink e u v → Q.ends e =(swap) ends e)`.
This is consumed at `CaseI:1624` (`hasGenericRealization_transport_ends H ends QH … (hswap QH hQHg) …`)
but is **never discharged** — it is carried in the green-modulo `h…` bundle alongside `htransport`.
It has the identical defect: it asserts an arbitrary IH realization's `ends` aligns with the
manufactured parent selector. So the layer already *assumes* the property U3a would need to prove; U3a
is not "the last research-shaped brick" — it is one of *two* faces (contraction-leg + `H`-leg) of a
single missing motive guarantee.

**The honest resolution is a motive strengthening, scoped by a recon — not a U3a build.** The realizations
the induction actually produces are *all* `ofNormals G ends q₀` with a **link-recording** `ends`
(the producers `hasGenericFullRankRealization_of_{splice_set,couple}_ofNormals` take/forward the
edge-restricted `hends : ∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2`, manufactured from
the canonical `Graph.endsOf`). So the natural fix is to add that guarantee to the motive — e.g.

> `HasGenericFullRankRealization k G := ∃ Q, Q.graph = G ∧ Q.IsGeneralPosition ∧`
> `  (∀ e u v, G.IsLink e u v → ((Q.ends e).1 = u ∧ (Q.ends e).2 = v) ∨ …swap…) ∧`
> `  Q.toBodyHinge.IsInfinitesimallyRigidOn V(G)`

(the realization's selector records its own graph's links). With that conjunct, the `H`-leg `hswap`
and the contraction-leg alignment both *derive* (compose the realization's link-recording with the
parent selector's link-recording — both pin the same unordered pair, so they agree up to swap),
discharging the `hswap` conjunct of `hbundle` directly and unblocking U3a's transport. **But this is
a Phase-21/22-touching structural edit**, not a Phase-22b leaf: it re-types the motive that
`theorem_55_generic` / the base case / every producer concludes, so each must be shown to *supply* the
new conjunct (the producers do, via their `hends`, but it must be threaded). The scope is comparable to
the §1.3/§1.4 two-motive split, not to the green U3b bricks. Whether to (i) strengthen the motive,
(ii) keep the `H`-leg `hswap` + the new contraction-leg alignment as *explicit* `hbundle` conjuncts
(the current pattern, honest green-modulo, deferring the discharge to a later structural pass) and
flip nothing this phase, or (iii) re-localize the contracted realization differently so a link-recording
selector is available — is the recon decision. It must be settled before any U3a/U4 build.

**Net.** §1.20's "U3a — alignment transport (O1; bricked, medium); RESOLVED in principle" is corrected
to: U3a is *blocked* on a motive guarantee (the realization's `ends` records its graph's links) that
`HasGenericFullRankRealization` does not carry, and that the `H`-leg already assumes undischarged in
`hbundle`. The U3b bricks are sound and remain green (they take a framework rigid at an external
link-recording selector — that hypothesis is exactly what is now seen to need manufacturing). The
discharge of `htransport` does not reduce to one more leaf commit; it needs the motive recon above.
The recon-process lesson (a "rigid realization" motive that drops the selector-link-recording conjunct
cannot feed any selector-sensitive transport) is a sibling of §1.22's rigid-on-what sharpening and is
lifted to `DESIGN.md` *Match the source's argument structure …* → *A realization motive must carry the
selector invariants its consumers read* (companion to *Realization motive must be V(G)-relative*).

### 1.24 Route-(i) scope verification + the U3a/U4 commit sequence — the motive strengthening is *generic-motive only*, all producers supply link-recording from `endsOf`, the three risk items confirmed (with two refinements) (2026-06-05)

The user **decided route (i)** (§1.23: strengthen the motive to carry "the realization's `ends`
records its own graph's links", then discharge the `hbundle` alignment conjuncts and build U3a/U4).
This section is the **scope-verification recon** — every claim below was traced against the live
code (no Lean written), and the commit sequence front-loads the provable-now bricks so the big
re-type lands with no missing deps. **The inventory CONFIRMS the proposed scope** (no contradiction);
two of the three risk items sharpen in the project's favour.

**Scope item 1 — "generic motive only" — CONFIRMED.** Strengthen *only*
`HasGenericFullRankRealization` (`PanelHinge.lean:938`); leave the bare `HasFullRankRealization`
(`:913`) and `theorem_55` (`:976`) untouched. Verified: the `ends`-transport lives **entirely** in
the generic Case-I flow. The swap brick `infinitesimalMotions_ofNormals_eq_of_ends_swap`
(`CaseI.lean:332`) has exactly **one** call site — inside its own consumer
`hasGenericRealization_transport_ends` (`:375`, used at `:396`) — and that consumer has exactly
**one** call site, `case_I_realization`'s `H`-leg (`:1623`). `HasGenericFullRankRealization` occurs
in only three files (`PanelHinge`/`GenericityDevice`/`CaseI`), all generic Case-I. The bare-motive
couplings (`hasFullRankRealization_of_couple_ofNormals` `:70`, `…_set` `:240`,
`…_splice_ofNormals` `GenericityDevice:869`) take each leg's rigidity **pre-aligned at the parent
selector as an explicit hypothesis** (`hrigH`/`hrigc` at `ofNormals … ends …`) — they do *no*
`ends`-swap, extract *no* IH. `theorem_55_generic`'s bare conjunct (`hcontract`, `PanelHinge:1054`)
feeds the IH's bare half `(hIH …).2`; only the GP conjunct (`hcontractGP`, `:1059`) routes through
`case_I_realization`. So no bare-motive producer/consumer transports across `ends` or needs
link-recording. **The scope is correct.**

**Scope item 2 — producer inventory — CONFIRMED (every generic producer constructs fresh, supplies
link-recording from a parameter).** Sites concluding `HasGenericFullRankRealization`:
| Site | Role | Witness | `ends` source |
|---|---|---|---|
| `…_of_couple_ofNormals` `CaseI:170` | coupling (all-`V`) | **fresh** `ofNormals G ends q₀` | param, all-`β` `hends : ∀ e, G.IsLink e (ends e).1 (ends e).2` |
| `…_of_splice_set_ofNormals` `CaseI:520` | splice (body-set) | **fresh** | param (caller supplies) |
| `…_of_couple_ofNormals_set` `CaseI:568` | coupling (body-set) | **fresh** | param, **edge-restricted** `hends : ∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2` |
| `…_of_couple_asymm_ofNormals_set` `CaseI:667` | coupling (asymm, superseded) | **fresh** | param, edge-restricted |
| `…_of_splice_ofNormals` `GenericityDevice:869` | device-free splice (N6-G1) | **fresh** `ofNormals G ends q₀` `:881` | param |
| `…_of_couple_blockTriangular_ofNormals_set` `CaseI:1388` | block-triangular coupling | **fresh** `ofNormals G ends q` | param, edge-restricted |
| `case_I_realization` `CaseI:1591` | composer | forwards via the coupling | **manufactures** `ends := G.endsOf`, `hends` from `isLink_endsOf` `:1602` |
None forwards an IH realization's `Q` as the witness; every one builds `ofNormals G ends q₀` and
takes `ends` as a parameter with a link-recording `hends`. So **link-recording is free for every
producer** once the motive carries it (the composer already manufactures the canonical link-recording
`endsOf`). The *only* place a link-recording selector must be *manufactured from an arbitrary IH*
is inside the swap-transport (the IH's own `Q.ends`), which is exactly what the new motive conjunct
supplies.

**Scope item 3 — the three risk items — CONFIRMED, two sharpen:**
- **(a) `hne_ends` unsatisfiable for `endsOf` — CONFIRMED (stronger than feared).** `endsOf` returns
  the junk `(default, default)` on non-edges (`Operations.lean:80–81`), so the all-`β`
  `hne_ends : ∀ e, (ends e).1 ≠ (ends e).2` (the second `hbundle` conjunct, `CaseI:1579`, and the
  bare couplings' parameter at `CaseI:73`/`:243`) is **genuinely unsatisfiable** for `ends = G.endsOf`.
  The swap-transport brick `hasGenericRealization_transport_ends` must be **edge-restricted** on its
  `hne_ends` (consume it only on linking edges, where `supportExtensor_ne_zero` is actually read),
  and that edge-restricted form discharges from `endsOf`-on-links distinctness via `G.Simple`
  (a simple graph has no loops, so a link's two ends differ). Commit 1.
- **(b) `hswap` discharge — CONFIRMED, and the bridge already exists.** The first `hbundle` conjunct
  (`CaseI:1575–1578`) is exactly the alignment §1.23 found undischarged. With the new motive conjunct
  ("`Q.ends` records `Q.graph`'s links"), `hswap` discharges by composing it with the parent
  selector's link-recording (`endsOf`, `isLink_endsOf`) — both pin the *same unordered pair*, so they
  agree up to swap. The bridge `endsOf_eq_or_swap` (`Operations.lean:102–107`) is **already landed** —
  it is precisely `isLink_endsOf` + mathlib `IsLink.eq_and_eq_or_eq_and_eq`, the lemma the prompt
  anticipated needing. So (b) is even cheaper than expected; the motive conjunct + the existing
  bridge close it.
- **(c) contraction-leg `IsLink.map`-under-`collapseTo` — CONFIRMED, bounded (one small lemma).**
  `rigidContract G H r = (G.deleteEdges E(H)).map (collapseTo r V(H))` (`ReducibleVertex.lean:680`),
  so the contracted graph is `Gc.map f` with `Gc = G.deleteEdges E(H)`, `f = collapseTo r V(H)`. The
  mathlib fact `Graph.map_isLink` (`Mathlib.Combinatorics.Graph.Maps`:
  `(map f G).IsLink e a b = Relation.Map (G.IsLink e) f f a b`) gives the forward direction
  `G.IsLink e x y → (map f G).IsLink e (f x) (f y)` directly. So the relabelled selector
  `endsᵐ := f ∘ (parent ends)` records the contracted link whenever the parent `ends` records the
  `Gc`-link — a **small derived lemma**, not a research wall. This is the one genuinely new (if minor)
  brick; it lands inside the U3a/U4 build (Commits 4–5), not as a front-loaded provable-now brick.

**Verified commit sequence (route (i)).** Front-load the two provable-now bricks so the re-type
threads through a complete dep set; the new `IsLink.map` lemma rides U3a; U4 is the flip + close.

1. **Edge-restrict `hasGenericRealization_transport_ends`'s `hne_ends`** (consume distinctness only on
   linking edges) **+ add the `endsOf`-on-links distinctness fact** (`Operations.lean`, off `G.Simple`
   + `isLink_endsOf`). Provable now; no motive dependency. Closes risk (a). *First buildable.*
2. **Add the `linkRecording (ofNormals G G.endsOf q₀) G` bridge lemma** — that the canonical-`endsOf`
   realization records `G`'s links (its `.ends e = G.endsOf e` by `ofNormals_ends`, link-recording by
   `isLink_endsOf`). This is the term every fresh producer will hand the strengthened motive. Provable
   now (no re-type yet — states the conjunct the producers already satisfy). De-risks Commit 3.
3. **The re-type of `HasGenericFullRankRealization`** — add the link-recording conjunct
   (`∀ e u v, G.IsLink e u v → ((Q.ends e).1 = u ∧ (Q.ends e).2 = v) ∨ swap`) to the `def` (`:938`);
   thread it through every conclusion site (the 6 producers + the base-case `hbaseGP` and the
   `theorem_55_generic` motive `Pc`), each supplied by Commit 2's bridge (fresh `endsOf` producers) or
   the IH (the composer forwarding); re-destructure every consumer's `let ⟨Q, hQg, hQgp, hQrig⟩`. Big
   mechanical commit, no missing deps after 1–2. (`hasFullRankRealization_of_generic` `:948` forgets
   the new conjunct just as it forgets GP — one extra `_`.)
4. **Discharge `hswap`/`hne_ends` from the strengthened bundle + build U3a** — with the motive
   conjunct in hand, the `H`-leg `hswap` derives via `endsOf_eq_or_swap` (already landed) and the
   contraction-leg alignment via the new `IsLink.map`-under-`collapseTo` lemma (risk (c)); transport
   `Qcf`'s rigidity on `sc = V(Gc.map f)` to the `endsᵐ` selector by
   `infinitesimalMotions_ofNormals_eq_of_ends_swap`. This is the U3a §1.20 plan, now *buildable*.
5. **U4 — assemble `htransport`, delete it from `hbundle`, flip `lem:claim-6-4` green, phase-close.**
   U3b (landed) gives projected-*collapsed* independence; U2 (landed) carries it to
   projected-*uncollapsed* rows at `q₀^deg`; assemble `(q₀^deg, t, hsupp, hcount, hindep)` into
   `htransport`; delete `htransport` (and, with route (i), the `H`-leg `hswap`) from `hbundle`;
   `\leanok` `lem:claim-6-4`; then the full phase-close ceremony.

**Net.** Route (i) is verified buildable: the scope is generic-motive-only, every producer supplies
link-recording for free, and the three risk items hold — (a) needs the edge-restriction (Commit 1),
(b)'s bridge is already landed, (c) is one small `IsLink.map` lemma. The motive recon owed by §1.23
is settled; the next concrete commit is **Commit 1** (edge-restrict `hne_ends` + `endsOf`-on-links
distinctness, provable now). No exposition-ledger entry: this is project-side motive plumbing, not a
new KT-math insight (the KT crux is U3b, already bricked).

---

### 1.25 Phase 22c opens — Case III at `d=3` (KT Lemma 6.10): the layer design recon, first pass (2026-06-05)

22b closed (Claim 6.4 discharged; `lem:case-I-realization` fully green). **Phase 22c opens on Case III
at `d=3` / Track B** — KT §6.4.1, Lemma 6.10, the `theorem_55.hsplit` branch at `k=0`, the
conjecture's crux (the single largest proof in KT, ~12 pages). Per `DESIGN.md` *Scale-up: design the
LAYER, not just the node* and the user's design-pass-first instruction, 22c opens with a **layer-level
design recon, not a build** — Case I burned ~10 node-by-node commits before a layer pass surfaced the
binding gap; Case III is more interlocking (three candidate frameworks sharing one candidate
structure + Claim 6.11 wiring the row matroid to `M(G̃_v^{ab})` + Claim 6.12's extensor-span
genericity), so the layer recon runs first. This is the **first recon pass** (docs-only, no Lean /
`\leanok` / blueprint): read the whole Lemma-6.10 argument against the primary source + the green
infra it bottoms on; the per-piece needs/supplies map + the open recon questions are recorded in
`notes/Phase22c.md` (its *First design-recon pass* + *open recon questions*), the canonical 22c log.

**Verified against the KT 2011 primary source (pdf pp. 34–45).** Lemma 6.10: `G` 2-edge-connected
minimal 0-dof, `|V| ≥ 3`, no proper rigid subgraph, (6.1) holds ⟹ a *nonparallel* panel-hinge
realization in 3-space at `rank R(G,p) = 6(|V|−1)` (`D = 6` at `d=3`). The one-row shortfall: a single
eq. (6.12) degenerate placement `p₁` (`p₁(vb) = q(ab)`, the `vb`-row reproducing the `e₀=ab`-row) is
block-triangular with `R(G_v^{ab},q)`, giving `rank ≥ (D−1) + D(|V∖{v}|−1) = D(|V|−1) − 1` — one
short (KT printed p. 680). The `D`-candidate argument supplies the missing row: KT build three
candidates `(G,p₁),(G,p₂),(G,p₃)` (pdf p. 37) and show one is full rank, via Claim 6.11 (the
redundant `(ab)i*`-row, eq. 6.23 `rank R(G_v^{ab}∖(ab)i*,q) = rank R(G_v^{ab},q) = 6(|V∖{v}|−1)`, off
Lemma 4.3(ii) + the IH — the combinatorial↔linear bridge to `M(G̃_v^{ab})`) and Claim 6.12 (if all
candidates fail, a nonzero `r ∈ ℝ⁶ ⟂` all extensors on `d+1` generic panels, which by the green
Phase-17 **Lemma 2.1** span `ℝ⁶` — contradiction; the degree-2 condition forces all candidates to
test the *same* `r`, eq. 6.44). General-`d` (Lemma 6.13, pdf p. 46) stays Phase 23.

**Scope cut settled** (`notes/Phase22c.md` *Sub-phase scope cut*): 22c = Case III at `d=3` (the crux);
the `d=3` assembly (`prop:rigidity-matrix-prop11` `hub` + `thm:theorem-55` flip + the
`case_I_realization`→`theorem_55_generic` Case-I wiring) is the **likely 22d, deferred** until 22c's
shape is clear (same defer-the-finer-cut discipline as 22a→22b+, 22b→22c+). **Next concrete commit:**
continue the recon (still docs-only) — settle the four open recon questions (candidate normal form vs.
three inlined copies; `d=3`-first; Claim 6.11's row-matroid bridge shape; Claim 6.12's "same `r`"
packaging) — *before* cutting the first Lean node. No exposition-ledger entry yet: the captured Case-III
ledger lines (`lem:case-II-realization`/eq. 6.12; Case III at large) already exist (`notes/BlueprintExposition.md`),
status stays `pending` (write at 22c close, once `sorry`-free).

### 1.26 Phase 22c recon, second pass — the candidate structure, the four open questions resolved, and the FIRST-CHUNK scope cut (2026-06-05)

Second (still docs-only, decision-support) recon pass, **re-read against the primary source**
(KT 2011 §6.4.1, pdf pp. 34–37 [candidate construction + sketch], pp. 44–45 [Claims 6.11/6.12
rigorous]). It (a) pins the shared candidate structure, (b) answers the four open recon questions
from §1.25 / `notes/Phase22c.md`, and (c) — folding in the user's fresh direction that Case III at
`d=3` *and* the `d=3` assembly may each need multiple phases — **re-cuts 22c's scope to the first
tractable chunk**, not all of `lem:case-II-realization` + `lem:case-III`.

**The shared candidate structure (verified, KT pp. 34–37).** No proper rigid subgraph + `d=3` ⟹
(Lemma 4.6) two *adjacent* degree-2 vertices `v, a`, with `N_G(v) = {a,b}`, `N_G(a) = {v,c}`. Both
`G_v^{ab}` and `G_a^{vc}` are minimal 0-dof (Lemma 4.8), and `G_a^{vc} ≅ G_v^{ab}` (the panel of `a`
in `(G_v^{ab},q)` plays the role of the panel of `v` in `(G_a^{vc},q_ρ)`, Fig. 6(b)(f)(g)). The IH
(6.1) supplies one generic nonparallel realization `(G_v^{ab}, q)` with `rank R = 6(|V∖{v}|−1)` (eq.
6.18). **All three candidates share this one `q`**: `(G,p₁)`/`(G,p₂)` are built on `(G_v^{ab},q)`
(eqs. (6.12)/(6.19), differing only in which of `va`/`vb` carries the degenerate `q(ab)` placement),
`(G,p₃)` on `(G_a^{vc},q_ρ)` (eqs. (6.31)/(6.32)), where `q_ρ` is `q` transported across the iso. So
the *shared data* parametrizing a candidate is `(q, the degenerate hinge choice, the free panel line
L ⊂ Π(·))`; the three differ only in which panel (`Π(a)`, `Π(b)`, `Π(c)`) the free line lives on.

**Open question 1 — candidate normal form: ABSTRACT a single candidate lemma, instantiate ×3.**
The three candidates are *not* three independent constructions: `p₁`/`p₂` are literally symmetric
(`a ↔ b`, KT eq. (6.19) "symmetric to Claim 6.9"), and `p₃` is `p₁` precomposed with the iso `ρ`.
Their row-ops are *identical* (KT performs them once for `p₁`, then says "the same analysis" for
`p₂`/`p₃`, p. 35). So the formalization should state the per-candidate row-op + `+(D−1)` argument
**once**, parametrized by `(degenerate hinge, free panel)`, and instantiate three times — KT's own
structure. The Claim-6.12 contradiction then quantifies over the three instances' residual normals
`r, r', r''` and uses the eq. (6.44) forcing (below) to identify them.

**Open question 2 — `d=3`-first: YES, build the `D=6`/3-candidate case concretely first.** KT itself
does §6.4.1 (`d=3`, three candidates) then §6.4.2 (general `d`, Lemma 6.13, a length-`d` chain); the
project follows that cut (general `d` stays Phase 23). The "candidate normal form" of question 1 is
the right *internal* abstraction even within `d=3` (it is what Lemma 6.13 later re-instantiates along
the chain), but the candidate *count* and the `(4 choose 2)=6` extensor span are concretely `d=3`.

**Open question 3 — Claim 6.11's row-matroid bridge: it routes through KT Lemma 4.3(ii) + the IH,
landing as a *redundant-row existence* fact `R(G_v^{ab}, q; (ab)i*, ·)` is a row-combination of the
others.** KT's redundant row comes from: in `M(G̃_v^{ab})`, at least one `ãb` fiber edge is *not* in a
base (Lemma 4.3(ii) — there are `D=6` parallel `ãb` copies but a base uses at most `D−1` of any single
fiber when… [the IH `def`-count]); the IH then converts that combinatorial non-base edge to a linear
row-dependency (eq. 6.24 / 6.43). The Lean bridge is the green Phase-19 `M(G̃)` ↔ row-independence
machinery (`matroidMG_indep_iff`, the `def = corank` bridge `thm:def-eq-corank`), but the *conversion*
"combinatorial non-base edge ⟹ a redundant rigidity row at the IH realization" is genuinely new analytic
content — it is the IH applied at the rigidity matrix, the hardest non-extensor step (KT calls it out
on p. 680). This is the **D-candidate crux**, not the first chunk.

**Open question 4 — Claim 6.12's "same `r`": it is eq. (6.44), and it FOLDS into the candidate normal
form's contradiction step, NOT a separate brick.** The forcing is: `r := Σ_j λ_(ab)j r_j(q(ab))` is the
residual normal of `M₁`/`M₂`; for `M₃` the residual is `Σ_j λ_(ac)j r_j(q(ac))`, and eq. (6.44) shows
`r = −Σ_j λ_(ac)j r_j(q(ac))` **because `a` is degree-2 in `G_v^{ab}`** (only `ab, ac` incident to `a`,
so the `a`-block of the row-dependency (6.43) has exactly two terms). So all three candidates'
singularity puts the *same* `r` in the orthogonal complement of the extensors on `Π(a)`/`Π(b)`/`Π(c)`
respectively; Claim 6.12 then takes four affinely-independent points `p₁ = Π(a)∩Π(b)∩Π(c)`, `p₂ ∈
Π(a)∩Π(b)∖Π(c)`, etc., and **Lemma 2.1** (`omitTwoExtensor_linearIndependent`, green, the `(4 choose
2)=6` 2-extensors of 4 aff.-indep. points span `ℝ⁶`) contradicts `r ≠ 0`. The extensor half maps onto
Phase-17's Lemma 2.1 *directly*; the residual-normal bookkeeping (eq. 6.44, the degree-2 forcing) is
the candidate-normal-form's shared `r`, so it does not need its own node — it is the glue between the
three candidate instances and the Lemma-2.1 application.

**The first-tractable-chunk cut (the load-bearing scope decision, folding in the user's direction).**
The recon partitions Lemma 6.10 into three strata of difficulty:
1. **The eq. (6.12) `+(D−1)` block-triangular placement** — `buildable`. `p₁(va) = L ⊂ Π(a)`,
   `p₁(vb) = q(ab)` reproduces the `e₀ = ab` row; column ops (KT eq. (6.16)) make `R(G,p₁)`
   block-triangular with `R(G_v^{ab},q)` a submatrix ⟹ `rank ≥ 5 + 6(|V∖{v}|−1) = D(|V|−1)−1`. This is
   the *direct* reuse of the green Phase-21b row infra (N7b-0/1/2/3 + `linearIndependent_sum_pinned_block`),
   the same machinery the eq. (6.12) warm-up in §3 Track B already names. **This is the first chunk** —
   it is the largest self-contained, green-infra-fed piece, and it produces the candidate scaffold the
   crux then completes.
2. **Claim 6.11 (the redundant `(ab)i*`-row)** — `research-shaped`, the **D-candidate crux**. The
   combinatorial↔linear conversion (Lemma 4.3(ii) ⟹ a redundant rigidity row at the IH realization).
   The single highest-risk node in Phases 22–23 (`notes/Phase22-realization-design.md` §4).
3. **Claim 6.12 (the extensor-span contradiction) + the candidate normal form + eq. (6.44)** — the
   assembly that turns "each candidate singular ⟹ `r ⟂` its panel extensors" + "same `r`" + Lemma 2.1
   into "some candidate is full rank". Bottoms on the green Lemma 2.1, but needs all three candidates'
   residual-normal data, so it composes *after* strata 1 and 2.

**Decision: 22c = stratum 1 (the eq. (6.12) `+(D−1)` placement) as the first sub-phase, with the
candidate-framework scaffold it sets up.** Strata 2–3 (the redundant-row crux + the candidate-normal-form
/ Claim-6.12 assembly) are **likely their own later sub-phase(s)** — name the *next* distinct sub-phase
when stratum 1's shape is clear, do NOT pre-commit its internal node list now (the same defer-the-finer-cut
discipline as 22a→22b+, 22b→22c+, and 22c→22d). 22c does **not** claim to land all of
`lem:case-II-realization` + `lem:case-III` in one phase. This matches both the user's explicit direction
("let's not try to cram too much into 22c") and the design-pass-first mandate: stratum 1 is the buildable
warm-up that exercises the placement + row infra on the `k=0` target and exposes the candidate structure,
*before* the genuinely-research-shaped crux is scheduled.

**Why this is the right first cut and not, e.g., the crux first.** The crux (stratum 2) is research-shaped
and its math-first decomposition is the natural target for a *dedicated* sub-phase (it is ~half of KT's
~12-page proof and the single highest-risk node). Stratum 1 is `buildable` from green infra and is a
*prerequisite scaffold* for strata 2–3 (the candidate frameworks, on which the residual-normal `r` and the
missing row are defined, are exactly the eq. (6.12)/(6.19)/(6.32) placements). Building the scaffold first
de-risks the crux's recon (it makes the candidate structure concrete in Lean) and gives a green, useful
`+(D−1)` lower-bound brick even before the crux lands. This is the same staging as Track A's "N6a first,
then the simple-case crux" and Track B's own "eq. (6.12) placement is the buildable warm-up; Lemma 6.10 is
the crux and the natural decompose-math-first target for a dedicated sub-session" (§3 Track B build order).

**Next concrete commit (post-this-recon).** With the four questions settled and the first-chunk cut made,
the next commit is the *first Lean node* of stratum 1 — the eq. (6.12) degenerate placement producing the
`+(D−1)` block-triangular lower bound, cut leaf-most-first against the green N7b-0/1/2/3 +
`linearIndependent_sum_pinned_block` infra. Re-recon stratum 1's node order at that build's open (it is
`buildable`, so a math-first decomposition is light, but confirm the count `5 + 6(|V∖{v}|−1) = D(|V|−1)−1`
closes from the named green inputs before scheduling — the honesty gate's second half). The crux (strata
2–3) gets its math-first decomposition when its sub-phase opens.

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
| **Claim 6.4 collapse transport (G3a, superseded)** | `PanelHingeFramework.rigidContract_rigidity_transport` | **GREEN-MODULO** (2026-06-05; the motion-space `∃`-seed form of Claim 6.4 / eq. (6.9), carried as `htransport`; superseded by the block-triangular reframe — kept as a library brick) | (none; superseded) |
| **Claim 6.4 rank transport (N-22b-1)** | `PanelHingeFramework.rigidContract_exterior_rank_transport` (`CaseI.lean`) | **GREEN-MODULO** (2026-06-05; the §1.16 exterior-projected-row form of Claim 6.4 / eq. (6.9), carries `htransport` = the single-placement projected surviving-row independence; feeds N-22b-2 packaging; axiom-clean, no `sorry`) | Case I composer (N-22b-3 wire-up) |
| **Claim 6.4 packaging (N-22b-2)** | `PanelHingeFramework.exists_rankPolynomial_of_rigidOn_linking_set_proj` (`CaseI.lean`) | GREEN (2026-06-05; the bounded `D∘panelRow` producer variant) | Case I composer (N-22b-3 wire-up) |
| **`prop:rigidity-matrix-prop11` `hub`** | carried as hypothesis (`:2527`) | RED (multi-commit, Phase-19 partition count) | Prop 1.1 only |

**Reading:** the entire device + witness-transfer + splice + count + N4
substrate is GREEN; **(G2) is now GREEN too** (2026-06-04,
`exists_generalPosition_polynomial`). The Case-I substrate is **almost** complete:
the **Case-I Claim-6.4 collapse transport** (G3a, `rigidContract_rigidity_transport`)
landed **GREEN-MODULO** 2026-06-05, carrying KT eq. (6.9) as the explicit
hypothesis `htransport` (the relabel-induced normal change makes it irreducible — the
linking-edge lever fails). The composer that consumes it (`case_I_realization`) was
briefly valid-but-VACUOUS (commit c1ef55a, false `hpinc`); the **§1.12 fix has now
landed** — the asymmetric coupling `hasGenericFullRankRealization_of_couple_asymm_ofNormals_set`
removes the contraction leg's rank-polynomial round-trip, deletes `hpinc`, and supplies
the contraction rigidity directly from the `∀`-over-GP-seeds conjunct `htransportGP`
(KT eq. (6.9)); the composer is now honest GREEN-MODULO the Claim-6.4-only bundle,
axiom-clean. The N6b/N6c couplings are an
assembly of green bricks *given both legs as `≤ G` rigid `ofNormals`*; G3a supplies the
second such leg's *rigidity* (modulo `htransport` = KT Claim 6.4), but the **symmetric**
body-set coupling cannot consume it without `hpinc` — hence the asymmetric replacement.
The remaining *missing* analytic content across the layer is the Case-I contraction
transport (G3a's `htransport`, re-entering via `lem:case-III` / 22b+) and the
**Case-III missing row** via Lemma 2.1 (Track B, 22b+). (G1) was not a missing brick
— it was the motive decision of §1, dissolved by the two-motive split.

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
