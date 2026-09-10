## §(K-clos) — the polarity over an algebraically closed field: generalizing it is **bookkeeping**, one of §(K-σ)'s two `ℝ`-refutations **REVERSES**, the route it buried stays buried **for a new and field-neutral reason**, and `hK` splits cleanly into *characteristic 0* (all of it equivalent to the `ℂ̄` case) and *characteristic p*

Read against §(K-σ) — this section extends its *Field scope* three-way
classification rather than restating it, and corrects it in two places. Notation
inherited from §(K-Λ) *Standing notation*; `⋆` is the project's polarity
`screwComplementIso` (`Molecular/Molecule/Duality.lean:69`), `Q ⊂ P³` its fixed
quadric `{x ⬝ᵥ x = 0}`, and `Λ²₊`, `Λ²₋` the `±1` eigenspaces of `⋆` on `Λ²K⁴`.

**Status, stated before the mathematics.**

- **Settled — the polarity generalizes, and the cost is one section.** **(AC-1)**.
  Nothing is obstructed, characteristic 2 included *for the definition*. The
  general-`K` **transport** the route needs is not a new object either: it is
  already in tree as `BodyHingeFramework.mapSupport`
  (`Molecular/GenericLift/HingeGeneric.lean:462`), with its rank lemma
  (`:544`). Source-verified; **no compiler witness** was taken (the dispatch
  carried a no-Lean constraint), and a ~20-line typecheck spike would settle it
  outright.
- **Settled — one of §(K-σ)'s two `ℝ`-refutations REVERSES.** **(AC-2)**,
  **(AC-3)**. Over `ℂ̄` σ-fixed pencil configurations **exist**; they are exactly
  the `P¹ × P¹` grids on `Q`; and — refuting the *degeneracy* framing §(K-σ)
  *Step σ6* attaches to them — they are **nondegenerate** (all four
  `IsNondegPencilRealization` conjuncts, every star of rank 3) and **reach the
  Tay target**, at all **15 tight** shapes of the pinned pool (all eight
  §(K-flank) flank shapes among them) and at the (K-res) inhabitant `W19`,
  which is rigid but *not* count-tight.
- **Settled — but §(K-σ)'s VERDICT survives, on a new and field-neutral
  argument.** **(AC-5)**: at a σ-fixed seed `σu = u`, so **route σ *is* route A**
  — the two uniform-failure criteria coincide as subspace conditions. A
  σ-equivariant seed recipe buys route σ's obligation 1 for free and deletes
  route σ in the same stroke. *"σ-equivariant seed recipes are dead" stands; its
  stated reason (`ℝ`-definiteness) does not port and is replaced by this one.*
- **REFUTED as a class statement; OPEN only on the tight stratum.** **(AC-6)**:
  the same grids are a **combinatorial recipe** — a ruling 2-colouring of `E(G)`
  — for target-rank nondegenerate pencil realizations. Over a **pinned 21-shape
  pool** it reaches the Tay target at **15/15 tight** shapes (all eight §(K-flank)
  flank shapes among them) and at `W19`, and **fails at three**. One of the three,
  the bare odd cycle **`C11`**, satisfies *every* hypothesis `hK` carries, so the
  class statement is **refuted, not open** — with the mechanism identified and
  complete: *no admissible colouring exists iff `G` has a bare odd cycle
  component*, a **parity** obstruction, which a tight shape cannot have. The other
  two misses are at shapes outside `hK`'s habitat, and one of them is *correct
  behaviour* (the shape has no nondegenerate pencil realization at all). What is
  left open is the narrow question — does the recipe reach the target at every
  **tight** shape — and only that; if it did it would discharge `hK` there
  **directly, with no escape route at all**. This arc's record says the base rate
  for such a question is "no" (`pencil/strategy.md` §2.3).
- **Settled — the field-generality of `hK` factors.** **(AC-7)**: `hK` over
  `ℂ̄` **implies** `hK` over every infinite field of characteristic 0, `ℝ` and
  `ℚ` included. Working over `ℂ̄` is therefore **not** a weakening; it is the
  strongest characteristic-0 instance. The residual content of the headline's
  `[Infinite K]` is **positive characteristic only**.
- **Settled — characteristic 2 is a genuine exception, but only to the
  *geometry*.** **(AC-8)**: `x ⬝ᵥ x = (∑ xᵢ)²` there, so `Q` degenerates to a
  double plane, and `⋆` is unipotent rather than diagonalizable, so `Λ²` does
  not split. **(AC-1)** is unaffected; **(AC-2)**–**(AC-6)** all need `char ≠ 2`.

### Step Z0 — the question, and what "over `ℂ̄`" is modelled by

Three sub-questions, from the dispatch: does the polarity generalize; do
§(K-σ)'s two `ℝ`-refutations reverse; and is the conjecture easier over `ℂ̄`.

**The model.** All computation is over the **Gaussian rationals `ℚ(i) ⊂ ℂ`**,
the smallest extension of `ℚ` in which `∑ xᵢ² = 0` has a nonzero solution — and
that single fact is the *whole* difference the dispatch is about. The driver uses
the harness's **own** `⋆` (`repin.hodge_star`), its **own** rigidity-row builder
(`hybrid_gates.build_rigidity_extensors`) and its **own** nondegeneracy checker
(`flanks.nondeg_conjuncts`), unchanged; only the scalar field is enlarged
(`closure.py`'s `Gauss`, exact, no floating point). An **existence** statement
verified over `ℚ(i)` is an existence statement over `ℂ̄`; a **non**-existence
statement over `ℚ(i)` is not, and none is claimed.

### Step Z1 — (AC-1): the polarity generalizes; the general-`K` transport is already landed

> **(AC-1)** *(proven-informally from the landed source; no compiler witness).*
> `screwComplementIso` has a verbatim general-`K` companion. Both ingredients
> are already field-general in tree, all the helper inputs of the four
> `ℝ`-fixed theorems are field-general, and the missing transport is **not**
> missing.

Verified declaration by declaration (each opened, not taken from a docstring):

| ingredient | field | source |
|---|---|---|
| `ScrewSpace (K) [Field K] (k)` | general | `Molecular/RigidityMatrix/Basic.lean:117` |
| `ScrewSpace.equivExteriorPower (K) [Field K] (k)` | general | `…/Basic.lean:185` |
| `complementIso {j} (hj : j ≤ k+2)` | general, **no characteristic hypothesis** | `Molecular/Meet.lean:479` |
| `structure BodyHingeFramework (K) [Field K] (k) (α β)` | general | `…/Basic.lean:310` |
| `BodyHingeFramework.mapSupport (M : ScrewSpace K k ≃ₗ[K] ScrewSpace K k)` | **general** | `Molecular/GenericLift/HingeGeneric.lean:462` |
| `finrank_span_rigidityRows_mapSupport` | **general** | `…/HingeGeneric.lean:544` |
| `mem_span_of_dotProduct_perp_pair` | general | `Pencil/Statement.lean:133` |
| `dotProduct_eq_zero_of_mem_span` | general | `Pencil/Statement.lean:114` |
| `exists_extensor_eq_panelSupportExtensor` | general | `AlgebraicInduction/PanelLayer.lean:649` |
| `panelSupportExtensor`, `panelSupportExtensor_ne_zero_iff`, `normalsJoin` | general | `PanelLayer.lean:233, 244, 67` |
| `extensor_ne_zero_iff_linearIndependent` | general | `Molecular/Extensor.lean:343` |
| `finrank_toDualPerp_pair_eq` | general | `Molecular/Meet.lean:1562` |

**(a) The definition is a writing choice.** `screwComplementIso :=
equivExteriorPower ≪≫ₗ complementIso ≪≫ₗ equivExteriorPower.symm`; every factor
is `[Field K]`-general, so the composite typechecks verbatim with `K` for `ℝ`.
**Nothing in it uses definiteness** — `complementIso` is built from the volume
form `screwAlgebraTopEquiv` and the basis pairing `Pi.basisFun.toDual`
(`Meet.lean:88`), and the pairing is nondegenerate over **any** field because its
Gram matrix is the identity. Definiteness is used nowhere in the construction and
is not available over `ℂ̄`; only nondegeneracy is, and only nondegeneracy is
needed.

**(b) Characteristic 2 does not obstruct the definition.** `complementIso` is
landed at `[Field K]` with **no** characteristic hypothesis, so it compiles in
char 2; `⋆² = (−1)^{p(N−p)} = (−1)^4 = +1` at `p = 2`, `N = 4` in every
characteristic. What char 2 *does* break is the geometry — *Step Z8*.

**(c) The transport is already general — this corrects §(K-σ)'s pricing.**
§(K-σ) *Field scope* counts "exactly five declarations in `Pencil/` fix `ℝ`",
which is **correct as stated** (`Pencil/Statement.lean:166, 185, 216, 258, 665`;
`Pencil/Arms.lean`'s only `ℝ` is in prose — re-verified this pass). But the
*machinery* those theorems are phrased in — `BodyHingeFramework.mapExtensor` and
its 19-declaration API in `Molecular/Molecule/ProjectiveInvariance.lean` — is
**also `ℝ`-fixed**, and route σ's statement is literally about
`F.mapExtensor screwComplementIso`. That looks like a much larger bill than "one
section". **It is not**, because `mapExtensor` and `mapSupport` are the *same*
construction at two field generalities (`mapSupport F M` has
`supportExtensor e := M (F.supportExtensor e)`, exactly `mapExtensor`'s field),
and `mapSupport` is general-`K` **with its rank lemma**. So the general-`K`
statement is phrased through `mapSupport` and `ProjectiveInvariance.lean` needs
no generalization at all.

**(d) The precedent §(K-σ) cites is exactly right, and stronger than it says.**
`Pencil/Arms.lean`'s W3-L4 section header records the same mismatch verbatim and
supplies "the `K`-level transport, built on the change-of-screw-coordinates
machinery (`BodyHingeFramework.screwEquivOfLinearEquiv`, `mapSupport`)". Note the
scope: `screwEquivOfLinearEquiv g` covers **collineations** (automorphisms of
`K⁴`); the polarity is a **correlation** and is *not* of that form, so the W3-L4
section does not already contain the polarity. `mapSupport` does cover it.

**Net bill for a general-`K` polarity:** one `def` (`Duality.lean:69`), one
extensor-level bridge (`Statement.lean:166`), two predicate transports (`:185`,
`:216`), and one self-duality theorem (`:258`) restated with `mapSupport` in
place of `mapExtensor`. Every input is already general. **No new mathematics.**

*Confidence: proven-informally, source-level. Not compiler-checked.*
*What would change this: a typecheck spike that fails — most plausibly on an
instance-resolution or `rfl` step in `screwComplementIso_lineExtensor` /
`screwComplementIso_mk_extensor`, both of which close by `rfl` at `ℝ`. This is
the one claim in this section whose right instrument is a 20-line scratch
`.lean`, and the dispatch's no-Lean constraint is why it was not taken.*

### Step Z2 — (AC-2): the σ-fixed locus over `ℂ̄` is the `P¹ × P¹` grid on the fixed quadric

A pencil configuration is **σ-fixed** in the sense §(K-σ) *Step σ6* uses:
`normal_v ∝ point_v` for every body (projectively fixed — the hinge extensors are
then `⋆`-eigenvectors up to sign, which is all the predicate and the rank see).

> **(AC-2)** *(proven; driver leg `--fixed` AC-C0)* Over a field with isotropic
> vectors, a σ-fixed pencil configuration is exactly the following. Every body
> point lies on the fixed quadric `Q = {x ⬝ᵥ x = 0}`; adjacent body points are
> conjugate; hence **every hinge line lies on `Q`**. Writing `Q ≅ P¹ × P¹` by
> its two rulings and `p(s:t ; u:v)` for the corresponding point,
>
> `p ⬝ᵥ p′ = 2 · (s t′ − s′ t) · (u v′ − u′ v)`,
>
> so **two points of `Q` are conjugate iff they share a ruling parameter**. A
> σ-fixed pencil configuration is therefore a map `V(G) → P¹ × P¹` in which
> adjacent bodies agree in exactly one coordinate: a **grid**. Each edge is
> labelled by the ruling its hinge lies in, and — the reason this is a *finite*
> combinatorial object — the hinge screw of a ruling-A edge lies in `Λ²₊` and of
> a ruling-B edge in `Λ²₋`.

*Proof of the last clause.* A line `ℓ ⊂ P³` lies on `Q` iff `ℓ ⊆ ℓ^⊥`, and
`dim ℓ = dim ℓ^⊥ = 2`, so iff `ℓ = ℓ^⊥ = σ(ℓ)`: **the lines on `Q` are exactly
the `⋆`-fixed points of the Klein quadric**, i.e. the decomposable vectors of
`Λ²₊ ∪ Λ²₋`. Each eigenspace is 3-dimensional and `ℚ`-rational, they are
`⬝ᵥ`-orthogonal to each other (`⟨x,⋆y⟩ = ⟨⋆x,y⟩` and `⋆x = x`, `⋆y = −y` give
`2⟨x,y⟩ = 0`), and on each the ambient form restricts to `2(α²+β²+γ²)` — a smooth
conic, **empty over `ℝ`** (definiteness: this is *Step σ1(a)*'s and *Step σ6*'s
argument, seen from the Plücker side) and a `P¹` over `ℚ(i)`. ∎

**So §(K-σ) *Step σ6*'s structural sentence is exactly right and its scope is now
sharp**: "a *symmetric* correlation forces every body point onto the fixed
quadric and every hinge line to lie on that quadric (a union of two
one-parameter rulings)". That is (AC-2). What *Step σ6* got wrong is what
follows from it — see *Step Z3*.

**Two `ℝ`-verdicts of §(K-σ), re-classified.** *Step σ1(a)*'s refutation of the
**literal** intertwining question also reverses: it needs `pt(a)` self-conjugate,
i.e. `pt(a) ∈ Q`, which over `ℝ` forces `pt(a) = 0` and over `ℂ̄` is simply a
codimension-1 condition on that body, satisfied by **every** body of a σ-fixed
configuration. So over `ℂ̄` the literal intertwining is not impossible; it is the
defining condition of the grid locus. The **covariant** statement *Step σ1(b)* is
field-neutral and unaffected.

### Step Z3 — (AC-3): the grids are nondegenerate and reach the Tay target — *Step σ6*'s "degenerate" is REFUTED for the symmetric correlation

§(K-σ) *Step σ6* priced the σ-fixed locus as *"worse than empty, it is
degenerate"*. For the **null** (symplectic) correlation that is proven there
(every hinge in a linear line complex, a self-stress per cycle, measured deficit
exactly 1 at 6/6 on tight `C₆`). For the **symmetric** correlation — which is the
project's polarity, and the only one at issue over `ℂ̄` — the degeneracy was
asserted, never measured. It is **false**.

> **(AC-3)** *(exact, over `ℚ(i)`; driver leg `--fixed`)* At the tight control
> `ds-K4` (`|V| = 16`, `|E| = 18`, target 90) there is a σ-fixed pencil
> configuration that satisfies **all four `IsNondegPencilRealization` conjuncts**
> (checked by the canonical `flanks.nondeg_conjuncts`), has **every closed-star
> rank 3**, and has body-hinge rank **exactly 90 = the Tay target**. Twelve of
> the 64 ruling colourings do. *(The parenthetical "the `plane_basis`
> genericity guard" stood after "closed-star rank 3" until 2026-08-06; it is
> one of the four claims F13 falsified, and (AC-9) below is what it was
> hiding.)*

The confinement of (AC-2) is real; it simply **costs nothing**. Intuition for
why: the pencil condition *asks* each body's hinges to be concurrent and coplanar,
and at a point of `Q` the tangent plane `T_pQ = p^⊥` meets `Q` in exactly the two
ruling lines through `p` — so the pencil conditions are satisfied **by
construction**, not by accident. That is the same fact that makes the locus
non-empty and the same fact that caps each body at two distinct hinge directions.

**And that cap has a consequence nobody drew until the guard was adopted.**

> **(AC-9)** *(new 2026-08-06, slice S2; proven from the cap above, measured at
> every configuration `closure.py` builds)* **At a σ-fixed pencil configuration,
> every body of degree `≥ 3` carries a COINCIDENT HINGE LINE** — two of its
> hinges are projectively the same line, so the body is a free rotor about it.
> *Proof:* at `p ∈ Q` the tangent plane meets `Q` in exactly **two** lines
> through `p`, and every hinge at that body is one of them; a body of degree
> `≥ 3` has at least three hinges, so by pigeonhole two coincide. *Measured:*
> at the (AC-3) witness the coincidences are exactly one per hub —
> `(0, 4, 6)`, `(1, 12, 5)`, `(2, 11, 14)`, `(3, 15, 9)` — and over `--sweep`'s
> exhaustive 64 colourings the composite guard `repin.star_generic` accepts
> **0 of 64**, asserted in the driver.

What (AC-9) does and does not do. It does **not** touch (AC-3): all four
`IsNondegPencilRealization` conjuncts still hold, the closed-star ranks are
still 3, and the rank is still the Tay target — and those are the predicates
`hK` is quantified over, so *Step σ6*'s "the fixed locus is degenerate" stays
**refuted as a statement about that predicate**. What it does is tell you what
"nondegenerate" is worth here: the σ-fixed witnesses are **never generic** in
the harness's composite sense, so no rate, no genericity argument and no
"a σ-fixed seed is a typical seed" reading may be built on them — and *Step
σ6*'s instinct was right in a sense it did not state, namely the free-rotor
one, which costs no rank and violates no conjunct. It also explains, without
any appeal to sampling, why (AC-6) fails as a class statement whenever a body
has degree `≥ 3`.

### Step Z4 — (AC-4): the `⋆`-eigen decoupling, and the three conditions target rank forces

> **(AC-4)** *(proven, and driver-tested as an equality at every sampled
> configuration)* At a σ-fixed configuration the body-hinge rigidity matrix
> **decouples** over `Λ²₊ ⊕ Λ²₋` into two independent systems on `3|V|`
> variables each:
> `rank = rank₊ + rank₋`, with `rankₑ ≤ 3|V| − 3`.
> For an edge whose hinge lies in `Λ²₊`, the relative-screw condition splits into
> **3** equations in the `−` block (`m_u = m_w` there) and **2** in the `+` block
> (`m_u − m_w` parallel to the hinge); and symmetrically. Consequently, at a
> **tight** shape (`5|E| = 6(|V|−1)`), reaching the target forces all three of
>
> (i) **balance** `|E_A| = |E_B| = |E|/2`;
> (ii) **both ruling classes are forests** (a cycle in one class makes 3
> equations of the *other* block dependent);
> (iii) **both blocks isostatic** at `3|V| − 3`.
>
> and, separately, `IsNondegPencilRealization`'s conjunct 4 at a degree-2 body
> forces the two colours at that body to **differ** — so the colouring
> **alternates along every branch**, i.e. it is one free bit per branch.

*Why (i).* Summing the two blocks' equation counts gives `5|E|`, which at a tight
shape equals `6|V| − 6` exactly, so both blocks must be at their maxima with
**zero slack**: `2|E_A| + 3|E_B| = 3|E_A| + 2|E_B| = 3|V| − 3`, whence
`|E_A| = |E_B|`. *Why the alternation.* At a degree-2 body `v` with neighbours
`u, w`, if both edges took the same ruling then `pt(v), pt(u), pt(w)` would be
three points of one line — `LinearIndepOn point (closedNbhd v)`
(`Motive.lean:115`, imposed exactly at non-hubs) fails. *Why star rank 3 at a
hub.* A hub's neighbours lie on the ≤ 2 ruling lines through it; if all its edges
take one ruling, the whole closed star is collinear and the panel is not
determined.

Driver: at `ds-K4`, all **64** colourings satisfy `rank = rank₊ + rank₋`; every
target-rank colouring is balanced with both classes forests and both blocks at
`3|V| − 3 = 45`; every unbalanced colouring falls short. The identity
`rank = rank₊ + rank₋` is a *test*, not a restatement: the two blocks are built
from the eigen-structure and the full matrix from
`hybrid_gates.build_rigidity_extensors`, independently.

**Note the shape of the residual system.** Solving the `E_B` equations out of the
`+` block contracts every `E_B`-component to one node and leaves a **direction
network** in `K³` — place the `E_B`-components as points so that, for each
`E_A`-component, the points it meets are collinear in that component's ruling
direction. That is a 3-dimensional parallel-drawing / incidence system, with the
directions constrained to a conic exactly as body-hinge screws are constrained to
the Klein quadric in `K⁶`. Its generic combinatorics is the natural target of a
uniformity proof and is **not attempted here**.

### Step Z5 — (AC-5): at a σ-fixed seed **route σ IS route A** — the field-neutral replacement for *Step σ6*'s `ℝ` kill

This is the answer to the dispatch's sub-question 2 as posed ("would it revive
the σ-equivariant-recipe route §(K-σ) buried?"), and the answer is **no for route
σ**, for a reason that has nothing to do with the field.

> **(AC-5)** *(proven; driver leg `--collapse`, 32/32)* Let `u` be a σ-fixed
> hard-stratum seed. Then `σu = u`, and for **every** body `b`
>
> `r ⊥ Λ²Π̂(b)` **⟺** `r ⊥ α_{pt(b)}` as conditions on the residual load `r`,
>
> i.e. route A's uniform-failure criterion at `b` (§(K-tight) *Step 2.4*) and
> route σ's (§(K-σ) (σ6)) **coincide**. Route σ contributes no escape direction
> route A does not already contribute.

*Proof.* σ-fixedness gives `Π(b) = pt(b)^⊥`, hence `Λ²Π̂(b) = β_{pt(b)^⊥} =
⋆ α_{pt(b)}`. The decoupling (AC-4) puts the 1-dimensional `R_a` inside one
eigenspace, so `⋆r = εr` with `ε = ±1`. Then, for every `a ∈ α_{pt(b)}`,
`⟨r, ⋆a⟩ = ⟨⋆r, a⟩ = ε⟨r, a⟩`, so `r ⊥ ⋆α_{pt(b)} ⟺ r ⊥ α_{pt(b)}`. ∎
Equivalently in §(K-Λ)'s coordinates: `C(M) = ⋆C(bc)` there, and
`★r ∥ C(M) ⟺ ★r ∥ C(bc)` once `★r ∝ r`. The driver checks the two conditions as
**subspaces** of each eigenspace (a basis-wise check would not settle an iff),
16 bodies × 2 eigenspaces, 32/32.

**Reading, and the correction it makes.** A σ-equivariant seed recipe would make
§(K-σ) *Step σ5* obligation 1 — the σ-nondegeneracy of the transported seed, the
route's single crux — **free by construction**, since `σu = u` and `u` is
nondegenerate by hypothesis. That is exactly the revival the dispatch asked
about, and it is real. But it is worthless: at the same seeds the route it would
discharge **degenerates onto route A**. §(K-σ) *Step σ6*'s own sentence *"route σ
does not use equivariance — it applies `σ` once to move to a **different** seed,
which is exactly why it escapes this wall"* is, with (AC-5), upgraded from a
remark to the **reason**: route σ's content is precisely `σu ≠ u`, so the fixed
locus is the one place it cannot help. **The verdict "σ-equivariant seed recipes
are DEAD" survives algebraic closure; the `ℝ`-definiteness argument for it does
not, and (AC-5) replaces it.**

### Step Z6 — (AC-6): the grids as a **direct** recipe — **REFUTED as a class statement over `hK`'s habitat**, with the mechanism identified, and a partial recipe left standing

The grids are not useless — they are just not useful *to route σ*. What they are
is a **combinatorial recipe for target-rank nondegenerate pencil realizations**:
input a ruling 2-colouring of `E(G)`, output an exact configuration. That is the
shape of thing `pencil/strategy.md` §2.2 says the whole arc lacks, and it exists
only over a field with isotropic vectors. **It is not class-uniform, and the same
run that produced it produced the counterexample.**

**The pool, pinned.** Every figure below is over exactly the **21** shapes of the
`--shapes` and `--flanks` tables and nothing else; the aggregate is printed by
`--pool` from those same rows, so it cannot drift from them. (This is the
`63/63`-across-inconsistent-pools defect, `notes/dispatch-log.md`; the aggregate
is not hand-counted here.) Note `def = 0` and *count-tightness*
(`5|E| = 6(|V|−1)`) are **different** predicates and the pool separates them.

> **(AC-6)** *(measured, `--shapes` / `--flanks` / `--pool` / `--parity`)*
> **REFUTED as a class statement over the habitat `hK` is quantified over**, and
> **OPEN, with no identified obstruction, on the tight stratum**. Over the pinned
> 21-shape pool:
>
> | group | at the Tay target |
> |---|---|
> | **tight** (`def = 0` **and** `5\|E\| = 6(\|V\|−1)`) | **15 / 15** |
> | rigid but **not** count-tight (`def = 0`, excess 2) — `W19` alone | **1 / 1** |
> | **not rigid** (`def > 0`) | **2 / 5** |
> | overall | 18 / 21 |
>
> The 15 tight shapes are `ds-K4`, `ds-(K5−M)`, θ(3,4,5), θ(4,4,4), θ(3,3,6),
> θ(2,4,6), θ(1,5,6), and **all eight** §(K-flank) named flank shapes — `K5`
> 5-chromatic, 6v11e, `K222`, `K5+v`, wheels `W5`/`W7`, the menu-blocked `K4`,
> `P21` — i.e. every shape *no* class-uniform mechanism of this arc covers. The
> 16th `def = 0` shape is the **(K-res)** inhabitant `W19`, also at the target.
>
> **The three misses, attributed by the driver against `hK`'s own hypotheses:**
>
> | miss | `def` | cause | `hnoRigid` | feasibility-necessary | in `hK`'s habitat? |
> |---|---|---|---|---|---|
> | θ(1,2,9) | 3 | the colouring forces two bodies to **coincide** | ✗ | ✗ | **no** |
> | θ(2,3,7) | 1 | all 4 legal colourings give rank 58 vs target 59 | ✗ | ✓ | **no** |
> | `C11` (bare odd cycle) | 5 | **no proper alternation colouring exists** | ✓ | ✓ | **YES** |
>
> `C11` is the counterexample: simple, 2-edge-connected, `hnoRigid`, `\|V\| ≥ 5`,
> with a degree-2 body — every hypothesis `hK` carries — and the construction
> does not merely fall short there, it **does not exist**.

**The mechanism at `C11` is parity, and it is completely characterized.** An
alternation chain closes into a cycle only if every body along it has degree 2,
i.e. only inside a component of `G` that *is* a cycle, and that cycle is odd
exactly when the component has odd length. So:

> **no admissible ruling colouring exists ⟺ `G` has a bare odd cycle component.**

Driver `--parity`: over `C3 … C14` the shapes with no admissible colouring are
exactly `{3,5,7,9,11,13}`, and all **19** non-cycle shapes of the pool admit one.
The two `θ` misses are **not** parity — one is a coincidence of bodies, one a
rank shortfall — and both sit at shapes `hK` never sees. **θ(1,2,9)'s miss is
correct behaviour, not a defect**: its length-1 and length-2 branches form a
triangle with two hubs, which `not_pencilNondegFeasible_of_triangle_two_hubs`
already forbids, so it has **no** nondegenerate pencil realization at all,
σ-fixed or otherwise.

**What survives, stated so it cannot be over-read.** A **partial** recipe: at
every shape of the pool that `hK` actually quantifies over, the construction
reaches the target; the single in-habitat failure is a bare odd cycle, which is
an `index ≥ 1` habitat already discharged by the corank stratification (gap map,
*the arc in one paragraph*) and **cannot** be a tight shape, since a tight shape
has hubs. So the refutation is real, mechanistically understood, and **does not
transfer to the tight stratum, where (K-tight) lives**. That leaves exactly one
live question, and it is the *narrow* one:

> **Open.** Does an admissible colouring reaching the Tay target exist at *every*
> **tight** class shape? Measured: yes at 15/15. No obstruction identified.

**What that narrow question would be worth, stated exactly.** `hK`'s conclusion
(`Escape.lean:555`) is `∃ hubSel q s`, `|s| = 6(|V|−1) − def`, with
`pencilRow hubSel G.endsOf q` linearly independent on `s`: *the pencil rigidity
matrix at some chart seed has rank ≥ the target*. It does **not** require the
realization to be nondegenerate. A uniform recipe delivering a target-rank
realization at `G` **in the chart's image** would therefore discharge `hK` on the
tight stratum **directly — no escape route, no split, and no use of the inductive
hypothesis `HasGenericPencilRealization K 3 (G.splitOff …)`**.

**Chart-image membership — argued, not verified.** At a hub `v`,
`pencilChartNormal` reads the free seed and `pencilChartPoint v` is
`cross₃` of the hub-slot normals of `closedHubNbhd v` padded by free fills, so it
realizes *any* point of `v`'s panel; the grid asks for `point_v = normal_v`, legal
precisely because `pt(v) ⬝ᵥ pt(v) = 0` on `Q`. At a non-hub `v`,
`pencilChartNormal v = cross₃` of the closed-neighbourhood slot points, which is
`pt(v)` exactly when the star has rank 3 — which the driver asserts. So the grid
looks chart-realizable. **This is a prose argument against the chart definitions
(`Engine.lean:154–235`, `Chart.lean:393–412`), not a compiler-checked one**, and
it is the second place a small Lean spike is the right instrument.

**Three reasons to distrust even the narrowed question.** (1) The isostaticity of
the two contracted direction networks is **measured, never proven**, and it is
exactly the "rank condition becomes combinatorial" step `pencil/strategy.md` §2.2
identifies as this arc's recurring failure. (2) The flank rows probe only the
**first 6 filter-passing colourings per shape** — the `hit` column there
*saturates* at 6 and is **not** a fraction of `pass`; the load-bearing column is
`best`. A full census was run only at `ds-K4` (64/64 colourings) and in
`--shapes` (all colourings, ≤ 8 alternation chains). (3) 15 tight shapes is a
small pool, and this arc's record is that every uniform claim so far has been a
negative (`pencil/strategy.md` §2.3) — the base rate says the tight-stratum
answer is "no" and the obstruction has simply not been probed for yet.

*Confidence: **refuted** as a class statement over `hK`'s habitat (one exhibited
in-habitat shape, one identified mechanism, both driver-backed). On the tight
stratum — **superseded by §(K-grid)** (2026-08-06, direction T): the census ran
(907/907, no kill), the direction-network hope as worded here is refuted
((GR-2)) and corrected to two proven counting families ((GR-3)/(GR-4)), and the
residual — since direction G (Steps G8–G13) — is **(GR-10)** alone,
geometry-free ((GR-9) discharging the geometry; (GR-4) refuted-as-stated and
repaired off the critical path).*
*What would change this: see §(K-grid)'s own "what would change this" — the
tight-stratum question is owned there now; the habitat-level refutation (`C11`)
is permanent.*

### Step Z7 — (AC-7): `hK` over `ℂ̄` **implies** `hK` over every infinite characteristic-0 field

This is the dispatch's sub-question 3, and the answer inverts the expected sign:
over `ℂ̄` the statement is not weaker, it is **at least as strong**.

> **(AC-7)** *(proven; source-level, no driver)* Let `K ⊆ L` with `K` infinite.
> Then **`hK` at `L` implies `hK` at `K`**. In particular `hK` over `ℂ`
> implies `hK` over `ℝ`, `ℚ`, `ℚ̄`, every number field and every infinite
> subfield of `ℂ`; and since for fixed finite `α, β` the statement is a
> first-order sentence in the language of rings, `hK` over one algebraically
> closed field of characteristic 0 gives it over all of them, hence over
> **every infinite field of characteristic 0**.

*Proof.* Three observations, each verified against the landed statement.
(i) `hK`'s **antecedent** base-changes upward: `HasGenericPencilRealization K 3 G′`
is a conjunction of equalities, non-vanishings and `LinearIndependent`s at an
explicit configuration, all preserved by `K ↪ L` (matrix rank does not change
under field extension). (ii) `hK`'s **conclusion** existentially quantifies
`hubSel` and `s`, which are **field-free**, and a seed `q : α × Fin 4 × Fin 4 → K`
subject to `LinearIndependent K (pencilRow hubSel G.endsOf q)` on the finite `s` —
i.e. the non-vanishing of **some** `|s| × |s|` minor. (iii) That minor is a
polynomial in `q` with **coefficients in the image of `ℤ → K`**: the chart's point
and normal polynomials are `cross₃Poly` = `Matrix.det` of rows built from seed
variables and `Pi.single i 1` (`Engine.lean:117–119, 154, 207`), and `pencilRow`
is `hingeRow ∘ annihRow` of `extensor ![·,·]`, a `2 × 2` minor (`Engine.lean:318`).
So: given `hK` at `L`, apply it to the base-changed antecedent, get `q₀ ∈ L^N`
with `P(q₀) ≠ 0` for some ℤ-coefficient minor `P`; hence `P ≢ 0` as a polynomial;
hence `P ≢ 0` over `K`, whose prime ring contains the same coefficients; hence,
`K` being infinite, some `q ∈ K^N` has `P(q) ≠ 0`, and the same `hubSel`, `s`
work. ∎

**Three consequences, stated plainly.**

1. **Descending from `ℂ̄` to `ℝ` costs nothing** — *provided what you produce is a
   non-vanishing certificate for a `ℤ`-defined polynomial on the chart*, which is
   what the chart's **totality** (a free seed, no chart-image side condition —
   §(K-σ) *Step σ5* repair (c), first bullet) makes automatic. The dispatch's
   caution ("a complex realization need not be real") is correct about
   *realizations* and irrelevant to *`hK`*, because `hK` quantifies a seed over a
   free affine space, not a point of a variety with no real points. **(AC-6)'s
   `ℚ(i)` witnesses therefore already certify target rank over `ℝ` and `ℚ`** — a
   conclusion §(K-flank) *F2* reaches independently by direct `ℚ`-sampling, which
   is a useful consistency check on (AC-7) rather than a new result.
2. **The converse fails, and this is the asymmetry that matters.** `hK` at `ℝ`
   does **not** give `hK` at `ℂ`: a graph can have a `ℂ`-generic pencil
   realization and no `ℝ`-one, and then the `ℝ`-statement is silent about it. So
   **route σ discharged at `ℝ` closes `hK` at `ℝ` only**, while a proof over `ℂ̄`
   closes all of characteristic 0. If a field must be chosen, `ℂ̄` is the correct
   one — the opposite of the usual "algebraically closed = easier = weaker"
   reflex. (§(K-σ) *Step σ5*'s "instantiate the headline at `ℝ` first" is
   therefore the **narrowest** of the available options, not merely *a*
   narrowing.)
3. **The residual content of `[Infinite K]` is positive characteristic, and only
   that.** By (AC-7) the whole characteristic-0 family collapses to one
   statement. For char `p` the same minor `P` must be non-zero **mod `p`**, which
   is a genuinely separate condition on the same integer coefficients. Nothing in
   this arc has ever probed it. The `--char2` leg exhibits the phenomenon at the
   proxy level (a rational target-rank `ds-K4` configuration whose row matrix,
   denominators cleared, drops rank mod 2, 3, 5, 7, 11, 13 while holding at
   `10⁹+7`); that is a statement about **one seed**, not about the polynomial,
   and is reported as such.

*Confidence: proven-informally. The `ℤ`-coefficient step is a source-level
reading of four definitions and is the one place to attack it.*
*What would change this: a `pencilRow` entry whose construction introduces a
denominator (none does — `cross₃Poly` is a determinant and `annihRow` a minor),
or a chart-image side condition that makes `q` range over less than `K^N` (the
landed `pencilChartPointPoly_eval` / `pencilChartNormalPoly_eval` identities say
it does not).*

### Step Z8 — (AC-8): characteristic 2

> **(AC-8)** *(proven; driver leg `--char2`)* In characteristic 2 the polarity
> still **exists** (`complementIso` carries no characteristic hypothesis and
> `⋆² = id`), but its **geometry** collapses twice over:
> (i) `x ⬝ᵥ x = ∑ xᵢ² = (∑ xᵢ)²` — the quadratic form is the square of a linear
> form, so the "fixed quadric" is the **double plane** `{∑ xᵢ = 0}`, not a
> smooth quadric, and there are no rulings; (ii) `⋆ − 1 = ⋆ + 1`, so `⋆` is
> unipotent, its two "eigenspaces" coincide in one 3-space, and `Λ²K⁴` does
> **not** split.
> Hence **(AC-2)–(AC-6) all require `char K ≠ 2`**; **(AC-1)** does not; and
> **(AC-7)** is a characteristic-0 statement by construction.

Checked exactly: the identity on all 16 vectors of `𝔽₂⁴`; `rank(⋆−1) =
rank(⋆+1) = 3` over `ℚ` with the two kernels intersecting in `0`, against
`⋆−1 ≡ ⋆+1` entrywise mod 2.

### Verification

`notes/scripts/w4/closure.py` (**new with this section**; exact `ℚ(i)`,
stdlib-only, no CAS, no rng — nothing to seed, no `set` printed; a `w4/` leaf, so
its import closure is itself). It imports the canonical `⋆` (`repin.hodge_star`),
rigidity rows (`hybrid_gates.build_rigidity_extensors`), nondegeneracy
(`flanks.nondeg_conjuncts`, `repin.star_generic`), deficiency
(`nogood_subdiv.deficiency`), the shape generators (`pencil_escape`,
`pitch.theta_edges`, `widened.W19`, `flanks.named_shapes`,
`kslidecomb.shape_data`) and `kbare_common.rank_modp`; the only new primitive is
the scalar field. Every sampled configuration is guarded: all points asserted
isotropic, all edges asserted conjugate, every hinge asserted a `⋆`-eigenvector
whose sign matches its colour, every eigen-direction asserted on the conic, every
span's dimension asserted, and the contracted subsystem cross-checked against the
uncontracted one and against the full `6|V|`-column matrix.

```
PYTHONHASHSEED=0 python3 notes/scripts/w4/closure.py --fixed     # (AC-2), (AC-3)
PYTHONHASHSEED=0 python3 notes/scripts/w4/closure.py --sweep     # (AC-4), ds-K4 census
PYTHONHASHSEED=0 python3 notes/scripts/w4/closure.py --shapes    # (AC-6), the 13-shape table
PYTHONHASHSEED=0 python3 notes/scripts/w4/closure.py --flanks    # (AC-6), the 8 flank shapes
PYTHONHASHSEED=0 python3 notes/scripts/w4/closure.py --pool      # (AC-6) THE PINNED AGGREGATE
PYTHONHASHSEED=0 python3 notes/scripts/w4/closure.py --parity    # (AC-6) the C11 mechanism
PYTHONHASHSEED=0 python3 notes/scripts/w4/closure.py --collapse  # (AC-5)
PYTHONHASHSEED=0 python3 notes/scripts/w4/closure.py --char2     # (AC-8) + the char-p proxy
PYTHONHASHSEED=0 python3 notes/scripts/w4/closure.py --validate  # all eight, ~43 s
```

**`--pool` is the only place an aggregate figure may be read from.** It runs over
exactly the union of the `--shapes` and `--flanks` rows, tallies them into three
disjoint groups (**tight**; rigid-but-not-count-tight; not rigid), prints the
three fractions and the overall, and then attributes every miss against `hK`'s
own hypotheses (`hnoRigid` via `rigid_vertex_sets`, and the landed *necessary*
feasibility conditions `hcard` + no-two-hub-triangle). Quoting an aggregate from
anywhere else is what the σ recon's `63/63` did. **`--flanks`'s `hit` column
saturates at the probe cap (6) and is not a fraction of `pass`** — the driver
prints that caveat above the table, and the load-bearing column there is `best`.

`--validate` verified **byte-identical** under two different `PYTHONHASHSEED`
values (`0` and `999`), exit 0, 43 s each (re-verified at landing). Adding this
driver modified no tracked script, so the figure-invariance gate discharged on
the `git diff --name-only -- '*.py' '*.m2'` check alone
(`notes/scripts/README.md`, first bullet).

> **RE-BASELINED 2026-08-06 (slice S2).** `closure.py` *was* modified, by the
> guard adoption, so the full obligation ran. Four legs moved and each is
> repointed here: `--fixed` and `--sweep` now report the **composite** guard in
> the column that used to read `starOK` (hence (AC-9) above), `--validate`
> carries both, and `--char2`'s rational seed moved `2 → 6` because its
> `flanks.clean_pencil_seed` now applies the composite guard — its mod-`p` table
> is an explicitly-labelled *proxy* and its rank drops moved with the seed
> (`p = 2, 3, 5, 11` now `76, 78, 80, 76`). `--shapes`, `--flanks`, `--pool`,
> `--parity` and `--collapse` are **byte-identical**, so every (AC-6) and
> (AC-5) figure below is untouched.

**Which driver tests which sentence (F11).**

| claim | leg | figure |
|---|---|---|
| (AC-1) | — | **none; source-level only.** Named as such, not asserted more strongly |
| (AC-2) | `--fixed` AC-C0 | no `ℚ`-isotropic vector in `[−3,3]⁴`; explicit `ℚ(i)` one; eigenspaces `3+3`, `ℚ`-rational, mutually orthogonal; the two rulings realize both `⋆`-signs; the conjugacy law on 3 configurations |
| (AC-3) | `--fixed` | 4/4 conjuncts + star ranks 3, rank 90 = target at `ds-K4` |
| **(AC-9)** | `--fixed`, `--sweep` | the (AC-3) witness' four coincident hinge lines printed, one per hub; and the composite guard `repin.star_generic` accepts **0 of 64** colourings, asserted |
| (AC-4) | `--sweep` | `rank = rank₊ + rank₋` at **64/64** colourings; every target-rank colouring balanced, both classes forests, both blocks at 45; every unbalanced one short |
| (AC-5) | `--collapse` | 32/32 (16 bodies × 2 eigenspaces), as a **subspace** equality |
| (AC-6) positives | `--pool` (over `--shapes` + `--flanks`) | **tight 15/15**, rigid-not-count-tight **1/1**, not-rigid **2/5**, overall **18/21** — one pool, one leg, three disjoint groups |
| (AC-6) refutation | `--pool`, `--parity` | the three misses attributed: θ(1,2,9) and θ(2,3,7) **out of** `hK`'s habitat, `C11` **in** it; and `C3…C14` with no admissible colouring = exactly the odd ones, all 19 non-cycle pool shapes admitting one |
| (AC-7) | — | **none; source-level only** (four definitions read). The `--char2` leg's mod-`p` table is a *proxy* for its third consequence and is labelled so |
| (AC-8) | `--char2` | 16/16 on `𝔽₂⁴`; the two rank tables |

### Confidence verdict

- **(AC-1) the polarity generalizes: proven-informally**, source-level, **not
  compiler-checked**. Nothing obstructed; char 2 fine for the definition; the
  general-`K` transport already landed as `mapSupport`. The dispatch's question
  "is anything actually obstructed, or is this bookkeeping?" — **bookkeeping.**
- **(AC-2), (AC-3), (AC-4), (AC-5), (AC-8): proven-informally**, each exact and
  each with a driver leg asserting that sentence.
- **(AC-9) (every σ-fixed body of degree `≥ 3` carries a coincident hinge
  line): proven** — pigeonhole against the two-ruling-lines cap of *Step Z3* —
  and measured at 0/64 by the guard. It **qualifies (AC-3) without weakening
  it**: the σ-fixed witnesses satisfy the Lean predicate and reach the target,
  and are nevertheless never *generic*. New 2026-08-06 with the re-baselining
  round's slice S2, which is what made the harness able to see it.
- **(AC-6): REFUTED as a class statement over `hK`'s habitat** — `C11`, a bare
  odd cycle, satisfies every hypothesis `hK` carries and admits **no** σ-fixed
  nondegenerate configuration at all; the mechanism (parity) is identified and
  characterized exactly. **Open only on the tight stratum**, where all three
  misses are absent by construction and the measurement is 15/15 with no
  obstruction found. The per-shape positives are exact; the narrowed class
  statement is neither proven nor refuted.
- **(AC-7): proven-informally**, source-level.
- **The dispatch's sub-question 2, answered:** §(K-σ)'s two `ℝ`-refutations
  **both reverse as arguments** — over `ℂ̄` a σ-fixed pencil configuration exists,
  and it is *not* degenerate. But the **verdict** they support survives, on the
  field-neutral (AC-5). Net effect on route σ: **nil**. Net effect on the arc: one
  partial construction, (AC-6), which is *not* route σ and which is already
  refuted as a class statement.
- **The dispatch's honesty bar.** The field question is largely bookkeeping
  ((AC-1)) plus one clean structural payoff ((AC-7)); §(K-σ)'s route-σ verdicts
  are unmoved; and the one thing that did change — the σ-fixed locus being
  non-empty and non-degenerate — buys route σ nothing. **No route was
  manufactured**, and the one construction that looked like a route was
  **refuted by its own driver in the same run**, with the counterexample named
  and its mechanism characterized. What survives is a *partial* recipe with a
  known boundary, which is worth having and is not a closure of anything.

### What would change this

*(i)* A typecheck spike that fails on the general-`K` `screwComplementIso` or one
of its four theorems — the one instrument this dispatch could not use — would
downgrade (AC-1) from *bookkeeping* to *a real gap*.
*(ii)* A **tight** class shape at which no admissible ruling colouring reaches the
Tay target closes (AC-6)'s remaining question negatively. The cheapest probe is a
census over the `kslidecomb` class-shape pool, and the most likely failure mode is
combinatorial, not geometric: an admissible colouring must simultaneously
alternate along every branch, avoid a monochromatic hub, keep both ruling classes
acyclic **and** balance `|E_A| = |E_B|`, and those four can conflict — θ(1,2,9)
shows the conflict is real (there it forces two bodies to coincide), at a
non-tight shape. **Parity is already excluded as the tight-stratum obstruction**
by (AC-6): a tight shape has hubs, so it is not a bare cycle, so it always admits
*some* alternation colouring. Whatever kills the tight case, if anything does, it
is one of the other three conditions or the geometry.
*(iii)* A proof that the contracted direction network of *Step Z4* is isostatic
whenever (AC-4)(i)–(ii) hold would turn (AC-6) into a **tight-stratum-uniform**
theorem (never a habitat-uniform one — `C11` is permanent), and with it discharge
(K-tight) on the tight stratum directly, with `hK` then
following over every infinite characteristic-0 field by (AC-7). This is the
highest-value single item this section produces and it is **squarely inside the
project's existing formalized technology**: it is a 3-dimensional
body-hinge/Tay-style packing question (screws on a conic in `K³`, hinges shared
by more than two bodies), not new geometry.
*(iv)* A verified chart-image membership for the grid configurations (a small
Lean spike against `pencilChartPoint` / `pencilChartNormal`) is a **prerequisite**
for (iii) buying anything for `hK`; without it (AC-6) certifies target-rank
*realizations*, which §(K-flank) *F2* already has per shape, rather than
target-rank *chart seeds*, which is what `hK` asks for.
*(v)* Any characteristic-`p` probe at all: (AC-7) shows this is the **entire**
residual content of `[Infinite K]`, and the arc has never looked at it. A single
class shape whose escape minor vanishes identically mod some `p` would refute
`hK` at that characteristic and force a re-pin of the headline's typeclass — a
cheap, high-information experiment nobody has run.
