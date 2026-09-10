## §(K-ann) — the annihilator as a self-stress of the contracted framework: a class-uniform bracket recipe for `dλ`, and the mixed-stratum independence statement it still needs (**the recipe's KERNEL is delivered — the arc's first *formula* rather than a search — and its two INPUTS are not; the crux moves to (ANH-R1), relocation #4**)

Answering the second fan-out's **direction A** — `notes/pencil/strategy.md` §4.6's
**U1** (retarget the image problem from `Gr(3,6)` to the annihilator), **U2** (the
hinge-rate / cycle-space presentation, whose ground set is `E(H)`) and kernel-(K)
**option B** (the stress-function reading), fused. Read against §(K-pitch)
*Step 5b* ((T5)), §(K-Λ) *Steps 3–5a* ((Λ2), *Theorem (Λ-completeness at length-4
companions)*, (OUT)) and §(K-dom) *Steps D1/D2*, whose notation is inherited
verbatim. Option B's infrastructure is **not** used and its standing NO-GO is
untouched — everything below is pointwise exact linear algebra, and `τ` is a
kernel, not a chart rational function.

**Status, stated before the mathematics.**

- **The headline is (ANH-2)/(ANH-3): a *recipe*, in `pencil/strategy.md` §2.2's
  sense — a formula, not a search, and the first the arc has produced.** The
  **reciprocity identity** `dλ(π_P ω) = Σ_e ω_e B(τ_e, δC_e)` is local at the
  moved vertex, holds at every class member with no genericity hypothesis, and at
  the named move (translate one non-hub 2-valent far body) collapses to **one
  Klein pairing**. Carry its caveat with it wherever it is quoted: *the formula's
  kernel is bounded-size and class-uniform; what it pairs against (`τ`, `ω`) is
  not.* That is exactly why the pass delivers half of U1 and not all of it.
- **(ANH-1) upgrades (T5)/(D2) from measured bounds to a mechanism.** `λ` **is a
  self-stress** — of the *contracted* framework `H/P` (weld the whole companion
  into one body) — with stress dimension exactly `k − 3`. So §(K-dom) *(D2)*'s far
  block `3(k−3)`, until now a measured attainment, is `dim Gr(k−3, k)` **for that
  stress space**: a previously unexplained number now has its reason. 18 seeds, 9
  habitats, `k = 3..6`.
- **(ANH-4) is a proof, and it is `k = 4`-only, provably.** At `k = 4` the far
  edge set `E(H/P)` is a **circuit of the generic Tay matroid** — from 5/6-sparsity
  plus `hnoRigid`, with the count `5k + 10 ≤ 6k + 6` tight **exactly** at `k = 4`.
  That reproduces §(K-dom) *(D3)*'s `k ≥ 4` with `k = 4` as the equality case. On
  the realized side the support is the **whole** far edge set at every class seed
  (14/14), so the named move needs **no support-location step**.
- **(ANH-7): on the ~89 % of triples whose `H/P` carries a length-5 branch the
  whole criterion is ONE 4-point bracket**, correct at 56/56 sites.
- **The residual is one sentence, and it is (ANH-R1)** — *`τ_β ≠ 0` at the pencil
  placement*, i.e. `H/P − β` is pencil-rigid. **That is relocation #4** (after C1's
  `rank dV = 9` and the ∀λ seed's realizability), it is a *different kind* of
  relocation for three reasons given in *Step A8*, and **whether it is genuinely
  easier than its parent or merely smaller is OPEN** — nothing in this pass settles
  it, and the three reasons must not be read as settling it. It does **not** evade
  `pencil/strategy.md` §2.3: `τ_β ≠ 0` is a rank **lower** bound. Limiting, not
  fatal.
- **No gap-map *status* moves.** The (K-wit) row's *what would close it* cell gains
  (ANH-R1) as a named, scoped, `k = 4`-only sufficient route; the (K-dom) row gains
  (ANH-1) as the mechanism behind (D2). Class uniformity is untouched.

**Three corrections this pass owes the record**, all of them to claims that were
written down before it ran:

1. The coordinator's dispatch reading — *"`λ` is an annihilator covector, escape
   failure is a stress condition, and cocircuits are minimal supports in an
   orthogonal complement, so option B and U2 are the same object from opposite
   ends"* — is **directionally right and specifically wrong**, and correcting it is
   what makes the pass work. `λ` *is* a stress, but a self-stress of the contracted
   **far** framework `H/P`; it is **not** `[r]`, the transmitted wrench of the split
   that option B is about. Different frameworks, no shared infrastructure.
2. **U2's cocircuit reading is the DUAL of what the recipe needs.**
   `pencil/strategy.md` §4.6-U2 is right that `supp(λ)` is a **cocircuit** of the
   linear matroid on `E(H)` — that is the object §(K-Λ) *Step 5a*'s (OUT) half
   needs. The *recipe* question turns on `supp(τ)`, a **circuit** of the contracted
   framework. Same ground set, dual objects; everything below is about the circuit.
3. **This pass's own first analysis was wrong**, and its driver caught it: the kill
   set of (ANH-5) is *not* `⟨C(z₁z₂)⟩` always — that holds only at `dim U_y = 2`,
   and at `dim U_y = 1` the kill set is the strictly larger `α_{u₀}`. The general
   criterion is `ρ_y ⊥_B (V_y ∧ U_y)`.

### Standing notation (on top of §(K-Λ) and §(K-dom))

Split chain `b–v–a–c` at a hard-stratum target-rank `G′`-seed; `H := G − v − a`;
`P = b x₁ … x_{k−1} c` a shortest `b`–`c` path of `H` (the companion, of length
`k`); `S_P := span{C_e : e ∈ P}`; `V_bc ⊆ S_P` by path-sum containment;
`Λ := {λ ∈ S_P* : λ ⊥ V_bc}`, of dimension `k − 3`, is (T5)'s annihilator — the
*only* channel through which the far graph reaches `V_bc`. `B` is the Klein form,
`α_p` / `β_π` the two families of maximal isotropic 3-spaces.

**Hinge rates.** A motion of `H` is `m(x) − m(y) = ω_e C_e` per edge (§(K-ind)
*Step I3*'s identity), so `Z(H) = ker N` with `N` the cycle-condition matrix
(`dominance.cycle_data`), and `W := Z(H)^⊥ ⊆ (K^{E(H)})*`. Writing `π_P` for the
restriction of `ω` to the companion coordinates, `Λ ≅ W ∩ (K^P)*`.

**`H/P`** is `H` with the companion path contracted: weld `b, x₁, …, x_{k−1}, c`
into a single body `X`. It is a body-hinge multigraph on `|V(H)| − k` vertices with
`|E(H)| − k` edges (no loops: a chord among companion vertices would be a cycle of
`G` of length `≤ 4`, and 5/6-sparsity forces girth `≥ 6`), and

>  `5|E(H/P)| − 6(|V(H/P)| − 1) = k − 3`.

### Step A1 — (ANH-1): the annihilator IS the self-stress space of `H/P`

> **(ANH-1)** *(proven-informally)* At a hard-stratum target-rank seed, the map
> `τ ↦ (B(τ_e, C_e))_{e ∈ P}` is an isomorphism
>
>  `{ self-stresses of the contracted body-hinge framework H/P }  ⟶  Λ`,
>
> `H/P` is **rigid** there, and its stress space has dimension exactly `k − 3`.
> Equivalently: **the far graph reaches `V_bc` only through the self-stresses of
> the graph obtained by welding the companion.**

*Proof.* `W = im(Nᵀ)`, and an element of `im(Nᵀ)` is exactly `μ_e = B(τ_e, C_e)`
for a **screw circulation** `τ ∈ 𝒵(H) ⊗ Λ²K⁴` — `𝒵(H)` the graph cycle space, i.e.
`Σ_{e ∋ u} ± τ_e = 0` at every body `u`. Such a `μ` is supported inside `P` iff
`B(τ_e, C_e) = 0` for every `e ∉ P`, i.e. iff each non-companion hinge transmits
`τ_e` legitimately. Equilibrium plus transmissibility off `P` is verbatim the
self-stress system of `H/P`: the companion's own `τ_e` are recovered as partial
sums of the residuals along `P`, and the whole map is injective because `H` itself
carries **no** self-stress (`5|E(H)| − 6(|V(H)|−1) = −3`, and `H` is independent at
a target-rank seed). Finally `dim Λ = k − 3` forces `dof(H/P) = 0`, i.e. rigidity —
welding the companion kills exactly `V_bc`'s three degrees of freedom. ∎

Two immediate readings, and the first is the one to quote.

**(i) (D2) gets a mechanism, so a measured number becomes an explained one.**
§(K-dom) *(D2)* bounds the far block of `d(H ↦ V_bc)` by `3(k−3)` because the
annihilator is a point of `Gr(k−3, k)`, and *Step D4* measures that bound attained
at `0, 3, 6, 9` for `k = 3, 4, 5, 6`. (ANH-1) says **which** `Gr(k−3,k)`-point: the
self-stress space of `H/P`, whose dimension `k−3` is forced by a **count**, not by
a rank measurement. The `3(k−3)` is `dim Gr(k−3, k)` for that stress space. This is
the pass's contribution to the *settled* part of the arc: (T5) and (D2) stop being
bounds that happen to be attained.

**(ii) U2's ground set survives contact — with the correction above.** `E(H)`
really is the index set, and the matroid really has exchange (it is linear). Its
*generic* form is combinatorial: for `A ⊆ E(H)`, `r(A) = |A| − dof(H/(E∖A))`, and
`dof` of a generic body-hinge graph is Tay's count — so `pencil/strategy.md` §2.2's
ingredient 3 (Edmonds / Nash-Williams, the project's Phase-12/13/14 machinery) is
available too. What U2 named is the **cocircuit** `supp(λ)`; the recipe turns on the
**circuit** `supp(τ)`.

### Step A2 — (ANH-2): the reciprocity identity, and why it is local

> **(ANH-2)** *(proven)* Let `δ` be any chart direction and `ω ∈ Z(H)`. Then
>
>  `dλ(π_P ω)  =  Σ_{e ∈ E(H)} ω_e · B(τ_e, δC_e)`,
>
> and `δC_e = 0` unless `e` is incident to a vertex the direction moves. Both sides
> are independent of how `λ(t)` is scaled and of which particular solution of the
> derived system is taken.

*Proof.* `λ(t)·ω(t) = 0` for a curve `ω(t) ∈ Z(t)` gives `dλ(π_P ω) = −λ·ω̇`.
Differentiating the cycle condition `Σ_{e ∈ Z} ± ω_e C_e = 0` and pairing with
`τ`'s cycle certificate gives `Σ_e (ω̇_e B(τ_e,C_e) + ω_e B(τ_e, δC_e)) = 0`; the
first sum is `λ·ω̇` because `B(τ_e,C_e)` vanishes off `P`. ∎ Well-posedness:
`π_P ω` ranges over `ker λ`, on which the ambiguity `λ̇ ↦ λ̇ + ḟλ` dies; and
`λ ∈ im(Nᵀ)` kills the `ker N` ambiguity in `ω̇`.

This is a **virtual-work / reciprocity** statement: the rate at which the
annihilator moves under a far-chart deformation is the pairing of the motion
against the stress, evaluated **only at the moved hinges**. It is the formula U1
asked for, and it is bounded-size: two terms at a 2-valent body.

### Step A3 — (ANH-3): the named move, and the one-pairing form

> **The named move.** *Translate a single non-hub far body `y` of `H`-degree 2,
> inside the intersection of its hub neighbours' panels.* (Legal in the pencil
> chart: `y` appears in a hub's incidence constraint only through its hub
> neighbours, so the admissible velocities are `⋂_u n_u^⊥`, of dimension
> `3 − #(hub neighbours)`.)

> **(ANH-3)** *(proven)* With `y`'s neighbours `z₁, z₂`, `ρ_y` the screw
> transmitted through `y` (equilibrium at a 2-valent body makes the two incident
> `τ`'s equal up to orientation) and `v` the velocity,
>
>  `dλ_y(v)(π_P ω)  =  B( ρ_y ,  v̂ ∧ (ω_{e₁} ẑ₁ − ω_{e₂} ẑ₂) )`,
>
> **one Klein pairing** — a bracket-linear form, degree 1 in `v` and 1 in the hinge
> rates. (It is a *single* 4-point bracket `[w₀,w₁,v,u]` exactly when `ρ_y` has zero
> pitch; measured **0 of 192**, so in practice it is the Klein pairing, not one
> bracket.)

### Step A4 — (ANH-4): at `k = 4`, `E(H/P)` is a circuit of the Tay matroid

This is the pass's main *combinatorial* theorem, and it is what makes the named
move need no support-location step.

> **(ANH-4)** *(proven-informally)* At a `k = 4` class habitat (tight, `def = 0`,
> `hnoRigid`, both chain ends hubs), **every proper subset of `E(H/P)` is
> independent** in the generic body-hinge (Tay) matroid. Since `E(H/P)` itself has
> excess 1, it is a **circuit**: the generic self-stress of `H/P` is nonzero at
> **every** edge.

*Proof.* Suppose `A ⊊ E(H/P)` is dependent. By Tay + Lee–Streinu some vertex set
`W′` of `H/P` is over-braced: `5|E_A(W′)| > 6(|W′|−1)`.

*Case `X ∉ W′`.* Then `W′ ⊆ V(H) ∖ V(P)` and `E_A(W′) ⊆ E_G(W′)`, contradicting
`G`'s 5/6-sparsity (`f(W) ≤ 0` for every `W`, which `def(G) = 0` at a tight `G`
forces).

*Case `X ∈ W′`.* Put `W := (W′ ∖ {X}) ∪ V(P) ⊆ V(H)` and `W̃ := W ∪ {v, a}`, so
`|W̃| = |W′| + k + 2` and `|E_G(W̃)| ≥ |E_A(W′)| + k + 3` (the `A`-edges, the
companion's `k`, the split chain's 3). Then

>  `5|E_G(W̃)| ≥ 5|E_A(W′)| + 5k + 15 ≥ (6(|W′|−1) + 1) + 5k + 15 = 6|W′| + 5k + 10`,
>
>  `6(|W̃| − 1) = 6(|W′| + k + 1) = 6|W′| + 6k + 6`,

and `G`'s sparsity `5|E_G(W̃)| ≤ 6(|W̃|−1)` therefore forces `5k + 10 ≤ 6k + 6`,
i.e. `k ≥ 4`. **At `k = 4` that is an equality**, so every inequality in the chain
is tight and `f(W̃) = 0`. With every subset of `G` sparse that makes
`def(G[W̃]) = 0`, and `W̃ ⊊ V(G)` with `|W̃| ≥ 2` — a **proper rigid subgraph**,
contradicting `hnoRigid` (`Graph.IsProperRigidSubgraph`,
`Molecular/Deficiency.lean:483`: `H ≤ G ∧ H.IsKDof n 0 ∧ 2 ≤ |V(H)| ∧
V(H) ⊊ V(G)` — properness is on the *vertex* set, which is what this argument
produces). ∎

**Why `k = 4` and not `k ≥ 5`, and the (D3) calibration.** The inequality
`5k + 10 ≤ 6k + 6` is tight exactly at `k = 4`; at `k ≥ 5` it has slack, no
contradiction follows, and indeed the stress space then has dimension `k − 3 ≥ 2`
so `E(H/P)` cannot be a circuit. **The theorem is intrinsically a `k = 4`
theorem** — and note what its own count reproduces: §(K-dom) *(D3)* derives
`hnoRigid ⟹ k ≥ 4` from the proper cycle `C_{3+k}`, and the chain above derives the
same `k ≥ 4` from an over-braced set, with **`k = 4` the equality case** of both.
The two are the same tightness seen twice.

**Two independent corollaries, both verified.** *(a)* `girth(H/P) ≥ 6` unless
`|E(H/P)| = 5`, i.e. unless `G` is θ(3,4,5) itself (a `C_j` has body-hinge excess
`6 − j`, so a *proper* `C₅` would be a proper dependent subset). *(b)* no branch of
`H/P` has length `≥ 6` — which is the *Shared dictionary*'s **(SD-6)**, proved
there *independently and elementarily*, so the two agree and neither is assumed.

**And an incidental worth keeping.** θ(3,4,5) is the **unique** `k = 4` class shape
whose entire annihilator is the Klein-perp of a single 5-cycle (it is the only shape
in the whole census with `|E(H/P)| = 5`). That is a concrete reason for its role as
the arc's exemplar, rather than an accident of who picked it first.

### Step A5 — (ANH-5)/(ANH-6): branch constancy, and the exact vanishing criterion

> **(ANH-6)** *(proven)* Equilibrium at a 2-valent body transmits the wrench
> unchanged, so `τ` is **one screw per branch** of `H/P`, and transmissibility makes
> that screw `B`-orthogonal to **all `ℓ` of the branch's hinge lines**. Hence
> `dim Λ = 6·c(H/P) − |E(H/P)| = k − 3`, and a branch of length `ℓ` whose lines span
> `K⁶` carries a **forced-zero** screw.

> **(ANH-5)** *(proven)* At a **free** 2-valent far body `y` (no hub neighbour, so
> `v` sweeps the whole plane at infinity `H_∞`), with
> `U_y := {ω_{e₁} ẑ₁ − ω_{e₂} ẑ₂ : ω ∈ Z(H)} ⊆ K⁴`:
>
>  `dλ_y ≡ 0  ⟺  ρ_y ⊥_B (H_∞ ∧ U_y)`.
>
> When `dim U_y = 2` the right-hand kill set is exactly `⟨C(z₁ z₂)⟩`, i.e.
> **`dλ_y ≡ 0` iff the transmitted wrench is the pure force along the line joining
> `y`'s two neighbours.** When `dim U_y = 1` (spanned by `u₀`) the kill set is the
> larger `α_{u₀}`, so the criterion is weaker there.

*Reason for the `dim U_y = 2` form.* `B(ρ, v̂ ∧ ẑ_i) = 0` for all `v̂ ∈ H_∞` says
`ρ ⊥_B α_{z_i}`; an α-plane is maximal isotropic hence self-`B`-perpendicular, so
`ρ ∈ α_{z₁} ∩ α_{z₂} = ⟨C(z₁z₂)⟩`. The driver asserts the **subspace identity**
directly, not just the coincidence of two booleans.

*The general form is the correction of item 3 above.* The `⟨C(z₁z₂)⟩` reading was
this pass's first analysis and it is **false at `dim U_y = 1`**; `ρ_y ⊥_B (V_y ∧ U_y)`
is the criterion that holds at both, with `V_y` the space of admissible velocities.

**A collinearity corollary worth keeping.** On a chain of *consecutive* free
2-valent bodies the screw is one and the same, so `dλ ≡ 0` would force
`ρ ∝ C(w_{i−1}w_{i+1})` at two consecutive `i` — which makes four consecutive branch
points **collinear**, refuted at any generic chart point. So on such a chain the
only way `dλ ≡ 0` is `ρ = 0`.

### Step A6 — (ANH-8): every branch of a class member has length `≤ 5`

> **(ANH-8)** *(proven, elementary)* Every branch (maximal degree-2 chain) of a
> class member `G` has length `≤ 5`.

**This is promoted out of the section.** It is an elementary rigid-graph fact of
exactly the kind both workbooks reuse, so its statement and proof live **once**, in
the *Shared dictionary* as **(SD-6)**; `(ANH-8)` is this section's name for it and
is not restated here. Its consequence for the argument above is what this step
carries:

**Consequence.** Every branch screw lives in a space of dimension `6 − ℓ ≥ 1` —
**no branch is forced to zero**, which is exactly what (ANH-4) needs, and the two
proofs are independent. At `ℓ = 5` the screw is pinned to a **1-dimensional
Klein-perp `κ_β`**: an explicit bracket vector of the branch's six points, computed
by a `5 × 6` Laplace expansion, with **no global solve**.

### Step A7 — (ANH-7): the recipe, in one named move and one bracket

Let `β = w₀ w₁ w₂ w₃ w₄ w₅` be a length-5 branch of `H/P` (endpoints nodes, `w₁..w₄`
free 2-valent bodies), and take `y = w₂`.

`C(w₁w₃)` shares a point with `D₁ = C(w₀w₁)`, `D₂ = C(w₁w₂)`, `D₃ = C(w₂w₃)` and
`D₄ = C(w₃w₄)`, so it is automatically `B`-perpendicular to **four of the five**
branch lines. `κ_β` is the unique common perp of all five. Hence `κ_β ∝ C(w₁w₃)` iff
`C(w₁w₃)` is perpendicular to the fifth as well:

> **(ANH-7)** *(proven-informally, **conditional** — the two inputs below)* At a
> `k = 4` class habitat with a length-5 branch `β` of `H/P`, and at the free middle
> body `w₂` with `dim U_{w₂} = 2`,
>
>  **`dλ_{w₂} ≢ 0  ⟺  τ_β ≠ 0  and  [w₁, w₃, w₄, w₅] ≠ 0`.**
>
> One named far-chart move, one 4-point bracket, no quadric, no panel, no `pt(a)`,
> no `M`, and nothing whose size grows with the graph.

**The two inputs, named precisely.**

- **(ANH-R1) `τ_β ≠ 0`.** Generically forced: (ANH-4) makes `E(H/P)` a circuit, so
  the generic stress is nonzero on every edge. At the **pencil** placement it is the
  statement that `H/P − β` — a graph with count exactly 0, generically isostatic —
  is **rigid**, i.e. independent. Specialization only ever runs the other way
  (`dim S_pen ≥ dim S_gen`, hence `supp_pen ⊆ supp_gen`), so this is **not
  implied**. Measured `τ_β ≠ 0` at 56/56 sites and full support at 14/14 class
  seeds. *Step A8* is about this and nothing else.
- **(ANH-R2) `dim U_{w₂} = 2`.** Measured 32 of 56 sites; at the other 24 the kill
  set is the larger `α_{u₀}` and the *conclusion* still held (`dλ ≠ 0` at all 56), so
  (ANH-R2) restricts the **closed form**, not the conclusion.

**And the payoff, if the two inputs are discharged.** `dλ ≢ 0` on the FIXED-scoping
far chart makes `{λ = p⁺}` a *proper* closed subset there (`p⁺` is frozen in that
scoping), hence proper in the whole irreducible pencil chart; by §(K-Λ)'s **(Λ2)**
and *Theorem (Λ-completeness at length-4 companions)*, at a generic seed the escape
then holds — by pitch off the bad line, and by route A on the `λ ∝ q` branch. So a
class-uniform (ANH-7) would **close (K-wit)/(K-pitch) at every length-4-companion
class (shape, split)**, under (Λ0) in full and the standing (T1)/(T5) hypotheses. It
would *not* close the class — see *Step A9*.

### Step A8 — (ANH-R1) is relocation #4: what makes it a different kind, and the question it leaves open

**Is this relocation #4? Yes, and the record should say so in those words.** C1
relocated `Q(z) ≢ 0` to `rank dV = 9` (§(K-dom), struck as a route); the ∀λ seed
relocated it to `λ`'s realizability (`pencil/strategy.md` §4.6); this relocates it
to **(ANH-R1)**. Three things distinguish it, and none of them is "it is smaller so
it must be easier":

1. **It crosses `pencil/strategy.md` §2.2's ingredient-2 boundary in the right
   direction.** `Q(z) ≠ 0` is a Klein-form condition, invisible to any matroid
   (§(K-pure) *P5*). (ANH-R1) is an **independence** condition in the body-hinge
   matroid — a matroid whose ground set grows with the graph *and* which **has** a
   min-max (Tay + Nash-Williams / Edmonds, formalized in Phases 12–15). Its
   combinatorial half is not merely expressible, it is **proven**: that is (ANH-4).
   What is left is *only* the generic-vs-pencil gap.
2. **It lands on a strictly smaller graph.** `H/P − β` has `|E(G)| − 12` edges and
   `|V(G)| − 10` vertices. Every prior relocation stayed on `G`. This is the shape an
   induction needs — though §(K-ind) *Step I6* is exactly why `pencil_reduction` does
   not supply one: the welded body `X` carries non-concurrent hinges, so (ANH-R1)
   lives on the **mixed stratum**. It is therefore **not the same problem shrunk**,
   and it is `pencil/strategy.md` §4-C3's **second** concrete consumer, alongside
   §(K-Λ) *Step 5a*'s (OUT).
3. **It does not escape §2.3, and `pencil/strategy.md` §4.6-U2's honesty flag is
   confirmed as *limiting, not fatal* — say both halves.** (ANH-R1) is a rank
   **lower** bound, so the asymmetry is relocated onto a smaller contracted graph
   exactly as flagged, not evaded. The flag is *not* fatal because the smaller
   graph's matroid is Tay's, where independence **is** combinatorially
   characterised — unlike `R_3`, where §2.3's asymmetry is an open problem of the
   subject. The wall changes character: from *"no matroid sees this"* to *"the
   matroid sees it and the pin may not respect the matroid"*. That second wall is
   the **weak-map / specialization-stability** direction `pencil/strategy.md` §4.6
   named as the only remaining (M3)-passing literature lead, and it now has a
   specific statement to attach to, which that subsection said it could not supply.

> **The open question, stated as open.** *Is (ANH-R1) genuinely easier than its
> parent, or merely smaller?* **Nothing in this pass settles that.** The three
> reasons above say the relocation is of a different *kind*; they do **not** say it
> is a *reduction in difficulty*, and they must not be read as saying so. The arc's
> own base rate for "smaller and better-structured, therefore tractable" is
> unencouraging (`pencil/strategy.md` §2.3), and the honest position is that
> relocation #4 has better structure than #1–#3 and an unmeasured difficulty.

**Pointer (2026-08-19, direction OCON).** Since §(K-out) *Steps O13–O18*, (OUT)'s own residue
(OC-8) sits on the same object class as (ANH-R1) — one contraction tower apart,
`H/P = (H/X)/(b ∼ v*)` — so a rigidity statement at `H/X` is one weld away from a rigidity
statement at `H/P`. No status moves on either side.

### Step A9 — scope and the `k`-grading: the machinery transports, the target does not

- **(ANH-1), (ANH-2), (ANH-3), (ANH-5), (ANH-6)** and the *Shared dictionary*'s
  **(SD-6)** are **length-free**, and were verified at `k = 3, 4, 5, 6`.
- **(ANH-4) is `k = 4` only — provably**, the count being tight exactly there. At
  `k ≥ 5` the stress space has dimension `≥ 2`, `E(H/P)` is not a circuit, and "every
  far edge is stressed" is *measured* (`k = 5`: 10/10; `k = 6`: 9/9 and 15/15) but
  **not** forced. (ANH-7)'s closed form goes with it.
- **The target transports worse than the machinery.** At `k = 4`, `Bad_Λ` is two
  points of `P³`, so non-constancy of `λ` suffices. At `k = 5` the bad set is
  3-dimensional in the 6-dimensional `Gr(2,5)` (§(K-Λ) *Step 7*) and non-constancy
  buys nothing; at `k = 6` the target is `Gr(3,6)` again.
- **So no `k`-graded mechanism, this one included, can close the class** — `k = 4`
  is the `hnoRigid` **equality** case (§(K-dom) *(D3)*, (ANH-4) above) with `k ≥ 5`
  the interior, and both populations are non-empty in the arc's habitat table. This
  is the same verdict `pencil/strategy.md` §4.6 already carries, reached again from
  the inside; this pass does not claim otherwise.
- **What (ANH-R1) *would* close, if it fell, is the length-4-companion stratum
  outright** — a well-defined, non-empty chunk of `hK` — via §(K-Λ)'s Λ-completeness,
  since `dλ ≢ 0` makes `{λ = p⁺}` proper on an irreducible chart. That would be the
  first stratum an *argument* rather than a search delivers.

**Coverage, measured.** Over 4296 class (shape, split, length-4 companion) triples:
**3820 (89 %)** carry a length-5 branch of `H/P`, which is exactly where (ANH-7)'s
closed form applies (and exactly the triples carrying two consecutive free interior
bodies, so (ANH-5)'s collinearity corollary covers the same set). The remaining
**476** have every `H/P` branch of length `≤ 4`; there the branch screw is not pinned
by its own lines and the criterion needs `τ_β` itself. `girth(H/P) ≥ 6` at all but 8
triples, all of them θ(3,4,5).

### Verification

`notes/scripts/w4/annih.py` (**new with this section**; exact ℚ, stdlib only, no
CAS; a `w4/` leaf sitting beside `dominance`/`outer`/`sigma`/`closure`, importing
only catalogued §1 primitives — `dominance`'s `cycle_data` / `build_chart` /
`dV_rank` / `solve_multi` / `dC_along` / `base_seed`, `outer`'s `split_data` /
`companions4` / `named_inventory` / `sweep_shapes`, `repin`'s `hodge_star` /
`span_basis` / `in_span`, `pitch`'s `klein` / `Q` / `paths_graph`,
`nogood_subdiv`'s `deficiency` / `count_matroid_rank`, `kslide`'s
`no_rigid_branch_union`, and `lambda.HABITATS4` through `importlib`; the
composite `repin.star_generic` genericity guard rides in through
`dominance.base_seed`, since slice S2). All rng
seeded through `repin.seed_probe`'s integer seeds. Run from the repo root:

```
PYTHONHASHSEED=0 python3 notes/scripts/w4/annih.py --stress    # (ANH-1)
PYTHONHASHSEED=0 python3 notes/scripts/w4/annih.py --rate      # (ANH-2), (ANH-3), (ANH-5)
PYTHONHASHSEED=0 python3 notes/scripts/w4/annih.py --supp      # (ANH-4), realized side
PYTHONHASHSEED=0 python3 notes/scripts/w4/annih.py --recipe    # (ANH-7)
PYTHONHASHSEED=0 python3 notes/scripts/w4/annih.py --census    # (ANH-4) corollaries, (SD-6), coverage
PYTHONHASHSEED=0 python3 notes/scripts/w4/annih.py --validate  # the machinery
```

All six modes verified **byte-identical** under two different `PYTHONHASHSEED`
values (`0` and `999`), exit 0 at every one; runtimes at landing 8/9 s
(`--validate`), 30/30 s (`--stress`), 20/19 s (`--rate`), 81/87 s (`--supp`),
37/41 s (`--recipe`), 23/22 s (`--census`). Adding this driver modified no tracked
script, so the figure-invariance gate discharged on the
`git diff --name-only -- '*.py' '*.m2'` check alone (`notes/scripts/README.md`,
first bullet).

> **THE OWED §(K-ann) RE-READ, DONE 2026-08-06 (slice S2), and it is CLEAN.**
> `dominance.base_seed`'s genericity guard gained its coincident-hinge clause,
> so this section's seeds were re-drawn (`annih.py` is inside `flanks`' closure
> and all six modes re-ran). Result, exactly as F13's classification predicted
> for a section whose claims are **identities, ranks and pointwise
> attainments**: `--census` and `--validate` **byte-identical**; `--stress`,
> `--rate` and `--recipe` differ **only in which seed integer** each habitat's
> first clean draw is, with every dimension, rank, `yes`, "identity holds on all
> of them" and one-bracket verdict unchanged. **One figure improved**:
> `--supp`'s far block of `rank dλ` now attains (D2)'s bound `3(k−3)` at
> **every** seed, where the two contaminated `k = 6` draws used to report 5 and
> 7 of 9 — so *Step A4*'s "reproduces (D2)'s `3(k−3)`" is now an equality at
> every seed rather than at the clean ones. No (ANH-n) verdict moves.

Habitats: the four `lambda.HABITATS4` length-4-companion class shapes (θ(3,4,5),
NT21, NT24, NT30) plus the seven `dominance.HABITATS` (`k = 3..6`), plus **six swept
probes** — the first `(shape, split)` pairs of `outer.sweep_shapes`' `K4` family
whose `H/P` carries a length-5 branch, so (ANH-7) is tested on shapes nobody
hand-picked — plus one deliberate **off-class control**, `θ4(3,4,5,6)`, which is
tight with `def = 0`, `hcard` and triangle-free but **fails `hnoRigid`** (asserted at
load). The control is what makes the off-support tests non-vacuous: (ANH-4)'s
hypothesis is exactly what it violates, so its `H/P` is allowed the **proper**
circuit that no class shape has.

Per mode, what is asserted:

- `--stress`: `dim Z = dim mot(H) − 6`; the screw-circulation space has dimension
  exactly `k − 3`; it spans the **same** annihilator as the motion-side
  `nullspace(π_P Z)`; `H/P` is rigid both at the pencil placement
  (`dim(Z ∩ K^{E∖P}) = 0`) and combinatorially (`deficiency = 0`); the count
  `5|E(H/P)| − 6(|V|−1) = k−3`; `H` itself carries no self-stress.
- `--rate`: the reciprocity identity, direction by direction and `ω` by `ω`, against
  implicit differentiation of `ker N`; the locality of `dC`; the one-pairing form at
  every single-vertex move; and (ANH-5) **as a subspace identity** — that
  `(H_∞ ∧ U_y)^{⊥B}` is literally `⟨C(z₁z₂)⟩` — not merely as a coincidence of two
  booleans.
- `--supp`: `C_pen ⊆ C_gen` with `C_gen` from `count_matroid_rank` on `5(H/P)`;
  `C_pen` computed **twice** (from the full solve, and from a stress space rebuilt on
  the reduced edge list); `girth(H/P) ≥ 5`; the generic stress dimension `= k−3`; the
  closed form at every girth-5 case; and `dV = 0` at every single-vertex far move off
  `supp(τ)`.
- `--recipe`: `κ_β` is the 1-dimensional Klein-perp of the five branch lines;
  `τ_β ∝ κ_β`; the equivalence `κ_β ∝ C(w₁w₃) ⟺ [w₁,w₃,w₄,w₅] = 0`; the general
  `(V_y ∧ U_y)^{⊥B}` criterion; and, at `dim U_y = 2`, the one-bracket form.
- `--census`: `girth(H/P) ≥ 6` unless `|E(H/P)| = 5`; `E(H/P)` a circuit (budgeted);
  **every** `H/P` branch of length `≤ 5`; and the same generators re-run past length 6
  as an (SD-6) stress test.
- `--validate`: the Hodge dictionary `⟨★τ, C⟩ = B(τ, C)`; `λ` annihilates `π_P(Z)`;
  `λ ∈ row(N)`; transmissibility off `P`; and `V_bc` reconstructed from `Z` in the
  `C`-basis.

**Figures.**

| figure | value |
|---|---|
| `--stress` seeds | **18** over **9** habitats, `k = 3..6`; `dim(screw circulations) = k−3` and equal to the motion-side annihilator at every one; `dof(H/P) = def(H/P) = 0` at every one |
| `--rate` | the reciprocity identity at **276** far-chart directions × **828** motions, exact; the one-pairing form at **192** single-vertex moves |
| `--rate`: zero-pitch `ρ_y` | **0 / 192** — so it is one Klein pairing, never literally one 4-point bracket |
| `--supp` seeds | **16** (14 class + 2 control); `C_pen ⊆ C_gen` at all, with **equality** at all |
| `--supp`: `\|C_pen\|` vs `\|E(H/P)\|` at class seeds | equal at **14/14** — the support is the WHOLE far edge set, so the named move needs no support-location step |
| `--supp`: off-support single-vertex moves | **0** at every class seed (there are none), **13** at each control seed — and `dV = 0` at **13/13**, twice |
| `--supp`: `rank dλ` (far block) | **3** at all eight `k = 4` class seeds (and at both control seeds); **6** at both `k = 5` seeds; `9 / 5 / 9 / 7` at the four `k = 6` seeds — reproducing §(K-dom) *(D2)*'s `3(k−3)` through the annihilator, with the two sub-maximal `k = 6` values the usual non-generic seeds semicontinuity handles |
| `--recipe` sites | **56** (length-5 branch, free middle body); criterion correct at **56/56**, all with `dλ ≠ 0`; **32** with `dim U_y = 2` (one-bracket form), **24** with `dim U_y = 1` (general form) |
| `--recipe`: `[w₁,w₃,w₄,w₅] = 0` | **0 / 56** |
| `--census` triples | **4296** (shape, split, length-4 companion) over the named inventory + `outer.sweep_shapes` |
| `--census`: `girth(H/P)` | `{5: 8, 6: 2206, 7: 1822, 8: 260}`; all 8 girth-5 cases have `\|E(H/P)\| = 5`, i.e. `G = θ(3,4,5)` |
| `--census`: `E(H/P)` a circuit | certified at **400** triples (budgeted), no failures |
| `--census`: `H/P` branch lengths | `{1: 920, 2: 1924, 3: 3214, 4: 4184, 5: 6426}` — **max 5**, as (SD-6) predicts |
| `--census`: (SD-6) stress test past length 6 | θ3 to length 12, θ4 to length 12, `K4` to 7, `K4+par` to 7 — **identical shape counts** (2 / 0 / 540 / 740) and **max branch length still 5** |
| `--census`: coverage of the closed form | **3820 / 4296 = 89 %** carry a length-5 branch |
| determinism | all six modes byte-identical across two `PYTHONHASHSEED` values |

**Which driver tests which sentence (F11).**

| claim | mode | what asserts *that sentence* |
|---|---|---|
| (ANH-1) | `--stress` | the screw-circulation space and the motion-side annihilator are compared **as subspaces** at 18 seeds; `dof(H/P) = def(H/P) = 0`; the count `= k−3` |
| (ANH-2) | `--rate` | the identity itself, against an **independent** implicit differentiation of `ker N`, at 276 × 828 |
| (ANH-3) | `--rate` | the collapsed one-pairing form at 192 single-vertex moves, plus the zero-pitch census that keeps it from being over-claimed as one bracket |
| (ANH-4), combinatorial half | `--census` | the circuit certificate at 400 triples (budgeted) and both corollaries; the **proof** is the argument in *Step A4*, not the census |
| (ANH-4), realized half | `--supp` | `C_pen ⊆ C_gen`, equality at 16/16, full support at 14/14 class seeds, and the off-class control's proper 5-cycle with `dV = 0` off it |
| (ANH-5) | `--rate`, `--recipe` | the **subspace** identity `(H_∞ ∧ U_y)^{⊥B} = ⟨C(z₁z₂)⟩` at `dim U_y = 2`, and the general `(V_y ∧ U_y)^{⊥B}` criterion at both dimensions |
| (ANH-6) | `--stress`, `--recipe` | one screw per branch and its `B`-orthogonality to all `ℓ` lines; `κ_β` 1-dimensional at `ℓ = 5` |
| (ANH-7) | `--recipe` | the equivalence at 56/56 sites, on 6 swept shapes + 2 named exemplars + the control |
| (SD-6) | `--census` | branch-length histogram capped at 5 over 4296 triples, plus the past-length-6 stress test; the **proof** is elementary and lives in the *Shared dictionary* |
| **(ANH-R1)** | — | **none, and this is the point.** `--supp`/`--recipe` measure `τ_β ≠ 0` at the sampled placements (56/56, 14/14); *that the pencil placement can never shrink the support* is what no driver tests and what *Step A8* is about |
| (ANH-R2) | `--recipe` | `dim U_y` reported at all 56 sites (32 / 24) |

### Confidence verdict

- **(ANH-1)** (the annihilator is the self-stress space of `H/P`; `H/P` rigid;
  `dim = k−3`): **proven-informally**, length-free, with a driver mode asserting that
  sentence at 18 seeds over 9 habitats spanning `k = 3..6`, and three independent
  routes to `V_bc` agreeing in `--validate`. Its arc-level value is that **(T5) and
  (D2) stop being measured bounds**.
- **(ANH-2)** (the reciprocity identity) and **(ANH-3)** (the one-pairing form at the
  named move): **proven**, with a two-line derivation and 276 × 828 exact checks
  against an independent implicit differentiation. **This is the pass's headline**: a
  recipe in `pencil/strategy.md` §2.2's sense, and the first the arc has produced.
  Quote it with its caveat — *the formula's kernel is bounded-size and
  class-uniform; what it pairs against (`τ`, `ω`) is not.*
- **(ANH-4)** (`E(H/P)` is a Tay circuit at `k = 4`): **proven-informally** from
  5/6-sparsity + `hnoRigid` + the tight count, `hnoRigid` read off the landed
  `Graph.IsProperRigidSubgraph`. Its two corollaries are verified independently over
  4296 triples, and one of them ((SD-6)) has its own elementary proof. **This is the
  pass's strongest positive** and the first class-uniform discharge of a needed
  non-vanishing's *combinatorial* half in the arc. It is `k = 4`-only, provably.
- **(ANH-5)**, **(ANH-6)**: **proven**, each with its own asserted driver sentence.
  (ANH-8) is **proven** and lives in the *Shared dictionary* as **(SD-6)**.
- **(ANH-7)** (the one-move, one-bracket recipe): **true-modulo-named-gap** — the gap
  is exactly **(ANH-R1)** `τ_β ≠ 0` (plus (ANH-R2) `dim U_{w₂} = 2` for the closed
  form). Verified at 56/56 sites, 0 failures, on 6 shapes nobody hand-picked plus 2
  named exemplars plus the control.
- **U1 as posed — "a single named far-chart move with a bracket formula for `dλ`,
  valid at every class member at `k = 4`": HALF DELIVERED, and the halves must not be
  conflated.** The **move** and the **formula** are delivered: named, bounded-size,
  class-uniform, no genericity hypothesis. The **inputs** are not: the formula pairs
  against `τ` and `ω`, and while (ANH-4) discharges what `τ`'s support must be
  *generically*, whether the pencil placement respects that is open. The answer to
  U1's own honesty flag: **the move is not per-shape, but its certificate is** — a
  strictly better position than the arc's other per-shape positives, and still not a
  proof.
- **(ANH-R1): OPEN, and its difficulty is unmeasured.** *Step A8* argues it is a
  relocation of a different *kind*; it does not argue, and this section does not
  claim, that it is *easier*.
- **Class uniformity is untouched. No gap-map *status* moves on this pass.** The
  (K-wit) row's *what would close it* cell gains (ANH-R1) as a named, scoped,
  `k = 4`-only sufficient route; the (K-dom) row gains (ANH-1) as the mechanism behind
  (D2).

### What would change this

*(i)* **A class habitat + seed with `τ_β = 0` on every length-5 branch** — that would
exhibit the pencil specialization genuinely shrinking `supp(τ)` at a class shape, kill
(ANH-7) as stated, and be a sharp new obstruction of the same species as §(K-pure)
*P6*'s `P21` exhibit. Not found: 56/56 sites and 14/14 class seeds have full support.
The off-class control shows the phenomenon is real once `hnoRigid` is dropped.

*(ii)* **A proof that the pencil placement cannot shrink `supp(τ)`** — i.e. that
`H/P − β` is pencil-rigid whenever it is generically isostatic. That is **(ANH-R1)**,
and it closes `dλ ≢ 0` at `k = 4` outright and, with §(K-Λ)'s Λ-completeness, the whole
length-4-companion stratum of `hK`. It is a **mixed-stratum** statement (§(K-ind)
*Step I6*: `X` is not a pencil body) on a strictly smaller graph, and it is the second
concrete consumer `pencil/strategy.md` §4-C3 has, after (OUT).

*(iii)* **One of the 476 triples whose `H/P` branches are all of length `≤ 4`**, with
`dλ ≡ 0`. That is where the closed form does not reach, and it is the cheapest place to
look for a counterexample to non-constancy.

*(iv)* **A class shape with a branch of length `≥ 6`** — that would refute the *Shared
dictionary*'s (SD-6) and, with it, (ANH-4)'s second corollary. The proof is elementary
and the census stress test looked for one to length 12 (θ families) and 7 (`K4`,
`K4+par`) without finding any, but the sweep's hub multigraphs stop at `|V°| = 5`.

*(v)* **An error in the identification (ANH-1)** — guarded by three independent `V_bc`
routes, two independent `C_pen` routes, an independent implicit differentiation, and
the Hodge dictionary check, all in `--validate`/`--supp`.

*(vi)* **A `k ≥ 5` analogue of (ANH-4)** — measured true at 3 habitats but with no
proof, and provably not derivable from the count. Since the *target* does not transport
past `k = 4` (§(K-Λ) *Step 7*), this would be worth having only as part of a different
attack on `Gr(k−3,k)`.

---

**Continuation (2026-08-06, second fan-out direction R) — pencil-rigidity of the contracted framework: (ANH-R1) is one-point-decidable per shape and discharged at every probed triple, its bad locus is INHABITED by exact rational points of the honest chart, and the "easier or merely smaller" question is settled as scoped.**

Answering the second fan-out's **direction R** (`notes/pencil/fanout-archive.md`
§"Second fan-out" → Direction R). Read against *Steps A4/A7/A8* above
((ANH-4), (ANH-7), (ANH-R1)), §(K-out) *Steps O3/O6* ((OC-3)/(OC-4), whose
shape *Step A12* mirrors on the τ side), and `pencil/strategy.md` §§2.3/4.6
(the rank-lower-bound asymmetry and the weak-map lead). Driver:
`notes/scripts/w4/shrink.py` (imports `annih` read-only).

**Status, stated before the mathematics.**

- **(ANH-R1) stays OPEN as a class statement, and no gap-map status moves.**
  What moves is its *epistemic profile*, in both directions at once:
  per shape it is now **witness-decidable by one exact rank computation and
  discharged at every probed triple** ((ANH-9) + (ANH-10), 26/26 guarded
  seeds, 58/58 length-5-branch sites); pointwise it is now **refuted** —
  (ANH-12) exhibits exact rational legal chart points, most of them
  guard-accepted at target rank on the hard stratum, where `H/P − β` is
  dependent and the support strictly drops.
- **The pinned census probe (`notes/Phase39.md` (g)) is run and is a clean
  negative at random guarded seeds** — no class seed with
  `supp_pen ⊊ supp_gen` was found — **and a clean positive at constructed
  ones**: the same strict drop the census hunts is *reached deliberately*, at
  six class shapes, by two legal single-vertex chart moves, with every
  habitat predicate green. Weak-map specialization **does bite** on the
  pencil chart; it just does not bite at a *generic* point of any probed
  shape.
- **The sharp form of the "easier or merely smaller" question is answered:
  the pencil pin does NOT respect Tay's matroid pointwise — only
  generically, per shape.** So (ANH-R1) can never be delivered by a
  counting, matroid, or placement-blind argument (the τ-side analogue of
  §(K-out) (OC-3)), and the remaining geometric half has exactly the profile
  of §(K-out) (OC-8): a whole-chart genericity statement. That is
  `pencil/strategy.md` §2.3's wall, met from inside the relocation itself —
  see *Step A13* for what this does to §2.3's recorded stop-rule prediction.

### Step A10 — (ANH-9): the weak-map formulation, and one-point decidability

Fix a class (shape, split, length-4 companion) triple and write `M_gen` for
the generic Tay matroid on `E(H/P)` — a **circuit** by (ANH-4) — and
`M_pen(p)` for the linear matroid the hinge lines realize at a legal pencil
chart point `p`.

> **(ANH-9)** *(proven-informally)*
> (i) For every chart point `p`, `M_pen(p)` is a weak-map image of `M_gen`
> (rank of every subset can only drop under specialization).
> (ii) The pencil chart is the image of an irreducible rational
> parametrization (hub points, panel normals, panel-constrained interiors —
> the same standing fact §(K-dom) *(D4)* already consumes), so **"the matroid
> at the generic pencil placement" `M_pen^gen` is well-defined**, and it is
> the weak-map-maximal one among the `M_pen(p)`.
> (iii) (ANH-R1) at the triple ⟺ `E(H/P) − β` is independent in `M_pen^gen`
> ⟺ **some** chart point has `H/P − β` independent ⟺ **some rational** chart
> point does (ℚ-density of a nonempty open in the parameter affine space).
> So (ANH-R1) is **decidable per triple by one exact rank computation at one
> rational point**.
> (iv) At `k = 4`: `M_pen^gen = M_gen` ⟺ `supp(τ) = E(H/P)` at one guarded
> generic seed ⟺ `τ_β ≠ 0` for **every** branch `β` (the support is a union
> of branches, by (ANH-6)'s branch constancy).

*Proof.* (i) is rank lower-semicontinuity: realized rank ≤ generic rank,
subset by subset. (ii) irreducibility of the image of an irreducible variety;
the matroid at the generic point is the common matroid on a dense open where
all the finitely many subset-ranks are simultaneously maximal over the chart.
(iii) forward: generic point; backward: the rank of `H/P − β`'s matrix is a
lower-semicontinuous function of the parameters, so full rank at one point
forces full rank on a dense open, hence at the generic point; a rational
witness exists because a nonempty Zariski-open subset of affine space over ℚ
has rational points. (iv) `M_gen` is a circuit, so `M_pen^gen = M_gen` iff
every single-edge deletion stays independent generically, iff the (unique,
`dim = k − 3 = 1`) generic pencil stress has full support. ∎

Two immediate consequences. First, the *Shared dictionary*-level reading:
**the weak-map / specialization-stability lead of `pencil/strategy.md` §4.6
now has its precise statement** — *(ANH-R1) class-uniformly = the
specialization `M_gen ⇝ M_pen^gen` restricts to the identity weak map on the
co-branch family, at every `k = 4` class contraction* — which is what that
subsection said it could not supply. Second, **θ(3,4,5) is the trivial
case, proven at every chart point**: its `H/P` is the bare 5-cycle
(*Step A4*'s incidental), so `H/P − β` is empty and (ANH-R1) holds
unconditionally there (asserted in `--validate`).

### Step A11 — (ANH-10): the census — the pinned probe, run

> **(ANH-10)** *(measured; guard-gated, so quotable as a rate)* Over a pinned
> pool of **26** class `k = 4` (shape, split) pairs — the 4 named
> length-4-companion habitats plus **22 swept shapes nobody hand-picked**
> (2 theta3, 4 `K4`, 4 `K4+par`, 4 `V5e8`, 4 `V5e9`, 4 `V5e10`; the theta4
> family is empty of class shapes, matching *Step A6*'s census) — one
> `dominance.base_seed`-guarded seed each (composite guard
> `repin.star_generic`), all 26 on the hard stratum (`dim R_a = 1`):
>
> - `dim S_pen = 1` (H/P pencil-rigid) at **26/26**;
> - `supp_pen = E(H/P)` — every branch stressed — at **26/26**: **no strict
>   support drop at any guarded seed**;
> - **58** length-5-branch sites, `τ_β ≠ 0` at every one — so by (ANH-9)(iii)
>   **(ANH-R1) is discharged at the generic point of every pooled triple**;
> - an independent cross-check at every seed: the stress space of `H/P − β`
>   **rebuilt from scratch on the reduced edge list** is 0-dimensional exactly
>   when `τ_β ≠ 0` (both directions, every length-5 branch plus a shorter
>   spot-check per seed);
> - the generic side re-asserted per shape (`gen_stress_dim(H/P) = 1`,
>   Lee–Streinu pebble game).
>
> The **off-class control** θ4(3,4,5,6) (`hnoRigid` FAILS there) is the
> positive control: the machinery **finds** its zero branch — the length-6
> branch, whose screw is forced to zero by six independent lines, (ANH-6)'s
> mechanism — so "no drop found" is not an artifact of the hunt being unable
> to see one.

This extends *Step A4*'s realized-side 14/14 to 26/26 over a pool whose swept
majority was never hand-picked, and it upgrades each pointwise `τ_β ≠ 0`
into a per-shape generic-point discharge via (ANH-9). It does **not** touch
class uniformity: 26 shapes is evidence, not an argument — exactly
`pencil/strategy.md` §2.3's "every positive is per-shape".

### Step A12 — (ANH-11)/(ANH-12): the bad locus is inhabited, exactly

The census asks about generic seeds; (ANH-R1) as *Step A8* poses it is a
generic-point statement. What no prior step settled is whether the **bad
locus** `{p : H/P − β dependent at p}` even meets the honest (nondegenerate,
guard-accepted) part of the chart. It does — and not merely over `K̄` or at
sampler-degenerate boundary points, but at exact rational points satisfying
**every predicate the arc's habitat carries**.

> **(ANH-11)** *(proven)* — **the common-transversal mechanism.** Let `p` be
> a legal pencil chart point, `Z` a `c`-cycle of `H/P` edge-disjoint from a
> branch `β`, and `L` a line of `P³` such that **every hinge line of `Z`
> meets `L`**. Then the Klein extensor `C(L)` propagates to a self-stress of
> `H/P` at `p` supported on `Z` (together with the compensating flow along
> the **companion** edges when `Z` passes through the welded body `X` —
> allowed exactly because the weld demands no transmissibility there),
> vanishing on `β`. In particular `E(H/P) − β` — **independent in `M_gen`**
> by (ANH-4) — is **dependent in `M_pen(p)`**; and `Z` itself, a
> Tay-**isostatic** `c = 6`-cycle (*Shared dictionary* (R3): `def(C₆) = 0`),
> goes dependent.
>
> *Proof.* Lines meeting `L` are exactly the **special linear complex** of
> axis `L`: `B(C, C(L)) = 0` (the arc already uses "hinge lines in a linear
> line complex ⟹ a self-stress per cycle" at §(K-σ) *Step σ6* /
> `pencil/strategy.md` §2.4's null-correlation exhibit; this is its localized,
> single-cycle form). Put `τ_e = ±C(L)` along a traversal of `Z`, `0` on all
> other far edges, and the telescoping partial sums on the companion edges
> between `Z`'s two attachment vertices when `X ∈ Z`. Equilibrium: at a far
> cycle body the two incident cycle screws cancel; at a companion vertex the
> path flow balances by construction; elsewhere everything is zero.
> Transmissibility off `P`: `B(±C(L), C_e) = 0` for `e ∈ Z` since `C_e` meets
> `L`, and trivially off `Z`. `τ ≠ 0`, `τ|_β = 0`, and its restriction to
> `E − β` is a self-stress of `H/P − β`. ∎

> **(ANH-12)** *(proven at witnesses — exact, existence claims, so exempt
> from rate-gating; guard status reported anyway)* — **reachability.**
> Anchor `L = line(pt(u₀), pt(u₃))` at two opposite real bodies of `Z`. The
> four `Z`-edges incident to `u₀` or `u₃` meet `L` automatically; each of the
> remaining `c − 4` incidences is `[u₀, u₃, q, x] = 0` — **affine-linear in
> one movable far vertex `x`** (a plane condition), solvable exactly inside
> `x`'s legal move space (the intersection of its hub-neighbours' panels).
> So the bad point has **rational coordinates** and is reached from a guarded
> seed by `c − 4` legal single-vertex pencil-chart moves. Run at the 4 named
> habitats + the 6 swept probes (`shrink.py --bad`, 92 s):
>
> - **9/9 shapes constructed** (θ(3,4,5) is the proven trivial case), **all 9
>   guard-accepted** (`repin.star_generic`), `verify_pencil_witness` green at
>   every witness, and **8/9 at target rank on the hard stratum
>   (`dim R_a = 1`)**;
> - at the **six swept `K4`-family shapes**: `β` of **length 5** (count 0 —
>   the exact (ANH-R1) object), 6-cycles, and at the witness
>   `dim S(H/P) = 1` — **`H/P` still pencil-rigid** — with the unique stress
>   supported on the 6-cycle: **`supp` drops `11 → 6`**. This is *verbatim*
>   the strict `supp_pen ⊊ supp_gen` drop the census probe hunts, exhibited
>   at a guard-accepted, target-rank, hard-stratum legal chart point;
> - NT24 and NT30 (no length-5 branch in `H/P`): 7-cycles, `β` of length 4
>   (the matroid-drop form — `E − β` independent-with-slack generically),
>   same full predicate set, `supp` drops `17 → 7` and `23 → 7` with
>   `dim S = 1`;
> - NT21: an 8-cycle witness, guard-accepted but off target rank
>   (`dim S = 2` there); the dependency of `H/P − β` is still certified.
>
> Every witness is certified three ways: the constructed stress satisfies
> the stress system **equation by equation** (equilibrium body-by-body,
> transmissibility edge-by-edge — no solve), it lies in the independently
> **solved** stress space, and the reduced space of `H/P − β` is rebuilt from
> scratch and is nonzero. One witness in full (the others print from the
> driver): `swept:K4 (3,1,1,3,5,5) split 0/v100`, seed 1, anchors
> `(109, 3)`, moved `108 → (-135149673/59575628, 60222846/74469535,
> -217797/146738)`, `110 → (14145707/2039430, 7, -4/5)`.

**Consequences, and their exact strength.** (a) **(ANH-R1)'s bad locus meets
the honest chart — indeed the guard-accepted target-rank hard stratum — at
every probed shape**, so no counting, matroid, or placement-blind argument
can ever deliver (ANH-R1); any proof must be a genericity argument on the
whole-graph chart. This is the τ-side analogue of §(K-out) (OC-3), reached
by *construction* rather than by (OC-3)'s dimension count, and it lands
**inside** the stratum where (ANH-7)'s consumer runs — the analogue of
§(K-out) (OC-4)'s silent point. (b) **The pencil pin does not respect Tay's
matroid pointwise**: a Tay-isostatic set goes dependent at a legal
nondegenerate pencil placement. The pin respects the matroid only
*generically, per shape* — (ANH-10). (c) Nothing here refutes (ANH-R1) or
(ANH-7): the witnesses are deliberately special points, and the census says
generic guarded seeds show no drop.

**Combinatorial availability of the 6-cycle form** (`--comb`, 12 s,
placement-free): over the 4296-triple pool of *Step A9*, `3812 + 8 trivial
θ(3,4,5) = 3820` triples carry a length-5 branch (reconciling exactly with
*Step A9*'s 3820 — the bare-cycle `H/P` counts as one cyclic length-5 branch
there and as trivial here), and the 6-cycle construction is combinatorially
available at **2066** of the 3812 (edge-disjoint 6-cycle + real anchors + a
movable vertex per condition). `--bad` shows the reach is wider in practice:
the 7/8-cycle forms cover NT21/NT24/NT30, whose `H/P` has girth 7, 7, 7.

### Step A13 — the verdict: "easier or merely smaller", settled as scoped; and §2.3's prediction, checked

*Step A8* left one question open in those words: *is (ANH-R1) genuinely
easier than its parent, or merely smaller?* This pass answers the parts of
it that are answerable without closing the gap itself:

1. **The pointwise escape hatch is closed.** If the relocation had been
   "easier" in the strong sense — the smaller graph's independence provable
   pointwise from Tay's min-max — (ANH-12) forbids it: the matroid statement
   is false at legal nondegenerate chart points of every probed shape.
   What remains is a generic-point rank lower bound at a pencil placement of
   a contraction of `H` — **exactly §(K-out) (OC-8)'s profile**, now with the
   nonemptiness of the bad locus *witnessed inside the habitat stratum*
   rather than inferred.
2. **`pencil/strategy.md` §2.3's recorded prediction is checked, not
   admired.** The prediction said a third independent route should terminate
   on a rank lower bound at a pencil placement of a contraction of `H`, and
   that if it does, "stop looking for routes: the productive target becomes
   the wall itself". This pass is not a third route — it attacked one of the
   two named residuals directly — and its outcome *sharpens the wall's
   description*: the wall is precisely **generic-point** rank lower bounds
   (pointwise ones are now refuted objects), its bad loci are inhabited by
   rational points of the honest chart, and its per-shape instances are
   one-point-decidable. The stop-rule's premise is therefore *strengthened*:
   there is no cheaper reformulation left on this side.
3. **What a uniform route now needs, named exactly.** By (ANH-9)(iii),
   (ANH-R1) class-uniformly ⟺ a **class-uniform recipe producing, per
   triple, one legal chart point with `H/P − β` independent**. That is the
   same missing technology as §(K-grid)'s residual — since direction G,
   **(GR-10)** — a uniform constructed-witness generator for tight class
   shapes at the Tay target, with chart-image membership already proven there
   ((GR-5)) — so **directions T and R converge on one technology**: uniform
   constructed chart witnesses of rank attainment. If §(K-grid)'s recipe
   closes, the natural follow-up is whether a grid/counting recipe evaluates
   on the *mixed* contracted object `H/P − β` (the welded body `X` is not a
   pencil body — §(K-ind) *Step I6* — so this is strictly outside (GR-5)'s
   current scope; recorded as a lead, not a claim).
4. **The one symbolically tractable per-shape upgrade** (parallel to
   `pencil/strategy.md` §5.3): by White–Whiteley (WW87 Prop. 2.6, verified in
   `notes/Phase39.md` *Citations*), `H/P − β` at `k = 4` is count-0, so
   (ANH-R1) per shape is "`C(H/P − β)` (the pure condition, a bracket
   polynomial) does not vanish identically on the chart" — an M2-checkable
   **identity over the function field** per shape, which would upgrade
   (ANH-10)'s per-seed witnesses to per-shape symbolic proofs. Note this
   does *not* collide with §(K-pure) *P5*'s refutation of direction C: the
   target here is a rank statement, which is exactly what a pure condition
   sees; it was the *pitch* that the pure condition could not see.

So the honest one-line answer to *Step A8*'s question: **merely smaller in
difficulty class — the geometric half is the same wall — with two genuine
structural gains ((ANH-4)'s proven combinatorial half, and (ANH-9)'s
one-point decidability per shape) and one now-proven loss (pointwise
matroid-respect fails, (ANH-12)).**

### Verification (Steps A10–A13)

`notes/scripts/w4/shrink.py` (**new with this continuation**; exact ℚ, stdlib
only; imports `annih` and, through it / beside it, only catalogued §1
primitives — `annih`'s `prepared` / `stress_space` / `contracted_edges` /
`hp_branches` / `branch_lengths` / `branch_screw` / `girth` /
`gen_stress_dim` / `habitats4` / `control_shapes` / `swept_probes` /
`path_edges` / `single_vertex_dirs`, `outer`'s `split_data` / `companions4` /
`named_inventory` / `sweep_shapes` / `eligible_splits` / `stratum_at`,
`repin`'s `span_basis` / `in_span` / `star_generic`, `pitch`'s `klein` /
`det4`, `kbare_common.verify_pencil_witness`, `dominance.cycle_data`,
`exactcore`'s `rank` / `nullspace` / `wedge2` / `hat` / `dot` / `neighbors`;
it reimplements nothing and adds **no rng** — every sampled configuration
arrives through `dominance.base_seed`'s composite guard). Run from the repo
root:

```
PYTHONHASHSEED=0 python3 notes/scripts/w4/shrink.py --census    # (ANH-10)   ~106 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/shrink.py --bad       # (ANH-11/12) ~92 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/shrink.py --comb      # availability ~12 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/shrink.py --validate  # machinery    ~7 s
```

All four modes verified **byte-identical** under `PYTHONHASHSEED=0` and
`999`, exit 0. Adding this driver modified no tracked script, so the
figure-invariance gate discharges on the `git diff --name-only -- '*.py'
'*.m2'` check alone (`notes/scripts/README.md`, first bullet).

Per mode, what is asserted: `--census` — per seed: `gen_stress_dim(H/P) = 1`
(pebble game), `dim S_pen` from the full solve, branch screws via
`branch_screw` (constancy asserted), and the reduced-rebuild equivalence
`τ_β = 0 ⟺ dim S(H/P − β) ≥ 1` in both directions at every length-5 branch
plus a shorter spot-check; the off-class control must exhibit its drop.
`--bad` — per witness: every cycle line's Klein pairing against `C(L)` is
zero; `verify_pencil_witness` green; the constructed stress satisfies
equilibrium body-by-body and transmissibility edge-by-edge, lies in the
independently solved stress space, and `H/P − β`'s reduced space is nonzero;
guard and stratum reported per witness, never assumed. `--comb` — the
combinatorial precondition per triple, placement-free. `--validate` — the
contraction bookkeeping against `annih.contracted_edges`, the trivial
θ(3,4,5) case, reproduction of *Step A4*'s `--supp` verdicts at 2 habitats,
exactness of the affine plane-solver, the special-linear-complex fact on
synthetic data (rank 5, co-kernel `⟨C(L)⟩`), and the cycle finder against
`girth`.

**Figures.**

| figure | value |
|---|---|
| `--census` pool | **26** class `k = 4` (shape, split) pairs (4 named + 22 swept over 6 families; theta4 empty of class shapes), 1 guarded seed each, **26/26 hard stratum** |
| `--census`: `dim S_pen` | **1 at 26/26** (H/P pencil-rigid) |
| `--census`: `supp_pen = E(H/P)` | **26/26** — no strict drop at any guarded seed |
| `--census`: length-5-branch sites | **58**, `τ_β ≠ 0` at every one |
| `--census`: off-class control | drop **found** (the length-6 branch), 1/1 |
| `--bad` witnesses | **9/9 shapes** (+ θ(3,4,5) trivial), **9/9 guard-accepted**, **8/9 target-rank hard-stratum** |
| `--bad`: (ANH-R1)-exact witnesses | **6** (β length 5, count 0; all six: `dim S = 1`, supp drop **11 → 6**) |
| `--bad`: matroid-drop witnesses | NT24 **17 → 7**, NT30 **23 → 7** (`dim S = 1`); NT21 8-cycle, off target rank, `dim S = 2` |
| `--comb` | 4296 triples; `3812 (+8 trivial) = 3820` with a length-5 branch (matches *Step A9*); 6-cycle form available at **2066/3812** |
| determinism | all four modes byte-identical across two `PYTHONHASHSEED` values |

**Which driver tests which sentence (F11).**

| claim | mode | what asserts *that sentence* |
|---|---|---|
| (ANH-9)(i)/(ii) | — | **none; proof-level** (semicontinuity + parametrized chart). Named as such, not asserted more strongly; its (iii) consumes the census witnesses |
| (ANH-9)(iii)/(iv) per shape | `--census` | the one-point witnesses themselves: `τ_β ≠ 0` at 58/58 sites, full support at 26/26, with the reduced-rebuild equivalence asserted both ways |
| (ANH-10) | `--census` | the sentence is the aggregate; guard-gated via `dominance.base_seed`; the positive control proves the hunt can see a drop |
| (ANH-11) | `--bad`, `--validate` | per witness, the constructed stress is verified **equation by equation** (no solve) *and* against the independent full solve; the synthetic special-complex leg (`rank 5`, co-kernel `⟨C(L)⟩`) |
| (ANH-12) | `--bad` | the witnesses: rationality (exact coordinates printed), legality (`verify_pencil_witness`), guard, stratum, and the reduced dependency, per shape |
| "the drop the census hunts is exhibited" | `--bad` | `dim S = 1` **and** `supp` strictly smaller, printed and asserted at the six exact witnesses |
| the 6-cycle form's availability | `--comb` | the combinatorial precondition, per triple; explicitly **not** a success rate — the geometric halves are measured only in `--bad` |
| **(ANH-R1)** | — | **still none, and still the point**: what no driver can test is class uniformity; the census discharges the generic point per probed shape, the construction bounds what any future argument may assume |

### Confidence verdict (Steps A10–A13)

- **(ANH-9): proven-informally** (semicontinuity, chart irreducibility as
  already consumed by §(K-dom) *(D4)*, ℚ-density); its per-shape consequence
  is exercised 26 times by the census.
- **(ANH-10): measured**, guard-gated, 26/26 + 58/58 with an off-class
  positive control; a rate over a pinned pool, quotable as such.
- **(ANH-11): proven** (five lines; classical special-linear-complex
  geometry, the localized form of the arc's §(K-σ) *Step σ6* device), with
  every witness certified equation-by-equation.
- **(ANH-12): proven at 9 witnesses** (exact rational points; existence
  claims). The class-wide statement "the bad locus is inhabited at every
  class shape" is **measured-plus-mechanism, not proven** — the 6-cycle
  form's combinatorial precondition holds at 2066/3812 triples and the
  7/8-cycle forms covered every probed shape, but no proof is offered that
  some workable cycle/labeling exists at *every* shape.
- **(ANH-R1): OPEN**, unchanged in status, sharpened in profile: per-shape
  one-point-decidable and discharged at every probed triple; pointwise
  refuted; class-uniformly exactly as hard as a uniform
  constructed-witness recipe ((ANH-9)(iii)), the technology §(K-grid)'s
  residual (since direction G: (GR-10)) is building for the tight stratum.
- **Class uniformity is untouched. No gap-map status moves.** The (K-wit) /
  (K-ann) rows gain the (ANH-12) caveat (no placement-blind route to
  (ANH-R1)) and the (ANH-9) reduction, not a status change.

### What would change this (Steps A10–A13)

*(i)* **A guarded random seed with a zero branch at a class shape** — the
census extended (more swept families, more seeds per pair) finding
`supp_pen ⊊ supp_gen` generically would kill (ANH-7) as stated at that shape
and be the sharpest new obstruction since §(K-pure) *P6*.
*(ii)* **A class-uniform independent-point recipe** ((ANH-9)(iii)'s right
side) — closes (ANH-R1), hence via §(K-Λ)'s Λ-completeness the whole
length-4-companion stratum. The concrete candidate to watch is §(K-grid)'s
machinery, if its (GR-6)-style colouring existence can be made to evaluate
on the mixed contracted object.
*(iii)* **A per-shape M2 identity** `C(H/P − β) ≢ 0` over the function field
(*Step A13* item 4) — **RUN 2026-08-06 (direction Q, Steps A14–A17), and the
"upgrade" premise was WRONG**: (ANH-9)(iii) already makes each census row a
proof at its triple, so the identity is the pointwise restatement, not an
upgrade ((ANH-16)(i)); item 4 is **struck as an upgrade route**. What survives
is **(ANH-14)** — the whole bare-cycle stratum governed by ONE universal
irreducible degree-12 polynomial — and no shape was refuted anywhere.
*(iv)* **A shape where no cycle/labeling makes the construction work *and*
no other mechanism inhabits the bad locus** would weaken (ANH-12)'s
class-wide reading (currently measured at 9/9 probed); it would not affect
(ANH-11) or the consequences at the probed shapes.
*(v)* **An error in the witness certification** — guarded by the
equation-by-equation check being solve-free and independent of the solver
whose output it is compared against, and by `verify_pencil_witness` /
`star_generic` / `stratum_at` being imported from their canonical homes, not
reimplemented.


**Continuation (2026-08-06, third fan-out direction Q) — (ANH-R1) as a PURE CONDITION: a branch-core normal form and an exact size law, one UNIVERSAL irreducible degree-12 bracket polynomial governing the whole bare-cycle stratum, a bad locus strictly larger than (ANH-11)'s, and the verdict that the M2 identity is the *pointwise restatement* of (ANH-R1) rather than an upgrade of it.**

Answering `notes/pencil/fanout-archive.md` §"Third fan-out" → Direction Q, i.e. *Step A13*
item 4 and *What would change this (Steps A10–A13)* item (iii). Read against
*Steps A4/A6/A7* ((ANH-4), (ANH-6), (ANH-7)) and *Steps A10–A13* ((ANH-9)'s
one-point decidability, (ANH-10)'s census, (ANH-11)/(ANH-12)'s inhabited bad
locus); against §(K-pure) *Step P0*, whose reading of White–Whiteley's pure
condition this pass re-uses **verbatim on the τ side**; against §(K-out)
*Step O12* ((OC-16)'s chart-to-frame dominance residue, which turns out to be
this section's residue too); and against `pencil/strategy.md` §§5.2/5.3/5.4.
Drivers: `notes/scripts/w4/anhr1.py` (imports `annih` / `shrink` / `outer`
read-only) and `notes/scripts/m2/anhr1.m2`.

**Status, stated before the mathematics.**

- **No shape is refuted, and the experiment's *positive* half turns out to be
  logically redundant.** The dispatch's premise — *"a positive at a shape
  upgrades that shape's (ANH-10) census row from witness to proof"* — is
  **REFUTED**, and by this section's own predecessor: *Step A10*'s (ANH-9)(iii)
  already makes one exact rational chart point with `H/P − β` independent a
  **proof** of (ANH-R1) at that triple, by rank lower-semicontinuity on an
  irreducible chart. (ANH-10)'s 26/26 rows are therefore already proofs, not
  witnesses awaiting one. This is §(K-pure) *Step P0*'s point transposed to the
  τ side: WW87 offers two routes to `C ≢ 0`, **Cor. 2.7 pointwise** — which is
  the restatement, and which the exact-ℚ harness already executes in seconds —
  and **Thm 2.18 combinatorially**, which (ANH-11)/(ANH-12) have already closed
  off here (no counting / matroid route). An M2 identity per shape is Cor. 2.7
  again, at 10²–10³× the cost.
- **What the symbolic layer does buy is structure, and it is worth having.**
  Three results the sampling harness structurally cannot reach, all
  class-uniform over a named stratum: **(ANH-13)** the reduced object's
  branch-core normal form and the exact size law `deg C(H/P − β) = 12(c(G) − 2)`;
  **(ANH-14)** at the bare-cycle stratum (29.6 % of length-5-branch sites) the
  pure condition is ONE polynomial, the same at every shape of the stratum,
  **irreducible** of degree 12 — so (ANH-R1) there is *exactly* the statement
  that the shape's pencil chart does not lie inside one fixed hypersurface, a
  chart-to-frame dominance question with **no rank condition left**, the precise
  analogue of §(K-out) (OC-16); **(ANH-15)** the bad locus **strictly contains**
  (ANH-11)'s common-transversal locus.
- **The one-bracket recipe does NOT extend.** (ANH-14)'s irreducibility is a
  *negative* with teeth: `C(H/P − β)` admits no factorization into smaller
  bracket conditions, so there is no (ANH-7)-style "one named move, one 4-point
  bracket" certificate for (ANH-R1) itself, and no §(K-Λ) (Λ1)-style
  "product of two linear forms" either. The arc's two closed forms both came
  from *reducible* objects; this one is irreducible.
- **The M2 reach is measured and it stops at the bare-cycle stratum.** Generic
  point, all coordinates indeterminate: degree 12 in 24 point indeterminates
  **finishes at 578 s**; the next stratum up (a θ core, 12 free points, 48
  indeterminates) **does not finish at 600 s**. Together with §(K-Λ)'s recorded
  kill (degree 52 in 28, no finish) the layer's practical boundary is now
  bracketed from both sides.
- **Class uniformity is untouched. No gap-map *status* moves.** The (K-ann) row
  gains (ANH-13)–(ANH-16) as a sharpening of (ANH-R1)'s profile — the residue is
  now named identically to §(K-out)'s — not as a status change.

**The answer to the dispatch's question, per stratum.** (`c′ = c(G) − 2`; the
site counts are over the 4296-triple pool's 6426 length-5-branch sites. "Shape"
here means (shape, split, companion, β) site — the object depends on all four.)

| stratum | sites | the object | is `C ≢ 0` ? |
|---|---|---|---|
| `c′ = 0` (θ(3,4,5)) | 8 | empty (one body) | **TRUE at every chart point** — *Step A10*, unconditional |
| `c′ = 1`, `n = 0` | **1904** | ONE universal irreducible degree-12 bracket polynomial, the 7-point open chain | **TRUE**, proven *uniformly for the whole stratum* over the function field; (ANH-R1) at a shape then needs only chart-to-frame dominance, and needs nothing at a shape (ANH-10) probes |
| `n = 1` | 134 | a **product** of `c′` bare-cycle conditions | **TRUE**, by the same computation applied factorwise |
| `n = 2` (θ core) | 3812 | an order-6 branch-screw determinant; at the θ(5,5,2) length profile it collapses further to a **2 × 2** in two pinned screws (`κ_1, κ_2`, degree-10 brackets) | **TRUE at an exact witness** (the θ(5,5,2) profile, moment-curve points); the generic-point symbolic form is **M2-INFEASIBLE** (600 s kill) and the local frames are panel-constrained, so no universality |
| `n = 3` | 568 | order-12 branch-screw determinant | **not attempted** — infeasible by the same measurement |
| **refuted anywhere** | **0** | — | no stratum, no shape |

### Standing notation (on top of *Steps A1–A13*)

`β` a length-5 branch of `H/P`; **`H/P − β`** means: delete `β`'s five edges
**and its four interior bodies** (its two end bodies are nodes of `H/P` and
survive; an isolated body would make the framework disconnected, hence
dependent for a reason that has nothing to do with (ANH-R1)). `c(·)` is cycle
rank; `c' := c(H/P − β)`. `C(·)` is the White–Whiteley pure condition
(WW87 Prop. 2.6; the citation is verified in `notes/Phase39.md` *Citations*,
`.refs` copy, 2026-08-04). Nodes of a body-hinge multigraph are its bodies of
degree ≠ 2; `n` = their number, `m` = the number of branches.

### Step A14 — (ANH-13): the branch-core normal form, and the exact size law

> **(ANH-13)** *(proven; driver-asserted)* At a `k = 4` class (shape, split,
> length-4 companion) triple with a length-5 branch `β` of `H/P`:
>
> (i) **Size law.** `H/P − β` is connected with
> `|V′| = 5c′ + 1`, `|E′| = 6c′`, and
>
>  `c′ = c(H/P) − 1 = c(G) − 2`.
>
> (ii) **Normal form.** By (ANH-6)'s branch constancy a self-stress is one
> screw per branch, so the `5|E′| × 6(|V′|−1)` rigidity matrix reduces to the
> **square `6m × 6m` branch-screw matrix**: `ℓ_j` transmissibility rows
> `B(S_j, C_e) = 0` per branch, and `6(n−1)` equilibrium rows
> `Σ_{j at u} ±S_j = 0`. Its determinant **is** `C(H/P − β)`, up to a nonzero
> scalar.
>
> (iii) **Degree.** `deg C(H/P − β) = 2|E′| = 12c′ = 12(c(G) − 2)` in the point
> coordinates — so the pure condition's size **grows linearly with the shape**,
> and the object is bounded exactly on the finite part of the class.
>
> (iv) **Bare cycle.** `c′ = 1` ⟺ `c(G) = 3`, and — since every body of
> `H/P − β` has degree `≥ 2` unless `β` is a *loop* at a degree-3 node — a
> connected cycle-rank-1 object of min degree 2 is a **bare cycle**, `n = 0`
> (measured: `n = 0` at exactly the 1904 + 8 sites with `c′ ≤ 1`). There
> `C(H/P − β) = det[C_0; …; C_5]`, the 6 × 6 Plücker determinant of the cycle's
> hinge lines. `c′ = 0` ⟺ `H/P − β` is a single body — the trivial case
> *Step A10* already settles at every chart point (`G = θ(3,4,5)`).

*Proof.* (i) `G` tight gives `(|V|,|E|) = (5c+1, 6c)` (§(K-ind) *(I1)*);
`H = G − v − a` drops 2 vertices and 3 edges, so `c(H) = c − 1`; contracting the
companion path changes no cycle rank, so `c(H/P) = c − 1`; deleting a branch of
a connected graph, with its interiors, drops the cycle rank by exactly 1. Then
`|E′| = |E(H/P)| − 5 = (6c − 7) − 5 = 6(c−2)` and `|V′| = 5(c−1) − 4 = 5(c−2)+1`.
Connectivity: `H/P − β` disconnected would put its rank below `5|E′|`, so
(ANH-4)'s generic independence of `E(H/P) − β` already forbids it.

(ii) A self-stress is a screw circulation with `B(τ_e, C_e) = 0` off the
companion (*Step A1*); equilibrium at a 2-valent body makes `τ` constant along
a branch ((ANH-6)), so the unknowns are `m` screws and the constraints are the
`Σ_j ℓ_j = |E′|` transmissibility rows plus `6n` equilibrium rows of which
exactly 6 are dependent (each branch enters two nodes with opposite signs).
Squareness: `|E′| + 6(n−1) = 6c′ + 6(n−1) = 6(m−n+1) + 6(n−1) = 6m`. ∎

(iii) Each transmissibility row is linear in a hinge line, hence quadratic in
the points; the equilibrium rows are constant. So the determinant has degree
`2|E′|`.

(iv) At `n = 0` there is one branch, the whole cycle, and one screw `S`; the
matrix is the 6 × 6 matrix of `hodge C_e`, whose determinant equals
`det[C_0;…;C_5]` up to the sign of the Hodge permutation. This is the classical
statement that a closed 6-body loop is mobile exactly when its six hinge lines
lie in a **linear line complex**.

**Two traps this normal form sets, both worth recording.** *(a)* The reduced
object's branches may be **longer than 5**: deleting `β` drops two nodes of
`H/P` to degree 2 and merges their branches. (SD-6) bounds the branches of `G`,
not of `H/P − β`, and the driver observes reduced branches of length 6. Where
some `ℓ_j ≥ 6` the screw space `K_j = ⋂_e C_e^{⊥_B}` is generically **0** and
the branch is forced dead; the `6m × 6m` matrix is still the right object and
still square, but the "reduced order `6(n−1)` in the branch screws" reading is
only valid when every reduced branch has `ℓ_j ≤ 5`. *(b)* The welded body `X` is
**always** a body of `H/P − β` (it is a node of `H/P`, hence never a branch
interior), so at a bare-cycle site `X` always lies **on** the cycle.

**Measured** (`anhr1.py --size`, placement-free, over the full 4296-triple pool
of *Step A9*): 3820 triples carry a length-5 branch, giving **6426** labelled
instances of the pinned pool (not sites of the class — see the class-level
figures below); `c′` histogram `{0: 8, 1: 1904, 2: 3846, 3: 276, 4: 392}`
counts those same labelled instances; core-node histogram
`{0: 1912, 1: 134, 2: 3812, 3: 568}`; equilibrium-block order `6(n−1)`
histogram `{0: 142, 6: 5716, 12: 568}`. The identity `c′ = c(H/P) − 1` is
**asserted at all 6426 sites**. Cross-check of (ii) against the landed
machinery (`--reduce`): at all **58** length-5-branch sites of the (ANH-10)
census pool, the `6m × 6m` matrix's corank equals the dimension of the
`H/P − β` stress space rebuilt from scratch on the reduced edge list —
**58/58**, corank 0 at every one, reproducing (ANH-10)'s discharge through a
different matrix.

**Framing repair (2026-08-07, direction PEX) — the numbers above do not
change; every cell is a true labelled-instance count of the pinned pool.**
At the **class** level (§(K-frame) (FR-8)/(FR-14)): `c′ = 0` (`c(G) = 2`) is
**2** sites over **1** isomorphism class — θ(3,4,5), its unique inhabitant;
`c′ = 1` (`c(G) = 3`, the bare-cycle stratum) is **76** sites over **22**
isomorphism classes. At `c′ ≤ 1` the sweep above is **incomplete at the
iso-class level**: it carries 14 of the 22 `c′ = 1` classes, and §(K-frame)
(FR-8) supplies the complete list. The **29.6 %** ratio (`1904/6426`, *Step
A17*'s Verification table) survives as a **pool** ratio and should be read
as one — no class-level ratio is available, since the `c′ ≥ 2` cells sit
where the `|V°| ≤ 5` sweep cap genuinely binds.

**The boundedness is an artifact of the sweep, and the degree law is not.**
`n ≤ 3` and order `≤ 12` hold over the pool only because `outer.sweep_shapes`
caps `|V°| ≤ 5`; `n` is essentially the number of surviving hubs, `≤ 2c(G) − 1`,
and unbounded over the class — while `deg C = 12(c(G) − 2)` is unbounded
outright. The bounded end is therefore the **finite** end: `c(G) = 3` pins
`(|V|,|E|) = (16,18)`, finitely many graphs, and §(K-ind) *(I4)* says the
class's infinitude lives entirely in the `G°` direction, which is exactly the
direction `deg C` grows in. **`pencil/strategy.md` §2.2's ingredient-2 boundary appears here in
the mirror of §(K-Δ)'s (M3):** there the ground set was frozen at `[3]` and
never grew with the graph; here the certificate's *degree* grows with the graph,
and a bounded-size symbolic identity is impossible for exactly that reason.

### Step A15 — (ANH-14): the bare-cycle stratum has ONE pure condition, and it is irreducible

> **(ANH-14)** *(proven-informally; the algebra is an identity over the function
> field, the local-frame half is a placement-free combinatorial theorem with a
> driver over the whole pool)* At every bare-cycle site (`c′ = 1`):
>
> (a) **The local frame is a 7-point open chain** (or, degenerately, a 6-point
> closed hexagon). `X` always lies on the cycle ((ANH-13)'s trap (b)), and the
> six hinge lines are `C_i = z_i ∨ z_{i+1}`, `i = 0..5`, on seven points: five
> real far bodies and `X`'s **two companion attachment points**, which break
> the hexagon open. If those two coincide the chain closes and the object is
> (e)'s closed hexagon instead. **Either way one of two universal polynomials
> governs the site**, so the universality claim does not depend on which.
> (Measured: 7 distinct points at 6/6 bare-cycle sites of the (ANH-10) census
> pool; distinctness was **not** measured over the full 1904.)
>
> (b) **No panel of the pencil chart constrains that frame.** A panel `Π(u)`
> imposes a condition on the local points only when it carries `≥ 4` of them
> (three points always span a plane, and `pt(u)` may then be chosen inside it).
> **No bare-cycle site has such a panel: 1904/1904** over the whole 4296-triple
> pool, placement-free. Therefore the pure condition at a bare-cycle site is
> the pullback of **one shape-independent polynomial** in seven free points.
>
> (c) **That polynomial is irreducible of degree 12, and it is `≢ 0`.**
>
> (d) **Its square is an explicit bracket expression:**
> `det(Gram) = −C²`, where `Gram_{ij} = B(C_i, C_j) = [z_i, z_{i+1}, z_j, z_{j+1}]`
> has the five adjacent entries zero and ten surviving brackets. `C` itself is
> **not** a rational combination of the five non-adjacent perfect matchings of
> the six lines.
>
> (e) **The closed hexagon — the object at any loop whose body-cycle carries no
> `X`-break (the degenerate bare-cycle case of (a), and each factor of an
> `n = 1` site whose node is not `X`) — does have a two-term closed form:** for
> six points in a closed cycle,
>
>  `det[C_0;…;C_5] = B(C_1,C_3)B(C_3,C_5)B(C_5,C_1) − B(C_0,C_2)B(C_2,C_4)B(C_4,C_0)`,
>
> the ODD Gram triangle minus the EVEN one — an identity over the function
> field. It does **not** survive the break at `X`: (d) says the open chain has
> no such form.

*Proof of (c)'s irreducibility, which is the only non-computational step.*
`GL(4)` is connected, so it permutes — hence fixes — the irreducible factors of
the relative invariant `C`; each factor is therefore itself a relative invariant,
i.e. a bracket polynomial, and a relative invariant of weight `w` has total
degree `4w`. `deg C = 12`, so a factorization has a factor of degree 4, i.e. a
**single bracket**. On the gauge slice `z_0..z_3 = e_0..e_3` every bracket
meeting `{z_4, z_5, z_6}` stays non-constant, so irreducibility of the
restriction rules out every candidate factor except `[z_0z_1z_2z_3]`, which the
slice sends to 1; and that one is killed by a second specialization
(`z_0 = z_1+z_2+z_3`, which makes the bracket vanish while all six lines stay
nonzero) at which `C ≠ 0`. ∎

**On the gauge** (the same argument as §(K-Λ) `lambda1.m2` (M4)): `C` and every
triple-bracket product transform by `det(g)³` under `p ↦ gp`, so their
difference is a weight-3 relative invariant; for a configuration with
`z_0..z_3` independent, `g = [z_0|z_1|z_2|z_3]^{-1}` is the unique element of
`GL(4)` carrying them to the standard basis, so the slice meets that orbit
exactly once and vanishing on the slice gives vanishing on the dense open
`[z_0z_1z_2z_3] ≠ 0`, hence identically.

**What (ANH-14) does to (ANH-R1) at the bare-cycle stratum — say the logic
exactly, because the two directions are NOT symmetric.**

- **Refutation transports for free.** The pencil chart maps *into* the local
  frame's configuration space, so `C ≡ 0` on the latter would give `C ≡ 0` on
  every such shape's chart. (ANH-14)(c) says this does **not** happen: no shape
  of the stratum is refuted, and none can be by this route.
- **Identities transport for free.** (d), (e) and the irreducibility hold a
  fortiori on every shape's chart. This is the entire logical yield of the
  symbolic computation, and it is real.
- **Non-vanishing does NOT transport.** `C ≢ 0` on the local frame says nothing
  about `C ≢ 0` on a given shape's chart unless the chart **dominates** the
  frame. So at a bare-cycle shape,
  > **(ANH-R1) ⟺ the shape's pencil chart is not contained in the single fixed
  > irreducible hypersurface `{C = 0}`** — no rank condition, no matroid
  > condition, nothing but chart-to-frame dominance.
  That is **verbatim §(K-out) (OC-16)'s residue** on the other side of the arc,
  and it is the second time the same missing technology has been reached from
  an independent direction (the first pair being *Step A13* item 3's
  T/R convergence).
- **At any shape (ANH-10) covers, dominance is not needed:** the census's exact
  rational chart point already proves `C ≠ 0` there, by (ANH-9)(iii).

**A consequence for the `n = 1` stratum (134 sites), derived from the normal
form and (ANH-4).** There the equilibrium block is empty (`6(n−1) = 0`) and
`m = c′`, so the branch-screw matrix is **block-diagonal**, one `ℓ_j × 6` block
per loop, with `Σ_j ℓ_j = 6c′ = 6m`. If any `ℓ_j ≠ 6` some block is wider than
tall and the determinant vanishes **identically** — which (ANH-4)'s generic
independence of `E(H/P) − β` forbids. So every loop has length exactly 6, and

>  `C(H/P − β) = ∏_{j=1}^{c′} det[C_{j,0}; …; C_{j,5}]`,

a **product of `c′` bare-cycle pure conditions**, each an instance of (e) or of
(a)–(d) according to whether that loop's node is `X`. So the M2-computable
strata are `c′ = 0` (8 sites), `c′ = 1` (1904) and `n = 1` (134) —
**2046 of 6426 = 31.8 %** of length-5-branch sites. Note this is the arc's only
*genuine factorization* of a pure condition on this side, and it is a
consequence of the graph splitting, not of the algebra: the factors themselves
are irreducible by (c).

**And a contrast that shows the universality is special.** At the *other* sites
the local frames **are** constrained: the forced-coplanarity histogram is
`{0: 122, 1: 3396, 2: 540, 3: 264, 4: 200}`. So no shape-independent polynomial
governs them, and the θ-core computation below is per-type, not universal.

### Step A16 — (ANH-15): the bad locus strictly contains (ANH-11)'s

> **(ANH-15)** *(proven; (a) symbolically over the function field, (b) at an
> exact rational witness — an existence claim)*
>
> (a) **(ANH-11) on the chain object.** Anchor `L = z_1 ∨ z_4`. The four lines
> incident to `z_1` or `z_4` meet `L` automatically; placing `z_3` in the plane
> `⟨z_1, z_4, z_2⟩` and `z_6` in `⟨z_1, z_4, z_5⟩` makes the other two meet it.
> On that locus all six lines are `B`-perpendicular to `C(L)` and
> `C(H/P − β) ≡ 0` **identically**. So (ANH-11)'s mechanism is now a symbolic
> identity on the universal object, not only a property of nine sampled
> witnesses.
>
> (b) **A second, AXIS-FREE mechanism.** The screw `S = C(e_0e_1) + C(e_2e_3)`
> has `B(S,S) ≠ 0`, so it is no line extensor and its linear complex has no
> axis: lines in it have **no common transversal**. An explicit integer 7-point
> chain lies entirely in that complex, its six lines have `B(C_i, S) = 0`, their
> Plücker matrix has rank exactly **5** (so the perp is exactly `⟨S⟩`), and
> `C = 0` there. Hence
>
>  `{C = 0}` ⊋ `{`the six lines have a common transversal`}`,
>
> and (ANH-11) reaches only part of the bad locus. This is the localized form of
> §(K-σ) *Step σ6* / `pencil/strategy.md` §2.4's null-correlation device.
>
> (c) **Consistency with (ANH-12), checked in this section's own object.**
> Re-running `shrink.construct_at` read-only and evaluating the branch-screw
> matrix at each constructed bad point: at the **6 (ANH-R1)-exact** witnesses
> (β of length 5, count 0) the matrix is square and has **corank 1 — the pure
> condition vanishes at 6/6** — and the three matroid-drop witnesses
> (NT21/NT24/NT30, count `< 0`) also show corank 1. All **9** (ANH-12) witnesses
> lie in the pure condition's zero locus, as they must.

**What (b) does and does not say.** It says the *universal local* bad locus has
a component (or components) beyond the transversal locus, so
(ANH-12)'s *What would change this* item (iv) — *"a shape where no
cycle/labeling makes the construction work"* — would not by itself empty the bad
locus: a second mechanism is available in principle. It does **not** say the
pencil chart reaches that component at any class shape; whether it does is
open, and settling it is the same dominance question as everywhere else here.

### Step A17 — (ANH-16): the verdict on the method, and what is per-shape versus uniform

> **(ANH-16)** *(the pass's methodological finding; the cost figures are
> measured)*
>
> (i) **The per-shape M2 identity is the pointwise restatement of (ANH-R1)**
> (WW87 Cor. 2.7, in §(K-pure) *Step P0*'s reading), so at any shape carrying a
> guarded chart point it adds **no logical strength** over (ANH-9)(iii) + the
> exact-ℚ census — which decides the same question in seconds where the
> symbolic route takes minutes and, past the bare-cycle stratum, does not
> terminate. *Step A13* item 4 is hereby answered and **struck as an upgrade
> route**; what survives of it is (ANH-14).
>
> (ii) **Measured reach.** Generic point, ungauged: degree 12 in 24 point
> indeterminates, 10944 terms, **578 s** (finishes). A θ(5,5,2) core at the
> generic point: 12 free points, 48 indeterminates, two 5 × 6 Klein-perp
> kernels — **does not finish at 600 s**. With §(K-Λ)'s recorded kill (degree 52
> in 28 indeterminates) the layer's boundary is bracketed from both sides. On a
> **gauge slice** the bare-cycle identity is ~0.4 s, which is why the driver
> gauges.
>
> (iii) **Per-shape versus uniform, stated as the dispatch requires.** The
> *identity's proof* at the bare-cycle stratum **is uniform** — one polynomial,
> one computation, every shape of the stratum, with the local frame's
> unconstrainedness verified combinatorially at **1904/1904** sites. But the
> *transfer* to (ANH-R1) is **not**: it needs chart-to-frame dominance per shape
> (or, at a probed shape, the census witness). **Class uniformity therefore does
> not move**, and this section does not claim it does. What moves is the shape
> of the residue: at the bare-cycle stratum (ANH-R1) has **no rank condition
> left**, exactly as §(K-out) (OC-16) reports at degree-3 hubs.
>
> (iv) **No (ANH-7)-style recipe exists for (ANH-R1)'s own certificate**, by
> (ANH-14)(c)'s irreducibility. The arc's two closed forms — §(K-Λ) (Λ1)'s
> product of two linear forms and (ANH-7)'s single 4-point bracket — both came
> from reducible objects. This one is irreducible, and that is a theorem, not a
> failure to find a factorization.

### Verification (Steps A14–A17)

`notes/scripts/w4/anhr1.py` (**new with this continuation**; exact ℚ, stdlib
only, **no rng of its own** — every placement arrives through
`dominance.base_seed`'s composite guard `repin.star_generic` via
`annih.prepared`; imports only catalogued §1 primitives and the two owning
drivers read-only: `annih`'s `prepared` / `stress_space` / `hp_branches` /
`branch_screw` / `habitats4` / `control_shapes` / `swept_probes` /
`path_edges`, `shrink`'s `hp_edge_rows` / `branch_edge_ix` / `census_pool` /
`stress_dim_without` / `construct_at`, `outer`'s `split_data` / `companions4` /
`named_inventory` / `sweep_shapes`, `repin`'s `hodge_star`, `pitch`'s `klein`,
`kbare_common.verts_of`, and `exactcore`'s `rank` / `nullspace` / `wedge2` /
`hat` / `neighbors`). Run from the repo root:

```
PYTHONHASHSEED=0 python3 notes/scripts/w4/anhr1.py --types     # (ANH-13)(ii), the local-type census   62 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/anhr1.py --reduce    # (ANH-13)(ii) against the full solve   80 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/anhr1.py --size      # (ANH-13)(i)/(iii), (ANH-14)(b)        12 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/anhr1.py --frame     # (ANH-14)(a)/(b) at the census sites   63 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/anhr1.py --witness   # (ANH-15)(c)                           81 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/anhr1.py --validate  # the machinery                         <1 s
M2 --script notes/scripts/m2/anhr1.m2                          # (ANH-14)(c)(d)(e), (ANH-15)(a)(b)     <1 s
```

All six Python modes verified **byte-identical** under `PYTHONHASHSEED` `0` and
`999`, exit 0 at every one; the M2 driver byte-identical across two runs, 18
assertions, final line `PASSED`. Every invocation fits the 600 s foreground
budget with room to spare — which is itself the point of (ANH-16)(i): the
decision procedure the symbolic route would replace costs seconds.

`notes/scripts/m2/anhr1.m2` (**new**; the M2 layer's third driver, after
`lambda1.m2` and `lambda0.m2`). It obeys the layer's four conventions
(`notes/scripts/m2/README.md`): its output is **evidence, never a substitute for
a Lean proof**; it prints the pinned version line `1.26.06` second and
`randomness: none`; it lives only in `m2/`; and it is **additive** — it ports no
Python driver, and `annih.py` / `shrink.py` keep every recorded figure
unchanged. Convention 3's divergence pin is block **(ANH-Q0)**: the bracket
dictionary `B(C(uv), C(pq)) = [u,v,p,q]` tying the M2 re-derivation of
`PL` / `wedge2` / `hodge_star` / `klein` / `det4` to their canonical Python
homes, plus the two structural corollaries (line extensors are isotropic; two
lines through a common point pair to 0 — which is why a body-hinge cycle placed
by *joins* always has a banded Gram).

Adding these two drivers modified **no** tracked script, so the
figure-invariance gate discharges on the `git diff --name-only -- '*.py' '*.m2'`
check alone (`notes/scripts/README.md`, first bullet).

Per mode, what is asserted. `--types`: per site, that the branch-screw matrix is
square (`6m = |E′| + 6(n−1)`), the excess is 0, and the local type signature.
`--reduce`: corank of the branch-screw matrix **equals** `stress_dim_without`'s
independent from-scratch rebuild, both directions, at every site. `--size`:
`c′ = c(H/P) − 1` at every site, and **`forced == 0` at every bare-cycle site**
(the (ANH-14)(b) assertion). `--frame`: per census bare-cycle site, the point
chain and the panel local-incidence histogram, asserting no forced coplanarity.
`--witness`: at each (ANH-12) witness, corank `≥ 1` of *this* driver's matrix,
asserted where the object has count 0. `--validate`: the core decomposition and
the count identity on a synthetic bare 6-cycle and a synthetic θ(4,4,4) core.
M2 blocks: **(ANH-Q0)** the dictionary pin; **(ANH-Q1)** the closed-hexagon
identity; **(ANH-Q2)** the open chain — not in the matchings' span, `≢ 0`,
`det Gram = −C²`, irreducible on the slice, and no `[z_0z_1z_2z_3]` factor;
**(ANH-Q3)** both bad-locus mechanisms; **(ANH-Q4)** the θ(5,5,2) core's 2 × 2
form and its exact witness.

**Figures.**

| figure | value |
|---|---|
| `--size` pool | **4296** (shape, split, length-4 companion) triples; **3820** with a length-5 branch; **6426** length-5-branch sites |
| `--size`: `c′ = c(G) − 2` | histogram `{0: 8, 1: 1904, 2: 3846, 3: 276, 4: 392}`; the identity `c′ = c(H/P) − 1` asserted at **6426/6426** |
| `--size`: core nodes `n` | `{0: 1912, 1: 134, 2: 3812, 3: 568}` |
| `--size`: `deg C = 12c′` | `{0: 8, 12: 1904, 24: 3846, 36: 276, 48: 392}` |
| `--size`: bare-cycle stratum | **1904 / 6426 = 29.6 %**; with the `n = 1` and trivial strata, **2046 / 6426 = 31.8 %** is M2-computable |
| `--size`: unconstrained local frames | **1904 / 1904** bare-cycle sites have NO panel forcing a coplanarity (asserted) |
| `--size`: the other sites | forced-coplanarity histogram `{0: 122, 1: 3396, 2: 540, 3: 264, 4: 200}` — universality is special to the bare-cycle stratum |
| `--types` | **26** triples with a guarded seed, **58** length-5-branch sites (matching (ANH-10)'s 58), **44** distinct local types |
| `--reduce` | branch-core normal form agrees with the from-scratch solve at **58/58** sites; corank **0** at every one |
| `--frame` | **6** bare-cycle census sites; **7** distinct points at each; **6/6** with an unconstrained local frame |
| `--witness` | **6** (ANH-R1)-exact witnesses, pure condition vanishes at **6/6**; 3 matroid-drop witnesses also corank 1; 1 trivial θ(3,4,5) |
| M2 `(ANH-Q1)` | `det[C] = B(C_1,C_3)B(C_3,C_5)B(C_5,C_1) − B(C_0,C_2)B(C_2,C_4)B(C_4,C_0)` |
| M2 `(ANH-Q2)` | `C` irreducible, degree 12; `det Gram = −C²`; **not** in the 5 matchings' span |
| M2 driver | **18** assertions, ~0.4 s, version line `1.26.06`, `randomness: none`; byte-identical across two runs |
| feasibility, ungauged | degree 12 / 24 indeterminates, 10944 terms: **578 s wall clock, finishes** (whole-script, the determinant dominating); θ core at the generic point (48 indeterminates): **no finish at 600 s** |
| determinism | all six Python modes byte-identical across `PYTHONHASHSEED` `0` and `999` |

**Which driver tests which sentence (F11).**

| claim | mode | what asserts *that sentence* |
|---|---|---|
| (ANH-13)(i) | `--size` | `c′ = c(H/P) − 1` asserted per site over the whole pool; the arithmetic `c(H/P) = c(G) − 1` is *Step A14*'s proof, not the census |
| (ANH-13)(ii) | `--types`, `--reduce` | squareness `6m = |E′| + 6(n−1)` per site, and corank equality against an **independently rebuilt** stress space at 58/58 |
| (ANH-13)(iii) | — | **proof-level** (each transmissibility row is quadratic in the points); its input histogram is `--size`'s |
| (ANH-13)(iv) | `--size`, `--reduce` | `n = 0` at exactly the `c′ ≤ 1` sites in the two histograms; at `n = 0` `core_matrix` **is** the 6 × 6 Plücker matrix, and `--reduce` checks its corank against the from-scratch solve |
| (ANH-14)(a) | `--frame` | the point chain printed per site, with the count of distinct points |
| (ANH-14)(b) | `--size`, `--frame` | the panel local-incidence histogram, with `forced == 0` **asserted**, at 1904/1904 pool sites and 6/6 census sites |
| (ANH-14)(c) | `(ANH-Q2)` | `C ≠ 0`; `#factor == 2` on the slice; and the second specialization killing the one bracket the slice cannot see. The `GL(4)`-connectedness step is **proof-level** and named as such |
| (ANH-14)(d) | `(ANH-Q2)` | the matching-span solve returning `null`, and `det Gram + C² == 0` |
| (ANH-14)(e) | `(ANH-Q1)` | the identity itself on the gauge slice, plus the recorded ungauged 578 s confirmation |
| (ANH-15)(a) | `(ANH-Q3)` | all six pairings with `C(L)` zero **and** `det == 0`, symbolically |
| (ANH-15)(b) | `(ANH-Q3)` | the explicit chain: `ω(z_i,z_{i+1}) = 0`, all lines nonzero, `B(C_i,S) = 0`, `det = 0`, **rank exactly 5** |
| (ANH-15)(c) | `--witness` | corank at the reconstructed (ANH-12) bad points, in this section's matrix |
| (ANH-16)(i) | — | **argument**, from (ANH-9)(iii) + §(K-pure) *Step P0*; no driver can test a redundancy claim |
| (ANH-16)(ii) | — | **measured wall-clock**, both the finish and the kill; the kill's reconstruction recipe is in the driver's header comment |
| **(ANH-R1)** | — | **still none, and still the point.** Nothing here tests class uniformity; (ANH-14) tests one polynomial, (ANH-16)(iii) says what that does and does not buy |

### Confidence verdict (Steps A14–A17)

- **(ANH-13): proven** — (i) and (ii) are counting and linear algebra, (iii) is
  immediate, and (ii) has a driver comparing it to an independent solve at
  58/58 sites. The size law is the pass's most transportable output.
- **(ANH-14): proven-informally.** (a) is measured (6/6) with the degenerate
  closure **not excluded combinatorially** — a named soft spot. (b) is a
  placement-free combinatorial theorem asserted at 1904/1904 pool sites, but
  the pool is `outer.sweep_shapes`, so "every class shape" is **not** proven —
  what is proven is the criterion (`≥ 4` local incidences) and its verification
  over the pool. (c)/(d)/(e) are identities over the function field, gauge-
  transported by the argument above; (c)'s irreducibility rests on the
  `GL(4)`-connectedness step, which is standard but is **prose, not machine-
  checked**.
- **(ANH-15): (a) proven** (an identity), **(b) proven at an exact witness**
  (an existence claim), **(c) measured** at 9/9 reconstructed witnesses.
  The class-wide reading "the extra component is reachable inside the pencil
  chart" is **NOT claimed** — it is open.
- **(ANH-16): (i) is an argument, and it is only as strong as (ANH-9)(ii)** —
  it is (ANH-9)(iii) plus §(K-pure) *Step P0*, both already in the workbook, and
  it inherits (ANH-9)(ii)'s **proven-informally** irreducibility of the pencil
  chart. That dependence is shared, not differential: an M2 identity needs the
  same irreducibility to mean "the generic point", so nothing about the
  comparison changes if (ANH-9)(ii) is ever sharpened. (ii) is **measured**;
  (iii)/(iv) are the honest statements of what this pass did and did not
  deliver.
- **(ANH-R1): OPEN, unchanged in status.** Its profile sharpens once more: at
  the bare-cycle stratum it is a chart-to-frame dominance question against one
  fixed irreducible hypersurface, with no rank condition left — the same shape
  as §(K-out) (OC-8)/(OC-16), reached independently for the third time.
- **Class uniformity is untouched. No gap-map status moves.**

### What would change this (Steps A14–A17)

*(i)* **A chart-to-frame dominance theorem** — that a class shape's pencil chart
dominates its bare-cycle local frame — would close (ANH-R1) on the **whole**
`c(G) = 3` stratum in one step, since (ANH-14) has already done the algebra.
It is the same missing statement as §(K-out) (OC-16)'s residue, and the two
should be attacked together: a single dominance lemma for "the chart surjects
onto the free configuration of a panel-unconstrained local frame" would serve
both. **This is the direction's chief hand-off.**

*(ii)* **A bare-cycle class shape whose chart lies inside `{C = 0}`** would
refute (ANH-R1) there and, with it, (ANH-7) at that shape. None exists among the
shapes (ANH-10) probes (the census witnesses forbid it), so the hunt would have
to run at unprobed `c(G) = 3` shapes — where a single exact rank computation is
still the cheapest test, by (ANH-16)(i).

*(iii)* **A degenerate bare-cycle site where `X`'s two cycle edges hang off the
SAME companion vertex** would make the local object the *closed* hexagon of
(ANH-14)(e) rather than the open chain, and would then inherit that stratum's
two-term closed form. Not observed (0/6 census sites); not excluded by any
argument here.

*(iv)* **A pencil-chart witness inside (ANH-15)(b)'s axis-free component** would
show the bad locus is inhabited by a mechanism (ANH-11) cannot construct, and
would strengthen (ANH-12)'s class-wide reading from "measured at 9/9 by one
construction" to "two independent constructions". The construction is
one linear condition per chain step, so it is a plausible target for a
`shrink.py --bad`-style solver.

*(v)* **A symbolic route past the bare-cycle stratum** — the θ-core generic
point is a 600 s kill as posed, but the object is a **2 × 2** determinant in two
pinned branch screws `κ_1, κ_2` (each a degree-10 bracket vector, *Step A6*), so
a formulation that carries `κ` symbolically without expanding the 5 × 6 kernel
might get through. That would extend the universality question — though not the
universality itself, since those local frames are panel-constrained
(3396 sites carry a forced coplanarity).

*(vi)* **An error in the branch-core normal form** — guarded by `--reduce`'s
comparison against a from-scratch rebuild of the reduced stress space at 58/58
sites, by `--validate`'s synthetic bare-cycle and θ-core checks, and by
`--witness` finding corank exactly where (ANH-12) says it must be.

