## §(K-pure) — the pure condition of the limit carrier, un-specialized: the wrong invariant, the chord obstruction, and the support lever (**direction C REFUTED as a strategy; (K-slide-cl) REFUTED as stated; 5 of 6 flank shapes closed by reduced supports**)

Sibling of §(K-slide-cl)/§(K-slide-comb), answering the fan-out's **direction C**
(`notes/Pencil-fanout-archive.md` §"Direction C"). Standing notation inherited (`G°` the
hub multigraph on `n = |V°|` hubs, lengths `ℓ`, `E° = E(G°) ∖ {e₀}`, split edge
`e₀ = bc` of length 3, decorations, the slide support `Σ`, the per-edge limit
chain span `S_P` of dimension `ℓ_P`, witnesses (W1)–(W4),
`T = ⟨C_ab, C_ac⟩`, the reciprocal twist `z`, the pitch `Q`, the Klein form `B`).
Three new pieces of notation:

- `R_P := S_P^{⊥_B}` — the **available bars** of `G°`-edge `P`, of dimension
  `6 − ℓ_P`. The hub-level limit rows for `P` are `m ↦ B(m(u) − m(w), ρ)`,
  `ρ ∈ R_P`, so a **stress** of the limit carrier is an assignment `ρ_P ∈ R_P`
  with `Σ_{P ∋ u} ±ρ_P = 0` in `Λ²K⁴` at every hub, and a **loaded stress with
  load `ω`** is one whose vertex sums vanish except for `±ω` at `b`, `c`.
- `α(u) := {ω : ω ∧ û = 0} = û ∧ K⁴` — the 3-dimensional **totally isotropic**
  α-space of `pt(u)`: `ω ∧ û` is the velocity the twist `ω` gives the point
  `pt(u)`, so `α(u)` = the twists fixing `pt(u)`.
- `π := plane(pt a, pt b, pt c)`, with `Λ²π̂ = ⟨C_ab, C_ac, C_bc⟩` — 3-dimensional
  (three sides of a non-degenerate triangle) and **totally isotropic** (coplanar
  lines meet). `α(a)` and `Λ²π̂` are the **only two** maximal totally isotropic
  3-spaces containing `T`, and `T = α(a) ∩ Λ²π̂` — the classical fact that the
  maximal isotropics of the Klein quadric are the α-planes (lines through a
  point) and β-planes (lines in a plane), and that a pencil determines its vertex
  and its plane uniquely.

**Verdict (2026-08-05, sixth pass; fan-out direction C).**

(i) **Direction C is REFUTED as a strategy — not merely unproven.** WW87's pure
condition is a **rank** certificate: by their Cor. 2.7 it is nonzero at a
realization iff that realization is `k`-isostatic, which for the limit carrier
is exactly **(W1) ∧ (W2)** (Step P0). The escape needs (W1)–(W4), and (W4) is
not a rank condition: it asks whether a distinguished kernel vector is **off the
Klein quadric**. Measured at four class shapes — θ(3,4,5) 14/14 seeds, `K5`
`(3,3,3,4,3,4,4,4,4,4)` 12/12, `K5` `(3,3,3,4,4,4,4,4,4,3)` 12/12, `K222`
octahedron 11/11 — **(W1) ∧ (W2) hold at every valid seed** (so the pure
condition is already known *not* to vanish identically there) **and `Q(z) = 0`
at every one**. A non-vanishing theorem for `C(G°-limit)`, however
un-specialized, would leave the escape unsettled at exactly the shapes it was
commissioned to reach. `pure.py --pure`.

(ii) **The right object, exactly — (PC-Z).** Under (W1)–(W3),
> **`Q(z) ≠ 0` ⟺ `V_bc ∩ Λ²π̂ = 0` and `V_bc ∩ α(a) = 0`.**

So (W4) is the non-vanishing of **two `6×6` incidence determinants** of `V_bc`
against two *fixed totally isotropic 3-spaces* — not of a rank determinant. This
is the pure-condition-shaped object direction C was reaching for, and it is a
different polynomial from `C(G°-limit)`. Proven-informally (Step P3), asserted
against the computed `Q(z)` at **every seed of every mode**.

(iii) **(PC1)–(PC3)/(PC-OBS): the chord obstruction, proven-informally — the
arc's first identically-vanishing-pitch theorem.** Every limit line of a "short
and slid" `G°`-edge passes through `pt(u)` or `pt(w)`, hence **meets the chord**
`C_uw`; so `C_uw ∈ R_P` (PC1). Chord bars in equilibrium are **precisely** the
projective **bar-and-joint** self-stresses of the *hub-point* framework on those
edges (PC2). A chord self-stress using `e₀` forces `V_bc ⊆ C_bc^{⊥_B}`, whence
`V_bc ∩ Λ²π̂ ≠ 0` and, by (PC-Z), **`Q(z) = 0` at every decoration** (PC3). The
governing invariant is therefore **`R_3`-dependence** — the generic
**3-dimensional bar-and-joint** rigidity matroid of the hub graph — a completely
different matroid from the 6-fold graphic union that (C6) is about.
`pure.py --chord`.

(iv) **(K-slide-cl) is REFUTED as stated.** At the `K5` 5-chromatic flank shapes
`(3,3,3,3,4,4,4,4,4,4)`, `(3,3,3,4,3,4,4,4,4,4)`, `(3,3,3,4,4,4,4,4,4,3)` —
explicit **tight + `hnoRigid`** class members with `hcard`/`htf`, exactly the
ones §(K-slide-comb) exhibited — and at **θ(3,4,5)**, the **full-support**
slide-in limit system fails (W4) (or (W3)) at **every** decoration by (iii). So
"generic decorations of the slide-in limit system satisfy (W1)–(W4)" is *false*
at class shapes, not merely open.

> **Two refutations, two mechanisms — do not conflate them.** The arc now
> carries two distinct negative results, and they are independent.
> §(K-slide-comb) (2026-08-05, fifth pass) refuted the collapse's
> **combinatorial antecedent** (K-slide-comb) class-wide: its *colouring*
> premise fails inside the class (`χ(K5) = 5`; acyclic 4-colourability is not
> implied by 3-degeneracy). What (iii)/(iv) refute is the **statement**
> (K-slide-cl) *itself*, at the full support, by the **chord obstruction**
> (PC-OBS) — an `R_3`-dependence mechanism with **nothing to do with
> colouring**, and one that would fire even if every class shape were
> acyclically 4-colourable. The two conditions first bite at the same shape
> (`K5`) by an arithmetic coincidence, not by a common mechanism — Step P4
> separates them.

(v) **But the slide support is the lever, and it clears the whole probed flank
list.** (S1) remark (iii) makes `Σ` free, and `E_chord(Σ)` **shrinks with `Σ`**
(an `ℓ = 3` edge is chord-obstructed iff ≥ 1 end is slid, an `ℓ = 4` edge iff
both are, `ℓ = 5` never). Dropping the slide at the `c`-side interiors produces
full **(W1)–(W4) witnesses** — which is all (S1) consumes, *one* witness — at all
three obstructed `K5` 5-chromatic flank shapes (2/3, 3/3, 3/3 sampled seeds), at
the **`K222` octahedron flank** (3/3) and at **θ(3,4,5)** (3/3). So the slide
device **closes** those splits, and the gap map's `χ(G°) ≥ 5` row, its `K222`
entry and (for θ(3,4,5)) its parallel-`G°`-edge row stop being uncovered. The
**6v11e acyclicity flank** failed **(W2)** (`dim V_bc = 2`) at all four nonempty
probed supports, with only the degenerate `Σ = ∅` (the `ε = 1` chart, where (S1)
is **vacuous**) pitched; its split closed anyway, by the (K-pitch) Step-0
one-witness argument — full chart transfer certificates ((T1)–(T3) +
`Q(r) ≠ 0`, `dim R_a = 1`, the (T2) side conditions) at **11/11** valid seeds.
`pure.py --support`. *(Superseded 2026-08-06, §(K-mech): the four probed
supports all omitted b/c-side interiors — exactly the omissions (MX-6)'s flex
ledger shows keep both routes alive; a single far-side omission rescues the
device, (MX-7), so 6v11e is now closed by the slide device too.)* **This answers
§(K-flank) *Step F7* item 2**, which named reduced slide supports at the
structural flanks as the single most valuable follow-up its data pointed at.

(vi) **WW87 Thm 2.18 cannot transfer to the decoration variety** — direction C's
other half is independently dead. The decoration variety is a **proper closed
subvariety** of `∏_{P ∈ E°} Gr(6 − ℓ_P, 6)`, and Thm 2.18's
"packing ⟹ pure condition ≢ 0" is about the *generic point of the ambient
space*. Exhibited: at `P21` the free-bar system with the same multiplicities has
rank `15/15` (**independent**) and the (C6) packing exists, yet the
decoration-variety rows are **dependent at every support** ((S5), reproduced by
`kslide.py --flanks`). `pure.py --pure`.

(vii) **The parallel-`G°`-edge row is corrected in mechanism and in scope.**
(S5) proves a **(W1)** failure for two parallel **length-3** chains; that
mechanism **cannot occur inside the tight + `hnoRigid` class at all**, because a
parallel pair of lengths `(ℓ₁, ℓ₂)` is a cycle `C_{ℓ₁+ℓ₂}` of `G`, `C_k` is
rigid for `k ≤ 6` (R3), and a proper rigid subgraph contradicts `hnoRigid` — so
`ℓ₁ + ℓ₂ ≥ 7` and `(3,3)` is out (`P21` is thereby a **(K-res)** residual, not a
tight class member). At θ(3,4,5) — a parallel-edge shape that *is* tight +
`hnoRigid` — (W1) and (W2) **hold** at every probed seed and the full-support
obstruction is (W4) **by the chord stress** (two parallel bars `{e₀, the ℓ = 4
edge}` between `pt(b)` and `pt(c)` self-stress at *every* placement). And a
reduced support closes it. `pure.py --parallel`.

(viii) **Residual, unidentified.** Two (W4)/(W2) failures are *not* chord-stress
failures: the `K222` flank and the `K4` shape `(1,1,3,5,4,4)` fail (W4) with no
chord stress — measured cause `V_bc ∩ Λ²π̂ ≠ 0`, but **why** that codimension-1
incidence is forced there is open — and the **6v11e** flank's `dim V_bc = 2` has
no mechanism at all. Note `(1,1,3,5,4,4)` has `G° = K4`, so the residual
mechanism is *not* a dense-hub-graph phenomenon.

**What would change this.** *For (i)/(vi):* a reading of WW87 §2 under which the
pure condition sees more than isostaticity — Cor. 2.7 is explicit that it does
not. *For (ii):* an error in the two-maximal-isotropic-completions claim; it is
asserted per seed against the independently computed `Q(z)`. *For (iii):* an
error in the transversal bookkeeping (`C_uw ∈ R_P` is measured per edge per
decoration and cross-checked against the length/support rule on 90 instances) or
in the `★`-convention of the equilibrium identification (the chord stress is
assembled as an explicit row combination of the **actual** limit rows and its
covector checked to be a nonzero multiple of the `C_bc` load). *For (iv):* a
full-support decoration at one of the three `K5` shapes with `Q(z) ≠ 0` —
impossible by (PC3) unless `K5` is `R_3`-independent, which the Maxwell count
`10 > 3·5 − 6` forbids at *every* placement. *For (v):* the support menu is 5 of
the `2^{#slid interiors}` supports, so "not rescued" is not a verdict; a shape
where **no** support gives a witness would be the real class-level refutation,
and none is exhibited. *For (viii):* a mechanism for `V_bc ∩ Λ²π̂ ≠ 0` at
`K222`/`(1,1,3,5,4,4)` and for the 6v11e (W2) drop.

### Step P0 — what "the pure condition of the limit carrier" is, exactly

By (S2) the limit carrier is the hub-level serial-chain system: bodies at the
hubs of `G° − e₀`, one constraint `m(u) − m(w) ∈ S_P` per `P ∈ E°`, i.e.
`6 − ℓ_P` rows, `6n − 9` in total by tightness (Step C0). Close it up by adding
three rows `B(m(b) − m(c), ρ) = 0` for `ρ` in a **generic** 3-space `R₀`: the
system becomes `6(n−1) × 6n`, the body-bar shape of the multiplicity-weighted
`Ĝ` (`P` with multiplicity `6 − ℓ_P`, `e₀` included) that (C6) packs into six
spanning trees. Two facts fix the object.

- **The pure condition is the isostaticity determinant, and it sees (W1) ∧ (W2)
  and nothing more.** WW87 Prop. 2.6 makes `C(G) = det M(G, T)` a bracket
  polynomial; Cor. 2.7 says `C ≠ 0` at a realization iff it is `k`-isostatic.
  Adding `R₀`'s rows cuts `ker` by `dim V_bc − dim(V_bc ∩ R₀^{⊥_B})`, which for
  generic `R₀` is `dim V_bc`; so the closed-up carrier is isostatic (`ker` = the
  6 trivial twists) **iff** the `E°`-rows are independent ((W1), `dim ker = 9`)
  **and** `dim V_bc = 3` ((W2)).
- **"`C ≢ 0` on the decoration variety" is not a new statement.** The decoration
  variety is irreducible (a tower of affine-linear fibres, (S1)(e)), so
  `C ≢ 0` ⟺ some decoration is isostatic ⟺ (W1) ∧ (W2) generically. That is a
  *restatement* of half of (K-slide-cl), not a lever. A lever must be a
  **technique** for proving non-vanishing, and WW87 offers two: Cor. 2.7
  (pointwise — the restatement) and Thm 2.18 (combinatorial — Step P6 kills its
  transfer). Thm 2.18's own proof is a **specialization** (one shared coordinate
  frame per spanning tree), i.e. the tetrahedral collapse. So "un-specialized"
  can only mean "find an induction, or a better specialization"; it cannot mean
  "work with `C` directly".

### Step P1 — (PC1): on a short slid edge the chord is always a legal bar

> **(PC1)** *(proven-informally)* Under a slide support `Σ`, all limit lines of
> `G°`-edge `P = uw` meet the chord `C_uw = p̂t(u) ∧ p̂t(w)`, hence
> `C_uw ∈ R_P = S_P^{⊥_B}`, **iff**
>
>     ell = 1 : always            (the chain IS the chord)
>     ell = 2 : always            (both lines are hub-incident)
>     ell = 3 : at least one end slid
>     ell = 4 : both ends slid
>     ell = 5 : never.
>
> Call such an edge **chord-obstructed** and write `E_chord(Σ) ⊆ E°` for the set
> of them. At the full support `E_chord = {P ∈ E° : ℓ_P ≤ 4}`; at `Σ = ∅`
> (the `ε = 1` chart) `E_chord = {P : ℓ_P ≤ 2}`.

*Proof.* Two lines of `P³` meet iff `B = 0`; `pt(u)` and `pt(w)` both lie on
`C_uw`; so it suffices that every limit line pass through one of them. Read off
the limit-line rule ((S1)(b), the (S2) dictionary): a hub-incident hinge gives
the constant pencil line at its hub; a hinge with exactly one slid end gives
`p̂t(h) ∧ (the other point)`, through the hub `h` its slid interior collapsed to;
a slid–slid hinge gives the chord; an unslid–unslid hinge keeps its original
line, through neither hub. On `[u, y₁, …, y_{ℓ−1}, w]` the support touches only
`y₁, y_{ℓ−1}`, so only a *middle* hinge can fail to be hub-incident: `ℓ = 3` has
the one middle hinge `y₁y₂`, hub-incident as soon as either end is slid; `ℓ = 4`
has `y₁y₂` and `y₂y₃`, needing `y₁` resp. `y₃`; `ℓ = 5` has `y₂y₃` with neither
end ever slid, so it keeps a generic line missing the chord; `ℓ ≤ 2` has no
middle hinge. ∎

`ℓ = 5` is the one length that escapes — the same asymmetry §(K-slide-comb) Step
D4(b) saw from the other side (at `ℓ = 5` the transversal `R_P` need not be a
basis line).

### Step P2 — (PC2): chord bars in equilibrium are bar-and-joint self-stresses

> **(PC2)** *(proven-informally)* Put `ρ_P = λ_P · C_uw` on each
> `P ∈ E_chord(Σ)` and `0` elsewhere (legal by (PC1)). The resulting loaded-stress
> condition — vertex sums `0` at every hub except `±λ_{e₀} C_bc` at `b`, `c` — is
> **exactly** the self-stress condition of the **bar-and-joint framework**
> `(E_chord(Σ) ∪ {e₀}, pt)` in 3-space, with `e₀ = bc` an extra bar of
> coefficient `λ_{e₀}`.

*Proof.* The signed sum at hub `h` is `★(ĥ ∧ Σ_{P ∋ h} λ_P ô_P)` (`ô_P` = the
other end's homogenised point; the `★` is the harness's Euclidean-vs-Klein
bookkeeping — `rows_from_lines` pairs Euclideanly, so the legal per-edge
coefficient space is `S_P^{⊥_E} = ★R_P` and the chord contributes `★C_uw`; `★`
is linear and invertible, so it does not change the condition). It vanishes iff
`Σ_{P ∋ h} λ_P ô_P ∈ ⟨ĥ⟩`, i.e. affinely iff `Σ_{P ∋ h} λ_P = μ_h` and
`Σ_{P ∋ h} λ_P o_P = μ_h h`, i.e. iff `Σ_{P ∋ h} λ_P (o_P − h) = 0` — the
bar-and-joint equilibrium (the classical projective invariance of self-stresses).
At `b`, `c` the same computation leaves the residual `±λ_{e₀} ★C_bc`. ∎

So the obstruction is governed by the generic **3-dimensional bar-and-joint**
rigidity matroid `R_3` of the hub graph. This is the pass's structural punch
line: the collapse's combinatorics was a 6-fold **graphic-union** question
((C6), (C1)'s six forest classes); the invariant that decides the *pitch* is an
`R_3`-dependence question about the hub points. Different matroids, and (C6) —
uniform and proven — says nothing about this one.

**Decoration-free sufficient conditions.** A `λ` with `λ_{e₀} ≠ 0` exists at
generic hub points iff `e₀ ∈ cl_{R_3}(E_chord(Σ))`. Two cases need no genericity
at all:

- **Maxwell count.** If `F ⊆ E_chord(Σ) ∪ {e₀}` has `|E(F)| > 3|V(F)| − 6` then
  `F` self-stresses at *every* placement; if `F − e₀` is `R_3`-independent (so
  `F` is a circuit) the stress uses `e₀`. `K5` is the first instance: `10 > 9`,
  and `K5 − e` is generically isostatic.
- **Two parallel bars.** If `e₀` is `bc`-parallel to some `P ∈ E_chord(Σ)`, the
  two bars share both endpoints and `λ = (1, −1)` self-stresses at every
  placement. That is θ(3,4,5).

### Step P3 — (PC3)/(PC-Z): the two isotropic completions, and why a chord stress kills the pitch

The clean fact behind everything:

> **(PC-Z)** *(proven-informally)* `T = ⟨C_ab, C_ac⟩` (the pencil at `pt(a)` in
> `π`) is contained in exactly two maximal isotropic 3-spaces of `(Λ²K⁴, B)`:
> `α(a)` and `Λ²π̂`; both lie inside `T^{⊥_B}`; and `z` spans `V_bc ∩ T^{⊥_B}`.
> Hence, under (W1)–(W3),
>
> `Q(z) = 0 ⟺ z ∈ α(a) ∪ Λ²π̂ ⟺ V_bc ∩ α(a) ≠ 0 or V_bc ∩ Λ²π̂ ≠ 0.`

*Proof.* `Q(z) = 0` says `z` is a line extensor; `z ∈ T^{⊥_B}` says that line
meets both `a`-hinges, hence passes through `pt(a)` or lies in `π` (§(K-pitch)
Step 2's dichotomy (F-A)/(F-B)) — i.e. `z ∈ α(a)` or `z ∈ Λ²π̂`. Conversely both
spaces are totally isotropic, so any `z` in them has `Q(z) = 0`. For the second
equivalence: a maximal isotropic space is its own `B`-perp and contains `T`, so
`α(a), Λ²π̂ ⊆ T^{⊥_B}`; therefore any nonzero `y ∈ V_bc ∩ Λ²π̂` lies in
`V_bc ∩ T^{⊥_B} = ⟨z⟩`, giving `z ∈ Λ²π̂`; same for `α(a)`. ∎

`Λ²π̂ = ⟨C_ab, C_ac, C_bc⟩` is 3-dimensional whenever `pt a, pt b, pt c` are not
collinear (generic: `pt(a)` runs on `M = Π(b) ∩ Π(c)`, and `line(b,c) ⊆ Π(b)`
only if the panels are incident).

**The *reason* for the two-completions step is Witt's theorem — §(K-Λ) *Step 1*,
where it is derived independently.** (PC-Z) above stays the canonical
`V_bc`-level statement of the structural theorem and is not restated there; the
Witt argument is not restated here.

> **(PC3)** *(proven-informally)* A loaded stress with load `ω` forces
> `V_bc ⊆ ω^{⊥_B}`. With the chord stress of (PC2), `ω = C_bc ∈ Λ²π̂`, so
> `V_bc` and `Λ²π̂` both sit inside the 5-dimensional `C_bc^{⊥_B}`
> (`Λ²π̂` is isotropic), and `3 + 3 > 5` forces `V_bc ∩ Λ²π̂ ≠ 0`. By (PC-Z),
> `Q(z) = 0`. (If the containment is strong enough that `V_bc ⊆ Λ²π̂` — e.g.
> `V_bc = α(pt c)` at the `K5` shape `(3,3,3,3,4,4,4,4,4,4)` — the two
> `T`-conditions become dependent on `V_bc` and **(W3)** fails instead.)

*Proof of the first sentence.* A loaded stress says the functional
`m ↦ B(m(b) − m(c), ω)` is in the limit system's row space, hence vanishes on
its kernel, hence on `V_bc`. ∎

> **(PC-OBS)** *(proven-informally; the theorem)* Fix `(G°, ℓ, e₀)` and a support
> `Σ`. If `e₀ ∈ cl_{R_3}(E_chord(Σ))` at generic hub points, the slide-in limit
> system at support `Σ` fails **(W4)** — or (W3) — at **every** decoration: the
> reciprocal twist is a line in `plane(a,b,c)`, i.e. §(K-pitch) Step 2's failure
> mode **(F-B)**, realized structurally.

Two remarks. **(a)** This is the arc's first *proven* identically-vanishing-pitch
statement; every earlier (W4) obstruction was per-decoration observation, and the
(S5) parallel case was a (W1) statement. In particular it **explains** the `K5`
column of §(K-flank) *Step F6*'s table, where the full-support limit's degeneracy
at the structural flanks was measured (40 generic decorations per shape, an
independent driver) but had no mechanism: at the all-`{3,4}` `K5` shape
`V_bc = α(pt c)`, which is the strong-containment branch of (PC3), and the
(W3)-failure profile F6 records is exactly what (PC3) predicts there. The two
drivers agree at every shape they share — evidence, not redundancy — and the
mathematics is not repeated in F6. **(b)** It cannot threaten `hK` or the
pencil conjecture: it is a property of the *limit*. At `ε = 1` no interior is
slid, `E_chord = {ℓ ≤ 2}`, and the `K5` flank's chart-level transfer certificate
((T1)–(T3) with `Q(r) ≠ 0`) passes at every probed seed.

### Step P4 — where the chord obstruction bites

At the full support the necessary condition for the `G°`-local device is

> **(K-chord)** `e₀ ∉ cl_{R_3}(G°_{≤4} ∖ {e₀})` at generic hub points.

Length bookkeeping puts this exactly where the collapse's flanks are. Tightness
is `Σ_{E(G°)} ℓ = 6(m − n + 1)` with `m = |E(G°)|`; all `ℓ ≥ 3` gives
`m ≥ 2n − 2` and all `ℓ ≤ 4` gives `m ≤ 3n − 3`. Maxwell dependence needs
`m ≥ 3n − 5`, so for **simple** `G°`:

| `n` | `3n − 5` | max simple `m` | chord-obstructible with all `ℓ ≤ 4`? |
|---|---|---|---|
| 4 | 7 | 6 | **no** — the whole `K4` stratum is safe |
| 5 | 10 | 10 | **only `G° = K5`** |
| 6 | 13 | 15 | yes for `m ≥ 13`; `K222` (12) and 6v11e (11) are **not** |

Exhaustively over the 23 candidate hub graphs with `|V°| ≤ 6` (simple,
connected, min degree `≥ 3`), `R_3`-dependence holds **exactly** for the
Maxwell-overbraced ones — **5 dependent, 18 independent**: `|V°| = 5, |E°| = 10`
(`K5`, stress dim 1) and four at `|V°| = 6` with `|E°| ∈ {13, 13, 14, 15}` (stress
dims 1, 1, 2, 3) (`pure.py --chord`, census block). So the collapse's
four-colour ceiling and the chord
obstruction's `R_3` ceiling are **different conditions that first bite at the
same shape** — which is why the collapse's flank *looked* like the class's
flank. It is not the same: `K222` and 6v11e are collapse flanks with **no** chord
obstruction, and the two `K5` shapes carrying an `ℓ = 5` edge
(`(3,2,2,2,3,4,5,5,5,5)`, `(3,1,1,2,5,5,4,5,5,5)`) are collapse flanks that the
**full-support** device witnesses, pitched, at every probed seed. This is the
precise sense in which the fifth pass's refutation of (K-slide-comb) (colouring)
and this pass's refutation of (K-slide-cl) (`R_3`-dependence) are *independent*
results that happen to share their smallest witness.

Full-support verdicts (`pure.py --flanks`, 10–11 valid seeds per shape):

| shape | chord stress? | full-support verdict |
|---|---|---|
| dbl-subdiv `K4`; `K4` mixed `(3,4,2,3,3,3)` (controls) | no | PITCHED |
| `K5` `(3,3,3,3,4,4,4,4,4,4)` | yes | (W3) fails ×8, (W1) fails ×2 — `V_bc = α(pt c)` |
| `K5` `(3,3,3,4,3,4,4,4,4,4)`; `(3,3,3,4,4,4,4,4,4,3)` | yes | (W4) fails ×10 each |
| `K5` `(3,2,2,2,3,4,5,5,5,5)`; `(3,1,1,2,5,5,4,5,5,5)` | no | **PITCHED** ×11 each |
| 6v11e acyclicity flank | no | (W2) fails ×10 — mechanism open |
| `K222` octahedron flank | no | (W4) fails ×10 — `V_bc ∩ Λ²π̂ ≠ 0`, cause open |
| `K4` `(1,1,3,5,3,5)`; `(1,1,3,5,5,3)` (menu-blocked) | no | PITCHED ×10 each |
| `K4` `(1,1,3,5,4,4)` (menu-blocked) | no | (W4) fails ×10 — cause open |
| θ(3,4,5) | yes | (W4) fails ×11 |

Every row that §(K-flank) *Step F6* also measured agrees with it, on a driver
written independently (`flanks.py --limit` samples 40 non-aligned decorations per
shape; `pure.py --flanks` samples 10–11 chart seeds and additionally records the
chord predictor): `K5` (W3), 6v11e (W2) `dim V_bc = 2`, `K222` (W4), the
menu-blocked `K4 (1,1,3,5,3,5)` pitched.

### Step P5 — the invariant mismatch: why direction C cannot close the escape

Direction C asked for `C(G°-limit) ≢ 0` on the decoration variety; by Step P0
that is (W1) ∧ (W2) generically. The table has four class shapes where
(W1) ∧ (W2) hold at **every** valid seed and `Q(z) = 0` at every one. Hence:

> **(PC5)** A theorem "`C(G°-limit) ≢ 0` on the decoration variety for every
> class shape" would **not** close (K-slide-cl), (K-pitch) or `hK`. The escape's
> obstruction at the flanks lives in (W4), which the pure condition does not see.

The reason is structural. `C` is a determinant asking whether a kernel is as
small as the count allows. `Q(z)` asks whether a *particular* kernel vector is
off a *quadric* — by (PC-Z), whether `V_bc` misses two fixed isotropic
3-spaces. The Klein quadric is invisible to the matroid; it is exactly the extra
structure that makes body-hinge geometry more than body-bar combinatorics, and
exactly what (C6)'s uniform packing cannot reach. Direction C's premise ("the
obstruction the collapse hit is a property of the specialization, not of the pure
condition") is right about the collapse's four-point cap and wrong about the
*device*: the device has a second, pitch-side obstruction, and the collapse's
failure at `K5` was partly a symptom of it.

### Step P6 — WW87 Thm 2.18 does not transfer to the decoration variety

> **(PC6)** *(proven-informally)* The decoration variety maps into
> `∏_{P ∈ E°} Gr(6 − ℓ_P, 6)` with image a **proper closed subvariety** — `R_P`
> is determined by the hub points, the panels and a handful of per-edge
> parameters, and the hub points are **shared** by every edge at those hubs (an
> `ℓ = 3` edge's `R_P` is a point of the 9-dimensional `Gr(3,6)` cut out by two
> hub points and two pencil parameters). So Thm 2.18's equivalence "pure
> `k`-condition ≢ 0 ⟺ `k` edge-disjoint spanning trees", a statement about the
> generic point of the ambient realization space, does not descend.

*Witness, not merely a worry.* `P21` (`G° = K4 − 02` with `23` doubled, lengths
`(3; 3,3; 4,5,3,3)`; a **(K-res)** residual since its parallel `(3,3)` pair is a
rigid `C₆`). The (C6) packing exists (min-max slack `≥ 0`, explicit packing) and
the **free-bar** system with the same multiplicities `6 − ℓ_P` is
**independent** (rank `15/15` at seeded random screws) — so Thm 2.18's conclusion
holds in the ambient space. Yet the decoration-variety rows are **dependent at
every support** ((S5): coincident chords put a repeated line in a 6-hinge cycle;
reproduced by `kslide.py --flanks`). Same graph, same multiplicities, packing
satisfied, pure condition of the constrained family identically zero.

This also explains why (C6) — genuinely uniform, genuinely Phase-12/13/14
reachable — buys nothing here: it certifies the **ambient** hypothesis of a
theorem whose conclusion is about the ambient generic point.

### Step P7 — the support lever, the locality/pitch trade, and the rescued flanks

`E_chord(Σ)` shrinks with `Σ` (PC1), so the obstruction is support-dependent and
the device is not dead — it is *traded off*:

> **The locality/pitch trade.** The slide buys `G°`-locality by pushing chain
> lines through hub points. Pushing lines through hub points is exactly what
> makes the chord a legal bar. Chord bars generate `R_3` self-stresses as soon as
> the chord-obstructed hub graph is 3-dimensionally dependent, and any such
> stress through `e₀` puts `z` in the isotropic `Λ²π̂`. **The degeneration that
> makes the problem combinatorial is the same degeneration that kills the
> pitch.** The two extremes: `Σ` maximal is the collapse's `G°`-local system
> (maximal chord obstruction); `Σ = ∅` is the `ε = 1` chart itself
> (`E_chord = {ℓ ≤ 2}`, no locality) — which is (K-pitch) again.

**Rescues (`pure.py --support`; menu: full; drop the slide at `c`; at `b`; at
both; nowhere).** The rescue criterion is `≥ 1` seed with (W1)–(W4), because that
is exactly what (S1) consumes — *one* exact limit witness, not a majority. This
is the probe §(K-flank) *Step F7* item 2 called for, and it is the direction's
one positive class-side result.

- `K5` `(3,3,3,3,4,4,4,4,4,4)`: "no slide at `c`" removes the three `ℓ = 4` edges
  at `c` from `E_chord`, leaving the three `ℓ = 3` edges at `b` — a star on
  `{b,2,3,4}` not even spanning `pt(c)`, so `e₀ ∉ cl_{R_3}`; the chord stress is
  gone and full witnesses appear (2/3 seeds; the third has an unrelated (W1)
  drop). **Slide device closes it.**
- `K5` `(3,3,3,4,3,4,4,4,4,4)`, `(3,3,3,4,4,4,4,4,4,3)`: likewise, 3/3.
  **Closed.** (Note "no slide at `b`" removes the chord stress too but stays
  `Q(z) = 0` — the residual mechanism of Step P8 taking over; only the `c`-side
  reduction clears both.)
- `K222` octahedron: "no slide at `c`", 3/3. **Closed** — even though its
  full-support failure was *not* a chord stress.
- θ(3,4,5): "no slide at `c`" and "no slide at `b`", 3/3 each. **Closed** — and
  this is the parallel-`G°`-edge shape the gap map lists as reachable only by the
  companion forms ((K-Λ) at `ℓ = 4`). A slide witness reaches it directly.
- 6v11e acyclicity flank: (W2) fails (`dim V_bc = 2`) at **all four** nonempty
  supports *of this 5-support menu* — **superseded 2026-08-06, §(K-mech)
  (MX-6)/(MX-7): the drop is a forced welded flex whose routes these
  b/c-side omissions cannot kill; a far-side single omission rescues the
  device (9/9 prediction table)**. Only `Σ = ∅` is pitched here — but that is
  the `ε = 1` chart, where the
  slide is the identity and **(S1) is vacuous**: the "witness" is just a chart
  seed. The *split* is nevertheless closed, by (K-pitch) Step-0 one-witness
  logic: full chart transfer certificates ((T1)–(T3) + `Q(r) ≠ 0`, which also
  check `dim R_a = 1` and the (T2) side conditions that (W1)–(W4) do not) at
  **11/11** valid seeds. *(Both halves of the closing sentence this bullet used
  to carry — "the slide device does not reach this shape and no mechanism for
  its (W2) drop is known" — are **withdrawn 2026-08-06, §(K-mech)**: the
  mechanism is the welded flex (MX-6), and the device reaches the shape at a
  mechanism-guided support (MX-7).)*

Three riders. **(a)** The menu is 5 of `2^{#slid interiors}` supports; "not
rescued" is not a verdict. **(b)** A reduced support costs precisely what the
collapse was buying: unslid interiors survive as chart coordinates, so a
*class-uniform* argument on the reduced-support carrier has strictly more
parameters than the collapse's decorated multigraph. The rescue is a **per-shape
witness engine**, not a class program. **(c)** `Σ = ∅` must never be counted as a
slide-device rescue — it is the chart, and (S1) says nothing there; the driver
labels that row `CHART … ((S1) is VACUOUS here)` for exactly this reason.

### Step P8 — the residual mechanism, localized but open

The refuted guess, recorded so it is not re-made: `C_bc ∈ V_bc` (the chord as a
relative twist) would force `z ∝ C_bc` and `Q(z) = 0`, but it is **false** at
`K222`, at `K4 (1,1,3,5,4,4)` and at the `K5` shapes 2–3 — it holds only at `K5`
`(3,3,3,3,4,4,4,4,4,4)`, where `V_bc = α(pt c) ∋ C_bc` anyway. By (PC-Z) the
right question is sharper and single-valued:

> **Open.** At `K222` and at `K4 (1,1,3,5,4,4)`, why is `V_bc ∩ Λ²π̂ ≠ 0` — a
> codimension-1 incidence between a 3-space that moves with the whole decoration
> and the `Λ²` of the split triangle's plane — forced at every decoration, with
> **no** chord stress present? At the `K5` shapes it is forced by (PC3); here
> nothing explains it. And at 6v11e, why does `dim V_bc` drop to 2?

**Both questions are ANSWERED (2026-08-06, §(K-mech))**: the incidence is a
forced pole-cluster load through `pt(c)` ((MX-4)/(MX-5), bound 2 met with
equality, the chord stress being the special case `ω = C_bc`), and the 6v11e
drop is a forced welded flex ((MX-6)) — both in one calculus on the
realizable-load space `Ω`. They were the two honest gaps of this pass, and
(PC-Z)'s reduction — "why does the pitch vanish?" to "why does `V_bc` meet one
of two named isotropic 3-spaces?" — is exactly the form the mechanisms answer.

### Step P9 — what a class proof needs now

1. **The combinatorial residue is replaced, not removed.** As the *governing*
   combinatorics, (K-slide-comb)'s colouring/menu problem is superseded by
   **(K-chord)**: per shape, a support `Σ` with `e₀ ∉ cl_{R_3}(E_chord(Σ))`.
   (The supersession is of the *role*, not of a shared mechanism: the fifth
   pass refuted (K-slide-comb) by colouring, this pass refutes (K-slide-cl) by
   `R_3`-dependence — see the verdict's two-refutations note.) Unlike
   (K-slide-comb) this lives in a matroid with **no combinatorial
   characterisation** (generic 3-dimensional rigidity), so it is checkable per
   shape by exact rank but not obviously by a class argument.
2. **A class proof must handle both flanks of the trade.** Large `Σ` gives
   `G°`-locality and risks (PC-OBS); small `Σ` avoids it and loses locality. The
   natural repaired statement quantifies `∃Σ` — and even that is only
   *necessary*: 6v11e (and the `K222`/`K4` residual mechanism) show at least one
   further obstruction.
3. **(C6)'s role is downgraded** (not its status): it certifies the ambient
   hypothesis of a theorem that does not transfer (P6), and it concerns the wrong
   matroid for the pitch (P2).
4. **Option B is NOT required by this direction.** Everything above is linear
   algebra on the limit carrier's decoration variety plus (S1) for transfer; no
   stress-as-chart-rational-function object appears (the pitch sits on the motion
   side by (T1)/(T2), and the chord stress is a stress of the *limit* system in
   closed form). So direction C was pursuable under the standing adjudications —
   it is simply aimed at the wrong invariant. That is the verdict, not a
   permission problem.
5. **The honest next question**, if the arc continues on the slide device: is
   `∃Σ` with (K-chord) *and* (W1)–(W4) attainable at every class shape? That is a
   per-shape finite search the driver already performs on a 5-support menu;
   widening the menu and sweeping the `|V°| ≤ 6` strata is cheap, and would
   either produce a genuine class-level refutation or a much larger covered
   sub-class. 6v11e is where to start. **RUN 2026-08-06 as fan-out direction M
   (§(K-mech))**: 6v11e rescued ((MX-7)), the sweep measured
   complete-and-sound for the three-mechanism predictor ((MX-9)), one new
   (W4)-failing shape found-and-explained; the class-level refutation remains
   unexhibited.

### Verification

`notes/scripts/w4/pure.py` (tracked, new this pass; exact-ℚ, on top of
`repin.py`/`pitch.py`/`kslide.py`/`kslidecomb.py`; every sampled object carries a
rank/dimension assert; every shape is re-certified tight-count + `def = 0` +
`hnoRigid`; every limit system is built by `kslide.path_limit_lines` from an
honest `repin.seed_probe` chart seed — a hand-rolled "generic decoration" need
not be chart-realizable and would not transfer under (S1); `PYTHONHASHSEED=0`;
the one randomness literal is `RNG_SEED = 20260805`). **(PC-Z) is asserted at
every seed of every mode** (the computed `Q(z) == 0` against
`V_bc ∩ Λ²π̂ ≠ 0 ∨ V_bc ∩ α(a) ≠ 0`). Reproduce, from the repo root and with
`PYTHONHASHSEED=0`: `python3 notes/scripts/w4/pure.py --chord | --flanks |
--support | --pure | --parallel`.

| driver | ~time | what it asserts |
|---|---|---|
| `--chord` | 45 s | (PC1) as a length/support rule against the *measured* `C_uw ∈ R_P`, 90 `G°`-edge instances over 6 shapes; (PC2)+(PC3) by assembling the chord stress as an explicit row combination of the actual limit rows and checking its covector is a nonzero multiple of the `C_bc` load, then `z ∈ Λ²π̂` and `Q(z) = 0`; the biconditional "chord stress present ⟺ `V_bc ⊆ C_bc^{⊥_B}`"; and the **census**: over the 23 candidate hub graphs with `|V°| ≤ 6`, `R_3`-dependence ⟺ Maxwell-overbraced, smallest `K5` |
| `--flanks` | 385 s | full-support (W1)–(W4) at 13 shapes (2 controls, 5 `K5`, 6v11e, `K222`, 3 menu-blocked `K4`, θ(3,4,5)) with the chord predictor asserted against each verdict, and the residual-mechanism shapes printed by name |
| `--support` | 384 s | the 5-support menu at 3 `K5` shapes, 6v11e, `K222`, θ(3,4,5); rescue = `≥ 1` full witness at a **nonempty** support; `Σ = ∅` is reported separately as the chart (where (S1) is vacuous) and then the chart transfer certificate ((T1)–(T3) + `Q(r) ≠ 0`) is run and reported |
| `--pure` | 187 s | the invariant mismatch: (W1) ∧ (W2) at every valid seed while `Q(z) = 0` at every one, at 4 class shapes (14/14, 12/12, 12/12, 11/11); plus the free-bar contrast (rank `= 6n − 9`, independent) against (C6) at θ(3,4,5), `P21`, `K5` |
| `--parallel` | 4 s | at θ(3,4,5): (W1), (W2) hold, chord stress through `e₀` present, `z ∈ Λ²π̂`, `Q(z) = 0`, and the surviving `(4,5)` parallel pair's chain spans summing to dimension 6 (so **no** (S5) cycle stress); plus `def(C_k) = 0 ⟺ k ≤ 6`, hence `hnoRigid ⟹ ℓ₁ + ℓ₂ ≥ 7` on parallel pairs |

**Confidence verdict: direction C REFUTED as a strategy** — the pure condition is
a rank certificate (WW87 Cor. 2.7) and the escape's obstruction at the uncovered
flanks is **(W4)**, measured at four class shapes where the rank half holds at
every sampled decoration; **and WW87 Thm 2.18 does not transfer** to the
decoration variety (proper subvariety; `P21` exhibits the failure with (C6)
satisfied). **(PC-Z) proven-informally** — the exact reformulation
`(W4) ⟺ V_bc ∩ (Λ²π̂ ∪ α(a)) = 0`, which is the pure-condition-shaped object
direction C was reaching for and is *not* `C(G°-limit)`.
**(PC1)–(PC3)/(PC-OBS) proven-informally** — the arc's first
identically-vanishing-pitch theorem, governed by `R_3`-dependence of the
hub-point framework on the chord-obstructed edges, with an exhaustive
`|V°| ≤ 6` census. **(K-slide-cl) REFUTED as stated** at three `K5` class shapes
and θ(3,4,5) under the full support — a **statement**-level refutation by a
mechanism independent of §(K-slide-comb)'s **antecedent**-level one (colouring);
the parallel-`G°`-edge row's mechanism
corrected and the (S5) `(3,3)` mechanism proven **impossible** inside tight +
`hnoRigid`. **Five flank shapes CLOSED by reduced-support (S1) witnesses** — all
three obstructed `K5` 5-chromatic shapes, `K222`, and θ(3,4,5) — and the sixth,
the **6v11e acyclicity flank**, closed by its chart transfer certificate (11/11)
— *and, since 2026-08-06, by the slide device itself at a mechanism-guided
support (§(K-mech) (MX-7))*. So every
probed §(K-slide-comb) Step-D5 flank shape now has its split closed, per shape,
and §(K-flank) *Step F7* item 2 is answered. **Open** *(updated 2026-08-06)*:
the two anomalies this verdict used to list — 6v11e's (W2) drop and the
`K222` / `K4 (1,1,3,5,4,4)` incidence — are **mechanised in §(K-mech)**
((MX-6), (MX-4)/(MX-5)); what remains open is whether `∃Σ` with the
three-condition set ((K-chord) + cluster bounds ≤ 1 + no flex route) and
(W1)–(W4) is class-uniform.
**Option B is not required** by this direction.
