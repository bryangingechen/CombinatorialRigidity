## §(K-σ) — the polarity as a symmetry of the split: **route σ, a CANDIDATE third escape route** (**offered for adjudication, not settled**; the σ-intertwining question **REFUTED in its literal form** and **CONFIRMED covariantly**; **σ-equivariant seed recipes DEAD**)

Read against §(K-tight) *Steps 0–3* (whose criterion it uses verbatim),
§(K-pure) *Step P3* ((PC-Z)) and §(K-Λ) *Steps 1, 4, 5* (whose two-point
failure locus it explains). Notation inherited from §(K-Λ) *Standing
notation*.

**Status, stated before the mathematics, because four things here are settled
and one is not** — and because the whole section carries a **field-scope
qualifier** stated immediately after the bullets.

- **Settled — refuted, `ℝ`-specifically.** The σ-intertwining question *in its
  literal form*: σ does **not** intertwine `α(a)` and `Λ²π̂` of one
  configuration (*Step σ1(a)*). **The argument uses `ℝ`-definiteness and does
  not port** — see *Field scope*.
- **Settled — confirmed.** The **covariant** form `σ(α_p) = β_{p^⊥}`,
  `σ(β_π) = α_{pole(π)}`, which exchanges the two branches of (PC-Z) across an
  involution of the seed space (*Step σ1(b)*).
- **Settled — refuted; the verdict is field-neutral, its original `ℝ` argument
  is not.** **σ-equivariant seed recipes are dead**: over
  `ℝ` with
  the project's polarity there is *no* σ-fixed pencil configuration at all, and
  for a **null** correlation the fixed locus is degenerate — it
  forces every hinge line into a linear line complex and produces a self-stress
  per cycle (*Step σ6*, measured deficit exactly 1 at 6/6 on tight `C₆`). This
  is `notes/pencil/strategy.md` §2.4's *"degenerate enough to compute, and you
  break the thing you're computing"* wall, now with a proof. **Over `ℂ̄` the `ℝ`
  half REVERSES** — σ-fixed configurations exist and are *nondegenerate* at the
  Tay target (§(K-clos) (AC-2)/(AC-3)) — **and the verdict survives anyway**, on
  the field-neutral §(K-clos) (AC-5): at a σ-fixed seed route σ *is* route A.
- **CANDIDATE, offered for adjudication — not asserted as settled.**
  **Route σ**, a third escape route obtained by running route A at the dual
  seed `σu`. If the derivation below is right it closes (K-tight) on the hard
  stratum, *length-free*. It rests on **four named obligations** (*Step σ5*),
  the first of which — σ-nondegeneracy of the transported seed — was recorded
  as *observed 47/47, not proven* and is now **verified in both directions**
  (2026-08-05, `sigma.py --hunt`): the dual conjuncts **CAN fail at a
  hard-stratum, primally nondegenerate seed** (45 constructed witnesses), so
  the 47/47 was genericity and never an implication; but only **two** of the
  four are genuinely new, and the steering repair is exhibited **exactly** on
  a chart line through the failure. **No gap-map status moves on account of
  route σ**: (K-tight) keeps its status with a candidate noted, and `hK` stays
  carried as pinned.
- **Settled — proven, and new this pass.** *Step σ3*'s side condition
  `pt(b) ∉ Π(c)` is **free**: primal nondegeneracy at the split's middle body
  `a` forbids *both* halves of (Λ0d) from failing at once (**(σ7)**), so the
  σ-completeness span is `K⁶` via `α_{pt(b)}` or via `α_{pt(c)}`. This settles
  *What would change this* item (iv) at every both-ends-hubs split. It does
  **not** make the two-sided (Λ0d) of §(K-Λ) free — see (σ7)'s scope note.
  **(σ7) is the one result here that needs no polarity at all** — see *Field
  scope* immediately below.

### Field scope — read this before quoting anything in this section

**Recorded as an open gap, 2026-08-05 (coordinator verification of `bd270bce`);
NOT settled here — and SETTLED SINCE, in §(K-clos): read its (AC-1) (the
polarity generalizes; the general-`K` transport is landed) and (AC-7) (`ℂ̄`
dominates `ℝ` within characteristic 0) before quoting this subsection.** This whole section is
about a polarity that exists **in tree only over `ℝ`**, while the obligation it
aims to discharge is consumed at a **general infinite field**. Three landed
signatures, verified directly:

| object | field | source |
|---|---|---|
| `screwComplementIso` (= `σ`) | **`ℝ`-only**: `ScrewSpace ℝ 2 ≃ₗ[ℝ] ScrewSpace ℝ 2` | `Molecular/Molecule/Duality.lean:69` |
| `hasPencilPanelRealization_mapExtensor_screwComplementIso` | **`ℝ`-only**: `{F : BodyHingeFramework ℝ 2 α β}` | `Pencil/Statement.lean:257` |
| `pencil_conjecture_of_hcontract_hK_hbareSplit_of_card`, and **`hK` inside it** | **general**: `[Infinite K]`, `PencilPair K 3 G`, seed `q : α × Fin 4 × Fin 4 → K` | `Pencil/Escape.lean:555` |

`HasPencilPanelRealization`, `IsNondegPencilRealization`,
`HasGenericPencilRealization` and the whole chart/`pencilRow` engine are
**general-`K`** (Phase 33 made the core chain field-general). Exactly **five**
declarations in `Pencil/` fix `ℝ`, and **four of them are the polarity
cluster**: `screwComplementIso_mk_extensor` (`Statement.lean:166`), the two
forward predicate transports (`:185`, `:216`) and the self-duality theorem
(`:257`). The fifth, `exists_hasPencilPanelRealization_witness` (`:665`), is an
unrelated concrete `d = 3` non-vacuity certificate.

**Consequence, stated plainly.** "*Step σ5* obligation 1's conjunct 1 is free by
a landed theorem" is true **at `ℝ`**. At the general `K` where `hK` is
quantified there is no polarity in tree, so there is no `σ`, no route σ, and no
freeness claim. Nothing in this section is *wrong* — the numerics are ℚ ⊂ ℝ and
every verdict below holds over `ℝ` — but the qualifier was missing, and the gap
map advertised obligation 1 as "sized" without it.

**Which verdicts are field-neutral and which are genuinely `ℝ`-mathematics** (by
reading the arguments, not by re-deriving them):

- **Needs no polarity at all, so field-neutral outright: (σ7)** and the *Step
  σ3* span computation's linear algebra. (σ7)'s proof uses only the primal
  conjuncts and `dim M = 2`; the span computation uses the Klein form `B`, which
  is the volume form and exists over any field.
- **Field-neutral *modulo the polarity existing*: (σ1)–(σ6)**, the covariant
  statement *Step σ1(b)*, route σ itself, and the conjunct-1 freeness. Each is a
  statement about `⋆` and the standard (nondegenerate) pairing, neither of which
  needs `ℝ`.
- **Genuinely `ℝ`-mathematics, because it uses *definiteness*, not just
  nondegeneracy — and therefore **not** portable:** *Step σ1(a)*'s refutation of
  the literal intertwining (`pt(a) ∈ pt(a)^⊥ ⟹ pt(a)·pt(a) = 0 ⟹ pt(a) = 0`)
  and *Step σ6*'s "no σ-fixed pencil configuration exists". Over a field with
  isotropic vectors both arguments simply stop, and **§(K-clos) has now settled
  what happens to their conclusions: both REVERSE** — self-conjugacy is the
  defining condition of the σ-fixed grid locus ((AC-2)), which is non-empty and
  nondegenerate at the Tay target ((AC-3)). Do not re-cite these two as
  refutations over a general field; the *verdict* they were supporting
  ("σ-equivariant seed recipes are dead") survives on the field-neutral (AC-5).

**Does the polarity generalize past `ℝ`? SETTLED — YES, and the bill is one
section** (§(K-clos) (AC-1), 2026-08-06; source-level, **not compiler-checked**).
The reading recorded here was right, and §(K-clos) adds the piece it was
missing: **the general-`K` transport is already in tree** as
`BodyHingeFramework.mapSupport` (`Molecular/GenericLift/HingeGeneric.lean:462`,
with its rank lemma `finrank_span_rigidityRows_mapSupport` at `:544`) — the same
construction as the `ℝ`-fixed `BodyHingeFramework.mapExtensor` route σ's
statement is phrased through, at the general field. So **nobody should budget
for generalizing `Molecular/Molecule/ProjectiveInvariance.lean`'s 19-declaration
`mapExtensor` API**: phrase the general-`K` statement through `mapSupport` and
that file needs no change at all. The recorded reading, unchanged:
both ingredients of `screwComplementIso`
are **already field-general in tree**: `complementIso` is
`⋀[K]^j (Fin (k+2) → K) ≃ₗ[K] ⋀[K]^(k+2−j) (…)` (`Molecular/Meet.lean:479`),
built from `wedgePairing` (injective over any field, via `Pi.basisFun K`) and
`toDualEquiv`; and `ScrewSpace.equivExteriorPower (K) [Field K] (k)` is general
(`RigidityMatrix/Basic.lean:185`). So `screwComplementIso`'s `ℝ` looks like a
**writing choice, not a mathematical obstruction** — the definition would
typecheck verbatim with `K` in place of `ℝ`. The four ℝ-fixed *theorems*'
helper inputs are general-`K` too (`mem_span_of_dotProduct_perp_pair`
`Statement.lean:133`, `exists_extensor_eq_panelSupportExtensor`,
`extensor_ne_zero_iff_linearIndependent`, `panelSupportExtensor_ne_zero_iff`).
**No generalization is carried out here or there** — §(K-clos) (AC-1) prices it
(one `def` plus four theorems restated with `mapSupport`) and flags the one
instrument it could not use: a ~20-line typecheck spike.

**Precedent: the phase has already hit this exact mismatch once.** `Pencil/
Arms.lean`'s W3-L4 section header records it verbatim — the landed
Crapo–Whiteley projective invariance "is over `ℝ` … the pencil arm works over a
general field `K`", so that section **wrote the `K`-level transport itself**
rather than reusing the ℝ one. Same shape, same fix pattern, one section's cost.

**Headline.** The projective polarity `σ := screwComplementIso` is a genuine
symmetry of the pencil stratum, and it is *not* a symmetry of the escape
**analysis** — because that analysis is conducted in one frame of a dual pair.
In the other frame the carrier keeps a freedom the first frame's nondegeneracy
forbids. Concretely:

- §(K-Λ)'s two-point failure locus `{V_bc ⊥_B C(M)}` (recorded there as *the
  genuine (T3) failure*) and `{V_bc ⊥_B C(bc)}` (recorded as *route A escapes
  outright*) is **exactly a σ-orbit**: `σ` exchanges `C(M)` with `C(bc)`. The
  asymmetry the workbook records is therefore **not** evidence that the symmetry
  breaks; it is the signature that only one of the two dual frames is in scope.
- Transporting route A along `σ` gives **route σ**, whose uniform-failure
  criterion is `★r ∥ C(bc)`, the exact σ-image of routes A/B's `★r ∥ C(M)`. The
  two **cannot fail simultaneously**: `Λ²Π̂(b) + Λ²Π̂(c) + α_{pt(b)}` is all of
  `K⁶` whenever `pt(b) ∉ Π(c)`, so `r = 0`, contradicting `dim R_a = 1` — and
  when that half of (Λ0d) *does* fail, **(σ7)** (*Step σ3*) supplies the
  `c`-mirror, so no genericity hypothesis is added.
- Route σ's witness is a **nondegenerate** target-rank pencil realization of `G`
  satisfying the chart's binding point equations — the shape `hK` consumes, not
  a degenerate boundary point. It *looks* degenerate only when pulled back into
  the original frame, where it is the coincident-point configuration
  `pt(v) = pt(b)` on the carrier's forbidden locus — which is why the one-frame
  analysis could not see it.

**Why the gain is *evidence → argument*, not *bug fixed*.** The branch route σ
closes has **never been observed nonempty** (`lambda.py --adv` hunts for
`λ ∝ p⁺` and finds none; and at all 47 seeds sampled here routes A/B *already*
escape at `u`). Route σ does not repair an observed failure — it removes the
*possibility* of one, uniformly, which is precisely what "making some good seed
exist uniformly over the class" asks for.

### Step σ0 — the polarity in coordinates, and what it does to a pencil realization

`screwComplementIso` (`Molecular/Molecule/Duality.lean:69`, **`ℝ`-only** —
*Field scope*) is `complementIso`
at `j = k = 2` conjugated by `ScrewSpace.equivExteriorPower`; `Molecular/
Meet.lean:88` records that `complementIso` is built from the volume form
(`screwAlgebraTopEquiv`) and the standard dot product (`Pi.basisFun.toDual`),
*"i.e. it **is** the Hodge star `⋆`"*. So on `Λ²K⁴` in Plücker coordinates
`σ = ⋆` is the signed swap of complementary index pairs (`repin.hodge_star`),
and three facts are elementary and exact:

> **(σ1)** `σ² = id` (`⋆² = (−1)^{p(N−p)} = +1` on `Λ²` of a 4-space).
> **(σ2)** `σ` is a Euclidean isometry *and* self-adjoint, so `(σC)^⊥ = σ(C^⊥)`.
> **(σ3)** `σ` is an isometry of the Klein form: `B(x,y) = ⟨x, ⋆y⟩ = vol(x ∧ y)`
> and `vol(⋆x ∧ ⋆y) = ⟨x, ⋆y⟩`. Hence `σ` preserves `Q`, the Klein quadric and
> every `⊥_B` condition, and it exchanges the two families of maximal
> isotropics: **`σ(α_p) = β_{p^⊥}`** and **`σ(β_π) = α_{pole(π)}`**.

On a pencil realization the landed
`hasPencilPanelRealization_mapExtensor_screwComplementIso`
(`Pencil/Statement.lean:257`) carries `(F, normal, point)` to
`(F.mapExtensor σ, point, normal)` — same multigraph, roles swapped. In
coordinates this has a completely elementary form, which is what makes it
computable:

> **(σ4)** *(exact; 47/47 seeds)* Write `p̂_w` for a body's homogeneous point and
> `ν_w` for its homogeneous panel normal. Then for every edge `uw`,
> `span(ν_u, ν_w) = span(p̂_u, p̂_w)^⊥`, i.e. `ν_u ∧ ν_w ∝ ⋆(p̂_u ∧ p̂_w)`.
> **So `σ` is: replace every body's point by its own panel normal.** The
> incidences `ν_w · p̂_w = 0` and `ν_u · p̂_w = 0` (`w` a neighbour of `u`) are
> exactly what makes this work, and they *are* the pencil conditions.

Consequently `σu` is a pencil realization of the same `G′`, with the same
hub/non-hub combinatorics, and `rank R(σu) = rank R(u)` (transport along a
linear automorphism). Verified exactly: `rank`, `s₀`, `dim R_a` agree at 47/47.

### Step σ1 — what σ does to the split data, and the two readings

Fix the split chain `b–v–a–c` at a `G′`-seed `u`. Everything below is exact.

| object at `u` | its image at `σu` |
|---|---|
| `Π(b), Π(c)` (panels) | `p̂_b^⊥, p̂_c^⊥` |
| `M = Π(b) ∩ Π(c)` (meet line) | `σ(C(bc))` — the polar of `line(b,c)` |
| `C(bc) = line(b,c)` | `σ(C(M))` — the meet of the image panels |
| `α_{pt(a)}` (lines through `pt a`) | `β_{pt(a)^⊥}` |
| `β_{π_a}`, `π_a = plane(a,b,c)` | `α_{pole(π_a)}` |
| `V_bc` | `σ(V_bc)` (motions transport by post-composition) |
| `r` (the transmitted boundary load) | `σ(r) = ★r` (verified 47/47) |
| `dim R_a`, `s₀`, target rank | unchanged (verified 47/47) |

**(a) The literal question is answered NO — REFUTED.** `σ` does **not**
intertwine `α(a)` and `Λ²π̂` *of one configuration*: that needs
`pt(a)^⊥ = π_a` and `pole(π_a) = pt(a)`, i.e. `pt(a)` self-conjugate with `π_a`
its polar plane — a codimension-3 condition, and over `ℝ` with the project's
polarity (built on the **definite** standard dot product, `Molecular/
Meet.lean:88`) it is *impossible*: `pt(a) ∈ π_a` always, and `pt(a) ∈ pt(a)^⊥`
forces `pt(a) · pt(a) = 0`, hence `pt(a) = 0`.

**(b) The covariant statement is YES, and it is the useful one — CONFIRMED.**
`σ` carries the `(α, β)` pair of the seed to the `(β, α)` pair of the image
seed, roles swapped. Since `σu` realizes the **same** graph with the **same**
split, the two branches of (PC-Z) are exchanged by an involution of the seed
space. In particular §(K-Λ)'s two-point locus is a single σ-orbit:

> **(σ5)** Because `σ` is a `B`-isometry with `C(M') = σ(C(bc))` and
> `C(bc)' = σ(C(M))`:
> `V_bc ⊥_B C(M)` **at `u`** ⟺ `V_bc' ⊥_B C(bc)'` **at `σu`**, and
> `V_bc ⊥_B C(bc)` **at `u`** ⟺ `V_bc' ⊥_B C(M')` **at `σu`**.
> The two branch *labels* swap across `σ`; the two branch *consequences*
> recorded in §(K-Λ) (genuine failure vs. route A escapes) do not — that
> asymmetry is explained by *Step σ2*.

Equivalently on the load side, using `⟨r⟩ = (V_bc ⊕ T)^⊥` ((T1)) and
`★C(M), ★C(bc) ⊥ T`:

> `★r ∥ C(M)` ⟺ routes A/B fail uniformly at `u` ⟺ `r ⊥ β_{Π(b)} + β_{Π(c)}`;
> `★r ∥ C(bc)` ⟺ `r ⊥ α_{pt(b)} + α_{pt(c)}` ⟺ routes A/B fail uniformly at `σu`.

### Step σ2 — route σ, and why the one-frame analysis missed it

**Definition.** *Route σ at `u`* = route A run at the seed `σu`. It is a
construction of a realization of `G`, and that is all the escape needs: `hK`'s
hypothesis is only that `G′` *has* a generic realization and its conclusion is
about `G`; no compatibility between the two is required, so it is irrelevant
that the produced realization extends `σu` rather than `u`.

**Its criterion.** Route A's uniform-failure criterion at `σu` is
`r(σu) ⊥ Λ²Π̂_{σu}(b)` (§(K-tight) *Step 2.4*, whose two derivation ingredients
both hold at `σu`: `b` is still a hub, and `pt_{σu}(a) ∈ Π_{σu}(b)` ⟺
`pt_u(b) ∈ Π_u(a)`, true because `ab ∈ E(G′)`). Now
`Λ²Π̂_{σu}(b) = β_{p̂_b^⊥} = σ(α_{pt(b)})` and `r(σu) = ★r`, and `σ` is
orthogonal, so

> **(σ6)** *(exact; verified as an equivalence at 47/47 seeds)*
> **route σ fails uniformly ⟺ `r ⊥ α_{pt(b)}` ⟺ `★r ∥ C(bc)`.**

**Why it was invisible.** Pull route σ's witness back into `u`'s frame (one more
application of `σ`): it becomes the configuration with `point(v) = pt_u(b)` —
the two points of the adjacent bodies `v` and `b` *coincide* — and `point(a)`
sliding along `Π_u(a) ∩ Π_u(c)`, with `C(va) = C_ab` pinned. That is **KT's dead
route M₁**, sitting at the extreme point `pt(v) = pt(b)` of the carrier's
forbidden locus `pt(v) ∈ line(a,b)` (§(K-tight) *Step 1*, row 1). So in `u`'s
frame route σ is a nondegeneracy-violating boundary construction, correctly
excluded — *but the same family, read in the dual frame, is perfectly
nondegenerate*. `IsNondegPencilRealization`'s conjuncts (`Motive.lean:110–115`)
are **not** σ-stable (conjunct 2 asks adjacent *points* distinct; there is no
adjacent-*panel* mirror), and this is the one place in the arc where that
asymmetry bites.

> **M₁ is killed twice in this workbook, for the same reason — so route σ faces
> exactly ONE crux, not two** (coordinator scrutiny, 2026-08-05). §(K-tight)
> *Step 1* rules M₁ out as *"the nondegeneracy-forbidden locus"*, and §(K-tight)
> *Step 2.6* rules it out again as *"M₁'s span is carrier-unrealizable"* — but
> the stated reason of the second is *"its construction pins `hinge(vb) :=
> q(ab)`, forbidden"*, i.e. the **same** pinning as the first. The two are one
> obligation. This materially bounds what verifying route σ costs.

This also explains, in one line, §(K-tight) *Step 2.6*'s "the carrier keeps 5 of
KT's 6 escape dimensions": the 6th dimension is not lost, it is in the other
frame. Route σ restores a 6th direction — `α_{pt(b)}`, not KT's `Λ²Π̂(a)`.

### Step σ3 — the completeness statement (the candidate)

> **Theorem (σ-completeness of the escape at a hard-stratum split) — CANDIDATE.**
> *(informal; the criterion is §(K-tight) *Step 2*'s, the rest is exact linear
> algebra. Conditional on obligation 1 of *Step σ5*.)* Let `u` be a target-rank
> nondegenerate pencil `G′`-seed with `s₀ = 0`, `dim R_a = 1` and both chain
> ends `b, c` hubs. Then **at least one** of
>
> `Λ²Π̂(b) + Λ²Π̂(c) + α_{pt(b)} = K⁶`,  `Λ²Π̂(b) + Λ²Π̂(c) + α_{pt(c)} = K⁶`
>
> holds, so from `r ≠ 0` at least one of **route A at `u`** (`r ⊥̸ Λ²Π̂(b)`),
> **route B at `u`** (`r ⊥̸ Λ²Π̂(c)`), **route σ at the `b`-end**
> (`r ⊥̸ α_{pt(b)}`) and **route σ at the `c`-end** (`r ⊥̸ α_{pt(c)}`) attains
> the target rank for `G`. The escape does not fail.

*Proof of the span.* `(β_{Π(b)} + β_{Π(c)})^{⊥_B} = β_{Π(b)} ∩ β_{Π(c)} =
⟨C(M)⟩`, so the sum is the 5-space `C(M)^{⊥_B}`. `α_{pt(b)} ⊆ C(M)^{⊥_B}` iff
every line through `pt(b)` meets `M`, iff `pt(b) ∈ M`, iff `pt(b) ∈ Π(c)`. So
under `pt(b) ∉ Π(c)` the sum is 6-dimensional (`α_{pt(b)} ∩ (β_b + β_c) =
pencil(pt b; Π(b))` is 2-dimensional, and `3 + 5 − 2 = 6`); symmetrically for
`α_{pt(c)}` under `pt(c) ∉ Π(b)`; and (σ7) supplies one of the two. ∎

`r ≠ 0` is exactly `dim R_a = 1` (`r` spans `R_a`). The `c`-end criterion is
already driver-tested at the pinned pool: `--transport` V3 asserts
`crit_B(σu) ⟺ r ⊥̸ α_{pt(c)}` at 47/47 alongside the `b`-end one.

**The side condition is FREE — this is new (2026-08-05) and it is a proof, not
a measurement.** The earlier statement carried `pt(b) ∉ Π(c)` as a hypothesis
and noted only that it is "one half of the already-named (Λ0d)", with the
`c`-mirror available "under the other half". That leaves open whether *both*
halves could fail. They cannot:

> **(σ7)** *(proven; validated `sigma.py --hunt` H4/H5)* Let `u` be a
> **primally nondegenerate** pencil realization of `G′` at a split whose chain
> ends `b, c` are hubs and whose middle body `a` is a non-hub with
> `closedNbhd a = {a, b, c}` (which is what `orient`'s degree-`2` `a` gives
> after `splitOff` adds `ab`). Then **at least one** of `pt(b) ∉ Π(c)`,
> `pt(c) ∉ Π(b)` holds.
>
> *Proof.* `ab, ac ∈ E(G′)` and `b, c` are hubs, so the cross-incidence
> (`dotProduct_eq_zero_of_extensorInPanel_of_extensorThroughPoint`, the fact
> `closedHubNbhd` is built on) puts `pt(a) ∈ Π(b) ∩ Π(c) = M`. Conjunct 3 at
> `a` reads `LinearIndepOn normal (closedHubNbhd a)` and `closedHubNbhd a` is
> exactly `{b, c}`, so `Π(b) ≠ Π(c)` and `dim M = 2`. Suppose **both** halves
> failed: `pt(b) ∈ Π(c)` gives `pt(b) ∈ Π(b) ∩ Π(c) = M`, and likewise
> `pt(c) ∈ M`. Then `pt(a), pt(b), pt(c)` all lie in the 2-dimensional `M`,
> contradicting conjunct 4 at `a` — `LinearIndepOn point (closedNbhd a)` on the
> 3-element set `{a, b, c}`. ∎

**Scope note, stated because it is easy to over-read.** (σ7) is about the
**disjunction** and nothing more. It does *not* make §(K-Λ) *Step 6*'s
two-sided (Λ0d) free — (Λ2) needs **both** halves, and (σ7) supplies only one.
Nor does it make *Step σ5* obligation 1's dual conjunct 2 free at `a`'s two
edges: that conjunct *is* two-sided (Λ0d) (see obligation 1), and one half can
fail, as `--hunt` H4 exhibits at 35 hard-stratum primally-nondegenerate
configurations. **The span is free; the dual conjunct is not.**

**Consequence for the (K-Λ) trichotomy, IF the candidate stands.** §(K-Λ)'s
*Theorem (Λ-completeness at length-4 companions)* reads: exactly one of
`Q(z) ≠ 0` (escape by pitch), `V_bc ⊆ C(bc)^{⊥B}` (escape by route A),
`V_bc ⊆ C(M)^{⊥B}` (**the escape genuinely fails**). The third branch is
precisely `★r ∥ C(M)`, i.e. route σ's *success* case. So the trichotomy would
have **no failure branch**, and the conclusion would be length-free — route σ
never mentions a companion, so it does not pass through (K-pitch), (K-wit),
(K-Λ) or the `ℓ ∈ {5,6}` obstruction at all. Those results stand as mathematics
either way; what changes is whether they are on the escape's critical path.

### Step σ4 — machine validation (exact ℚ)

Driver `notes/scripts/w4/sigma.py` (tracked, new this pass). **47** hard-stratum
seeds across two splits of the tight control (double-subdivided `K4`,
`|V| = 16`, target 90 / `G′` target 84): seeds 440–479 at chain 0 (23 valid) and
500–529 at chain 1 (24 valid), all with `s₀ = 0`, `dim R_a = 1`. Every figure is
`n/n` over that pool.

> **POOL RE-BASELINED 2026-08-06 — 63 → 47, and every `n/n` below survives
> verbatim.** Slice S2 of the harness re-baselining round adopted the composite
> genericity guard `repin.star_generic` at `sigma.hard_stratum_seed`
> (`notes/scripts/README.md` *Harness debt* item 4): **16 of the former 63
> seeds carried a coincident hinge line** — a body with two of its hinge lines
> equal, which the closed-star rank test alone passes and no
> `IsNondegPencilRealization` conjunct excludes ((OC-7)). The pool is now
> `23 + 24 = 47`, strictly cleaner, and **not one check changed its verdict**:
> every row of the table below reads `47/47` where it read `63/63`, and the
> `--hunt` counts moved the same way (H1 `52 + 55` → `45 + 47`, H2 `27 + 26 =
> 53` → `22 + 23 = 45`; H4's 35 and H5's 39 are unchanged). The numerals in
> this section are the **new** ones throughout; the three places a `63/63`
> survives are explicitly about the *2026-08-05 defect* of quoting an aggregate
> across inconsistent pools (F11), not about this pool.

| check | mode | result |
|---|---|---|
| homogeneous pencil data `ν_w·p̂_w = 0`, `ν_u·p̂_w = 0` on edges | `--transport` V0 | 47/47 |
| **(σ4)** `ν_u ∧ ν_w ∝ ⋆(p̂_u ∧ p̂_w)` on every edge | V1 | 47/47 |
| `rank R(σu) = ` target, `dim R_a`, `s₀` agree with `u` | V2 | 47/47 |
| `r(σu) ∝ ★r(u)`, and **(σ6)** `crit_A(σu) ⟺ r(u) ⊥̸ α_{pt(b)}` (+ the `c` mirror) | V3 | 47/47 |
| **`dim(β_{Π b} + β_{Π c} + α_{pt b}) = 6`** — *genericity, not necessity: see the correction below* | V4 | 47/47 |
| route A at `σu` reaches target rank for `G`; its pullback into `u`'s frame is the `pt(v) = pt(b)` family | V5 | 47/47 |
| `dim(α_{pt b} + α_{pt c}) = 5`, perp generated by `★C(bc)` | `--adv` A | 47/47 |
| `dim(β_{Π b} + β_{Π c}) = 5`, perp `★C(M)`; `C(M) ∦ C(bc)` | `--adv` B | 47/47 |
| the pullback is a legal pencil realization (nonzero hinges, incidences, target rank) | `--adv` D | 47/47 |
| `predA` (= `r ⊥̸ α_{pt b}`) true; **`predAfalse = 0/47`** | `--adv` C | 47/47 |
| routes A/B at `u` *already* escape | `--adv` | 47/47 |
| `u` satisfies all four `IsNondegPencilRealization` conjuncts | `--nondeg` | 47/47 |
| **`σu` satisfies all four conjuncts** (each reported separately) | `--nondeg` | 47/47 — *genericity, not an implication: `--hunt` H2 breaks conjuncts 2 and 4 by construction* |
| **the route-σ witness is a nondegenerate pencil realization of `G`** | `--nondeg` | 47/47 |
| the witness satisfies the chart's binding point equations | `--nondeg` | 47/47 |

*(The "chart" row checks that each body's point is the common point of its
closed-hub-neighbourhood panels — a `cross₃` where that set has three members,
an orthogonality where it has fewer; it does **not** perform the `fillHub`
solve, so it is evidence for, not proof of, chart-image membership.)*

**The (K-res) residual habitat is UNSAMPLED, not tested-and-passed.** `--adv`
also probes two `W19` splits over seeds 600–619 and finds **0** valid
hard-stratum seeds (17 of 20 draws per split are rejected at the stratum test —
`W19` has `f(V) = 2`). The driver asserts that this leg stays empty, so a
successor who makes it nonempty is forced to update this section.

### Step σ4b — the obligation-1 hunt (`--hunt`, 2026-08-05), and one correction

**Pool discipline first.** `--hunt` runs on **three pools of its own**, printed
in its header and deliberately **disjoint from the pinned 47**: random
1000–1059, coplanar-chain 2000–2029 and (Λ0d) 3000–3019, *per split*, over the
same two tight-control splits. **No figure below is over the pinned pool and
no *Step σ4* figure is over these.** (The discipline is explicit because the
pass that opened this section first reported its "63/63" as an aggregate across
scratch drivers running *different* pools, and only its landing dispatch caught
it before the figure was recorded. Here the separation is structural: `--hunt`
never touches `CHAIN0_SEEDS`/`CHAIN1_SEEDS` and the other four modes never touch
the hunt pools.)

| leg | what it establishes | result |
|---|---|---|
| **H0** the shape's *conjunct arithmetic* | no hub–hub edge; `closedHubNbhd v = {v}` at every hub; `closedHubNbhd v ⊆ closedNbhd v` everywhere | asserted at both splits |
| **H1** the fresh random pool | 92 fresh hard-stratum seeds (45 + 47), all four dual conjuncts at `σu` | **0 failures** — random draws never reach the locus |
| **H2** the **constructive** failure | a legal, hard-stratum, **primally nondegenerate** placement whose dual conjuncts **2 and 4 FAIL** at `σu` (1 and 3 hold) | **45/45** (22 + 23), exact pattern `(T, F, T, F)` |
| **H3** the **steering** | on the chart line `x(τ)`, the bracket is `τ·bracket(1)` *identically* with `bracket(1) ≠ 0`; at every `τ ≠ 0` the seed is hard-stratum with primal **and** dual 4/4 | 12 lines, 60 steered points, all `n/n` |
| **H4** (Λ0d) one-sided | `pt(b) ∈ Π(c)` **is** reachable on the hard stratum at a primally nondegenerate seed: the `b`-span drops `6 → 5`, the `c`-mirror span is 6, and the failing scalar **is** dual conjunct 2 on the edge `ac` | **35/35** (18 + 17) |
| **H5** (Λ0d) both halves | forcing both is a legal pencil placement with adjacent points distinct, but `rank(pt a, pt b, pt c) = 2` and `a` has **no panel at all** — the witness for **(σ7)** | **39/39** (19 + 20) |

**The construction (H2), because it is the whole content.** In a chain
`h – x – y – h′` with `h, h′` hubs and `x, y` degree-2, `x`'s only panel
constraint is `x ∈ Π(h)` and `y`'s is `y ∈ Π(h′)`. Pick `z` on the meet line
`Π(h) ∩ Π(h′)`, put `x` on the line `h z` and `y` on the line `h′ z`: both
constraints hold and `h, x, y, h′` are **coplanar**. Coplanarity makes `x`'s
panel (the plane `h x y`) and `y`'s (the plane `x y h′`) coincide, so at `σu`
the adjacent "points" `N[x]`, `N[y]` are projectively equal. Nothing primal
notices — **the four primal conjuncts only ever look at the points.**

> **CORRECTION to *Step σ4* (F11: this pass's own predecessor).** V4's
> "`dim(β_{Π b} + β_{Π c} + α_{pt b}) = 6` at 47/47" is a **genericity**
> observation. H4 exhibits 35 hard-stratum, primally-nondegenerate
> configurations of the *same* two splits where that span is **5**. The *Step
> σ3* theorem survives — it now quotes (σ7)'s disjunction instead of the
> `b`-form side condition — but no reading of V4 as "the span is forced" is
> licensed. The same caution applies to *Step σ5* obligation 1's "observed
> 47/47": the observation was true and the implication it suggested is
> **false**.

### Step σ5 — the four obligations, stated so they can be attacked

1. **`σ`-nondegeneracy of the seed: NOT implied — and now witnessed, reduced
   to two conjuncts, and steered.** `IsNondegPencilRealization u` does **not**
   imply it at `σu`. The four conjuncts (`Motive.lean:110–115`) split three
   ways, and the split is the useful part:

   - **Conjunct 1 is SELF-DUAL as a landed theorem, not as an observation.**
     `hasPencilPanelRealization_mapExtensor_screwComplementIso`
     (`Pencil/Statement.lean:257`) says exactly that
     `HasPencilPanelRealization G F normal point` gives
     `HasPencilPanelRealization G (F.mapExtensor σ) point normal`. That *is*
     conjunct 1 at `σu`. (Verified against the landed proof, 2026-08-05: it is
     stated at `K = ℝ`, `k = 2`, and the framework it produces is
     `F.mapExtensor screwComplementIso`, which is the right one — route σ
     works with the σ-image framework throughout.) **Free — AT `ℝ` ONLY.**
     `screwComplementIso` is `ScrewSpace ℝ 2 ≃ₗ[ℝ] ScrewSpace ℝ 2`, while `hK`
     is quantified at the general `[Infinite K]` of
     `pencil_conjecture_of_hcontract_hK_hbareSplit_of_card`, so at that `K`
     there is no `σ` in tree and this bullet says nothing. See *Field scope*:
     the gap is recorded, not settled, and the reading suggests the polarity
     generalizes.
   - **Conjunct 3 is implied by the PRIMAL conjuncts whenever no two hubs are
     adjacent.** At `σu` it reads `LinearIndepOn point (closedHubNbhd v)`. At a
     hub `v` with no hub neighbour, `closedHubNbhd v = {v}`, so it is
     `point v ≠ 0` — primal conjunct 1. At a non-hub `v`,
     `closedHubNbhd v ⊆ closedNbhd v`, so it is primal conjunct 4 restricted
     (`LinearIndepOn.mono`). Asserted combinatorially on the sampled shapes by
     `--hunt` H0, and observed to hold at all 45 constructed failures.
     **Free on the no-adjacent-hubs shapes; a genuine condition otherwise.**
   - **Conjunct 2 at the split's two edges `ab`, `ac` is exactly two-sided
     (Λ0d)**, an already-named condition rather than a new one: `a`'s panel is
     the plane through `pt(a), pt(b), pt(c)`, so `N[a] ∥ N[c] ⟺ pt(b) ∈ Π(c)`
     and `N[a] ∥ N[b] ⟺ pt(c) ∈ Π(b)`. By **(σ7)** at most one half fails —
     but one half *does* fail on the hard stratum (`--hunt` H4, 35/35), so this
     is **not** free.
   - **Conjunct 2 at the remaining edges, and conjunct 4 at every non-hub, are
     the genuinely new content — and they FAIL.** `--hunt` H2 constructs
     **53** legal, target-rank, `s₀ = 0`, `dim R_a = 1`, **primally
     nondegenerate** `G′` seeds at which dual conjuncts 2 and 4 both fail at
     `σu` (the coplanar-chain degeneration, *Step σ4b*). So the 47/47
     observation was genericity; the implication is **false**, and obligation 1
     cannot be discharged by "it always happens to hold".

   Three repairs, in increasing cost, unchanged in shape but now with a
   measured verdict on each:

   (a) carry the dual conjuncts as extra hypotheses on the induction's motive.
   They are open conditions and the ℚ-witnesses certify non-vacuity — but H2
   shows the extra hypotheses genuinely **cut** the seed space, so (a) is a
   real strengthening of the motive, not a free annotation.
   (b) re-seed. **`exists_pencilSeed_of_nondeg` (`Reseed.lean:65`) is NOT the
   bridge and would be circular if used as one** — it *takes*
   `IsNondegPencilRealization` as a hypothesis, i.e. exactly obligation 1
   (coordinator-verified against the landed statement, 2026-08-05). Repairs
   (b) and (c) are therefore **not interchangeable**, which the earlier
   wording implied.
   (c) **the named repair, and now the only one with a validated mechanism** —
   the dual conjuncts are nonvanishing polynomial conditions on the pencil
   chart, so steer to a common seed where target rank *and* they hold, via the
   landed `exists_common_seed_pencilRow_and_polynomials` (`Engine.lean:476`).
   Its own docstring already names its intended consumer as "W5-L7's rank
   target *and* its candidate-`M₁` escape polynomial". Three things about it
   are worth recording so the eventual Lean pass does not rediscover them:

   - **There is no chart-image side condition.** `pencilChartPointPoly` /
     `pencilChartNormalPoly` (`Engine.lean:200–235`) are polynomials in a
     *free* seed `q : α × Fin 4 × Fin 4 → K` with eval identities to
     `pencilChartPoint/Normal (PencilSeed.ofCoord q)`. The chart is a **total
     parameterization**, so the theorem's hypothesis
     `hP : ∀ i, ∃ q, eval q (P i) ≠ 0` needs merely *some* seed per polynomial
     — any seed, not a nondegenerate one and not one reproducing the ℚ
     witnesses.
   - **The LI conjuncts are not literally one polynomial's nonvanishing.**
     Dual conjuncts 2/3/4 are `LinearIndependent` / `LinearIndepOn`
     conditions, i.e. "**some** maximal minor ≠ 0" — a *union* of basic opens.
     The repair only needs **sufficiency**, so fix **one specific minor per
     conjunct** whose nonvanishing implies it. That choice is graph-dependent
     and is the actual (bounded) Lean content.
   - **The steering is exhibited exactly, not sampled** (`--hunt` H3). On the
     chart line `x(τ) = (1−τ)·x_deg + τ·x_gen` inside `Π(h)`, the offending
     scalar is the bracket `[P_h, P_x(τ), P_y, P_h′]`, which is **affine in
     `τ`** (multilinear bracket, affine `hat`) and vanishes at `τ = 0`, hence
     equals `τ·bracket(1)` identically; with `bracket(1) ≠ 0` the failure locus
     meets the line in the **one** point `τ = 0`. At every `τ ≠ 0` tested the
     seed is hard-stratum with primal **and** dual conjuncts 4/4. That is
     repair (c) in exact arithmetic: one polynomial, degree 1 along the line,
     steered off while the rank is kept.

   **Net.** Obligation 1 is not vacuous and is not free, but it is **smaller
   than it looked**: two of four conjuncts are free **at `ℝ`** (one by a landed
   theorem, one by the primal conjuncts on the shapes in scope), one is a
   re-labelling of the already-named (Λ0d), and the remaining content has a
   validated steering mechanism. It remains **Lean engineering against a landed
   pattern, not new mathematics** — with **two** design decisions, not one: the
   minor-choice above, and **the field**. Discharging `hK` at `ℝ` (instantiate
   the headline first) needs no new duality work; discharging it at the general
   `K` the landed headline quantifies over needs a **general-`K` polarity**,
   which does not exist in tree. *Field scope* prices that; the choice is not
   made here — but it is no longer a symmetric one. **§(K-clos) (AC-7): `hK`
   over `ℂ̄` implies `hK` over every infinite characteristic-0 field, and the
   converse fails**, so "instantiate at `ℝ`" is the **narrowest** available
   option, not merely *a* narrowing; and **§(K-clos) (AC-1)** prices the
   general-`K` polarity at one section with every input already landed
   (`mapSupport`). The residual content of `[Infinite K]` after a
   characteristic-0 proof is **positive characteristic only**.
2. **Scope.** Verified only at `s₀ = 0`, `dim R_a = 1`, both ends hubs, on the
   tight control — and the `--hunt` pools do not widen that: they are further
   configurations of the *same* two splits of the same shape, chosen
   adversarially rather than randomly. The `dim R_a = 0` stratum is
   **untouched** — `r = 0` there and
   route σ helps no more than routes A/B; §(K-flank) *F5(d)*'s five `P21`
   uniform-failure seeds sit there and remain uniform failures (`hK`'s ∃-form
   over seeds is what covers them, unchanged). The `s₀ ≥ 1` residual habitat
   ((K-res); `W19` `s₀ = 2`, `S29`) is **unsampled** — the criterion is stated
   for the hard stratum generally, but route σ has not been run there.
3. **The criterion at `σu` is IMPORTED, not re-derived.** §(K-tight) *Step
   2.4*'s criterion is applied at a different seed with its two derivation
   ingredients checked there; `repin.py`'s per-placement 80/80 biconditional was
   validated at `u`-type seeds only. No seed with `crit_A(σu)` **false** exists
   in the pool (`predAfalse = 0/47`), so the **failure direction** of (σ6) is
   **unwitnessed**.
4. **The branch route σ closes has NEVER been observed nonempty.**
   `lambda.py --adv` hunts `λ ∝ p⁺` (= `★r ∥ C(M)`) and finds none; at all 47
   seeds here routes A/B already escape at `u`. So route σ does not repair an
   observed failure; it removes the *possibility* of one, uniformly. State the
   gain as **evidence → argument**, never as *bug fixed*.

### Step σ6 — three settled negatives, so they are not re-derived

- **Involutivity is not on the critical path.** `σ² = id` holds exactly, but
  route σ applies `σ` **once**, to the seed, and never returns; the pull-back in
  *Step σ2* is exposition. In tree: `screwComplementIso`, the two forward
  predicate transports
  (`extensorInPanel_screwComplementIso_of_extensorThroughPoint` and its dual),
  the stratum self-duality
  `hasPencilPanelRealization_mapExtensor_screwComplementIso`, and
  `complementIso_toDual` / `complementIso_map_contragredient_eq`. **Every
  `screwComplementIso` entry in that list is `ℝ`-fixed** (*Field scope*; the
  `complementIso` ones are general-`K`). **Not** in
  tree: any statement that `σ` is self-adjoint, an isometry, or an involution.
  The natural route to `σ² = id` is (i) self-adjointness — immediate from
  `complementIso_toDual` (`⟨⋆X, Y⟩ = vol(X ∨ₑ Y) = vol(Y ∨ₑ X) = ⟨⋆Y, X⟩`, even
  grades commute) — then (ii) a `Module.Basis.ext` evaluation on the six-element
  exterior-power basis of `Λ²K⁴`. One focused leaf; the `rfl` closing
  `screwComplementIso_lineExtensor` is evidence the reduction computes. (This is
  the same missing lemma the phase note's *Blockers* records as off every
  critical path.)
- **A strictly σ-equivariant seed recipe is a DEAD END — and since §(K-clos) the
  reason is field-neutral, not `ℝ`-definiteness.**
  A σ-fixed pencil configuration needs `normal_v ∝ point_v`; the landed
  incidence conjunct `point v ⬝ᵥ normal v = 0` then forces
  `point_v · point_v = 0`, so **over `ℝ` with the project's (definite) polarity
  there are no σ-fixed configurations at all**. Over a field with isotropic
  vectors they **do** exist: a *symmetric* correlation
  forces every body point onto the fixed quadric and every hinge line to lie
  **on** that quadric (a union of two one-parameter rulings) — that confinement
  is exactly §(K-clos) (AC-2), and it is **not** a degeneracy. §(K-clos) (AC-3)
  exhibits σ-fixed configurations satisfying all four nondegeneracy conjuncts at
  the Tay target, so the *"worse than empty, it is degenerate"* framing this
  bullet used to attach to the **symmetric** branch is **REFUTED**; what earned
  that framing is the **null** branch, and only it. A *null*
  (symplectic) correlation `J` makes the incidence automatic and forces every
  hinge line into the **linear line complex** of `J`, whence `ω_e := c_e ★S` is
  a self-stress for every cycle-space flow `c` (`S` = the complex's screw), so
  the rank drops by at least the cycle rank. Measured on `C₆` (tight,
  `5|E| = 30 = 6(|V|−1)`, cycle rank 1): **deficit exactly 1 at 6/6**
  linear-complex placements (`sigma.py --fixed`). **The verdict stands on
  §(K-clos) (AC-5)**: at a σ-fixed seed `σu = u`, so route σ's uniform-failure
  criterion and route A's *coincide* as subspace conditions — an equivariant
  recipe would buy obligation 1 for free and **delete route σ in the same
  stroke**. *Route σ does not use
  equivariance* — it applies `σ` once to move to a **different** seed, which is
  exactly why it escapes this wall; (AC-5) upgrades that remark from an aside to
  the reason.
- **The `K222` self-duality hint does not connect through `σ`.** The
  octahedron's self-duality is a *graph/planar* duality; `σ` acts on
  realizations of **every** graph without any self-duality of the graph. So `σ`
  acting non-trivially is not a discriminator of the anomalous shapes, and
  §(K-pure) *P8*'s two mechanisms get nothing from this section — except the
  observation that `V_bc ∩ Λ²π̂ ≠ 0` is the σ-image of `V_bc ∩ α(·) ≠ 0` at the
  dual seed, which is worth one probe in the mechanisms pass.

### Verification

`notes/scripts/w4/sigma.py` (tracked; opened with this section, `--hunt` added
2026-08-05; exact-ℚ, stdlib-only, no
CAS; sits beside `dominance`/`outer` as a `w4/` leaf and imports only catalogued
§1 primitives from siblings; every sampled placement guarded by the composite
`repin.star_generic` (`flanks.star_span_ranks` alone until 2026-08-06, slice
S2) and every span's dimension asserted; all rng seeded;
output verified byte-identical under two different `PYTHONHASHSEED` values, so
no printed collection depends on hash order). Run from the repo root:

```
PYTHONHASHSEED=0 python3 notes/scripts/w4/sigma.py --transport   # (σ1)–(σ6), V0–V5
PYTHONHASHSEED=0 python3 notes/scripts/w4/sigma.py --adv         # the adversarial half
PYTHONHASHSEED=0 python3 notes/scripts/w4/sigma.py --nondeg      # nondegeneracy at σu
PYTHONHASHSEED=0 python3 notes/scripts/w4/sigma.py --fixed       # σ-fixed is degenerate
PYTHONHASHSEED=0 python3 notes/scripts/w4/sigma.py --hunt        # obligation 1 (~135 s)
```

The first four modes assert every counter equals the pinned seed pool and print
`OK`; the pool size `47` is itself asserted, so a sampler change that silently
moved the pool fails the run. **`--hunt` runs on its own three pools** (*Step
σ4b*), never on the pinned pool, and asserts each of H0–H5's counters against its own
leg — including `dualfail == 0` on the random leg, so a successor who *does*
find a random failure is forced to rewrite *Step σ4b*, and `bracket(τ) =
τ·bracket(1)` exactly, so a non-affine bracket would fail the run rather than be
averaged away. Neither pool's figures are quoted over the other.

Adding `--hunt` modified a tracked driver, so the figure-invariance gate fired
in full for `sigma.py` (a `w4/` leaf: nothing imports it, so its import closure
is itself). Baselined before the edit, re-run after: `--transport`, `--adv`,
`--nondeg`, `--fixed` all **byte-identical** at `PYTHONHASHSEED=0`, and
`--hunt` byte-identical under two different hash seeds.

**Confidence verdict.**

- **(σ1)–(σ4), (σ5), (σ6), (σ7) and the *Step σ3* span computation:
  proven-informally**, each exact and each with a driver mode asserting that
  sentence. **(σ7)** in particular is a proof from the primal conjuncts, with
  `--hunt` H5 as its witness that the excluded configuration really is
  excluded by conjunct 4 and not by the sampler.
- **The σ-intertwining question, literal form: REFUTED** (*Step σ1(a)*).
  **Covariant form: confirmed.**
- **σ-equivariant seed recipes: REFUTED** (*Step σ6*) — the verdict stands, but
  since 2026-08-06 **on §(K-clos) (AC-5)** (at a σ-fixed seed route σ *is* route
  A), not on `ℝ`-definiteness. The `C₆` witness still carries the **null**-
  correlation half; the *symmetric* half's "degenerate" is refuted by (AC-3).
- **"the dual conjuncts hold automatically at `σu`": REFUTED** (*Step σ4b* H2,
  45 constructed hard-stratum primally-nondegenerate witnesses). The 47/47 of
  *Step σ4* was genericity.
- **Route σ as a closure of (K-tight) on the hard stratum: CANDIDATE, offered
  for adjudication — and, as landed machinery, an `ℝ`-only one.** Obligation 1
  is still the single crux, now **sized**: two of its four conjuncts are free
  **at `ℝ`**, one is the already-named (Λ0d), and the steering repair is
  exhibited exactly. Obligations 2–4 bound the scope and the claim's strength.
  **No gap-map status moves.**
- **Field scope: SETTLED by §(K-clos)** (2026-08-06), where it was recorded here
  as open. `σ` is still `ℝ`-only *in tree* and `hK` is still consumed at general
  `[Infinite K]`, but the polarity **does** generalize — bookkeeping, one
  section, transport already landed ((AC-1)) — so (σ1)–(σ6), route σ and the
  conjunct-1 freeness all port; (σ7) and the span linear algebra were
  field-neutral outright; and *Step σ1(a)* and *Step σ6*'s two refutations
  **reverse** over `ℂ̄` ((AC-2)/(AC-3)) without moving the verdict they support
  ((AC-5)). Field choice is no longer symmetric: `ℝ` is the **narrowest** option
  ((AC-7)).

**What would change this.** *(i)* A seed where `crit_A(σu)` is false *and* route
A at `σu` nevertheless escapes (or vice versa) refutes (σ6) and with it *Step
σ3*. *(ii)* A hard-stratum seed where `σu` violates a nondegeneracy conjunct
**and** cannot be steered to one that does not would reduce route σ to the bare
(degeneracy-permitting) statement — still useful (that is `hbareSplit`'s shape),
but no longer a closure of `hK`. Half of this is now settled: violating seeds
**exist** (H2), and on every chart line tested the steering **works** (H3); what
is open is whether the steering survives *in Lean*, i.e. whether one can name
the specific minors and discharge their `≢ 0`-somewhere certificates.
*(iii)* Running route σ at a (K-res) residual (`W19`, `S29`, `s₀ = 2`) and
finding the span drops below 6 both ways, or `dim R_a = 1` failing there, would
cut the scope to the tight class. *(iv)* **SETTLED** at every both-ends-hubs
split by **(σ7)**: both halves of (Λ0d) cannot fail at once at a primally
nondegenerate seed, so `C(M) = C(bc)` is unreachable there and no genuine
residue is left. The one-sided failure §(K-Λ) *Step 6* exhibits at θ(3,4,5)
seed 345 is now known to be reachable on the **tight control's** hard stratum
too (H4, 35/35) — harmless for *Step σ3*, load-bearing for obligation 1.
*(v)* A class shape with **two adjacent hubs**: dual conjunct 3 stops being
free there (H0's hypothesis), and obligation 1 grows back to three conditions.
*(vi)* **ANSWERED, 2026-08-06 — §(K-clos).** The field question was recorded
here as open in all three of its parts, and all three are now settled. **The
polarity generalizes** ((AC-1)): bookkeeping, one section, and the general-`K`
transport is already landed as `mapSupport` — so route σ, conjunct-1 freeness
and (σ1)–(σ6) port, which is what obligation 1 needs. **The σ-fixed
configurations this item guessed "might well exist" DO exist** ((AC-2)) and are
nondegenerate at the Tay target ((AC-3)), so *Step σ1(a)* and *Step σ6*'s two
refutations **reverse** rather than merely failing to port — **but they do
NOT revive the σ-equivariant-recipe route**, because at a σ-fixed seed route σ
collapses onto route A ((AC-5)). And the field choice is **not** symmetric:
`hK` over `ℂ̄` implies `hK` over every infinite characteristic-0 field with the
converse false ((AC-7)), so instantiating at `ℝ` is the narrowest option, and
the residual content of `[Infinite K]` is positive characteristic. Nothing here
is left for a successor except the ~20-line typecheck spike (AC-1) names.
