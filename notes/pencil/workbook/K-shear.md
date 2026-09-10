## §(K-shear) — the Witt shear as a uniformity device is **DEAD**, and the reason is that it is a **gauge transformation**: the skew shears are exactly the `Λ²`-image of the affine translations, the pitch quadric is **their own defining invariant**, and the §(K-tight) criterion matrix is not merely rank-invariant but **literally the same matrix** in the pushed basis

Direction **ZSHEAR** (`notes/Pencil-fanout.md` §"ZSHEAR"), the first direction
`notes/Pencil-strategy.md` §9's external-technique shelf has ever produced,
dispatched on unprompted user initiative as a side line. It settles candidate
**(ZH-1)** of that shelf (§9.2). Read against §(K-tight) *Steps 0–3* (the
boundary-load calculus and its escape criterion), §(K-flank) *Step F5(d)* (the
adversarial bed), §(K-pitch) *Step 0* (the pitch quadric), and
`notes/Pencil-strategy.md` §2.5 / §4.6 (the two filters). Driver
`notes/scripts/w4/zshear.py`; all exact ℚ, the two structural modes fully
**symbolic** (identities in `ℚ[…]`, no sampling).

**Provenance, and it is a hard bar, not a formality.** The idea source is an
**unrefereed preprint** whose own acknowledgment credits an AI assistant with
the refinement of proof details, the Lean formalization and its verification,
and which **this project has not independently checked**. Per top-level
`CLAUDE.md` *Referencing prior work* and `DESIGN.md` *Formalize everything the
argument uses*, it is an **idea source, never a citation**: **no theorem of it
is imported, assumed, or leaned on anywhere in this section**. Everything below
stands on (a) classical facts already in `notes/Pencil-strategy.md` §7's in-use
list — the Klein quadric, its α/β maximal isotropics, Witt's theorem — and (b)
this project's own drivers and definition bodies. Nothing here needs the
source's Lemma 3.4 or Proposition 3.3, and nothing here is evidence for or
against them.

**Status, stated before the mathematics.**

- **(ZH-1) is REFUTED as a uniformity device, and the refutation is a
  computation-free identity plus its exact verification.** The skew shears
  `Φ_S(ω, b) = (ω, b + Sω)` are **not new machinery**: writing `s` for the
  axial vector of `S`, `Φ_S = Λ²(T_{−s})` **identically in `ℚ[s₀,s₁,s₂]`**,
  where `T_t` is the affine translation `x ↦ x + t` of 3-space. So the shear
  group *is* — not "is isomorphic to" — the **translation subgroup of `PGL(4)`**
  acting on line coordinates, i.e. a subgroup of the carrier's own projective
  gauge group. **(SH-1)**.
- **It cannot move the quantity §(K-pitch) needs moved, because that quantity
  is its own invariant.** `Φ_Sᵀ ★ Φ_S = ★` identically, so `Q(Φ_S x) = Q(x)`
  for every skew `S` and every `x`. The pitch quadric is the shear group's
  **defining invariant**. **(SH-2)**.
- **On the arc's own adversarial bed the failure locus is shear-invariant
  exactly, and by more than rank equality.** At all 35 valid `P21` seeds of
  §(K-flank) *Step F5(d)* — both strata, none skipped — the shear carries the
  whole §(K-tight) criterion: `U′ = Φ^{−T}U` and `R_a′ = Φ^{−T}R_a` as
  subspaces (45/45), `Λ²Π̂(b)′ = Φ·Λ²Π̂(b)` and `C(ab)′ = Φ·C(ab)` (45/45), the
  `2 × dim U` criterion matrix **equal entry-for-entry** in the pushed basis
  (150/150), and the exact rank equal at every corresponding placement on both
  KT routes (222/222). **(SH-4)**.
- **Therefore the (ZH-1) mechanism has nothing to act on.** For a fixed seed
  the set of "bad `S`" is **all of `so₃`** (if the seed fails) or **empty** (if
  it escapes) — never a *proper nonempty* affine subspace. "Finitely many
  proper affine subspaces cannot cover an affine space over an infinite field"
  is a true and useful principle that is **vacuous here**. **(SH-4)**.
- **The coordinator's offered repair — one shear per body — does not survive
  either, and the two halves of why are both exact.** Off the diagonal the
  product action does not preserve the form generator-wise: identically,
  `Q(Φ_{t_u}X_u − Φ_{t_v}X_v) = Q(X_u − X_v) + 2(t_u − t_v)·(dir X_u × dir X_v)`.
  And on the carrier side, the maximal family of **per-body translations**
  preserving the pencil conditions at fixed panel normals is computed exactly
  (dim 49 of 3|V| = 63 at `P21`) and acts **simply transitively on the
  fixed-normal slice of the pencil chart** — it *is* that slice re-labelled
  (§(K-slide) *Step 1(e)*'s linear-fiber tower with normals frozen), and it
  moves `dim R_a` (6/6 fields kill the forced failure). **(SH-5)**.
- **The general reason, which subsumes §4.6's predicted death and is stronger
  than it.** §4.6's growing-ground-set filter predicted that `so₃(k)` is
  fixed-dimensional and "cannot see the graph". That is true but not the sharp
  statement: the shear cannot see **anything** — it is a gauge, and every
  ingredient of the criterion is transported with it. The sharp statement is a
  **dichotomy**: a group under which the criterion is equivariant cannot turn a
  failing seed into an escaping one, and a family that *does* move a failure is
  not a symmetry and propagates no witness. **(SH-6)**.
- **Gap-map effect: NONE.** No *State of (K)* row moves and no status keyword
  changes. What moves is `notes/Pencil-strategy.md` §9's shelf: **(ZH-1) is
  struck**, and §9.3's order advances to **(ZH-4)**.

### Standing notation

`G`, the split `b–v–a–c`, `G′ = G^{ab}_v`, `s₀`, `U`, `R_a`, `Λ²Π̂(b)`,
`Λ²Π̂(c)`, the meet line `M` and the transmitted wrench `r̃ = ★r` are
§(K-tight) *Step 2*'s, unchanged. `Q(x) = ⟨x, ★x⟩` is §(K-pitch) *Step 0*'s
pitch quadric. Plücker coordinates are the harness's: `PL = [(0,1),(0,2),
(0,3),(1,2),(1,3),(2,3)]`, `hat(c) = (c₀,c₁,c₂,1)`, so index 3 homogenizes and
the plane at infinity is `x₃ = 0`; for `w ∈ Λ²K⁴`,
`dir(w) = (p₀₃,p₁₃,p₂₃)` and `mom(w) = (p₁₂,−p₀₂,p₀₁)`, and a line through
affine `x, y` has `dir = x − y`, `mom = x × y`. `T_t : x ↦ x + t`.

### Step SH1 — what the shear IS: the form is ours, and the group is the translations

> **(SH-1)** *(proven; a symbolic identity, `--iso`)* Three identities, over
> `ℚ` with free indeterminates and no sampling anywhere:
>
> 1. `Q(w) = ⟨w, ★w⟩ = 2·dir(w)·mom(w)` identically in `ℚ[w₀,…,w₅]`. So
>    §(K-pitch) *Step 0*'s pitch quadric and the split form `q(ω,b) = ω·b` are
>    **the same form in the harness's own coordinates**, with the dictionary
>    `ω ↔ dir`, `b ↔ mom`. This upgrades `notes/Pencil-strategy.md` §9.1's
>    "same form, same vanishing locus, same meaning" from a reading to an
>    identity in the project's convention.
> 2. Writing `s` for the axial vector of the skew `S` (i.e. `Sx = s × x`),
>    `Φ_S = Λ²(T_{−s})` identically in `ℚ[s₀,s₁,s₂]`. The two sides are built
>    **independently** in the driver — one from the `(dir, mom)` shear formula,
>    one as the second compound matrix of the `4 × 4` translation — so the
>    comparison is a real identity check, not a restatement.
> 3. `s ↦ S` is a linear isomorphism onto `so₃`, and `dim so₃ = 3 = ` the
>    dimension of the translation group. So the shear group is **exactly** the
>    translation subgroup, with no room for a larger or smaller image.

The dimension coincidence in item 3 is the `d = 3` accident `d(d−1)/2 = d`, and
it is worth naming because it is the *only* dimension at which the skew-shear
group and the translation group could coincide at all. (§9's own dimensional
note about the source sitting on a `d = 3` boundary is a **different**
observation about a different object; the two are not evidence for each other,
and nothing here is a claim about the source.)

> **(SH-2)** *(proven; a symbolic identity, `--iso`)* `Φ_Sᵀ ★ Φ_S = ★`
> identically in `ℚ[s]`, so `Q(Φ_S x) = Q(x)` for every skew `S` and every
> `x ∈ K⁶`: **`Q` is the shear group's own defining invariant**. The maximal
> isotropic the shears fix *pointwise* is `span(e₀₁, e₀₂, e₁₂)` = the lines
> lying in the plane at infinity — a **β-plane** of the Klein quadric,
> i.e. one of the classical objects already in `notes/Pencil-strategy.md` §7's
> in-use list. Conversely the shears **exhaust** that β-plane's pointwise
> stabilizer in `O(Q)`, by the classical argument: `W₀` maximal isotropic gives
> `W₀^⊥ = W₀`, so `g` trivial on `W₀` is also trivial on `K⁶/W₀ ≅ W₀^*` (the
> two actions are inverse-transpose under the `Q`-pairing), whence `g = 1 + φ`
> with `φ : K⁶/W₀ → W₀` killed on `W₀` and *alternating* by the `O(Q)`
> condition — so the stabilizer is `Λ²W₀`, of dimension 3, which the shears
> already fill. (Sanity aside, for the reader who expects the projective
> homotheties here: `x ↦ λx` fixes the plane at infinity pointwise only
> *projectively*, and rescaling it into `O(Q)` forces `λ = 1`.) **Nothing
> larger is on offer.**

**Two consequences worth recording independently of (ZH-1).**

- **The shear was already available to the arc, and so is everything like it.**
  Every carrier condition is a projective incidence condition and is therefore
  `GL(4)`-covariant under the triple action `point ↦ g·point`,
  `normal ↦ g^{−T}·normal`, `supportExtensor ↦ g ∘ supportExtensor` — read off
  the definition **bodies** this pass, not their docstrings:
  `HasCoplanarPanelRealization` (`Theorem55.lean:3059`) is `F.graph = G` plus
  nonzero-ness plus `ExtensorInPanel`; `HasPencilPanelRealization`
  (`Statement.lean:88`) adds `point v ≠ 0`, `point v ⬝ᵥ normal v = 0` and
  `ExtensorThroughPoint` at both endpoints; `IsNondegPencilRealization`
  (`Motive.lean:110`) adds link-pair linear independence of `point`,
  `LinearIndepOn normal (closedHubNbhd v)`, and `LinearIndepOn point
  (closedNbhd v)` at non-hubs. Each is a pairing/span condition, hence
  preserved. So no *subgroup of `PGL(4)`* can be a uniformity device on a fixed
  seed, and the shear is the 3-dimensional tip of a 15-dimensional group the
  arc has had all along.
- **No gauge-fixing can ever supply `Q(r̃) ≠ 0`.** Since `Λ²g` scales `Q` by
  `det g`, the condition `Q(r̃) ≠ 0` is `PGL(4)`-invariant. Normalizing a local
  frame — as `m2/lambda1.m2` block (M4) does, the "gauged local frame with `λ`
  free" — is legitimate and useful *for computation*, and it is provably
  incapable of *producing* the non-vanishing. That is a small, new, permanent
  negative about the arc's own habits, and it is where this direction's residue
  actually lands.

### Step SH2 — the adversarial bed, guarded before anything is concluded from it

> **(SH-3)** *(measured, exhibited; `--bed`)* §(K-flank) *Step F5(d)*'s bed is
> re-derived from scratch and **asserted against that step's recorded values
> before use**: at `P21` (|V| = 21, |E| = 24, split `v = 100`, `a = 101`,
> `b = 0`, `c = 1`), over seeds 101..140, exactly **30** seeds have
> `dim R_a = 1` / `s₀ = 0`, exactly **5** have `s₀ = 1`, `dim R_a = 0`,
> `dim U = 1` (seeds 101, 111, 128, 136, 138), and **5** are invalid — the
> recorded `(30, 5, 5)`, matched, with §(K-tight) *Step 2*'s three structure
> identities (`dim U = dim R_a + 1`, `U ∩ C(ab)^⊥ = R_a`, `R_a ⊆ U`) asserted at
> every valid seed. The `localtest.plane_basis` precedent is **exactly** this
> bed (§(K-out) **(OC-38)**(iii)), so the composite gate is *reported*, not
> assumed: `repin.star_generic` rejects **5/5** forced-failure seeds and
> accepts **26/30** escaping ones — so gate rejection is **necessary but not
> sufficient** for the `dim R_a` jump in this range (4 escaping seeds are also
> rejected). The five remain **legal** chart points; every figure in *Step SH3*
> is stated about them as **exhibited points, never as a rate**.

### Step SH3 — the equivariance theorem, and why it is fatal rather than merely true

> **(SH-4)** *(proven, and verified exactly; `--inv`)* Let `Φ = Φ_S` be a
> shear, `Φ = Λ²(T_t)` with `t = −s` by **(SH-1)**, and shear a seed by
> translating every body point. Then every ingredient of the §(K-tight)
> criterion is **transported**:
>
> - hinge extensors push forward, `C(uv)′ = Φ·C(uv)`, so the motion space
>   `{m : m(u) − m(v) ∈ ⟨C(uv)⟩}` maps isomorphically under `m ↦ Φ ∘ m`, and
>   every rank/corank in sight — `rank(G′)`, `rank(G)`, `s₀`, `corank` — is
>   **unchanged**;
> - loads push forward by `Φ^{−T}`: `U′ = Φ^{−T}U` and `R_a′ = Φ^{−T}R_a`;
> - panels push forward: `Λ²Π̂(b)′ = Φ·Λ²Π̂(b)`, likewise at `c`;
> - and the two placement functionals of *Step 2.1* are **literally the same**
>   in the pushed basis, because `⟨Φ^{−T}u, Φ·C⟩ = ⟨u, C⟩`. So the
>   `2 × dim U` criterion matrix at placement `x + t` for the sheared seed
>   **equals**, entry for entry, the matrix at `x` for the original — not
>   merely has the same rank.
>
> Consequences. Attainment holds at `x` iff it holds at `x + t`; uniform
> failure is preserved; `dim R_a = 0` stays `dim R_a = 0`; and `Q(r̃)` is
> preserved outright by **(SH-2)**, with `r̃′ ∈ ⟨Φ·r̃⟩`. Hence, for a fixed
> seed, `{S : the sheared seed still fails}` is `so₃` or `∅` — **never a proper
> nonempty affine subspace**. The (ZH-1) mechanism is not wrong; it is
> **vacuous on this criterion**.

*Measured, at the cap disclosed in the driver docstring:* 35/35 bed seeds pass
the re-keying guard (the placement-driven criterion reproduces
`repin.seed_probe` field-for-field at `t = 0`); 45 shears applied; 45/45
subspace transports; 150/150 criterion-matrix equalities; 222/222 exact rank
equalities at corresponding placements across both routes; 45/45 attainment
verdicts equal; 30/30 pitch checks. **Zero exceptions** — and every one of
these is an `assert`, so a single exception would fail the run rather than
appear in a rate.

*Scope, stated rather than hidden.* The driver verifies the translation
subgroup exactly, in the harness's 5-rows-per-hinge model. The extension to all
of `PGL(4)` is the **same two-line duality argument** with `Φ` replaced by
`Λ²g` (and `Q` scaling by `det g`), and the Lean-side rank invariance is that
argument modulo §(K-tight)'s **already-recorded** model-to-Lean dictionary item
(*what would change this*: the scripts' Euclidean-perp rigidity model vs
`BodyHingeFramework.rigidityRows`). That is a known item, not a new gap.

### Step SH4 — the graph-indexed repair, decided in both of its readings

The coordinator's offered reading — make the group **graph-indexed**, a shear
per body, `so₃(k)^V` rather than one global `S` — is the only repair with a
chance at §4.6's filter. It has two candidate liftings and **both** are
settled.

> **(SH-5)** *(proven; a symbolic identity plus an exact computation, `--prod`)*
>
> *(i) On twists (the direction-complex reading).* For per-body translations
> `t_u`, identically in `ℚ[dir X_u, mom X_u, dir X_v, mom X_v, t_u, t_v]`:
>
> > `Q(Φ_{t_u}X_u − Φ_{t_v}X_v) = Q(X_u − X_v) + 2 (t_u − t_v)·(dir X_u × dir X_v)`.
>
> So the product action preserves the form **generator-wise iff**
> `t_u − t_v ⊥ dir X_u × dir X_v` at every edge — one linear condition per
> edge, and the conditions **depend on the point**. Off the diagonal the defect
> is nonzero (`dir X_u = e₀`, `dir X_v = e₁`, `t_u − t_v = e₂` gives 2). So the
> product is **not an action on the variety**; only the diagonal — the global
> shear of *Step SH1* — is. What survives is a *point-dependent* linear
> subspace, cut by `|E|` conditions that depend only on the `dir` components,
> hence closed under addition on each `dir`-fiber: a fiberwise abelian group,
> not a group acting on the family. It is not obviously useless, but it is not
> a symmetry, and this section neither prices nor pursues it.
>
> *(ii) On the carrier (the reading that matters here).* In the pencil carrier
> a hinge is **determined** by its endpoints' points, so a per-body translation
> field is simply a new placement. Requiring it to keep the carrier legal at
> **fixed** panel normals is exactly `normal_h·(t_u − t_h) = 0` for every hub
> `h` and every `u ∈ N(h)` — one linear condition per hub-neighbour incidence.
> Computed exactly at `P21` seed 101: 14 incidences, constraint rank 14, family
> dimension **49** of `3|V| = 63`, containing the 3-dimensional diagonal
> (asserted). The family therefore **passes** §4.6's growing-ground-set filter,
> unlike `so₃`. And it is the wrong kind of object anyway: since the
> fixed-normal legal set is an **affine subspace** of `(K³)^V` and this family
> is its direction space, the family acts **simply transitively** on it — it
> *is* the fixed-normal slice of §(K-slide) *Step 1(e)*'s chart, re-labelled.
> It is **not** a symmetry of the criterion: 6/6 seeded fields move the
> forced-failure seed off `dim R_a = 0` (against 0/45 for the global shear —
> the same three coordinates per body, the whole difference being whether they
> are **shared**).

### Step SH5 — the verdict, and the general form it takes

> **(SH-6)** *(proven-informally; an argument, and the one to attack)* Two
> statements, the second the reason (ZH-1)'s *shape* was never going to help.
>
> *(a) The propagation dichotomy.* Let `Γ` act on a habitat's pencil chart. If
> the escape criterion is `Γ`-equivariant, the escaping set is a union of
> `Γ`-orbits, so `Γ` **cannot** convert a failing seed into an escaping one:
> "one witness certifies a whole orbit" only ever re-delivers the orbit of a
> witness already exhibited, and class uniformity — *a witness at every member
> of an infinite class* — is untouched unless `Γ` has a dominant orbit in the
> chart. The shear's orbits are 3-dimensional inside a chart whose dimension
> grows with `|V|` (49 already at `P21`, *Step SH4*), so they cover nothing.
> Conversely, if `Γ` is **not** equivariant it may well move a failure — that
> is *Step SH4*(ii) — but then a witness at one point says nothing at another.
> **Either way there is no propagation.** The two horns are exhaustive, which
> is why this is a statement about the *shape* of the device rather than about
> `so₃`.
>
> *(b) The mechanism is the arc's own, and it relocates the gap rather than
> closing it.* "Avoid finitely many proper subvarieties over an infinite field"
> is precisely what §(K-pitch) *Step 0* already does: the criterion is a
> polynomial non-vanishing `P ≢ 0` on the seed variety, and once `P ≢ 0` is
> known, avoidance over an infinite field is **free** and the number of
> components is irrelevant. The arc's gap is not avoidance; it is
> **properness** — establishing `P ≢ 0` uniformly over the class. (ZH-1) buys
> avoidance, which the arc already has, and supplies nothing towards
> properness. This is the fourth instance of the relocation pattern
> `notes/Pencil-strategy.md` §4.6 (R1) names (C1 relocated the crux to
> `rank dV = 9`; `∀λ` to "`λ ≠ p⁺` is realizable"; §(K-out) (OC-8) to
> chart-to-frame dominance), and the first where the relocation is **backwards**
> — onto a step that was never the difficulty.

### Confidence verdict, per claim

| claim | verdict | instrument |
|---|---|---|
| **(SH-1)** the shear is `Λ²` of a translation; the form is §(K-pitch)'s | **proven** — identities in `ℚ[s]`, `ℚ[w]`, two independent constructions compared | `--iso` |
| **(SH-2)** `Q` is the shear group's defining invariant; β-plane stabilizer is 3-dim | **proven** (identity) / the stabilizer sharpness **proven-informally** (the `λ = 1` computation, in prose) | `--iso` |
| **(SH-3)** the bed, re-derived and matched to *Step F5(d)*'s `(30,5,5)` | **measured, exhibited** — asserted, not sampled | `--bed` |
| **(SH-4)** the criterion is carried exactly; bad-`S` set is all-or-nothing | **proven** for the translation subgroup in the script model, verified at 35/35 seeds with 0 exceptions; `PGL(4)`-wide by the same argument, **proven-informally** | `--inv` |
| **(SH-5)**(i) generator-wise defect identity | **proven** (identity in 18 indeterminates) | `--prod` |
| **(SH-5)**(ii) the carrier-side family = the fixed-normal chart slice | **proven-informally** (the affine-subspace/direction-space argument), the dimension **computed exactly** at `P21` | `--prod` |
| **(SH-6)** the dichotomy and the relocation reading | **proven-informally** — arguments, no driver, and the two a successor should attack | — |
| **(ZH-1) as a uniformity device** | **REFUTED**, with the exact reason | `--iso` + `--inv` |

### What would change this

- **(SH-1)/(SH-2)** would fall only to an error in the harness's Plücker
  convention, which `--iso` pins by comparing two independent constructions of
  the same matrix; a divergence between `exactcore.PL`/`repin.hodge_star` and
  the Lean `supportExtensor` convention would move the *dictionary*, not the
  mathematics.
- **(SH-4)** would fall if some ingredient of the criterion were **not** built
  from the realization — a fixed auxiliary datum not transported by the gauge
  (a distinguished point, plane, frame or decoration chosen once for the class).
  That is the *only* way a gauge subgroup can be a genericity device, and it is
  the one thing to look for if (ZH-1) is ever revisited: **exhibit the
  extraneous fixed datum, or the device is vacuous.**
- **(SH-5)**(ii) would change if a per-body motion were allowed to move the
  panel **normals** as well; that is no longer a translation field and is a
  different (and larger) object, un-analyzed here.
- **(SH-6)**(a) would be evaded only by a `Γ` with a dominant orbit in the
  chart, i.e. essentially a rational parametrization of the chart by a group —
  which is a strictly stronger thing to have than the escape.
- **(SH-6)**(b) would change if properness of the bad locus were reduced to
  avoidance somewhere; nothing in this direction does that.

### Verification

```
PYTHONHASHSEED=0 python3 notes/scripts/w4/zshear.py --iso        #   0.0 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/zshear.py --bed        #  41.7 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/zshear.py --inv        # 426.3 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/zshear.py --prod       #  46.3 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/zshear.py --validate   # 353.0 s
#   validate legs: --iso 0.0 / --bed 42.9 / --inv 303.7 / --prod 6.4
```

(Wall-clock seconds are the driver's own self-timing prints — the one
documented exception to byte-identical output, `notes/scripts/README.md`.)

`--validate` **fits a 600 s foreground budget** (measured 353 s; the bed is
built once per process and reused, which is why the sum of the individual modes
exceeds it). Every headline figure above is an `assert` inside the mode named in
the table, so the verification bar is: **the modes exit 0**. No mode prints a
rate that is not also asserted, and no mode's conclusion rests on a sample —
`--iso` and `--prod`(i) are identities in polynomial rings, and `--bed`,
`--inv`, `--prod`(ii) are equalities checked at every probed point of a
disclosed, seeded, fully-enumerated bed.

**F11 mapping** (each headline sentence to the mode that tests *that*
sentence): "the shear is a translation" → `--iso`(ii); "the pitch is its
invariant" → `--iso`(iii); "the bed is *Step F5(d)*'s" → `--bed`; **"the
failure locus is shear-invariant"** — an *invariance* claim, so tested as one:
`--iso`(iii) makes it an identity in `ℚ[s]` for the form, and `--inv` checks
the transport of every criterion ingredient as a **subspace/matrix equality**
rather than sampling a few `S`; "the product action does not preserve the form"
→ `--prod`(i), an identity with an exhibited nonzero defect; "the per-body
family is the chart slice" → `--prod`(ii), an exact rank/dimension computation
plus the 6/6 failure-moving measurement.

---

## Secondary deliverable — the OWED §2.5 filter check on (ZH-2)/(ZH-3)

Prose only, per the dispatch: **no driver, no labels, no pricing onto §8's
board.** This is a verdict on `notes/Pencil-strategy.md` §9.2's two held
candidates against **§2.5** (counting saturation), which is the check they owe.
The shelf stays off-board either way.

**What §2.5 actually forbids, stated sharply enough to apply.** On the tight
class `index(G) = 0` forces `dim R_a = 1` by the count identity, and §(K-flank)
*Step F5(d)*'s five seeds have count-predicted `dim R_a = 1` and geometric
`dim R_a = 0` **at the same graph and the same split** as the thirty escaping
seeds. So the operative form of the filter is: *any invariant that is a
function of the combinatorial data alone is constant where it must vary, and
the count is provably blind to the discriminating phenomenon.*

- **(ZH-2)** `∆ = (self-stress dim) + trdeg_k K − 3|V|`. **Verdict: SURVIVES
  §2.5 in its stratified reading, and DIES by §2.5 in its whole-chart
  reading** — and the distinction is the whole content of the check.
  `3|V|` is a count. `trdeg_k K` is a *dimension*: if `K` is the function field
  of the **whole** pencil chart of a fixed graph, then `trdeg_k K = dim(chart)`,
  and that chart is §(K-slide) *Step 1(e)*'s irreducible linear-fiber tower
  whose dimension is a function of the hub/degree data alone (3 per hub point
  plus the panel-normal freedom, 2 per single-hub interior, 1 per two-hub
  interior, 3 per hub-free body). In that reading `∆` is count-expressible and
  §2.5 bites exactly. If instead `K` is the function field of the **stratum**
  carrying the degeneracy, `trdeg` is that stratum's dimension, which
  *Step F5(d)* and §(K-out) **(OC-38)**(iii) show is **not** count-predicted —
  the count says `dim R_a = 1`, the geometry delivers 0 on a nonempty locus. So
  the filter passes only for a **stratified** potential. A caution that is not
  part of the filter but is the first thing to test if the candidate is ever
  spent: pointwise self-stress dimension is upper semicontinuous and jumps *up*
  on a smaller stratum exactly where `trdeg` drops, so the two terms of `∆` move
  in opposite directions along a stratification — which is *why* such a
  potential can be near-constant at all, and why the sign of the increment must
  be checked per reduction move rather than assumed additive.
- **(ZH-3)** the codimension-count rank lower bound (*a stratum of codimension
  `c` has generic self-stress dimension `≤ c`, hence rank `≥ m − c`*).
  **Verdict: SURVIVES §2.5 — and is CIRCULAR as a route, which is the sharper
  finding and does not need §2.5 at all.** It survives because `c` is the
  codimension of a subvariety of the realization space, a geometric dimension
  and not a count of combinatorial objects, and because it *does* separate
  seeds at a fixed graph (the five failing seeds sit on a proper closed subset,
  the thirty escaping ones do not) — with the identical caveat as (ZH-2): if
  `c` is taken to be the *count-predicted* codimension, §2.5 bites at once,
  since *Step F5(d)* is precisely a place where actual and count-predicted
  codimension differ. The circularity is the real obstacle. On the tight class
  the row count is `m = 5|E| = 6(|V|−1) = target`, so `rank ≥ m − c` reaches
  the target **only** at `c = 0`; and at `c = 0` — the open dense stratum — the
  statement reads *the pencil chart's generic self-stress dimension is 0*,
  which on the tight class **is** the phase's own target
  (`HasGenericPencilRealization`, `Motive.lean:140`). So a transferred (ZH-3)
  would not be an input to the tight case; it would *be* the tight case. Its
  content is the expected-codimension transversality of the degeneracy locus
  **relative to the pencil chart** — and that relative statement is §2.4's
  degenerate-enough-to-compute wall, i.e. the arc's open problem. At `c ≥ 1`
  the bound gives `target − 1`, which is exactly the shortfall already observed
  at *Step F5(d)* and at §(K-bare-ext) **(BE-1)**. **§9.2's "no theorem
  transfers" was right, and this is the mechanism.**

Neither verdict prices either candidate. **(ZH-2)** stays a held candidate with
its §2.5 debt now **discharged in the stratified reading only**; **(ZH-3)**
stays held, and should be re-labelled on the shelf as *circular as posed*
rather than merely *owing a filter check* — its live residue is the relative
transversality statement, which is a restatement of the kernel and not a route
into it.

---

## TERMINATION check (E1/E2/E3) — reported, never fired

**E1, E2, E3: all NO.**

- **(E1)** no g-flank. This direction never touches colourings, orientations,
  chunks or the §(K-grid) ladder; nothing here is a `D = 0` shape or a binding
  chunk, so E1 has no subject matter.
- **(E2)** not applicable and not triggered: the orientation theorem is
  untouched, and the §(K-grid) ledger is unchanged, with (a′)/(b′)/(d′) and
  (GR-15) exactly as they were. This direction's own target — is (ZH-1) alive? —
  is **settled negative**, and settling a candidate negatively with its exact
  reason leaves a named, dispatchable successor on the shelf ((ZH-4)), so no
  no-attack-left condition arises anywhere.
- **(E3)** the phase target is **not** proven. **E3 stays ARMED by GBAL and is
  neither fired nor disarmed.**
