## §(K-mech) — the mechanisms of the residual (W2)/(W4) anomalies: the load space Ω, the α-confinement calculus, and the 6v11e rescue

Sibling of §(K-pure), answering its *Step P8* and *Step P9* item 5 (the
second fan-out's direction M, `notes/pencil/fanout-archive.md` §"Direction M").
Standing notation inherited from §(K-pure): the slide-limit carrier at a
support `Σ`, witnesses (W1)–(W4), chain spans `S_P`, available bars
`R_P = S_P^{⊥_B}`, loaded stresses and loads, `T = ⟨C_ab, C_ac⟩`,
`π = plane(pt a, pt b, pt c)`, the two maximal totally isotropic 3-spaces
`α(a)` and `Λ²π̂` of §(K-pure)'s (PC-Z), `α(p) = p̂ ∧ K⁴`. One new object:

- **Ω := V_bc^{⊥_B}, the realizable-load space.** A covector
  `m ↦ B(m(b) − m(c), ω)` vanishes on the limit motion space iff it lies in
  the limit system's row space, i.e. iff `ω` is the load of a loaded stress;
  so Ω is exactly the set of realizable loads, and it is computable as a
  perp. (Under (W1) the realizing stress is unique.)

**Verdict (2026-08-06, second fan-out direction M).**

(i) **Both residual anomalies of §(K-pure) *Step P8* now have mechanisms,
and both mechanisms live in one calculus** — forced elements of Ω produced
by the α-confinement of slid chain spans (MX-2). The 6v11e `dim V_bc = 2`
drop is a forced **welded flex** with two overlapping α-routes (MX-6); the
`V_bc ∩ Λ²π̂ ≠ 0` incidence at `K222` and `K4 (1,1,3,5,4,4)` is a forced
**pole-cluster load** through `pt(c)` (MX-4/MX-5), with §(K-pure)'s chord
stress (PC3) as the special case `ω = C_bc`.

(ii) **6v11e is RESCUED — the slide device closes it after all** (MX-7).
The mechanism names its own off switches; omitting a **single interior**
(the 5-side end of chain `b–5` or `c–5`) kills both flex routes, and the
resulting nonempty-support limit systems carry full (W1)–(W4) witnesses
(3/3 sampled seeds each, `repin.star_generic` green). §(K-pure) *Step P7*'s
"the slide device does not reach this shape" is therefore **withdrawn**: its
5-support menu omitted only b/c-side interiors, and every one of those
supports keeps both routes alive — exactly as the ledger predicts. The
gap map's 6v11e entry ("chart certificate the only closure") moves: the
device closes the split.

(iii) The full prediction table — 3 single-omission rescues, 2 two-omission
rescues, 4 predicted-stuck controls — is verified 9/9 by `mech.py --wide`.
A wrong ledger would have missed on at least one row.

### (MX-1) — self-duality of the (PC-Z) incidence *(proven)*

> For `W` a maximal totally isotropic 3-space of `(Λ²K⁴, B)` (so
> `W^{⊥_B} = W`) and any subspace `V_bc ⊆ Λ²K⁴`,
>
>     dim(Ω ∩ W) = dim(V_bc ∩ W) + 3 − dim V_bc.

*Proof.* `Ω ∩ W = V_bc^⊥ ∩ W^⊥ = (V_bc + W)^⊥`, so
`dim(Ω ∩ W) = 6 − dim V_bc − 3 + dim(V_bc ∩ W)`. ∎

Consequences, with (PC-Z): under (W1)–(W3) with `dim V_bc = 3`, **the escape
fails at a decoration iff some realizable load is a line through `pt(a)` or
a line in `π`** (`Ω` meets `α(a)` or `Λ²π̂`). The chord obstruction (PC3) is
the case `ω = C_bc ∈ Λ²π̂`. And at `dim V_bc = 2` both incidences are
automatic — so a (W2) failure subsumes the (W4) question. Asserted at every
guarded seed of every driver mode.

### (MX-2) — α-confinement of slid chain spans *(proven; strengthens (PC1))*

> Every limit line of a chain of length `ℓ ≤ 4` passes **through one of the
> two hub points** — not merely meets the chord — provided the same slide
> pattern (PC1) requires for chord-obstruction, and in the following
> refined per-line form. For `P = uw`, `[u, y₁, …, y_{ℓ−1}, w]`:
> hub-incident lines are pencil lines (through the hub point, always);
> a line with a slid end passes through that end's hub point; so
>
>     S_P ⊆ α(u) + α(w)   for  ℓ ≤ 2 (any support);  ℓ = 3 with ≥ 1 end
>                          slid;  ℓ = 4 with both ends slid,
>
> and `S_P` splits into an α(u)-part and an α(w)-part of sizes
> (by `(ℓ, slide)`-case) `(1,1), (1,2), (2,1), (2,2)` etc. — read off the
> (S1)(b) dictionary exactly as in (PC1)'s proof.

*Proof.* The same case analysis as §(K-pure) *Step P1*, keeping the stronger
observation at each case: `(slid, slid) ↦` the chord (through both);
`(hub, nbr) ↦` a pencil line at the hub; `(slid, fixed) ↦ p̂t(h) ∧ x̂`
(through `pt(h)`); only `(fixed, fixed)` middle lines are unconfined, and
they occur exactly in the complementary cases. ∎

Everything below is bookkeeping on top of (MX-2); the driver measures each
containment it uses rather than trusting the rule (and asserts the rule
against the measurement).

### (MX-3) — two-path forced loads *(proven-informally)*

> For an internal hub `h` adjacent to both `b` and `c`, every element of
> `R_bh ∩ R_hc = (S_bh + S_hc)^{⊥_B}` is a realizable load (the loaded
> stress puts the same bar on both chains, equilibrium at `h` is
> automatic). Its dimension is `6 − dim(S_bh + S_hc)`, and (MX-2) forces it
> positive in enumerable patterns: for two ℓ3 chains with their h-side ends
> slid, `S_bh + S_hc ⊆ ⟨L_b⟩ + α(h) + ⟨L_c⟩` is ≤ 5-dimensional, so a load
> exists **at every decoration** — it lies in `α(h)` (a line through
> `pt(h)`) and B-annihilates `L_b`, `L_c`. For `ℓ_bh = 1` (a hub-hub edge)
> the count `dim R_bh = 5` gives a forced load against any `ℓ_hc ≤ 4`
> chain; the bar can be taken to be the **chord `C_hc` on both edges**.

At 6v11e (hubs 3, 4, 5 all joined to both `b` and `c` by ℓ3 chains) this
already forces three independent loads `ω₃, ω₄, ω₅ ∈ Ω`, each in `α(pt h)`,
measured 3-dimensional at every guarded seed — but three loads alone do not
drop `dim V_bc`. The drop is the flex (MX-6).

### (MX-4) — pole-cluster stresses *(proven-informally; `--inc` green)*

> Fix the split end `c` (the *pole*; everything mirrors for `b`) and a hub
> set `X ∋ c` with `b ∉ X`. Consider stresses built from: one **chord** bar
> per chord-obstructed chain inside `X` ((PC1)); the **α-bars**
> `α(h) ∩ R_P` on each chain from `h ∈ X` to `b` (dimension
> `δ = 3 − #(non-α(h) lines of the chain)` by (MX-2) — at the full support
> `δ = 3` at ℓ1, `2` at ℓ2 and ℓ3, `1` at ℓ4, `0` at ℓ5; the driver
> computes the space directly, support-aware); zero on chains leaving `X`
> elsewhere. Every bar at a hub `h ∈ X` passes through `pt(h)`,
> so each internal equilibrium drops from 6 conditions to 3, and with
> `U := #chords + Σ δ`:
>
>     dim(Ω ∩ α(pt c)) ≥ U − 3(|X| − 1).
>
> If the bound reaches **2**, then since `α(c) ∩ Λ²π̂ = pencil(pt c; π)` is
> 2-dimensional (`pt(c) ∈ π`), two planes inside the 3-space `α(c)` must
> meet: **`Ω ∩ Λ²π̂ ≠ 0`, and by (MX-1)+(PC-Z) the pitch vanishes at every
> decoration.** If it reaches **3**, `Ω ⊇ α(c)` forces `Ω = α(c) = V_bc`
> (both 3-dim, `α(c)` self-perp): the strong-containment branch where (W3)
> fails.

*Proof of the bound.* The constrained stress system has `U` unknowns and at
most `3(|X|−1)` independent conditions (each non-pole hub's vertex sum lies
in its own 3-dim `α(h)`); a solution's load at `c` is the sum of `c`'s bars,
all through `pt(c)`, hence in `α(c)`; a zero-load solution would be an
unloaded stress of the limit system, impossible under (W1); realizability is
by construction. ∎

### (MX-5) — the incidence anomalies, explained *(proven-informally; `--inc` green)*

Measured (`mech.py --inc`, acceptance gated on `repin.star_generic`, 2
guarded seeds per shape; the cluster bound is additionally *asserted* ≤ the
measured `dim(Ω ∩ α(pole))` at every shape/seed, and every cluster load is
asserted realizable and through the pole point):

| shape | best c-cluster bound (at X) | measured `dim(Ω∩α_c)` | measured `dim(Ω∩α_b)` | verdict |
|---|---|---|---|---|
| `K222` | **2** (X = all internal + c) | 2 | 0 | W4 FAILS |
| `K4 (1,1,3,5,4,4)` | **2** (X = {c, 2, 3}) | 2 | 0 | W4 FAILS |
| `K5 (3,3,3,3,4,...)` | **3** (X = {c, 2, 3, 4}) | 3 (`V_bc = α(pt c)`) | 1 | W3 FAILS |
| dbl-subdiv `K4` | 1 | 1 | 1 | PITCHED |
| `K4` mixed | 1 | 1 | 1 | PITCHED |
| `K4 (1,1,3,5,3,5)` | 1 (X = {c, 2}) | 1 | 0 | PITCHED |
| `K4 (1,1,3,5,5,3)` | 1 (X = {c, 3}) | 1 | 0 | PITCHED |

- **`K4 (1,1,3,5,4,4)`** (relabeled: `b` has ℓ1 hub-hub edges to hubs 2, 3;
  `c` has ℓ4 chains to both; the ℓ5 edge `2–3` is never chord-obstructed):
  `X = {c, 2, 3}` gives `U = 2 + 3 + 3 = 8`, bound `8 − 6 = 2`. The unique
  (up to scale) incidence load passes through `pt(c)`; the realizing stress
  is supported on the two 2-paths `b–2–c`, `b–3–c`, carrying the chords
  `C_{2c}`, `C_{3c}` as uniform bars; the loads span the 2-plane
  `⟨C_{2c}, C_{3c}⟩ ⊆ α(c)`, whose forced meet with `pencil(c; π)` is the
  line `π ∩ plane(pt 2, pt 3, pt c)` — through `pt(c)`, exactly as measured.
- **`K222`**: `X = {c, 2, 3, 4, 5}` gives `U = 8 chords + (2+2+2) α-bars on
  the three ℓ3 b-chains = 14`, bound `14 − 12 = 2`. Incidence load through
  `pt(c)` at every seed; stress supported on all 11 chains — chords on the
  8 internal ones, α-bars (through the far hub point, meeting `L_b`) on the
  three `b`-chains.
- **`K5 (3,3,3,3,4,4,4,4,4,4)`**: bound `12 − 9 = 3` — **the mechanism of
  the strong-containment branch** `V_bc = α(pt c)` that §(K-pure) (PC3)
  could only observe; (W3) fails exactly as its parenthetical predicts.
- **The two pitched menu-blocked `K4` controls** show the sharpness: their
  ℓ5 edge replaces one ℓ4, killing one path's chord, and the bound drops to
  1 — no incidence, pitched.
- **The b/c asymmetry and the silent α(a) branch are structural**: the
  b-side best bound is 0 at all three anomaly shapes (measured `dim(Ω∩α_b)`
  0, 0, 1); and `a` is not a hub of the limit carrier, so no cluster
  produces loads through `pt(a)` — matching `dim(Ω ∩ α(a)) = 0` ((MX-1)
  duality asserted) at every probed class seed. The α-branch of (PC-Z)
  never fires in this family.

### (MX-6) — the 6v11e welded flex, mechanised *(proven-informally; `--flex` green)*

> `dim V_bc = 3 − dim F` where `F` is the space of limit motions with
> `m(b) = m(c) = 0` (the *welded flex*; the map `ker → V_bc` has exactly
> the trivial twists and `F` in its kernel). Dually `dim Ω = 3 + dim F`.
> At 6v11e (hubs `b=0, c=1, 2, 3, 4, 5`; ℓ3 on all six b/c chains and on
> `2–3`; ℓ4 on `2–4`, `2–5`, `3–4`), `dim F ≥ 1` is forced at every
> decoration of every support that keeps the far-side ends of the six
> b/c chains slid and both ends of `3–4` slid, through **two overlapping
> α-routes**:
>
> - **Route A (localized on hubs 2, 5).** Parameters: `φ₅ = t·ξ₅` with
>   `ξ₅` spanning the forced 1-dim `S_{b5} ∩ S_{c5} ⊆ α(5)` ((MX-3)'s
>   primal twin: two 2-dim α(5)-parts meet inside the 3-dim `α(5)`), and
>   `φ₂ = s·ζ₂` with `ζ₂` spanning the 1-dim `S_{23} ∩ S_{24}`, which is
>   forced into `α(2)` (from `S_{23}` an element is in `α(2) + ⟨L₃⟩`, from
>   `S_{24}` in `α(2) + α(4)`-parts; generically the extra directions
>   miss). One condition: `φ₂ − φ₅ ∈ S_{25}`, which costs **1**, not 2,
>   because `⟨ζ₂⟩, ⟨ξ₅⟩, S_{25}` all lie in the 5-dim `α(2) + α(5)` where
>   the 4-dim `S_{25}` has codimension 1. Count `2 − 1 = 1`.
> - **Route B (spread over 2, 3, 4, 5).** Parameters: the three forced
>   meets `ξ₃, ξ₄, ξ₅` plus `φ₂` free: `3 + 6 = 9`. Conditions:
>   `3 + 2 + 2` at hub 2's chains, plus **1** — not 2 — at the edge `3–4`
>   (its constraint lives in the 5-dim `α(3) + α(4)` ⊇ the fully-slid
>   4-dim `S_{34}`). Count `9 − 8 = 1`.
>
> Both routes pass through the hub-5 meet `ξ₅`. Since the decoration
> variety is irreducible ((S1)(e), as used in §(K-pure) *Step P0*), a
> generic forcing extends to every decoration by upper semicontinuity of
> kernel dimension; hence (W2) fails identically wherever a route is live —
> which includes all four supports the 5-menu probed (their omissions are
> all b/c-side, touching no ingredient).

Measured (`mech.py --flex`, acceptance gated on `repin.star_generic`,
2 guarded seeds × 4 supports + controls): `dim F = 1`, flex localized on
hubs `{2, 5}` with `φ₅ ∈ S_{b5} ∩ S_{c5}`, `φ₂ ∈ S_{23} ∩ S_{24} ⊆ α(2)`,
all containments as stated; controls (dbl-subdiv `K4`, `K4` mixed):
`dim F = 0`. Hub 5 is the only common neighbour of `b, c` whose single
other chain closes a route — hubs 3 and 4 have their candidate routes
killed by the extra `3–4` edge condition, and the driver's stuck-support
rows confirm the asymmetry.

### (MX-7) — the widened support menu and the rescue *(verified 9/9)*

`mech.py --wide` runs the ledger's full prediction table at 6v11e:

| support (omissions from the full slide) | ledger predicts | measured (3 seeds) |
|---|---|---|
| 5-side end of chain `b–5` (1 interior) | A+B dead → rescue | **PITCHED (W1)–(W4) ×3**, `star_generic` green |
| 5-side end of chain `c–5` (1 interior) | rescue | **PITCHED ×3** |
| both of the above (2) | rescue | **PITCHED ×3** |
| 3-side of `3–4` + both interiors of `2–3` (3) | B and A dead separately → rescue | **PITCHED ×3** |
| 3-side of `3–4` + 2-side of `2–5` (2) | rescue | **PITCHED ×3** |
| 3-side of `3–4` only (1) | route A survives → stuck | W2 FAILS ×3 |
| both interiors of `2–3` (2) | route B survives → stuck | W2 FAILS ×3 |
| 2-side of `2–4`, `2–5` (2) | route B survives → stuck | W2 FAILS ×3 |
| 3-side of `b–3` (1) | route A survives → stuck | W2 FAILS ×3 |

Since (S1) consumes exactly one full (W1)–(W4) limit witness, **the slide
device closes the 6v11e split** at (e.g.) the single-omission support. The
rescue rows are existence witnesses (guard-exempt by the standing rule) and
nevertheless pass the composite guard.

### (MX-8) — the σ rider (§(K-σ) *Step σ6* / the dispatch's rider probe) *(`--sigma` green)*

The rider asked whether the two incidence configurations are σ-images of
one another (`V_bc ∩ Λ²π̂ ≠ 0` being the σ-image of `V_bc ∩ α(·) ≠ 0` at
the dual seed). Verdict: **NO — inside the probed family**, for three
verified reasons and one structural surprise:

1. **The transport itself is exact** (asserted at 2 guarded seeds × both
   shapes): starring every limit line gives a system whose motion space is
   `σ`-conjugate, so its `V′_bc = σ(V_bc)` (asserted as spans), and the
   incidence transports to `σ(V_bc) ∩ α(pole π) ≠ 0` — an **α-branch**
   incidence at `pole(plane abc)`, per §(K-σ) *Step σ1(b)*'s covariant
   dictionary. The pole point is asserted distinct from `pt(a)`, `pt(b)`,
   `pt(c)` and every hub point, so this α-space is one the carrier family
   never produces.
2. **But the starred system is not a slide-limit carrier of the dual
   placement**: a starred chord `σ(C_uw)` is the meet line of the two dual
   panels, not the dual seed's chord — asserted on every chain of length
   ≥ 2 whose ends are both hubs. **Structural exception, forced and now
   proven (the probe's assert caught it)**: on an ℓ1 (hub-hub) chain the
   hinge lies in *both* panels, so `C_uw = Π(u) ∩ Π(w)` and its polar IS
   the dual chord — the one bar type the polarity maps back into the
   dual-seed carrier family.
3. **Both measured incidences are the same c-side β-branch type** (loads
   through `pt(c)` in `π`, (MX-5)), so `K222` and `K4 (1,1,3,5,4,4)` are
   parallel instances of one mechanism, not a σ-dual pair; each one's
   σ-image lives at a meet-line carrier outside the probed family.

### (MX-9) — the |V°| ≤ 6 strata sweep *(measured; `--sweep` green)*

One sampled class shape per candidate hub graph (23 graphs, simple,
connected, min degree ≥ 3; length assignments drawn from
`random.Random(20260806)` with `e₀` at ℓ3, certified by
`kslidecomb.shape_ok`; full support; one `star_generic`-guarded chart seed
each; two shapes skipped at the |V| ≤ 41 cost cap — the |E°| ∈ {14, 15}
Maxwell-overbraced stratum, where §(K-pure) *Step P4*'s chord census
already speaks). Predictor per shape: CHORD (a chord stress through `e₀`,
(PC2)/(PC3)) ∨ CLUSTER ≥ 2 (MX-4) ∨ FLEX ≥ 1 (MX-6). Result, 21/21:

- **20 shapes PITCHED, all with every mechanism silent** (chord absent,
  cluster bounds ≤ 1, flex 0);
- **1 new (W4) failure found in the wild** — `|V°| = 6, |E°| = 11`, lens
  `(3,4,3,4,4,1,4,3,3,4,3)` — with cluster bound **2** and no chord, no
  flex: a fresh instance of the (MX-4)/(MX-5) mechanism, predicted by the
  calculus that was built from `K222`/`K4`, on a shape it had never seen;
- **0 unexplained failures, 0 mechanism-fired-yet-pitched rows** (the
  latter asserted — a violation would abort the driver).

So on the sampled strata the three-mechanism predictor is *measured
complete and sound* at the full support. This is a measurement, not a
theorem: sufficiency of "all three silent" for (W1)–(W4) remains open
(and is exactly the shape of the honest next question §(K-pure) *Step P9*
item 5 asked).

### What this buys (K-chord) and the class program

The dispatch named the target shape: *"a structural characterization of when
the incidence happens ... feeds (K-chord)"*. The calculus delivers exactly
that, in load form:

- **Exact reformulation ((MX-1) + (PC-Z)):** under (W1)–(W3), the escape
  fails at a decoration **iff** some realizable load lies in
  `Λ²π̂ ∪ α(a)`; and (W2) fails iff `dim Ω ≥ 4`.
- **The forced part of Ω is combinatorially computable per (shape, Σ):**
  chord stresses (§(K-pure) (PC2)/(PC3), governed by `R_3`), two-path loads
  (MX-3), pole-cluster loads (MX-4), and welded-flex routes (MX-6). So the
  slide device at support `Σ` now carries **three named necessary
  conditions**, all decoration-free:
  1. `e₀ ∉ cl_{R_3}(E_chord(Σ))` — (K-chord), unchanged;
  2. both pole-cluster bounds ≤ 1 — else (MX-5) kills (W4) or (W3);
  3. no forced flex route — else (MX-6) kills (W2).
  Whether these three are jointly *sufficient* on the |V°| ≤ 6 strata is
  what `--sweep` measures (a measured completeness, not a theorem).
- **6v11e closes**, so §(K-pure) *Step P9* item 5's "6v11e first" is
  discharged with a *rescue*, not a refutation: no class shape is currently
  known where the device fails at every support — the class-level
  refutation possibility named in the (K-chord) row's "what would close it"
  cell remains unexhibited, and the covered sub-class grows by 6v11e.
- The pole-cluster bound also gives the arc's first mechanism for the
  **strong-containment branch** of §(K-pure) (PC3) (`V_bc = α(pt c)` at the
  all-{3,4} `K5`), and explains the b/c- and α/β-branch asymmetries as
  structural, not accidental.

### Verification

`notes/scripts/w4/mech.py` (untracked in this dispatch; imports `pure` /
`kslide` / `repin` / `kslidecomb` / `widened` and — via `importlib` —
`lambda.span_meet`; exact ℚ; `RNG_SEED = 20260806` is the file's only
randomness literal, used by `--sweep`'s length sampler; every limit system
is built by `pure.limit_data` from an honest `repin.seed_probe` chart seed;
every sampled object carries a rank/dimension assert; batteries quoted as
rates gate acceptance on the composite guard `repin.star_generic`, and the
(W1)–(W4) rescue rows are existence witnesses reported with their guard
status). Reproduce, from the repo root:

| invocation | ~time | what it asserts |
|---|---|---|
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/mech.py --flex` | ~4 min | (MX-6) at 6v11e: dim V_bc = 2, dim F = 1, the flex's hub support, every ledger containment (the three 1-dim α-meets, `S_34 ⊆ α(3)+α(4)`, `S_25 ⊆ α(2)+α(5)`, `φ₂ ∈ S_23∩S_24 ⊆ α(2)`), at all four probed supports × 2 guarded seeds; controls dim F = 0; (MX-1) asserted per seed |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/mech.py --wide` | ~5 min | (MX-7): the 9-row prediction table — 5 rescue rows each with a full (W1)–(W4) witness (asserted present), 4 stuck controls (asserted `W2 FAILS` at every seed) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/mech.py --inc` | ~4 min | (MX-3)/(MX-4)/(MX-5): the cluster bound vs measured `dim(Ω∩α(pole))` at 3 anomaly shapes + 4 controls (per-X assert that the bound never exceeds the measured value; per-load asserts realizable + through the pole); the forced incidence and its `pencil(c;π)` meet; (MX-1) at every seed |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/mech.py --sigma` | ~3 min | (MX-8): `V′_bc = σ(V_bc)` as spans; the branch swap to `α(pole π)`; pole ≠ any carrier point; the ℓ1 (forced equality) vs ℓ≥2 (forced difference) starred-chord dichotomy |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/mech.py --sweep` | ~10 min | the |V°| ≤ 6 strata predictor pass (one guarded seed per sampled class shape; asserts no mechanism-fired-yet-pitched row) |

### Confidence verdict

- **(MX-1), (MX-2): proven** (two-line linear algebra; the (S1)(b) case
  analysis, the same casework as §(K-pure) (PC1) with a stronger per-line
  conclusion).
- **(MX-3), (MX-4), (MX-6): proven-informally**, each ingredient asserted
  by a driver mode at every guarded seed; the genericity step in (MX-6)
  rests on the decoration variety's irreducibility ((S1)(e)) exactly as
  §(K-pure) *Step P0* already uses it.
- **(MX-5): proven-informally** (`--inc` green: bounds 2, 2, 3 met with
  equality at the three anomaly shapes, ≤ 1 at all four controls; every
  cluster load asserted realizable and through the pole).
- **(MX-7), the 6v11e rescue: proven-informally** — exact (W1)–(W4)
  witnesses at five distinct reduced supports, 3/3 sampled seeds each; the
  claim consumed is (S1)'s one-witness transfer, unchanged; the 9-row
  prediction table (5 rescues, 4 stuck controls) verified with per-row
  asserts.
- **(MX-8): the σ-rider verdict is settled as NO within the probed
  family**, with the transport identity, the pole-point disjointness, and
  the ℓ1/ℓ≥2 starred-chord dichotomy asserted (the ℓ1 equality being a
  small proven fact: a hub-hub hinge is its panels' meet line, so σ maps
  it to the dual chord).
- **(MX-9): measured** (a 21-shape sampled census, not a theorem).
- **Class uniformity: untouched.** These are mechanisms and per-shape
  closures; no uniform gap moves. What changes is the *shape* of the
  residue: §(K-pure) *Step P8*'s "two measured anomalies with no
  mechanism" is now empty, and the slide device's failure modes on the
  probed strata are exactly three named, decoration-free conditions.

**What would change this.** *(For (MX-6))* a decoration where the asserted
containments fail — they are open conditions verified per guarded seed; a
failure would break the driver's asserts, not the semicontinuity step.
*(For (MX-4))* an unloaded stress at a (W1) seed — excluded by (W1)
itself. *(For the rescue)* the witnesses are exact; only an error in
`pure.limit_data`'s construction (shared with the whole §(K-pure) arc)
could void them. *(For (MX-5))* a control with cluster bound ≥ 2 or an
incidence shape with every bound ≤ 1 — none exists in the probed pool.
*(For (MX-9))* it is one guarded seed per shape and one sampled length
assignment per hub graph at the full support only; a wider census could
surface a fourth mechanism — that, not a refutation of (MX-1)–(MX-6),
is the live risk, and finding one would be a finding, not a defect.

---

### Steps O42–O46 (2026-08-26, single dispatch, direction OGEOM) — the geometric route to a disproof of `hK`: **NO HIT, and the route is now confined to a named, finite, unsearched frontier.** `H = G − v − a` is an **induced** subgraph of `G`, so the restriction of `G`'s pencil chart to `H`'s own chart is **dominant** ((OC-46)) and `σ` depends on `H` alone; every topological path of length `≥ 6` has full chain span and is **dead** ((OC-47)), so `σ` is the corank of `H`'s **live core**, whose branch lengths are all `≤ 5` and whose size is bounded by a budget derived from (Λ4)(iii); the live cores are therefore **finite per cell** and **91 260** of them — every one with `n(F°) ∈ {2,3}` at any `|E(F°)|`, every one with `n(F°) = 4` at `|E(F°)| ≤ 8`, every one with `n(F°) = 5` at `|E(F°)| = 8` — carry an exact-ℚ **corank-0 witness** ((OC-48)), with **zero** candidates. Consequently `{σ = 0} ≠ ∅` is a **theorem, not a certificate**, at **275 342** class (shape, split) pairs over **63 013** shapes — including **all 3368** of (OC-39)'s sampled pairs, which become consequences of an argument ((OC-49)). **The `slack = 0` mechanism — the only topology at which ONE geometric unit suffices — is dead class-uniformly, by an argument.** §8.5's row does **not** close: the unsearched cells are `n(F°) = 4` at `|E°| ≥ 9`, `n(F°) = 5` at `|E°| ≥ 9`, and every `n(F°) ≥ 6`.

> **Read this first.** This direction was dispatched as the arc's first
> disproof-aimed direction since SIGZ. **It did not hit.** It is *not* a
> refutation of anything and it does *not* fire the TERMINATION test. What it
> delivers is the dispatch's **outcome 2, restricted**: a class-uniform
> *argument* (not a sample) that the geometric half is free, valid on an
> explicitly named finite frontier, plus the reduction that makes the
> remaining frontier finite and searchable. Every cap below is stated beside
> the figure it caps; the headline negative is an **emptiness** claim and is
> written "not found under cap C" everywhere, never "does not exist".

#### Standing notation (on top of *Steps O31–O36*)

`H := G − v − a` at a class split; `σ := corank R(H)` ((OC-23)). `G°` is the
hub multigraph (topological reduction of `G` at its degree-`≥ 3` bodies),
`|V°|`, `|E°|` its counts, `c = |E°| − |V°| + 1` its cycle rank, `ℓ_e` the
branch lengths. `F°` is the topological reduction of a support `F` (SIGZ's
`sigz.topo_reduce`, **not** `branch_decomposition`). "Class shape" is tight,
`def(G) = 0`, `hnoRigid`, **`hcard`**; `hcard` is read at branch granularity
as *"every hub has at most two hub neighbours"*
(`ncard_closedHubNbhd_le_three_of_isNondegPencilRealization`,
`Molecule/Pencil/Motive.lean:409`), which is exactly what
`widened.place_pencil_general` enforces when it refuses a hub with three
independent hub neighbours. **Modelling note, stated because it is a choice:**
`hK`'s `hcard` is a hypothesis at `G′`; it is imposed here at `G`. A shape
violating it has no nondegenerate pencil realization at all, so `hK` is
vacuous there and it cannot be a counterexample — excluding it is safe in the
direction this pass needs.

---

#### Step O42 — (OC-45): the class-shape branch bounds, and (OC-39)'s "exhaustive" re-checked adversarially

> **(OC-45)** *(proven; the class input is (Λ4)(iii), cited)* Let `G` be a
> class shape. Then
>
> **(i)** `G°` has **no bridge**;
> **(ii)** every branch has length `ℓ_e ≤ 5`;
> **(iii)** `|E°| ≤ 6(|V°| − 1)`, and the number `k` of length-1 branches
> (hub–hub edges) satisfies `4k ≤ 6|V°| − 6 − |E°|`.

*Proof.* Tightness is `Σ ℓ = 6c(G°)`. (Λ4)(iii) says every **proper** branch
subset `F` with `c(F) ≥ 1` has `Σ_F ℓ ≥ 6c(F) + 1`. Take `F = G − e` for a
branch `e`: every hub has `G°`-degree `≥ 3`, so `F` still has min degree `≥ 2`
and is a legal branch subset. If `e` is a bridge then `c(F) = c(G°)` and
`6c − ℓ_e ≥ 6c + 1` is impossible, proving (i). Otherwise
`c(F) = c(G°) − 1` and `6c − ℓ_e ≥ 6(c − 1) + 1`, i.e. `ℓ_e ≤ 5`, proving
(ii). Summing `ℓ ≤ 5` over `E°` gives `6(|E°| − |V°| + 1) ≤ 5|E°|`, and
summing with `k` branches at their minimum 1 gives `6c ≤ k + 5(|E°| − k)`,
which is (iii). ∎

**Why this is worth a label: it is the adversarial check on (OC-39).**
`sigz.k4_stratum` enumerates the `G° = K4` stratum over lengths in
`{1..5}^6`, and (OC-39) calls the result **exhaustive**. (ii) says that range
is a *theorem*, not a cap. Re-enumerated here at `{1..12}^6`: **877 = 877**,
the same shapes. **(OC-39)'s exhaustiveness claim survives.**

*Exact, enumerated, no cap:* `ogeom.py --bound`. Lengths `1..5`: **877**
class shapes with a length-3 branch (the split needs one —
`widened.orient`); lengths `1..12`: **877**, equal. A further **286** `K4`
class shapes have no length-3 branch at all and therefore carry **no**
eligible split. Over the 877: max branch length **5** (bound 5); max number
of length-1 branches **2** (bound `(6·4 − 6 − 6)/4 = 3`), attained at
`K4(1,1,3,5,3,5)`.

---

#### Step O43 — (OC-46): restriction-dominance — the ambient shape drops out

> **(OC-46)** *(proven-informally; the proof is a construction, and the
> construction is what the driver runs)* Let `G` be a class shape (in
> particular `hcard`), and let `F ⊆ G` be a min-degree-`≥ 2` subgraph that is
> an **induced** subgraph of `G`. Then the restriction map
>
> `{pencil chart of G} ⟶ {pencil chart of F}`
>
> is **dominant**; more precisely, every pencil-chart point of `F` in general
> position extends to a pencil placement of `G`, and the extension is a legal
> chart point for a generic choice of the extension's own free parameters.
> Consequently
>
> **`corank R(F)` at the generic `G`-chart point = `corank R(F)` at the
> generic `F`-chart point** — a quantity depending on **`F` alone**.
>
> **`H = G − v − a` is a vertex deletion, hence always induced**, so this
> applies to `H` itself and `σ` is a function of `H` and nothing else.

*Proof.* Write `Π(h)` for the panel (2-plane of the pencil) at a hub `h`; the
model is `widened.place_pencil_general`'s: a body of `G`-degree `≥ 3` has its
closed star coplanar, a body of degree `≤ 2` is unconstrained, and the hinge
extensor of `uw` is `pt(u) ∧ pt(w)`. Fix a general-position chart point of
`F`'s own chart.

*(a)* Every `G`-hub `h ∈ V(F)` gets its panel **from `F` alone**: `Π(h)` is
the plane through `pt(h)` annihilated by all `pt(u) − pt(h)`, `u ∼_F h`. That
nullspace is exactly 1-dimensional — an `F`-degree-2 vertex supplies two
independent directions, and an `F`-degree-`≥ 3` vertex is an `F`-node, whose
star the `F`-chart point already made coplanar. Nothing outside `F` is
consulted, so nothing outside `F` can obstruct it.

*(b)* Every hub `k ∉ V(F)` is placed in the intersection of the panels of its
hub neighbours **that lie in `V(F)`**. By `hcard` there are at most two of
them, so that intersection is at least a line, hence nonempty.

*(c)* Its normal is drawn from the nullspace of `{pt(u) − pt(k)}` over **all**
hub neighbours `u` of `k` — again `≥ 1`-dimensional by `hcard`. This is what
makes the hub–hub condition symmetric: `pt(k) ∈ Π(h)` was arranged at (b),
and `pt(h) ∈ Π(k)` is arranged here.

*(d)* Every non-hub `z ∉ V(F)` has degree 2, hence at most two hub
neighbours, whose panels are now all fixed; place it in the intersection.

The pencil condition then holds at every hub of `G` by construction, and the
remaining requirements (distinct endpoints, nonzero normals, the four
conjuncts of `IsNondegPencilRealization`) are open conditions on the free
parameters introduced at (b)–(d). ∎

**Where the proof can fail, named exactly.** A **chord** — a `G`-edge joining
two `F`-vertices that is not an `F`-edge. Both its endpoints then have
`G`-degree `>` `F`-degree `≥ 2`, hence are hubs whose panels step (a) has
*already pinned from `F`*, so `pt` of each must lie in the other's pinned
panel: an equation on the `F`-chart point rather than something the extension
can solve. That is precisely the `is_induced` hypothesis, and it is **not** a
restriction for the object this pass needs, since `H` is a vertex deletion.

*Exact, per instance:* `ogeom.py --dom`, over 64 class shapes (the `K4`
stratum **capped at 40**, plus the first **24** off-`K4` shapes; caps
disclosed), the first **60** induced supports per shape. **1482** induced
proper supports: **1482** extensions constructed, each asserting the pencil
condition at *every* hub of `G` and distinct endpoints on every edge; **1430**
of those extensions also pass the composite gate `repin.star_generic` on `G`
at the first draw. **222** `F = H` pairs: `is_induced` asserted at all 222,
**222** extensions constructed. **0** extension failures. **99** non-induced
(chord) supports were **counted, not dropped**; (OC-46) does not apply to
them, and they are the named residue of this step.

---

#### Step O44 — (OC-47): the live-core reduction, and the death of the `slack = 0` mechanism

> **(OC-47)** *(proven-informally; Lemma A is an exact-ℚ determinant, computed
> in the driver, not quoted)*
>
> **Lemma A.** Six path extensors of seven points in general position in `K³`
> are linearly independent. Hence a topological path with `ℓ_Q ≥ 6` has
> `dim S_Q = 6` at the generic point of `F`'s own chart, so `S_Q^⊥ = 0` and
> its flow variable `ψ_Q` is forced to **0** by (OC-35): the path is **DEAD**.
>
> **The reduction.** Delete every dead path, take the 2-core, re-reduce
> topologically, iterate. The fixed point is the **live core**. It is empty,
> or it has min node degree `≥ 3` and **every topological path of length
> `≤ 5`**. `corank R(F)` at the generic chart point equals the corank of the
> live core.
>
> **(i) Cycles and bouquets are class-uniformly free.** A class shape has
> girth `≥ 7` ((Λ4)'s first consequence), so every cycle has `ℓ ≥ 7 ≥ 6` and
> is dead; a bouquet's corank is `Σ_loops (6 − dim S_loop) = 0` by (OC-36).
> **So the `slack = 0` mechanism — by (OC-37)(ii) the *only* topology at which
> a SINGLE geometric unit suffices — never fires at any class shape.** No
> enumeration; an argument.
>
> **(ii) The core budget.** A live core is a proper cyclic branch subset, so
> (Λ4)(iii) gives `Σ ℓ_Q ≥ 6c + 1`; with `ℓ_Q ≤ 5` and `d_Q := 5 − ℓ_Q`,
>
> `Σ_Q d_Q ≤ 6 n(F°) − |E(F°)| − 7` ,
>
> and `slack(F) = (6n(F°) − |E(F°)| − 6) − Σ d_Q`. This is what makes the
> (OC-48) search finite: at fixed `(n, |E°|)` the length vectors are the
> lattice points of a simplex of size `6n − |E°| − 7`.

*Proof of Lemma A and of the reduction.* Lemma A is verified by one exact-ℚ
`6 × 6` determinant at `(0,0,0), (1,0,0), (0,1,0), (0,0,1), (1,1,3), (2,5,1),
(7,1,2)`. A topological path has **no interior node**, so its interior
vertices are unconstrained on `F`'s chart, and only the two vertices adjacent
to the window's node ends lie in a node panel. There are exactly four ways a
length-6 window can meet a node panel, and each is verified by its own
exact-ℚ witness **inside the pattern** (a witness in a *specialisation* is
what is needed, since the pattern is a subvariety of the free configuration):
one constrained end; two nodes inside the window; both ends nodes with
distinct panels; and a **loop of length 7**, where `w₁` and `w₆` lie in the
node's *single* panel — the one case the other three miss, and girth `≥ 7`
forbids the loop of length 6 that would be worse. Deletion of a dead path is
exact rather than approximate: `ψ_Q = 0` removes that term from Kirchhoff's
law at both of its endpoints, which is the flow system of `F` minus that path;
a node then dropping to degree 2 merges two paths (`ψ` equal along the merge),
degree 1 forces `ψ = 0`, degree 0 drops. A dead path has `ℓ ≥ 6`, hence at
least five interior vertices, so **deleting it can never create a chord** and
the live core is induced in `F`. ∎

*Exact:* `ogeom.py --core`. Lemma A `dim S = 6`; patterns 1–4 all `dim S = 6`.
Cycles on their own charts (free position, a cycle having no node), min corank
over 6 gated seeds, `C₃…C₁₄`: `3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0` — exactly
`6 − min(ℓ, 6)` at all twelve.

**Consistency with (OC-38), the arc's only exhibited σ-jump — and it is a
cross-check, not a re-run.** `P21`'s recorded theta support has topological
path lengths `(3, 3, 6)` and `slack = 0` at `n = 2`. Read through this pass:
the length-6 path is dead at the generic point, the two length-3 paths then
reduce to a `C₆`, which is dead too, so **the live core is EMPTY and the
generic corank is 0**. Measured: `theta(3,3,6)` has an empty live core and
min corank **0** over 8 gated exact-ℚ draws of its own chart — which is
exactly (OC-38)(iv)'s **360/360** gate-accepted seeds. The recorded `σ = 1`
is therefore a **non-generic** point, precisely (OC-38)(iii)'s
`localtest.plane_basis` coincidence locus, where that path's span drops
`6 → 5`. And `theta(3,3,6)` is not a class-shape live core at all: its
`Σ d = 3` exceeds the core budget `6·2 − 3 − 7 = 2` — which is (Λ4)(iii)
refusing `f(V(F)) = 0`, i.e. **(OC-38)(ii)'s "one unit short", re-derived as a
budget overflow**.

---

#### Step O45 — (OC-48): the core search — 91 260 live cores, every one free, **NO HIT**

> **(OC-48)** *(a finite exhaustive search per cell; each core's verdict is a
> per-core **proof**, not a rate)*
>
> **(i) The boundary, first.** `{corank R(F) = 0}` is Zariski-open, so **one**
> gated exact-ℚ chart point with corank 0 is a *complete* certificate that the
> core is free; a core with corank `> 0` at every draw is **"not found free
> under the seed cap"** and is a **candidate** `hK` counterexample owing the
> (OC-38) coincidence check. A finite sample can only ever settle a core in
> the *free* direction.
>
> **(ii) The search.** Live cores are enumerated with **no cap inside a
> cell**, iso-reduced under `Aut(E°)` and under the interchange of parallel
> branches, and each representative's own pencil chart is drawn at exact ℚ
> under `repin.star_generic`. Cells run:
>
> | cell | live-core classes | free | candidates |
> |---|---|---|---|
> | `n(F°) = 2`, every `\|E°\|` | 7 | 7 | 0 |
> | `n(F°) = 3`, every `\|E°\|` | 393 | 393 | 0 |
> | `n(F°) = 4`, `\|E°\| = 6..8` | 20 686 | 20 686 | 0 |
> | `n(F°) = 5`, `\|E°\| = 8` | 70 174 | 70 174 | 0 |
> | **total** | **91 260** | **91 260** | **0** |
>
> **(iii) The verdict.** **NO HIT.** No live core in any searched cell is
> forced to carry a stress. Combined with (OC-47)(i), the geometric half of
> (a₂) is **free at every support whose live core lies in a searched cell**,
> class-uniformly in the ambient shape.
>
> **(iv) The cells NOT searched, named:** `n(F°) = 4` at `|E°| ≥ 9`;
> `n(F°) = 5` at `|E°| ≥ 9`; every `n(F°) ≥ 6`. `n(F°) = 4` at `|E°| ≥ 9`
> alone is 123 079 further classes and `n(F°) = 5` at `|E°| = 9` is 681 140;
> both are finite and enumerable — the frontier is a **compute** frontier, not
> an ideas frontier, at `n(F°) ≤ 5`, and an ideas frontier above it (the core
> budget bounds `|E°|` but not `n(F°)`).

**Two self-checks the exhaustiveness rests on, both run.** *(1)* The
vertex-set pruning of `binding_subsets` — which is what makes the
(Λ4)(iii) filter cheap — against **brute force over all `2^m` subsets**, on
every topology with `n(F°) ≤ 3` and every `n(F°) = 4` topology with
`|E°| ≤ 8`: **60 topologies, 21 086 accepted length vectors, identical**.
*(2)* The (OC-35) flow corank against the direct `5|E| × 6|V|`
rigidity-matrix corank at **32** (core, seed) instances: **0 mismatches**.

*Exact:* `ogeom.py --hunt` (the first three cells, 21 086 classes, 357 s) and
`ogeom.py --huntn 5 8 8 {0,1,2} 3` (the fourth, 23 392 + 23 391 + 23 391 =
70 174 classes, 318 s per slice). Seeds `random.Random(20260826 + 977·s +
13·Σℓ)`, seed cap **8** gated draws per core.

---

#### Step O46 — (OC-49): what that settles in the ambient — the `H`-live-core census

> **(OC-49)** *(a census; the per-pair conclusions are theorems given
> (OC-46)–(OC-48) and §(K-chart) (CH-1)(a))* For a class (shape, split) pair,
> the chain is:
>
> 1. (OC-48) supplies a corank-0 exact-ℚ point of the **core's** chart;
> 2. (OC-46) extends it to a **legal** `G`-chart point (all four conjuncts of
>    `IsNondegPencilRealization`);
> 3. (OC-47) makes `corank R(H)` there equal to the core's corank, i.e. **0**;
> 4. `{σ = 0}` is open and the `G`-chart is irreducible ((CH-1)(a)), so
>    `σ = 0` at the **generic** chart point, and by (OC-24)(i) input (a₂)
>    holds at that pair.
>
> Note step 4 uses irreducibility of the **`G`**-chart, which is landed; no
> irreducibility of a core's chart is needed anywhere.
>
> **Coverage measured:**
>
> | pool | shapes | pairs | settled by the theorem |
> |---|---|---|---|
> | the five **named** class habitats | 5 | 44 | **44 / 44** |
> | `G° = K4` (**exhaustive**, no cap) | 877 | 3 324 | **3 324 / 3 324** |
> | `G° ≠ K4`, `\|V°\| ≤ 5`, `\|E°\| ≤ 9` (exhaustive **inside that cap**, iso-reduced) | 62 131 | 271 974 | **271 974 / 271 974** |
>
> **The first two lines are exactly (OC-39)'s pool, and they upgrade it.**
> (OC-39) sampled **3368** (shape, split) pairs over 882 shapes = 877 `K4`
> shapes **plus** the five named habitats; here `3324 + 44 = 3368`, the same
> pairs. Every `K4`-stratum pair's `H`-live-core is either **empty** (3 204)
> or a **theta** `(n, |E°|) = (2, 3)` (120); the named habitats give 42 empty
> and 2 at `(4, 6)` — **all in searched cells**. So **all 3368 of (OC-39)'s
> per-pair certificates are now consequences of an argument**: at every
> `G° = K4` class shape, every named habitat and every eligible split,
> `{σ = 0} ≠ ∅`, with no per-shape sampling at all.
>
> **Off `K4` the core distribution is:** `(0,0)`: 47 972; `(2,3)`: 32 302;
> `(2,4)`: 1 962; `(2,5)`: 102; `(3,5)`: 42 874; `(3,6)`: 5 478; `(3,7)`: 462;
> `(3,8)`: 22; `(4,6)`: 31 048; `(4,7)`: 41 520; `(4,8)`: 10 330; `(5,8)`:
> 57 902 — **every cell searched**, which is why the coverage is 100 % inside
> the census's own cap and why the `(5,8)` cell was worth its three
> invocations.

**Two self-checks, and one cross-check.** The enumeration uses a **counting**
class predicate (`Σ ℓ = 6c`; `Σ_S ℓ ≥ 6c(S) + 1` on every proper cyclic
branch subset; `hcard`) rather than the oracle predicate
(`nogood_subdiv.deficiency` + `kslide.no_rigid_branch_union`), because the
oracle costs a matroid rank per subset. The two are asserted equal on **all
1163** `K4`-stratum length vectors (877 of them with a length-3 branch) and at
**101/101** spot-checked off-`K4` shapes (cell cap 3, `|E°| ≤ 8` — the
cross-check itself is capped, because the oracle is the expensive side).
Independently, **250** off-`K4` pairs (deterministic stride, **sample cap 250,
the cap is real**) were given a *direct* exact-ℚ **full-row-rank** certificate
for `R(H)`: **250/250**, 0 unresolved.

**And the chain was run end to end, 222 times.** `ogeom.py --dom`'s last leg
does exactly steps 1–3 above per pair: draw a gated corank-0 point of `H`'s
live core, extend it by (OC-46), assert the extension passes
`repin.star_generic` **and** all four conjuncts of `IsNondegPencilRealization`
(`flanks.nondeg_conjuncts`), and assert `corank R(H) = 0` there by the direct
rigidity matrix. **222 pairs, 222 certified** (170 of them with an empty live
core), **0 failures**. This is the pass's own guard against the reduction
being wrong in the free direction: a "dead" path that was in fact live would
show up as a nonzero `corank R(H)` at a corank-0 core point, and did not.

---

#### What this does **not** settle (the honest residue)

1. **Class uniformity does not follow.** The searched cells are finite; class
   shapes are not. `n(F°) = 4` at `|E°| ≥ 9`, `n(F°) = 5` at `|E°| ≥ 9`, and
   all `n(F°) ≥ 6` are **unsearched**. §8.5's *"the geometric route to a
   disproof"* row **stays open**, narrowed.
2. **A uniform proof still needs a new idea above `n(F°) ≤ 5`.** The core
   budget bounds `|E(F°)| ≤ 6n(F°) − 7` but does **not** bound `n(F°)`. What
   is now precisely posed, and was not before, is a *single* statement:
   *at every live core, the Kirchhoff map `⊕_Q S_Q^⊥ → (K⁶)^{nodes}` is
   injective at the generic chart point*. (OC-36) makes that equivalent to
   `corank = 0`, and `slack ≥ 1` makes the map's source strictly smaller than
   `6(n − 1)`, so it is a *general-position* statement about the branch perps
   at the nodes — not a counting statement, and not shape-indexed.
3. **Non-induced supports.** 99 chord-carrying supports were counted and are
   outside (OC-46). They do **not** affect `σ`, since `H` is always induced;
   they only mean the per-support corollary is stated for induced supports.
4. **(OC-46) and (OC-47) are proven-informally**, machine-asserted at every
   instance the driver ran, not formalized. No `.lean` (standing hold).

#### What would change this

- A live core with corank `> 0` at every gated draw in any cell — that is a
  **candidate** `hK` counterexample, and by (OC-46) it would be one at *any*
  class shape containing it as an induced branch subset. None was found.
- A counterexample to (OC-46) — a class shape and an induced support whose
  `F`-chart point does **not** extend. 1704 extensions were constructed
  without a failure, but the proof's genericity clauses are prose.
- An error in Lemma A's pattern enumeration — i.e. a fifth way a length-6
  window can meet a node panel. The four are argued from *"a topological path
  has no interior node"* plus girth `≥ 7`.

#### Named successors (dispatchable, in decreasing value)

1. **The `n(F°) = 4, |E°| ≥ 9` and `n(F°) = 5, |E°| ≥ 9` cells** — 804 219
   further live-core classes at the two cells' own counts, pure compute at
   ~15 ms each (`--huntn` already takes the cell range and a slice index).
   Finishing them makes the coverage statement *"every class shape with
   `|V°| ≤ 5`"* unconditional and extends it to `|E°| ≤ 10`.
2. **The injectivity statement of residue 2**, attacked directly — the first
   time the geometric half has been posed as one shape-free statement.
3. **The chord residue** — (OC-46) for non-induced supports, which needs the
   two pinned panels' compatibility equation analysed rather than avoided.

---

### Verification (Steps O42–O46)

`notes/scripts/w4/ogeom.py` (new, untracked at draft time; exact ℚ,
`fractions.Fraction`, no floating point; stdlib only; a `w4/` leaf **beside**
`sigz.py`, importing downward only and reimplementing nothing):
`exactcore`'s `rank` / `nullspace` / `wedge2` / `hat` / `neighbors` / `dot`;
`kbare_common.verts_of`; `pencil_escape`'s `build_rigidity` / `rvec3` /
`rquat`; `nogood_subdiv`'s `deficiency` / `branch_decomposition`;
`dominance.branch_pmap`; `widened.place_pencil_general`;
`repin.star_generic`; `flanks.nondeg_conjuncts`; `pitch.paths_graph`;
`kslide.no_rigid_branch_union`; `outer`'s `split_data` / `eligible_splits`;
`sigz`'s `topo_reduce` / `flow_system` / `ekey` / `sub_supports`.

**Sideways imports, recorded per §2 rule 2 (no move made).** `ogeom` sits
*beside* the `w4/` sibling leaves and imports from four of them —
`sigz` (`topo_reduce`, `flow_system`, `ekey`, `sub_supports`), `flanks`
(`nondeg_conjuncts`), `outer` (`split_data`, `eligible_splits`) and
`dominance` (`branch_pmap`). Each is a catalogued §1 primitive, none is a
private helper, and every one is already in some sibling's import closure; the
alternative is re-implementing `topo_reduce`, whose whole point ((OC-35)'s
*Divergences* row) is that it is **not** `branch_decomposition`. Recorded for
the coordinator to adjudicate, not acted on here.

**The verification bar, read off the shipped driver — THREE independent
double-implementations, each machine-asserted, not three re-runs of one
model.** *(1)* `corank R(F)` is computed by the **direct `5|E| × 6|V|`
rigidity matrix** (`pencil_escape.build_rigidity` + `exactcore.rank`) **and**
by the **(OC-35) branch-flow system** (`sigz.flow_system`), asserted equal at
32 (core, seed) instances here on top of SIGZ's 400. *(2)* The class predicate
is computed by the **oracle** (`nogood_subdiv.deficiency` +
`kslide.no_rigid_branch_union`) **and** by the **counting** form
(`class_ok_counting`), asserted equal at 1163 `K4` length vectors + 101
off-`K4` shapes. *(3)* The (Λ4)(iii) filter is computed by the **vertex-set
pruning** **and** by **brute force over all `2^m` subsets**, asserted equal at
60 topologies / 21 086 accepted vectors. Nothing in this draft is quoted from
a scratchpad probe; every figure in the table below is a line of the driver's
own output.

**No new local primitive shadows an existing name.** `ogeom.live_core` and
`ogeom.two_core` are new; `ogeom.class_ok_counting` is a *counting* restatement
of `kslidecomb.shape_ok`'s clauses and is asserted equal to the oracle form on
1163 + 101 shapes rather than assumed — a `Divergences` candidate only if a
successor wants to merge them, which it should not (the oracle is the
authority; the counting form is the enumerator).

| mode | ~time | asserts |
|---|---|---|
| `--bound` | 5 s | **(OC-45):** 877 = 877 at length ranges `1..5` and `1..12`; max branch length 5; max hub–hub count 2 ≤ 3; 286 `K4` class shapes with no eligible split |
| `--dom` | 90 s | **(OC-46):** 1482 induced supports, 1482 extensions, 1430 also `star_generic`; 222 `F = H` pairs, 222 extensions; 99 chord supports counted; **end-to-end 222/222** with all four `IsNondegPencilRealization` conjuncts and `corank R(H) = 0`; 0 failures |
| `--core` | 3 s | **(OC-47):** Lemma A + patterns 1–4 all `dim S = 6`; `C₃…C₁₄` min corank `= 6 − min(ℓ,6)`; `theta(3,3,6)` core EMPTY, min corank 0, `Σd = 3 > 2` |
| `--hunt` | 357 s | **(OC-48)**, cells `n = 2, 3` (all `\|E°\|`) and `n = 4, \|E°\| ≤ 8`: 21 086 classes, 21 086 free, **0 candidates**; self-check 1 (60 topologies, 21 086 vectors, pruned == brute force); self-check 2 (32 instances, 0 mismatches) |
| `--huntn 5 8 8 k 3`, `k = 0,1,2` | 318 s each | **(OC-48)**, cell `n = 5, \|E°\| = 8`: 23 392 + 23 391 + 23 391 = **70 174** classes, all free, 0 candidates |
| `--cert` | 190 s | **(OC-49):** predicate self-checks 1163 = 1163 and 101/101; named habitats 5 shapes / 44 pairs **44/44**; `K4` 877 shapes / 3324 pairs **3324/3324**; off-`K4` 62 131 shapes / 271 974 pairs **271 974/271 974**; 250/250 direct exact-ℚ full-row-rank cross-checks |

**`--validate` does not fit a 600 s foreground budget** (5 + 90 + 3 + 357 +
190 = 645 s measured), so it runs as the **two-invocation split** below (the
`flanks --limit` / `yloc --coll` / `sigz --hunt` precedent, recorded so a
successor plans around it rather than rediscovering it), with the `(5, 8)`
cell's three slices on top:

```
python3 notes/scripts/w4/ogeom.py --bound --dom --core --cert   # 288 s
python3 notes/scripts/w4/ogeom.py --hunt                        # 357 s
python3 notes/scripts/w4/ogeom.py --huntn 5 8 8 0 3             # 318 s
python3 notes/scripts/w4/ogeom.py --huntn 5 8 8 1 3             # 318 s
python3 notes/scripts/w4/ogeom.py --huntn 5 8 8 2 3             # 318 s
```

**Every cap in one place** (the headline negative is an emptiness claim, so
this list travels with the figure): the `K4` re-enumeration cap `1..12`
(non-binding, by (OC-45)(ii)); `--dom`'s pool caps (40 `K4` shapes, 24
off-`K4` shapes, 60 supports per shape); `--hunt`'s **seed cap 8** gated draws
per core; `--hunt`'s **cell** coverage (`n = 2, 3` complete; `n = 4` only
`|E°| ≤ 8`; `n = 5` only `|E°| = 8`; `n ≥ 6` **not searched at all**);
`--cert`'s census cap (`|V°| ≤ 5`, `|E°| ≤ 9`) and its 250-pair direct
cross-check cap; the off-`K4` predicate spot-check cap (cell cap 3,
`|E°| ≤ 8`). **The gap-map / §8.5 sentence must be quoted as "not found under
these caps", never as nonexistence.**

### What to hunt for as a refutation of *this* pass

1. **(OC-37) misread.** (OC-47)(ii)'s budget consumes (Λ4)(iii) at the live
   core; if the core is not a *proper* branch subset of `G` the inequality is
   the wrong one. It is proper because `H ⊊ G` (the split branch is deleted).
2. **The iso-reduction.** If `canon_lengths_key` merged two non-isomorphic
   cores, a candidate could be hidden behind a free representative. The key
   is a canonical form under `Aut(E°)` and parallel-branch interchange only.
3. **The gate.** `repin.star_generic` is applied to the **core's** chart draw;
   a gated draw is used to avoid the (OC-7)/(OC-38) coincidence artifact — but
   the *free* verdicts would survive an ungated draw too, since a corank-0
   point is a certificate whatever the gate says. The gate matters only for a
   would-be candidate, and there were none.

### TERMINATION check (E1/E2/E3) — this direction's reading

**E1, E2, E3 all NO.** *(E1)* no g-flank: this direction never touches
(GR-15), `D = 0` shapes or admissible colourings. *(E2)* the target is neither
refuted nor unprovable-as-posed — it is *partially settled in the negative
direction* (no counterexample, on a named finite frontier) and leaves
open-with-named-dispatchable-attacks (successors 1–3 above). *(E3)* the target
is **not** proven — the class-uniform statement is exactly what stays open —
so E3 **stays ARMED by GBAL, not fired**.

---

### Steps O47–O51 (2026-09-02, direction OWALL) — the wall-avoidance route **REFUTED AS A MATTER OF LOGIC**, (OC-44)(iii) **REDUCED**, and **19 of the 20** second-confinement points identified

*Step O41* left two named residuals: the wall-avoiding certificate-colouring
existence statement (OC-44)(iii), and the mechanism of the *second* confinement
(the 20 of 27 rank-2 first points that the (OC-42) wall does not explain). This
pass settles the second outright, reduces the first to a geometry-free
statement, and **kills the route *Step O41* named for it**.

The enabling move is a reduction, not a search. At a σ-fixed grid chart point
the entire (OC-40)/(OC-41) apparatus — target rank of `G`, `dim D = 3`, the
forced `(1,2)` ⋆-eigen profile, `Q(g)`, `Gram_B(D_Y)`, hence `rank(Q|_D)` — is
computed by **two direction networks in `K³`** with conic directions
`A(s) = (1, s, s²)` and `Q` the *discriminant of a symbol* ((OC-50)): no
Plücker coordinates, no `ℚ(i)`, no rigidity matrix of `G`. In that model the
`X`-condition is exactly a **matroid-independence** statement — `βγ` independent
of the block network's edges — decided by an O(1) rank test per colouring
((OC-51)(i)), with three *proven* combinatorial certificates of its failure: the
(OC-42) wall (W), a new monochromatic **cut** (C), and a new **`≤ 3`-class
cycle vanishing rule** (Z) that welds nodes and makes the wall visible on the
contracted network. **(Z) accounts for 19 of OQRANK's 20 unexplained rank-2
first points** ((OC-54)(iii)) — not, on this evidence, for all 20: the two
populations are **not directly comparable** (this leg stops at the first
certificate colouring and records 17 classes with no standing draw, a bucket
OQRANK's 147/7/20 has no counterpart for), so the honest statement is *19
accounted for, one unmatched, the mismatch a population difference until a
matched run says otherwise*. (Z) **inverts** *Step O41*'s guessed mechanism: a
`≥ 4`-class cycle is where a nonzero relation *lives*; what confines `g` is a
`≤ 3`-class cycle *forcing coefficients to zero*.

Independently, (OC-44)(iii)'s **wall-avoidance conjunct is implied by its rank
conjunct** ((OC-52)), so *Step O41*'s attack (2) — a tree-triple exchange
breaking the single-class connectivity — proves a **consequence** of the target,
never the target. The census makes that quantitative and the gap is not small:
at the pinned splits **252 of 2 340** confined colourings are unwalled, and over
a wider split population **380 of 672**.

With the colouring cap removed — *every* admissible colouring of *every* one of
the 174 classes, 8 514 certificate colourings ((OC-54)) — **(OC-44)(iii) holds
at 174/174 with no cap**, never fewer than four good colourings at a class; and at **98/98**
(shape, **split**) pairs, the variable OQRANK's sampler held fixed. What is left
is **(OW)** ((OC-55)): a partition-constrained colouring-existence statement with
no geometry in it, in the *same object class* as §(K-grid) (GR-10) and
§(K-slide-comb) (C6). **No gap-map status word moves**: input (a) stays OPEN as a
class-uniform statement and is not an independent gap; (OC-8) stays OPEN; (OC-44)(ii)
is untouched; (OC-44)(iii) is restated as (OW) and stays OPEN.

*(Everything cited that this pass did not mint, per `notes/pencil/labels.md`
clause L3: (OC-29)–(OC-34), (OC-40)–(OC-44), (OC-49) are §(K-out)'s own earlier
items; (AC-2)/(AC-4)/(AC-9) are §(K-clos)'s; (FR-2)/(FR-3) are §(K-frame)'s;
(GR-5)/(GR-9)/(GR-10) are §(K-grid)'s; §(K-slide-comb) (C6) is that section's.
POOL-OQ2 is OQRANK's — cited by recomputation as a control, never re-run or
extended; the new pool is **POOL-OW**.)*

Standing notation: §(K-out)'s plus *Steps O37–O41*'s. Two objects get names
here, both already present in (OC-42)(i):

- **the block network** `Ḡ_F` of a graph in family `F ∈ {X, Y}` at an admissible
  colouring: nodes are the components of the *other* family's edges, edges are
  the `F`-edges, each labelled by its `F`-**class** (its own colour component),
  and an edge of class `i` imposes `m(n) − m(n′) ∈ ⟨A_F(s_i)⟩` on a node
  assignment `m : nodes → W_F`. `H̄_F` likewise for `H = G − v − a`. Write
  `β := b̄`, `γ := c̄` for `b`'s and `c`'s nodes.
- **the flex space** `Λ_F` of `H̄_F`: `Mot(H̄_F)` modulo the translations `W_F`.

---

### Step O47 — (OC-50): the block model, and the symbol dictionary that makes `Q` a discriminant

> **(OC-50)** *(proven-informally; every clause asserted against the landed
> `ℚ(i)` devices at every standing point of the `--agree` control)*
>
> **(i)** *(the target-rank criterion is a pair of direction networks)* a σ-fixed
> grid point of `G` at an admissible colouring carries the Tay target
> `corank R(G) = 0` **iff both** block networks `Ḡ_A`, `Ḡ_B` are isostatic, i.e.
> `dim Mot(Ḡ_F) = 3`. The count is
> `2|E_F| = 3(n_c^{F̄} − 1)`, and `n_c^{F̄} = |V| − |E_{F̄}|` since a legal
> colouring's classes are forests; summing the two families reproduces
> **tightness** `5|E| = 6(|V|−1)` and subtracting reproduces **(GR-9)'s balance**
> `|E_A| = |E_B|` — the consistency check that the model is the right one.
>
> **(ii)** *(the profile)* at such a point `H̄_X = Ḡ_X − n_{va}` has
> `dim Mot = 4`, `H̄_Y = Ḡ_Y − e₀` has `dim Mot = 5`, so `dim Λ_X = 1`,
> `dim Λ_Y = 2`; `D_F` is the image of `m ↦ m(β) − m(γ)` and the `(1,2)` profile
> of (OC-40)(iv) is exactly `dim D_X = 1`, `dim D_Y = 2`.
>
> **(iii)** *(the symbol dictionary)* let `Θ : W_F → Poly_2(u)` be
> `Θ(q)(u) := B(q, A(u))/κ`, with `κ` the (OC-41)(ii) constant. Then `Θ` is a
> linear isomorphism with `Θ(A(s)) = (s − u)²`, and
>
> > `B` ↦ the **apolarity pairing**;  `Q` ↦ a nonzero multiple of the **discriminant**;
> > `f ⊥ A(s_i)` ↦ `f̃(s_i) = 0`.
>
> Hence **`Q(q) = 0 ⟺ q̃ has a double root`**, and a 2-space `U ⊆ W_F` is
> `B`-degenerate iff its symbols share a root — (OC-41)(ii)'s tangent-plane
> reading, restated so the whole criterion is one sentence about polynomials.
>
> **(iv)** *(normalization, and it is exact)* take `A(s) = (1, s, s²)`,
> `Q(x) = x_1² − x_0x_2`, `B(x,y) = x_1y_1 − (x_0y_2 + x_2y_0)/2`. The landed
> `closure.ruling_A_line((1,s))` is, in the `closure.EIG_P` basis,
> `(2is, 1 + s², i(s²−1))` — the image of `(1, s, s²)` under a fixed invertible
> `ℚ(i)` matrix, in the **same** affine parameter — and the landed `pitch.Q`,
> `pitch.klein` pull back to `−8Q`, `−8B`. So the model is not an analogue: it
> is the same object in a `ℚ`-rational basis.
>
> **(v)** *(the grid point itself)* `closure.grid_point((1,s),(1,u)) = M₄·(1, s, u, su)`
> with `M₄` an invertible `ℚ(i)` matrix, so *bodies distinct* and the (GR-5)
> closed-hub-neighbourhood LI clause are **`ℚ`-rank conditions on the rows
> `[1, s_x, u_x, s_xu_x]`** — no `ℚ(i)` needed for those either.
>
> Consequence: **the whole (a₁) grid criterion of (OC-33)(ii) is computed by two
> direction networks in `K³`.**

*Proof.* (i) By (AC-2) every hinge extensor of a σ-fixed grid configuration lies
in `W_A` or `W_B`, and by (AC-4) the constraint system decouples into a
`W_A`-system and a `W_B`-system on the same body set. Within family `F`, an
`F̄`-edge forces its endpoints' `F`-components to agree (the `W_F`-component of a
multiple of an `F̄`-line is `0`), so the `F`-system descends to the
`F̄`-components — the nodes of `Ḡ_F` — and an `F`-edge of class `i` imposes
exactly `m(n) − m(n′) ∈ ⟨A(s_i)⟩` by (FR-3)(i) (the family parameter is constant
on a colour component). Target rank is `Mot(G) = ` the 6-dimensional trivial
space, which under the decoupling is `Mot(Ḡ_A) = W_A` and `Mot(Ḡ_B) = W_B`,
i.e. both isostatic. The counts are the displayed ones. (ii) is (OC-42)(i)'s
identification `H̄_X = Ḡ_X − n_{va}`, `H̄_Y = Ḡ_Y − e₀`, plus the count:
deleting a degree-2 node removes 3 variables and 4 constraints (`3 → 4`);
deleting one edge removes 2 constraints (`3 → 5`). (iii) `Θ(A(s))(u) =
B(A(s), A(u))/κ = (s−u)²` is (OC-41)(ii); `{A(u)}` spans `W_F` and
`{(s−u)²}` spans `Poly_2`, so `Θ` is an isomorphism. `Q ∘ Θ^{-1}` and `disc` are
both quadratic forms on `Poly_2` vanishing exactly on the irreducible quadric of
perfect squares — the image of the conic of ruling lines — hence proportional,
with a nonzero factor since neither is zero. (iv)/(v) are computations, run and
asserted in `--controls`. ∎

**The control that licenses everything model-only below.** `--agree` runs the
landed `oqrank.point_at` — unmodified — and this model side by side **at the
same parameter draw**, at OQRANK's own seed and draw order, and requires
equality of *every* clause: the target-rank verdict, the `(GR-5)` LI verdict,
`Q(g) ≠ 0`, `rank Gram_B(D_Y)`, `rank(Q|_D)`, `suppX`, `suppY` and the component
ruling-line counts. **72 standing points over 36 colourings at 12 classes,
including walled and (Z)-confined ones: all equal.** No model-only figure below
is quoted without that control behind it.

---

### Step O48 — (OC-51): the confinement calculus — the exact criterion, and three proven combinatorial certificates

> **(OC-51)** *(proven; (i)–(v) derivational, each asserted per standing point)*
> Let `pt` be a target-rank σ-fixed grid point, `N := H̄_X`, `D_X = ⟨g⟩`.
>
> **(i)** *(the exact criterion — an O(1) rank test)* for any class `j` of `N`,
>
> > `g ∈ ⟨A(s_j)⟩ ⟺ dim Mot(N + (βγ)_j) = 4`
>
> where `(βγ)_j` is a new edge from `β` to `γ` of class `j`. Equivalently: `βγ`
> of class `j` is **dependent** on `E(N)` in the class-parametrized
> direction-network matroid. So `Q(g) ≠ 0` is decided by at most `#classes` rank
> computations at one rational draw — `x₁`-free, `λ`-free, stratum-free, and
> **free of `Λ²K⁴` entirely**.
>
> **(ii)** *(the reactions)* `D_X^{⊥B}` is the 2-space of residues `ψ` of
> `(K³)^*`-valued Kirchhoff flows `(f_e)` on `N` from `β` to `γ` with
> `f̃_e(s_{cls(e)}) = 0` for every edge. (`dim D_X = 1` makes it 2-dimensional.)
>
> **(iii)** *(W — the (OC-42) wall, restated in the model)* if `β ~ γ` inside the
> class-`i` edge set of `N` then every achievable value lies in `⟨A(s_i)⟩`, so
> `g ∈ ⟨A(s_i)⟩` and `Q(g) = 0` at every draw.
>
> **(iv)** *(C — the MONOCHROMATIC CUT; new)* if `β ≁ γ` in `N − E_i` —
> equivalently, some `β`–`γ` edge cut of `N` has **all** its edges in class `i`,
> equivalently `b` and `c` fall in different components of `H` minus the
> class-`i` `X`-edges — then `g ∈ ⟨A(s_i)⟩`.
>
> **(v)** *(Z — the `≤ 3`-CLASS VANISHING RULE; new)* let `S` be a set of at most
> **3** classes and `N_S` the class-`S` subgraph of `N`. Then for each `i ∈ S`
> the restriction of any flex to `E_i ∩ N_S` is a **coboundary on `N_S`**; in
> particular **every class-`i` edge of `N_S` whose two endpoints already lie in
> one component of `N_S − E_i` has `λ_e = 0` for every flex**, so the unique
> nontrivial motion is constant across it and its endpoints are **welded**.
> Welding such a pair (contract, drop the edge) preserves `Mot(N)` and `D_X`
> exactly, so (iii) and (iv) may be re-read on the contracted network — and that
> is where the confinement of the *second* kind becomes visible.
>
> **(vi)** *(the third-class clause)* any class `i` for which (iii), (iv) or
> (v)+(iii) fires at a target-rank point satisfies `i ∉ {cls(b), cls(c)}` —
> (OC-42)(ii)'s clause, for its reason: `g ∈ ⟨A(s_b)⟩` or `⟨A(s_c)⟩` would break
> (OC-40)(iv)'s direct sum `D_X ⊕ ⟨A(s_b), A(s_c)⟩ = W_X`.
>
> **(vii)** *(what is NOT claimed)* (iii)–(v) are **sufficient**, not known to be
> exhaustive. (OC-54)(ii) measures the residue: **4 of 2 340** confined
> colourings at the pinned splits carry none of them, and the residual mechanism
> is a matroid-**closure** event — a node set on which the flex is constant with
> **no rigid subnetwork** witnessing it.

*Proof.* (i) A motion of `N` extends over `(βγ)_j` iff
`m(β) − m(γ) ∈ ⟨A(s_j)⟩`; `D_X = ⟨g⟩`, so a nontrivial motion survives iff
`g ∈ ⟨A(s_j)⟩`, and otherwise the new edge's two constraints cut the flex,
dropping `dim Mot` from 4 to 3.

(ii) Standard duality for the constraint system: `ψ` annihilates `D_X` iff the
load `ψ(δ_β − δ_γ)` is resolvable, i.e. iff there are per-edge reactions `f_e`
annihilating the edge's direction with `∂f = ψ(δ_β − δ_γ)`; `f_e ⊥ A(s_i)` is
`f̃_e(s_i) = 0` by (OC-50)(iii).

(iii) Fix the `β`–`γ` path `P` inside class `i`; telescoping, every achievable
value is `(Σ_{e∈P} ±λ_e)A(s_i)` — (OC-42)(ii) verbatim, now read in `H̄_X`.

(iv) Let `S ∋ β`, `γ ∉ S`, `∂S ⊆ E_i`. For any admissible flow, summing
conservation over the nodes of `S` gives `ψ = Σ_{e ∈ ∂S} ε_e f_e`, and every
`f̃_e` with `e ∈ ∂S ⊆ E_i` vanishes at `s_i`; hence `ψ̃(s_i) = 0` for **every**
`ψ ∈ D_X^{⊥B}`. So `D_X^{⊥B} ⊆ A(s_i)^{⊥B}`, both 2-dimensional, hence equal,
hence `D_X = ⟨A(s_i)⟩` since `B` is nondegenerate. ∎

(v) Work in symbols: a flex is a node potential `p : nodes → Poly_2` with
`p_x − p_y = λ_e(u − s_{cls(e)})²` across an edge of class `cls(e)`, and
`g̃ = p_β − p_γ`. Around any cycle `C`, `Σ_i μ_i(C)(u − s_i)² = 0`, where
`μ_i(C)` is the signed class-`i` sum along `C`. If `C` lies in `N_S` with
`|S| ≤ 3` then at most three **distinct** Veronese points occur, and three
distinct Veronese points are linearly independent ((FR-2)(ii)) — so
`μ_i(C) = 0` for every `i ∈ S`. Zero circulation around every cycle of `N_S`
says exactly that the 1-chain `λ|_{E_i ∩ N_S}` (extended by `0` on `N_S`'s other
edges) is a coboundary `dφ` on `N_S`; and `dφ = 0` on those other edges means
`φ` is constant on each component of `N_S − E_i`. So a class-`i` edge `xy` with
`x ~ y` in `N_S − E_i` has `λ_{xy} = φ(x) − φ(y) = 0`. Then `p_x = p_y`, i.e.
every motion of `N` — translations included — is constant across `xy`, so
contraction is a bijection on motion spaces and leaves `D_X` unchanged (and
`β ≠ γ` survives, since `dim D_X = 1`). ∎

**Reading — the three certificates are genuinely different objects.** (W) is a
**path** condition inside one class; (C) is a **cut** condition inside one class;
neither implies the other, and the synthetic control exhibits both alone
((OC-54)(v): 7 networks with (W) and no (C), 38 with (C) and no (W)). (Z) is
neither: it is a **rank/independence** fact about `≤ 3`-class subgraphs that
*creates* the situation (W) then detects. What (Z) explains is exactly the class
of confinements that are invisible to a connectivity read of the raw network —
which is why OQRANK's `single_class_paths` predicate, a correct implementation
of a correct theorem, saw only 7 of its 27 rank-2 first points.

**Why the `≥ 4`-class guess was the wrong sign.** *Step O41* named "a value-level
cancellation through a `≥ 4`-class cycle relation" as the natural suspect,
reasoning that three distinct Veronese points are independent so no shorter
relation can cancel. The premise is right and the conclusion inverts it: a
`≥ 4`-class cycle is precisely where a **nonzero** relation lives, i.e. where the
flex is *free*; it is the `≤ 3`-class cycles that **kill** coefficients, and
killing coefficients is what collapses a `β`–`γ` path onto a single class.

---

### Step O49 — (OC-52)/(OC-53): the wall-avoidance route is refuted **as a matter of logic**, and the `Y`-block is never the binding half

> **(OC-52)** *(proven; one line, and it decides *Step O41*'s attack (2))*
> (OC-44)(iii)'s first conjunct is **implied by** its second: a certificate
> colouring with generic-draw `rank(Q|_D) = 3` carries no single-class `b`–`c`
> `X`-path, since by (OC-42)(ii) such a path would force `rank(Q|_D) = 2` at
> *every* draw. Hence
>
> > **(OC-44)(iii) ⟺ "every certified class, at its split, admits a certificate
> > colouring with generic-draw `rank(Q|_D) = 3`"**,
>
> and an argument that delivers only wall-avoidance — *Step O41*'s attack (2), a
> colouring exchange on the tree-triple structure breaking the single-class
> connectivity — proves a **consequence** of the target, never the target. The
> route is not merely incomplete; it is aimed at a redundant conjunct.
>
> **How large the gap is, measured** ((OC-54)): at the pinned splits, of 2 340
> confined certificate colourings **252 are unwalled** (11 %); over the wider
> split population, **380 of 672** (57 %). At the *non-pinned* splits the
> (OC-42) wall as literally stated is the **minority** mechanism.

> **(OC-53)** *(the `Y`-block: a proven sufficient condition, and a measurement
> with the sampler support named)*
>
> **(i)** `Gram_B(D_Y)` is singular iff the generator `n` of the 1-dimensional
> `D_Y^{⊥B}` — the residue space of `β′ → γ′` flows on `H̄_Y` — has a
> double-rooted symbol.
>
> **(ii)** *(sufficient, proven)* if **two distinct** `Y`-classes `j ≠ j′` each
> cut `β′` from `γ′` in `H̄_Y` (the (OC-51)(iv) predicate on the `Y` side), then
> `ñ(u_j) = ñ(u_{j′}) = 0` with `u_j ≠ u_{j′}`, so `n` has two distinct roots and
> `Gram_B(D_Y)` is **nonsingular at every draw**. (A single-class `Y`-*path* is
> vacuous at target rank — (OC-42)(iii).)
>
> **(iii)** *(measured, with the support named)* `rank Gram_B(D_Y) = 2` at
> **every** standing draw of **every** classified certificate colouring:
> **10 896** colourings (8 260 at the pinned splits of all 174 classes, 2 636
> over 98 (shape, split) pairs), each at up to 3 independent seeded draws. The
> figure is an `assert`, not a report — and, per `RESEARCH-ARC.md` §4's
> 2026-09-02 sharpening, the support it ranges over is stated: it varies the
> **colouring** (exhaustively), the **draw** (3 seeded per colouring) and the
> **split** (all eligible ones at 20 classes); it does **not** vary the shape
> beyond the 174, which is the same bounded stratum every §(K-out) census has
> used. So (OC-41)(iii)'s `secant`-`D_Y` observation at OQRANK's 297 points is
> not a coincidence of that pool: the `Y`-condition has never been the binding
> half, and this pass has not found a colouring where it is.

---

### Step O50 — (OC-54): the census with the colouring cap REMOVED, and the split quantifier

> **(OC-54)** *(measured, POOL-OW; every count a colouring count; caps disclosed;
> every hit an individual generic-draw witness by (OC-44)(i)'s openness, never a
> rate)*
>
> **(i)** *(the cap removed)* population: `oschu.out_classes()` — the (OC-34)
> key, 174 isomorphism classes, at POOL-OC2's pinned (shape, split), the same key
> OQRANK used. For each shape **every** admissible colouring is enumerated
> (`2^{branches}`, 8–1024 per shape; `COL_CAP = 2^16` never approached), filtered
> by `grid.combinatorial_filter`, `closure.build_fixed_config` and (GR-9)'s
> both-block tree-triple certificate: **8 514 certificate colourings**, no probe
> cap (`CERT_CAP_FULL = 4096` never reached). Classified at 3 independent seeded
> draws each:
>
> > **good** (generic `rank(Q|_D) = 3`) : **5 920**
> > **confined** (`Q(g) = 0` at every standing draw) : **2 340**
> > **mixed** : **0**
> > **no standing draw under 3 draws** : **254** (all rejected by the (GR-5)
> > closed-hub-neighbourhood LI clause)
>
> **(OC-44)(iii) holds at 174/174 with NO colouring cap**, and the good
> count is never below **4** at any class — thinnest **4 of 12** (`K4 menu-blocked`)
> and **4 of 28** (`V5e8`), so the thinnest *fraction* is 14 %, not a third. So
> OQRANK's *"never past the fourth
> certificate colouring"* is **explained, not lucky**: at **131 of 174** classes
> the very first certificate colouring is already good ((iii) below), and no
> class has fewer than four.
>
> **(ii)** *(the mechanism, and the residue)* of the 2 340 confined colourings:
> **2 088** carry the (OC-42) wall literally; a further **248** carry it only
> after the (OC-51)(v) weld-reduction; **4** carry none of (W)/(C)/(Z), all four
> on the `V5e10` stratum. **(C) fires 0 times** on this population. `Q(g) = 0`
> **always** put `g` on a *component* ruling line — asserted at every confined
> colouring: the double root is a **class** parameter, never a stray conic point.
>
> **(iii)** *(the first certificate colouring — OQRANK's own naive point,
> re-derived and LABELLED)* at the first certificate colouring per class:
> **131 good**, **7 confined by the (OC-42) wall**, **19 confined by (Z)**,
> **17 with no standing draw**. **Every one of the 19 is the (OC-42) wall on the
> weld-reduced network**, so (Z) **accounts for 19 of OQRANK's 20** unexplained
> rank-2 first points — *19 of 20*, not all of them. The wall side matches
> exactly (7 and 7, the same `K4+par` shapes at split 5). **The two populations
> are NOT directly comparable, and the mismatch must be read that way rather
> than as a residual mechanism:** OQRANK's leg advances to the *next* certificate
> colouring when the first never stands and reports the first point that does
> stand, while this leg stops at the first certificate colouring and reports
> **17 classes with no standing draw in 3 seeded draws** — a bucket OQRANK's
> 147/7/20 has no counterpart for. So the one unmatched class is
> **unaccounted for, not counted as a second mechanism**: it may sit inside
> those 17, or it may be a class this leg calls good at its first colouring and
> OQRANK reached later. **A matched re-run — OQRANK's advance rule against this
> leg's certificates — would settle it and has NOT been done**; `--first`'s cap
> is one certificate colouring per class, disclosed.
>
> **(iv)** *(the SPLIT quantifier — the variable the landed sampler holds fixed)*
> (a₁) is needed at **every** class (shape, split) (*Step O24*'s hand-off), and
> `oschu.out_classes` pins **one** split per class (its first eligible split
> carrying a length-4 companion). Run at **every** eligible split of 20 classes —
> **98 (shape, split) pairs**, 2 652 certificate colourings — **98/98 carry a
> good certificate colouring**. On that population the raw wall covers only
> **292 of 672** confined colourings and (Z) covers **376**: the pinned split was
> **unrepresentative of the mechanism split**, though not of the verdict.
>
> **(v)** *(the adversarial control on the calculus)* 20 000 seeded random
> class-labelled networks with `2|E| = 3|V| − 4` and every class a tree (the
> shape a block network must have): 81 target-rank-compatible (`dim D_X = 1`),
> 78 confined. On the **raw** network: (W)-only **7**, (C)-only **38**, both
> **33**, neither **0**. On the **weld-reduced** network the wall covers
> **78/78** and (C) is never needed. So (C) is a theorem with **zero
> realizations** in the class-shape population and 38 in the synthetic one —
> real, and not the second confinement.

**Cap disclosure, and it travels.** Every figure above is *not found under the
stated caps*, never nonexistence: 3 draws per colouring (a `confined` verdict is
"`Q(g) = 0` at 3 independent seeded draws", upgraded to a **theorem** exactly
when (W), (C) or (Z) fires — 2 336 of 2 340 at the pinned splits); the 174
classes are the same bounded stratum (`|V°| ≤ 6` `K4`-stratum plus the named
sweeps) every §(K-out) census has used, and *"every tight class shape"* is an
**infinite** family (§(K-ind) (I4)); the split probe covers 20 of 174 classes;
the synthetic sweep is 20 000 draws with a 4 %-yield of target-rank-compatible
networks, so its 78 confined cases are a small absolute number.

---

### Step O51 — (OC-55): what (OC-44)(iii) reduces to, and the verdict

> **(OC-55)** *(the landing statement)* **(OC-44)(iii) is REDUCED** — not proven,
> not refuted. By (OC-50) + (OC-51)(i) + (OC-53)(i) it is *equivalent* to a
> statement with no geometry in it — no chart, no `ℚ(i)`, no Plücker, no `λ`, no
> `x₁`, no stratum:
>
> > **(OW)** *every tight class shape, at every eligible split, admits an
> > admissible colouring that (a) carries both-block tree-triple certificates
> > ((GR-9)) and (b) leaves the pair `βγ` **independent** of `E(H̄_X)`, for every
> > `X`-class, in the class-parametrized direction-network matroid — with (c) the
> > `Y`-block Gram nonsingular, which no colouring has yet failed ((OC-53)).*
>
> Clause (b) is decided by at most `#classes` rank tests at one rational draw
> ((OC-51)(i)), so **(OW) is a finite, decidable predicate on a finite colouring
> set** — what *Step O41*'s attack (4) wanted operationally is delivered, and the
> whole of (OC-44)(iii) is now **decidable by enumeration at any given shape**
> (which is exactly what (OC-54) did, at 174 shapes and 98 (shape, split) pairs).
> What is **not** delivered is a *connectivity* characterization: (W)/(C)/(Z)
> cover 2 336 of 2 340, and the residue is a matroid-closure event.
>
> **The residue, named and priced.** A *complete* combinatorial characterization
> of `Q(g) = 0` is a **Laman-type characterization of the class-parametrized
> direction-network matroid** on `K³` — the matroid whose ground set is a
> class-labelled multigraph and whose independence is that of the constraints
> `m(x) − m(y) ∈ ⟨A(s_{cls})⟩`. That is a self-contained question of matroid
> theory with no pencil in it. **(OW)** itself is a **partition-constrained
> existence statement over admissible colourings** — the *same object class* as
> §(K-grid) (GR-10) and §(K-slide-comb) (C6), for which the arc has an
> off-the-shelf prototype (Nash-Williams/Tutte, Edmonds) but no min-max, and to
> which `pencil/strategy.md` §2.3's base-rate warning applies verbatim: every
> prior class-uniform combinatorial-existence claim of this arc was eventually
> either proven by a min-max or refuted by a structural flank.
>
> **What a flank would look like, and why the census is not one.** The route's
> genuine dead end is a tight class shape at some split where **every**
> admissible certificate colouring is confined. The exhaustive census found the
> *opposite* at 174/174 pinned pairs and 98/98 split pairs, with the good
> count never below four (two at the thinnest non-pinned split) — so no flank
> surfaced, and the hunt was not
> capped where a flank could hide (the colouring cap is gone; the shape stratum
> and the split coverage are the remaining caps, both disclosed).

**Scope line, unchanged and restated because it is load-bearing.** Nothing here
touches the (K-tight) event: that needs the ruling `M̂ ∧ w` at *every* `σ = 0`
chart point, and POOL-OC2 already exhibits `rank(Q|_D) = 3` `ℚ`-points at all
174. Nor does a confined colouring cost input (a) at its own points —
`rank = 3` is sufficient, never necessary ((OC-33)(iii)) — as *Step O41*'s scope
line already records. What (W)/(C)/(Z) kill is only the *recipe*.

**Confidence verdict.** **(OC-50), (OC-51)(i)–(vi), (OC-52), (OC-53)(i)–(ii):
proven-informally** (derivations above from landed inputs; every clause
machine-asserted at every standing POOL-OW point, and (OC-50) additionally
checked clause-by-clause against the landed `ℚ(i)` devices at 72 points).
**(OC-51)(vii), (OC-53)(iii), (OC-54): measured** (exact `ℚ`, seeded, caps
disclosed). **(OC-55): a reduction**, with (OW) **OPEN**. Input (a) as a
class-uniform statement: **OPEN, unchanged**; (OC-8): **OPEN, unchanged**;
(OC-44)(ii): **unchanged**; (OC-44)(iii): **restated as (OW), OPEN**; **no
gap-map status moves.**

**What would change this.**
*(1)* A **min-max for (OW)** — proves (OC-44)(iii) outright and upgrades
(OC-44)(ii) to the uniform per-class-and-split statement with no caps. Its
natural first target is the (GR-10)-shaped half: (OW)(a) *is* (GR-10)'s
certificate condition, and (OW)(b) is one extra independence clause about a
single distinguished pair.
*(2)* A **Laman characterization of the class-parametrized direction-network
matroid** — makes (OW)(b) a count, closes attack (4) as a connectivity read, and
would let (OW) be attacked by the (C6)/Edmonds machinery of Phases 12–15.
*(3)* A **tight class shape and split whose every admissible certificate
colouring is confined** — the route's dead end, still not exhibited: it makes
(OW) FALSE, sends (a₁) off the grid, and is the only outcome here that would
cost the recipe class. Hunt it where the good count is thinnest:
`K4 menu-blocked` (`4/12` at the pinned split and **`2/12`** at two of its
other splits — the thinnest observed anywhere) and `V5e8` (`4/28`).
*(4)* **A fourth certificate** covering the 4 residual closure events. Their
signature is precise and reproducible: a node set on which the flex is constant
with **no rigid subnetwork** containing it, all on `V5e10` (`dim D_X = 1`, `g`
on a component line, no (W)/(C)/(Z)).
*(5)* Widening the **shape** quantifier past the 174, or the **split** quantifier
past 20 classes — the two caps that remain, and the only ones under which
(OC-54)(i)/(iv)'s `174/174` and `98/98` could hide a miss.

---

### Verification (Steps O47–O51)

Driver `notes/scripts/w4/owall.py` (new, this pass), exact `ℚ`, seed **20260902**
printed by every mode; headlines are `assert`s, never reports. Run from the repo
root, foreground, one at a time:

```
PYTHONHASHSEED=0 python3 notes/scripts/w4/owall.py --controls     #   ~1 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/owall.py --agree 0 4    #  180 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/owall.py --agree 4 12   #  119 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/owall.py --full 0 60    #  ~90 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/owall.py --full 60 130  #  ~330 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/owall.py --full 130 152 #  ~200 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/owall.py --full 152 164 #  388 s (timed)
PYTHONHASHSEED=0 python3 notes/scripts/w4/owall.py --full 164 174 #  ~330 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/owall.py --splits 0 12  #  ~150 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/owall.py --splits 100 108 # ~90 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/owall.py --first 0 174  #   15 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/owall.py --synth        #  ~35 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/owall.py --validate     #  ~240 s
```

**The `--full` chunking is forced, and the boundaries are recorded because a
naive one does not fit**: `--full 130 174` reaches class 159 at 530 s and blows
the 600 s foreground budget. Per-class seeds are keyed by the **global** class
index, so chunk boundaries move no figure (the SIGZ/OQRANK precedent).

Asserted per standing point: the `(1,2)` block-motion profile `4/5` and
`dim D_X/D_Y = 1/2`; the (OC-41) identity
`rank(Q|_D) = [Q(g) ≠ 0] + rank Gram_B(D_Y)`; `rank Gram_B(D_Y) = 2`;
`(W) ⟹ Q(g) = 0` and `g` on that class's line; `(C) ⟹` the same;
`(Z)+(W)/(Z)+(C) on the reduced network ⟹` the same; two `Y`-cuts
`⟹ rank Gram_B(D_Y) = 2`; `Q(g) = 0 ⟹ g` on **some** component ruling line; and
no colouring `mixed` (`Q(g)` zero at some draws and nonzero at others) over the
**11 166** certificate colourings processed (10 896 of them with at least one
standing draw).

Must-reject / must-accept controls (`--controls`, 5/5): the Veronese
identification `ruling_A_line((1,s)) = M(1,s,s²)` with `det M ≠ 0` at four
parameters; `pitch.Q`/`pitch.klein` pulling back to `−8Q`/`−8B`; the grid-point
factorization `M₄(1,s,u,su)` with `det M₄ ≠ 0`; a planted ruling generator
(caught by `Q`); a planted tangent plane built with the exact derivative
`(A(t+1) − A(t−1))/2` (caught as degenerate); a clean two-class secant (accepted,
Gram rank 2). `--agree` is the adversarial control on the whole model: 72
standing points, every clause equal to `oqrank.point_at`'s.

**Harness debt, recorded not paid** (this pass modified no landed file):
`oschu.out_classes` gains a **third** consumer and `gridwit.tree_triple` a
**fourth** — `notes/scripts/README.md` §2 rule 2's move-down trigger, RE-DATED;
`oqrank.point_at` / `oqrank.single_class_paths` gain their **first** external
consumer, a NEW move-down item (they are the reference implementation of the
(OC-40)/(OC-41)/(OC-42) verdicts and are now load-bearing for a second
direction).

---

### Termination check (Steps O47–O51) — read at source in `notes/pencil/fanout-archive.md`

E1/E2/E3 read at `notes/pencil/fanout-archive.md` *"The route ledger and the
TERMINATION test"* (the GEXIST statement, and the GORIENT restatement with its
recorded deliberate E3 deviation) — not from a paraphrase. They are stated over
the **§(K-grid) / (GR-15) ledger**; *Step O41*'s reading transposed them, and
this check keeps that transposition explicit.

- **E1: NO.** No g-flank. E1 is a `D = 0` shape whose *every admissible colouring
  is binding* — a statement about colouring **goodness** on the §(K-grid)
  ledger. **The near-miss must be named, because it is E1-shaped:** (OC-55)
  *what-would-change* item (3) — a shape and split whose every certificate
  colouring is *confined* — is the same **shape** of statement about a
  **different object** (the (a₁) rank criterion, not colouring goodness), and it
  **did not occur**: 174/174 pinned pairs and 98/98 split pairs carry a good
  colouring, and with never fewer than four good ones. So E1 does not fire, and
  the reason is a positive measurement, not an absence of looking.
- **E2: NO.** The target is neither refuted nor unprovable-as-posed: it is
  **REDUCED**, with two named dispatchable successors ((OW)'s min-max; the
  Laman characterization of the class-parametrized direction-network matroid)
  and a third, cruder one (the thin-fraction flank hunt at `K4 menu-blocked` /
  `V5e8`). What *is* refuted is a **route** — *Step O41*'s attack (2) — which is
  a direction's local obligation, not the arc's target.
- **E3: NO — stays ARMED by GBAL, not fired.** The target is not proven
  (per-class-and-split-generic, not class-uniform), and the remaining entries are
  dispatchable rather than adjudication-gated. Firing is a coordinator action;
  this is a report.

Cap disclosure: every "not found" above is *not found under the stated caps* —
3 draws per colouring, 174 classes of a bounded stratum, all eligible splits at
20 of them, 20 000 synthetic networks — never nonexistence.

---

### Steps O52–O57 (2026-09-03, direction OBAR) — U3's residue: `H ∪ {bar along M}` is **NOT** an (OC-35) object, and the ledger it was waiting for has **nothing to compute** — the object's whole content is one Klein condition on `V_bc`, i.e. **(T3) restated**

> **Read this first.** This direction was dispatched to settle a *gate*, with
> an explicit instruction that a negative answer is a complete landing and that
> a positive one must not be manufactured. The gate is **negative**. What
> follows is the negative, the identity that replaces the ledger, and the
> reason the residue was never a separate object — nothing here re-plans the
> arc, moves a gap-map status, or bears on (OC-8), (GR-15), `{σ = 0}` or class
> uniformity.
>
> **Numbering.** This section opens at **(OC-56) / *Step O52***, the tail
> `notes/pencil/labels.md` declares for §(K-out) at OWALL's landing
> (*"the live tail is therefore (OC-56)+ / Step O52+"*). The dispatched
> reservation offered (OC-58)+ / O53+; the direction **deviated DOWN** to the
> declared tail and says so in its return, per that file's standing lesson
> (*"the registry outranks a coordinator's spec on label naming"*) and GLEAF's
> same-round precedent.

#### Standing notation (on top of §(K-out) *Steps O19–O24* and *Steps O31–O36*)

Split chain `b–v–a–c` at a hard-stratum target-rank `G′`-seed (`b, c` hubs,
`deg v = deg a = 2`, `dim R_a = 1`); `G′ = G − v + ab`; `H := G − v − a = G′ − a`;
`σ := corank R(H)`; `M := Π(b) ∩ Π(c)` the panels' meet line, with `pt(a) ∈ M`;
`T := ⟨C_ab, C_ac⟩`; `B(x,y) = ⟨x, ★y⟩` the Klein form and `Q(x) = B(x,x)`;
`V_bc := { m(b) − m(c) : m a motion of H } ⊆ K⁶` the relative twist system
(§(K-pitch) *Step 1*, (T1)); `r` the transmitted load, `⟨r⟩ = (V_bc ⊕ T)^{⊥_E}`
at a `dim W = 5` seed; `L_b := α_{pt(b)} ∩ β_{Π(b)}` the hub's 2-dimensional
pencil, `L_c` dually; `k` the **companion length** (the shortest `b`–`c` path of
`H`), `k ≥ 3` always. Two perps are in play and the whole pass turns on not
conflating them: `⊥_E` is Euclidean on Plücker coordinates (the **row** model —
`pencil_escape.build_rigidity` builds each hinge's five rows from
`perp_basis(C_e)`), `⊥_B` is Klein. `★` is a Euclidean isometry and
self-adjoint (§(K-σ) **(σ2)**), so `B(x,y) = ⟨★x, y⟩` as well as `⟨x, ★y⟩`; that
is the identity that turns a Klein constraint into a Euclidean row, and it is
asserted in the driver.

For a subspace `A ⊆ K⁶`, write **`H ⊕_A bc`** for `R(H)` with the rows
`ρ_φ : m ↦ ⟨φ, m(b) − m(c)⟩` adjoined, one for each `φ` in a basis of `A`. This
is not a new device: §(K-pure) *Step P0* already reads a Klein constraint
between two bodies as a **bar**, `R_P := S_P^{⊥_B}` — *"the available bars"* —
with *"the hub-level limit rows for `P` are `m ↦ B(m(u) − m(w), ρ)`, `ρ ∈ R_P`"*,
and §(K-slide-comb) already **closes a carrier up** by *"adding three rows
`B(m(b) − m(c), ρ) = 0` for `ρ` in a generic 3-space `R₀`"*. So:

- a **bar** along a line `L` between `b` and `c` is `A = ⟨★C(L)⟩` — **one** row;
- a **hinge** along `L` is `A = C(L)^{⊥_E}` — **five** rows, the *"one
  constraint `m(u) − m(w) ∈ S_P` per `P`, i.e. `6 − ℓ_P` rows"* of
  §(K-slide-comb) at `ℓ_P = 1`, and exactly what `build_rigidity` emits.

Everything below is at an arbitrary legal pencil chart point. **No genericity
hypothesis is used anywhere in *Steps O52–O55*.**

---

#### Step O52 — (OC-56): the gate, answered NEGATIVE — three independent hypothesis failures, and the middle one is an argument rather than a measurement

> **(OC-56)** *(proven; (i) and (iii) unconditional, (ii) **inheriting §(K-σ)
> (σ7)'s basis** — see the clause below and *Caps* item 8; asserted per
> instance)* `H ∪ {bar along M}` is **not** an object (OC-35) quantifies over.
> (OC-35) reads *"let `F` be a subgraph with min degree ≥ 2 at any pencil
> placement"* and its proof assigns to **each oriented edge** a covector
> *"annihilating `C_e` — a 5-space"*. The candidate fails all three clauses:
>
> **(i) It is not a subgraph of `G`.** `bc ∉ E(G)`: `H` is vertex-deleted hence
> induced, so `bc ∈ E(G)` would give `bc ∈ E(H)` and `k = 1`, against `k ≥ 3`
> (§(K-dom) *Standing notation*: *"`k ≥ 3` always, since `dim V_bc = 3` needs
> `dim span{C_e : e ∈ P} ≥ 3`"*; on the class `hnoRigid` forces `k ≥ 4`,
> **(D3)**). Equivalently `b–v–a–c–b` would be a 4-cycle against `girth(G) ≥ 7`
> ((R3) + `hnoRigid`, §(K-ind) *Step I2*).
>
> **(ii) `M` is an admissible pencil hinge at NEITHER hub, and that is
> unreachable rather than merely non-generic.** A hinge along `M` between `b`
> and `c` requires `C(M) ∈ L_b ∩ L_c`, i.e. `pt(b) ∈ M` **and** `pt(c) ∈ M`.
> Since `M ⊆ Π(b)` and `M ⊆ Π(c)`, that says `pt(b) ∈ Π(c)` **and**
> `pt(c) ∈ Π(b)` — **both** halves of **(Λ0d)** failing at once. §(K-σ)
> **(σ7)** rules that out: *"the two-sided failure is impossible at a primally
> nondegenerate seed whose split middle body `a` is a degree-2 non-hub adjacent
> to both hubs — **(σ7)** — so (Λ0d) can fail in at most one direction"*. The
> §(K-out) split is exactly that configuration: `deg a = 2`, `a` a non-hub, its
> `G′`-neighbours `b` and `c` both hubs.
>
> **INHERITED BASIS, stated because the conclusion is a strong one.** (σ7) is
> recorded in §(K-σ) as one of that section's **four settled verdicts**, and its
> support is *primal conjunct 4 at the split's middle body `a`* — an
> **argument** — together with **39/39 witnesses that forcing both halves
> leaves `a` with no panel**. So *"unreachable"* here means *"on (σ7)'s basis:
> conjunct 4's argument plus 39/39"*, **not** *"by a bare theorem with no
> population behind it"*. It is field-neutral, (σ7) needing no polarity at all
> (§(K-σ) *Field scope*). One half alone already gives `pt(b) ∉ M`
> ((OC-29)(i)'s proof, from (Λ0d)); what (σ7) adds is that the negative holds
> **even where (Λ0d) does fail** — precisely where a sceptic would look —
> which is what makes it chart-wide rather than generic, on that basis.
>
> **(iii) A bar is one row where the ledger counts five.** (OC-36)'s
> `f(V(F)) = 5|E(F)| − 6(|V(F)| − 1)`, and with it every one of `δ_Q`, `ρ_F`
> and `slack(F)`, is built on five rows per edge. A bar contributes **one**. So
> (OC-36)/(OC-37) are not merely inapplicable to the candidate — evaluated on
> it they are **numerically wrong**, by four rows.

*Proof.* (i) and (iii) are as stated. For (ii): `M = Π(b) ∩ Π(c)` is the unique
line lying in both panels, so it is the unique candidate hinge line between the
two bodies (the ℓ1 clause of §(K-mech) records the same fact from the other
side: *"on an ℓ1 (hub-hub) chain the hinge lies in both panels, so
`C_uw = Π(u) ∩ Π(w)`"*). The pencil condition at a hub confines its hinges to
`L_b`, the lines through `pt(b)` in `Π(b)`; membership of `C(M)` there forces
`pt(b) ∈ M`, and `M ⊆ Π(c)` then puts `pt(b) ∈ Π(c)`. Symmetrically at `c`.
Both together are the two-sided (Λ0d) failure (σ7) rules out. ∎

**What this already settles, before any ledger question.** The candidate can
only be read as a **bar** — the reading U3's own words take (*"a bar along the
meet line `M`"*). Under that reading it is a well-defined *rigidity-matrix*
object (`R(H)` plus one row) and a well-defined *bar* between the two bodies;
what it is not is a min-degree-≥ 2 hinge subgraph, so **(OC-35) and its ledger
do not reach it**. *Step O53* says what does.

*Exact, per instance:* `bc ∉ E(G)` and `pt(b), pt(c) ∉ M` at **18/18** seeds
and, with the split varied rather than held, at **36/36** (shape, split) pairs
with `dist_H(b,c) ∈ {3,4,5,6,7,9}` (`obar.py --admis`, `--splits`). The
dispatch's second suspected obstruction — that the construction *"may create
degree-1 vertices"* — is **REFUTED**, twice over: adding a bar only raises
degrees, and `H` itself has min degree ≥ 2 (every non-hub of `G′` has degree
exactly 2 — §(K-frame) *Step FR12*'s (GR-5)-at-`G′` hypothesis table, whose
proof there is girth-based; `H = G′ − a` lowers degrees only at `b`, `c`, both
hubs, so `deg_H(b) = deg_G(b) − 1 ≥ 2`), asserted at 18/18 with
`deg_H(b) = deg_H(c) = 2` throughout.

---

#### Step O53 — (OC-57): the attachment identity — what replaces the ledger, and it is one line

> **(OC-57)** *(proven; an identity, unconditional, no genericity, asserted per
> frame)* Let `A ⊆ K⁶` be any subspace of constraint covectors attached between
> the terminals `b` and `c`. Then at **every** pencil placement:
>
> **(a)** `corank R(H ⊕_A bc) = corank R(H) + dim(A ∩ V_bc^{⊥_E})`;
>
> **(b)** the set of `A`-components realized by self-stresses of `H ⊕_A bc` is
> **exactly** the subspace `A ∩ V_bc^{⊥_E}`. In particular the attachment is in
> the support of some stress **iff** `A ∩ V_bc^{⊥_E} ≠ 0`.
>
> No hypothesis on `H`, on `A`, on `dim V_bc`, or on the placement.

*Proof.* Over a field, `rowspace R(H) = (ker R(H))^⊥`, and `ker R(H)` is the
motion space of `H`. So for `φ ∈ K⁶`,
`ρ_φ ∈ rowspace R(H) ⟺ ⟨φ, m(b) − m(c)⟩ = 0` for every motion `m`
`⟺ φ ∈ V_bc^{⊥_E}`. The map `φ ↦ ρ_φ` is injective and linear, so
`rank R(H ⊕_A bc) = rank R(H) + dim A − dim(A ∩ V_bc^{⊥_E})`, and (a) follows
from `corank = #rows − rank`. For (b): a stress is a pair `(y, (c_i))` with
`y^{T}R(H) + Σ c_i ρ_{φ_i} = 0`, i.e. `ρ_{Σ c_i φ_i} ∈ rowspace R(H)`, i.e.
`Σ c_i φ_i ∈ A ∩ V_bc^{⊥_E}`; every such element is realized, by running the
argument backwards. ∎

**Why this is the right replacement, and not a consolation prize.** (OC-35)'s
value is that it turns `corank` into *topological* data — paths, chain-span
deficiencies `δ_Q`, a Kirchhoff deficiency `ρ_F`, a combinatorial `slack`. A
`b`–`c` attachment adds **no topological path**: `b` and `c` are already nodes
or path-interior bodies of `H°`, and the new rows touch only their two blocks.
So there is no `δ_Q` to compute, no `slack` term to bound, and (OC-37)'s
class-shape floor has nothing to say. The entire increment is
`dim(A ∩ V_bc^{⊥_E})` — a **placement** datum about the one object §(K-pitch)
has been studying since (T1). That is *Step O57*'s point, and it is why the
"unrun ledger" was never a computation waiting to be done.

**A consistency reading, flagged as a reading.** §(K-slide-comb)'s (C6) closes
its limit carrier with *"three rows `B(m(b) − m(c), ρ) = 0` for `ρ` in a
**generic** 3-space `R₀`"*. (OC-57)(a) with `A = ★R₀` gives jump
`= dim(★R₀ ∩ V_bc^{⊥_E}) = 0` for generic `R₀` (two 3-spaces in `K⁶`), i.e. the
closure adds no stress — which is exactly why that system is the isostaticity
determinant. **This is a reading of (C6), not something this pass's driver
tests:** (C6)'s object is the `ε = 0` limit carrier on `G°`, whose `V_bc` is the
*limit* one, so a consumer should re-derive it at source before quoting it.

*Exact, per frame:* (a) and (b) asserted at **21** attachment draws — `A`
random of **every** dimension `0..6`, three seeds — plus the three named
specializations at 18 seeds each (`obar.py --validate`, `--onerow`, `--hinge`).

---

#### Step O54 — (OC-58): the bar specialization — U3's target statement **IS** (T3), pointwise

> **(OC-58)** *(proven; unconditional at every placement, and the (T3)
> identification at a `dim W = 5` target-rank seed)* For a line `L`, take
> `A = ⟨★C(L)⟩` (the bar along `L`). Then by (OC-57):
>
> `corank R(H ∪ {bar along L}) = corank R(H) + [ V_bc ⊥_B C(L) ]`,
>
> and **a self-stress with the bar in its support exists ⟺ `V_bc ⊥_B C(L)`**.
> At `L = M` that right-hand side is, verbatim, §(K-pitch) *Step 3*'s
>
> > **(T3)** *at a `dim W = 5` target-rank seed, both hubs:* **escape ⟺ some
> > motion `m` of `H` has `B(C(M), m(b) − m(c)) ≠ 0`** *— the relative twist
> > system is not contained in the linear line complex of the meet line.*
>
> **So U3's target statement — *"for every class (shape, split), `H` together
> with a bar along `M` admits no chart-wide self-stress with the bar in its
> support"* — is the escape, restated.** Not equivalent-after-work: *pointwise
> identical*, at every single chart point, with the bar's stress coefficient
> `t ≠ 0` and the (K-wit) pairing `B(C(M), V_bc) = 0` being the same one linear
> condition read twice.

*Proof.* `⟨★C(L), m⟩ = B(C(L), m)` by self-adjointness of `★` ((σ2)), so
`★C(L) ∈ V_bc^{⊥_E} ⟺ B(C(L), V_bc) = 0 ⟺ V_bc ⊥_B C(L)`. Substitute in
(OC-57) at `dim A = 1`. The (T3) reading is that clause's own statement. ∎

**U3's own kill clause fires, and by a cheaper mechanism than the one it
names.** `pencil/strategy.md` §4.6 wrote: *"if chart-wide stresses turn out to
have no more structure than pointwise ones, U3 is only a change of wording"*.
The kill does fire — but it needs **no comparison of chart-wide with pointwise
structure at all**. The bar-support question is *pointwise* equivalent to the
escape criterion by rank–nullity, so there is no chart-wide/pointwise gap for
U3 to exploit in the first place. §4.6's *"the honest first step is prose, not a
driver: characterize which supports can carry a chart-wide (rather than
pointwise) stress"* asked for a support enumeration; the correct answer is that
the support in question is one coordinate, and its vanishing is (K-wit).

**And the logical-form move that motivated U3 does not survive the
identification.** `pencil/strategy.md` §2.3's asymmetry (negatives uniform,
positives per-shape) was the reason to care: U3 stated the target as a
**non-existence**. But (OC-58) shows the non-existence is the *escape*, i.e.
`V_bc ⊄ C(M)^{⊥_B}` — a rank **lower** bound, the same side of §2.3's wall the
arc has always been on, and precisely what the (K-wit) row already carries as
its close-it: *"one `H`-motion pairing non-trivially with `C(M)`, uniformly"*.
Restating a lower bound as *"no stress exists"* changes the sentence's grammar,
not its logical form.

*Exact, per frame:* `[V_bc ⊥_B C(M)]`, "the bar is in some support", and
`critA or critB` agree at **18/18** seeds and at **36/36** (shape, split) pairs
(`obar.py --onerow`, `--splits`). **The predicate's positive branch is
witnessed, but at other lines `L`, not at `M`** — see *Caps* item 1.

---

#### Step O55 — (OC-59): the hinge specialization — the only (OC-35)-shaped reading, and it makes U3 **FALSE** everywhere

> **(OC-59)** *(proven; unconditional, asserted per frame)* Take
> `A = C(M)^{⊥_E}`, the five-row hinge along `M` — the only reading under which
> the object would be an (OC-35) subgraph. Then by (OC-57):
>
> `corank R(H + hinge_M) − corank R(H) = dim(C(M)^{⊥_E} ∩ V_bc^{⊥_E})
>  = 6 − dim(V_bc + ⟨C(M)⟩) ≥ 6 − (dim V_bc + 1) = 2`
>
> whenever `dim V_bc = 3`, i.e. at every seed of the hard stratum. So
> `H + hinge_M` **always** carries self-stresses beyond `H`'s, and every one of
> them has the hinge in its support (the `H`-only stresses are exactly those
> with zero hinge component). **Under the hinge reading U3's non-existence
> statement is therefore FALSE at every legal chart point** — quite
> independently of (OC-56)(ii), which says the object is not reachable there in
> the first place.

*Proof.* `X^{⊥_E} ∩ Y^{⊥_E} = (X + Y)^{⊥_E}` gives the middle equality; the
inequality is subadditivity of dimension. The support claim is (OC-57)(b) with
`A ∩ V_bc^{⊥_E} ≠ 0`. ∎

**The dichotomy is now complete and both branches are negative.** Read U3's
object as a **bar** and it is well-defined but is (T3) restated ((OC-58)); read
it as a **hinge** and it is both unreachable ((OC-56)(ii)) and, forced anyway, a
**refutation** of the very statement U3 wanted ((OC-59)). There is no third
reading: an attachment between two bodies is a subspace `A`, and (OC-57) covers
every one.

*Exact, per frame:* jump `= 6 − dim(V_bc + ⟨C(M)⟩) = 6 − 4 = 2` with the hinge
supported at **18/18** seeds and **36/36** (shape, split) pairs (`obar.py
--hinge`, `--splits`).

---

#### Step O56 — (OC-60): the geometry — the redundant-bar family is a Klein conic, and `M` sits on it iff `C(M) ∝ ★r`

> **(OC-60)** *(proven; (i)–(iii) unconditional or as qualified, (iv) measured)*
>
> **(i)** The **redundant `b`–`c` wrench constraints** over `H` form the
> 3-space `V_bc^{⊥_B}` (at `dim V_bc = 3`), and `★r ∈ V_bc^{⊥_B}` — immediately
> from (T1)'s `r ⊥_E V_bc`, with `Q(★r) = Q(r)`.
>
> **(ii)** The **redundant bars along genuine lines** are exactly the Klein
> conic `{Q = 0} ∩ P(V_bc^{⊥_B})` — a plane conic, i.e. a one-parameter ruled
> family, not a single line.
>
> **(iii)** At a `dim W = 5` target-rank seed,
> **`V_bc ⊥_B C(M) ⟺ C(M) ∝ ★r`.** Indeed `C(M) ⊥_B T` is automatic
> (`pt(a) ∈ M`, so `B(C(M), C_ab) = B(C(M), C_ac) = 0`), whence
> `C(M) ⊥_B V_bc` gives `C(M) ⊥_B W` and so `★C(M) ∈ W^{⊥_E} = ⟨r⟩`. This
> **re-derives (T3) from the bar side**, independently of (OC-57), and recovers
> §(K-σ) (σ5)'s load-side form `★r ∥ C(M) ⟺` routes A/B fail uniformly.
>
> **(iv)** `rank B|_{V_bc^{⊥_B}} = rank B|_{V_bc}` (both equal
> `3 − dim(V_bc ∩ V_bc^{⊥_B})`, since `B` is nondegenerate on `K⁶`), so §(K-Δ)
> **(M1)**'s dichotomy transports verbatim: **3 off a serial chain, 2 on one**.
> Measured 3 at 13/18 seeds and 2 at 5/18 (all five at θ(3,3,6), the `k = 3`
> serial-chain habitat). **The *signature* is not combinatorial** — it takes
> both `(2,1)` and `(1,2)` at seeds of the *same* shape (dbl-subdiv `K4`) —
> another instance of (OC-3): what the class predicate sees is a rank, never
> the geometry on top of it.

*Proof.* (i) `V_bc^{⊥_B} = ★(V_bc^{⊥_E})` because `★` is a Euclidean isometry,
and `r ∈ V_bc^{⊥_E}` is (T1). (ii) A nonzero `x ∈ Λ²K⁴` is a line extensor iff
`Q(x) = 0`, and the bar along that line is redundant iff `x ∈ V_bc^{⊥_B}`
((OC-58)). (iii) as stated. (iv) the radical of `B|_S` is `S ∩ S^{⊥_B}`, and
`(V_bc^{⊥_B})^{⊥_B} = V_bc`. ∎

**A by-product worth naming, since it is a positive.** This is a further
independent arrival at `V_bc` — alongside (T1)'s load side, §(K-dom)
(D1)/(D2)'s dominance side and §(K-ann) (ANH-1)'s contracted-self-stress side —
now from the constraint-attachment side. *(No count is claimed here; the three
named arrivals are the ones this pass verified at source.)*

*Exact, per frame:* (i), (iii) and (iv)'s rank equality asserted at **18/18**
seeds; a genuine redundant **line** exhibited at **5/18** (the degenerate case,
where the radical is rational and automatically isotropic) and **not found
under cap** at the other 13 (`obar.py --conic`).

---

#### Step O57 — (OC-61): the verdict, and what it does and does not buy

> **(OC-61)** *(an assessment)*
>
> **(1) `pencil/strategy.md` §8.2's U3 gate is answered NEGATIVE and U3's one
> genuine residue is RETIRED.** Its kill condition — *"the `H ∪ {bar along M}`
> ledger run, or the admissibility check coming back negative"* — is exercised
> on its **second** branch. §8.2's U3 row and §4.6's residue paragraph both
> carried the flag *"UNVERIFIED — confirm before spending a slice"*; the slice
> is now spent, at one dispatch. **U3 is struck completely**, not merely
> already-pursued: with §8.2's U2 struck 2026-09-03 and U3 now retired, the
> interlocked `U1`–`U3` shortlist is **U1 alone**.
>
> **(2) The ledger has nothing to compute — the residue was never a
> computation.** By (OC-57) the whole content of a `b`–`c` attachment is
> `dim(A ∩ V_bc^{⊥_E})`: no new topological path, no `δ_Q`, no `ρ_F`, no
> `slack`. So *"SIGZ and OGEOM spent the whole ledger on `σ = corank R(H)` and
> never on `H ∪ {bar along M}`"* is a true observation about what was run and a
> **false inference** about what was left undone. There was nothing on the
> other side.
>
> **(3) The calibration, per (OC-24).** This moves **no gap** and is **not**
> disproof-risk reduction — (OC-24)'s standard, that such reduction *"can never
> be the binding obstruction"*, does not even need invoking, because nothing
> here bears on the disproof side at all. What it delivers is the retirement of
> a residue plus one identity ((OC-57)) and one geometric restatement ((OC-60))
> a successor can use.
>
> **(4) The filters the dispatch was told to apply, applied.** The
> **growing-ground-set** test: the object's index set is `E(H) ∪ {bar}`, so it
> passes ingredient 2 formally — and (OC-58) shows that is cosmetic, since the
> bar coordinate carries the entire question and it is one scalar, not a growing
> family. **Counting saturation** (`pencil/strategy.md` §2.5): consistent, and
> used only as a negative — `dim(A ∩ V_bc^{⊥_E})` is a placement datum with no
> count-expressible content, which is (OC-3) again. **§2.5 supplies no freeness
> here and is not quoted as if it did.**
>
> **(5) Status.** `hK`, (OC-8), (GR-15), `{σ = 0}`'s row, input (a), (OW) and
> class uniformity are **exactly where they were**. **No gap-map status move.**

---

### Verification (Steps O52–O57)

Driver `notes/scripts/w4/obar.py` (new, this pass), exact `ℚ`, fixed seed
`20260903`; every headline is an `assert`, never a report. Run from the repo
root, **foreground, one at a time**:

```
PYTHONHASHSEED=0 python3 notes/scripts/w4/obar.py --validate   #  10 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/obar.py --admis      #  33 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/obar.py --onerow     #  55 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/obar.py --hinge      #  45 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/obar.py --conic      #  33 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/obar.py --splits     # 439 s
```

All six modes are **byte-identical at `PYTHONHASHSEED=0` and `=1`** (checked);
`--splits` is the only mode near the foreground budget at 439 s, and it is a
single run, not chunked.

**A driver mode per headline sentence** (`RESEARCH-ARC.md` §4), with each
population's support and the variable it moves named:

| headline | mode | population support | which of the claim's own variables it varies |
|---|---|---|---|
| (OC-56)(i)/(ii) the gate | `--admis` | 18 (shape, split, seed) triples over 4 shapes | shape, chart point; **split held** |
| (OC-56)(i)/(ii) + (OC-58) + (OC-59), split varied | `--splits` | 36 (shape, split) pairs over 4 shapes, all 48 eligible splits attempted | **split** — the variable every other mode holds |
| (OC-57)(a)/(b) the identity | `--validate` | 21 attachment draws: `A` random of every dim `0..6`, 3 seeds | **`A`**, the identity's own quantified variable, over its full dimension range |
| (OC-58) the bar, both branches of the indicator | `--onerow` | 18 seeds × 4 attachment lines (`M`; a redundant generalized bar; a genuine redundant line; a random line) | **the line `L`** and the indicator's truth value |
| (OC-59) the hinge | `--hinge` | 18 seeds | shape, chart point, with `A = C(M)^{⊥_E}` |
| (OC-60)(i)/(iii)/(iv) | `--conic` | 18 seeds | shape, chart point; rank and signature both read off |

Asserted per seed: `B(x,y) = ⟨x,★y⟩ = ⟨★x,y⟩`, `★² = id`, `★` orthogonal (200
draws); `H` has min degree ≥ 2 and `deg_H(b), deg_H(c) ≥ 2`; `bc ∉ E(G)`;
`Q(C(M)) = 0` and `C(M) ≠ C(bc)`; `B(C(M), C_ab) = B(C(M), C_ac) = 0`;
(OC-57)(a) **and** (b) — the realized coefficient space equal to
`A ∩ V_bc^{⊥_E}` as a subspace, not merely in dimension; `★r ∈ V_bc^{⊥_B}` and
`Q(★r) = Q(r)`; `rank B|_{V_bc^{⊥_B}} = rank B|_{V_bc}`; and the two
cross-checks that make the pass a claim about the arc's objects rather than
about its own arithmetic — **`[V_bc ⊥_B C(M)] == (critA or critB)`** (the (T3)
identification, against `repin.seed_probe`'s own criteria) and
**`[V_bc ⊥_B C(M)] == [C(M) ∝ ★r]`** ((OC-60)(iii)).

Controls: a **redundant generalized bar** built from `V_bc^{⊥_E}` fires the
(OC-57) indicator **positive** at 18/18 (so the identity is witnessed in both
directions, not only on the side `M` happens to sit); a **genuine redundant
line** at 5/18; a **random line** fires it negative at 18/18.

**Harness debt, recorded not paid** (this pass modified no landed file):
`pitch.H_motions_vbc` gains a **sixth** `w4/` consumer (after `outerwide`,
`dominance`, `lambda`, `outer`, `outerline`) and `pitch.klein`/`pitch.Q` a
further one — `notes/scripts/README.md` §2 rule 2's move-down trigger,
**RE-DATED, no move made**, by the standing rule that a dispatch does not move
a landed name. **No new hazard item.** All three recorded silent hazards were
**navigated, not encountered**: no `Λ²`-side draw goes through `bimage.pt_in`
and no `kbare/` module is imported at all, so `bimage.span`'s width-6 special
case and `bwin.dehom`'s list return are unreachable from here; and every
`localtest.meet_line` call is followed by an explicit `assert` on the returned
direction (§4 convention 1's signal-not-raise contract), the idiom
`pitch.transfer_probe` already uses.

### Caps, disclosed rather than smoothed (Steps O52–O57)

1. **The one direction the evidence does not move, stated first because it is
   the BSATUR-shaped limit of this pass.** `V_bc ⊥_B C(M)` is **FALSE at 18/18
   seeds and 36/36 (shape, split) pairs**, so **(OC-58)'s failure branch is
   never exercised numerically at `L = M`**. What carries it is the *proof*
   (rank–nullity, no genericity) plus the fact that the *same predicate*'s
   positive branch is exercised at other lines by two controls. The failure
   locus is known nonempty and known to be a σ-orbit with `{V_bc ⊥_B C(bc)}`
   (§(K-σ) (σ5)), and reachable by a chart move at all four habitats — **this
   pass did not construct such a point**, and a successor quoting (OC-58)
   should say so. It does not affect the verdict: step 1 is negative on its own,
   and (OC-58) is a proof rather than a census.
2. **W19 contributes ZERO seeds.** Every seed of `range(3000, 3040)` at
   `split_usable(W19)[0][0][0]` is skipped — *a chain end is not a panelled
   hub*, so the seed is outside the both-ends-hubs stratum every claim here is
   stated over. The **(K-res)** habitat is therefore represented by **S29
   alone** (2 seeds in the per-seed modes, 18 splits in `--splits`).
3. **Seed windows are first-N, not random**, with per-population `need` caps
   (6/5/5/3/2); `--splits` uses a 12-wide window per split and reports **12 of
   48** eligible splits as *"no usable target-rank seed in the seed window
   (cap)"* — that is a cap, **not** a claim that those splits admit no
   target-rank seed.
4. **The conic rational-point search is capped**: `|t₂|, |t₃| ≤ 12` with an
   exact-square discriminant test. A genuine redundant **line** is found at
   5/18 seeds and only via the free degenerate route (the radical of a rank-2
   Gram is rational and automatically isotropic). At the other 13 the verdict is
   **"not found under cap"**, never "does not exist" — whether
   `{Q = 0} ∩ P(V_bc^{⊥_B})` has a rational point there is a Hasse question this
   pass did not settle and does not need.
5. **`--validate`'s random `A`** draws entries in `[−5, 5]` at **3 seeds of one
   shape** (21 draws). The `A`-variable's *range* is covered exhaustively (every
   dimension `0..6`); its *distribution* within a dimension is not.
6. **Four shapes, not the 174-class census.** dbl-subdiv `K4`, θ(3,4,5),
   θ(3,3,6) and S29. This is deliberate rather than a shortfall: (OC-56)(i) rests
   on `k ≥ 3`, (OC-56)(ii) on (σ7), and (OC-57)–(OC-60) are placement-free
   identities, so the driver's role is per-instance assertion, not coverage.
   Anything read as a *rate* — the rank-3-vs-2 split, the signature spread — is
   over these four shapes only.
7. **θ(3,3,6) is off `hnoRigid`.** Its `dist_H(b,c) = 3` (so `k = 3`, and girth
   6, not ≥ 7), which is why (OC-56)(i)'s per-instance floor is stated as
   `k ≥ 3` — the unconditional bound — rather than (D3)'s class-only `k ≥ 4`.
   The habitat is a control here, and the `k = 3` serial-chain case is exactly
   where (OC-60)(iv)'s rank-2 branch and the geometric control fire.
8. **(OC-56)(ii)'s "unreachable" is (σ7)'s basis, not more.** (σ7) is quoted,
   not re-proven; its own scope is *"a primally nondegenerate seed whose split
   middle body `a` is a degree-2 non-hub adjacent to both hubs"* and its own
   support is **primal conjunct 4's argument plus 39/39 witnesses**, recorded in
   §(K-σ) as one of four settled verdicts and field-neutral. **(OC-56)(ii)
   inherits exactly that standing — the chart-wide reading of this pass's
   step-1 negative is no stronger than (σ7) is**, and a summary of this section
   must not upgrade it to a bare theorem.

---
