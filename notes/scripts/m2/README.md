# `notes/scripts/m2` — the Macaulay2 symbolic layer

**Start from `notes/scripts/README.md`** — the harness-wide primitive index,
layering map, invocation table and mandatory conventions. This file is the
per-driver description list for this directory, plus the four conventions the
M2 layer adds on top (they were specified in advance in
`notes/Pencil-strategy.md` §5.4 and are binding here).

Opened 2026-08-05 with `lambda1.m2`; `lambda0.m2` followed the same day. This
is the **only** non-Python part of the harness.

**The 2026-08-06 re-baselining round left this directory untouched**, and that
is a fact about the closures: `m2/` sits outside all four slices' import
closures, so no driver here was edited and no `.m2` figure moved
(`../README.md` *Harness debt* → the **CLOSED** block, the canonical home for
the round). Two of its outcomes still reach the M2 side. **(a)** `lambda0.m2`'s
(Λ0f′) — proven here 2026-08-05 — is what slice S3 coded into
`lambda.omega_curves`, so the Python criterion and this layer's now agree; that
is convention 3's cross-language pin working as intended. **(b)** §4 convention
5, which convention 2's re-baselining procedure defers to, gained an explicit
statement of what it does *not* say: it forbids rewriting a script so its old
numbers look right, and **prices** rather than vetoes a deliberate re-baselining
repair. The same reading applies to an M2 driver found defective.

## Why the layer exists

`notes/scripts/`'s Python is **exact-pointwise**: it evaluates the geometry at
sampled rational points. That can *prove* `≢ 0` at a fixed shape and can
*refute* identical vanishing, but it can never establish a statement uniform
over an infinite family (`notes/Pencil-strategy.md` §5.2). The only symbolic
capability on the Python side is hand-rolled and **univariate**
(`pitch.lagrange_coeffs` and `lambda.poly_of` on top of it).

Macaulay2 buys **multivariate** exact polynomial algebra, and therefore
generic-point computation: treat the frame's coordinates as indeterminates and
an assertion becomes an identity over the function field, valid at *every*
frame at once. That is the one place symbolic tooling reaches something the
sampling harness structurally cannot.

## Sandbox mechanics — established 2026-08-05, not assumed

`notes/Pencil-strategy.md` §5.4 originally recorded only the *run-in-a-temp-dir*
pattern as confirmed, and flagged repo-internal I/O as possibly needing sandbox
directories added. Re-probed directly, and it is better than that — this is what
a dispatch can rely on:

| probe | result |
|---|---|
| `which M2` | resolves — `M2` is on `PATH` (installed by the platform package manager; nothing here depends on *where*) |
| `M2 --version` | `1.26.06` |
| `M2 --script notes/scripts/m2/<f>.m2` from the repo root | runs; `currentDirectory()` is the repo root |
| reading a tracked repo file from M2 (`get "notes/scripts/README.md"`) | works |
| writing + reading back + `removeFile` inside the repo | works |
| M2's `applicationDirectory()` | need not exist; nothing is created |
| a failing `assert` under `--script` | **exit 1** |

So no sandbox directories had to be added, and an M2 driver satisfies the
harness's "non-zero exit or missing verdict line = failure" rule directly. The
drivers here nevertheless **write nothing**: they print and assert.

## The four conventions of this layer

**1. Status of its output — evidence, never a substitute for Lean.** An M2
verdict is evidence for the workbook, at exactly the same standing as the
exact-ℚ numerics: it supports an *informal* confidence verdict in
`notes/Pencil-informal.md`, nothing more. The project **formalizes everything
its argument uses** (`DESIGN.md` *Formalize everything the argument uses*);
"cite as external" / "axiomatize" is not a planning option, and **"verified in
Macaulay2" is not a proof this project may cite in place of a formalization**.
A symbolic identity landed here is an input to a future blueprint node and a
future Lean proof — it does not discharge either, and no blueprint node may
carry `\leanok` (or a citation to this directory) on the strength of an M2
run. This is the convention most likely to erode, because M2 output *reads*
like a proof in a way that a table of sampled ranks does not; it is written
first here for that reason.

**2. Reproducibility — an external binary is a new reproducibility surface.**
The Python harness is reproducible because it is stdlib-only and seeded. M2 is
none of those things by default, so:

- **The M2 version is pinned and is part of the figure.** Baseline:

  ```
  $ M2 --version
  1.26.06
  ```

  Every driver **prints its version line as its second line of output**, so an
  upgrade shows up as a diff rather than as a silent change of meaning.
- **Every run is deterministic and states so.** No `random`, no
  `randomKRationalPoint`, no probabilistic Gröbner shortcuts, no
  characteristic-`p` sampling in place of an exact ℚ computation. Where the
  Python convention says *print the seed*, the M2 convention is: print
  `randomness: none` and mean it. A driver that genuinely needs randomness must
  seed it with `setRandomSeed <literal>` and print the literal — and should
  first be reconsidered, because a random certificate is not what this layer is
  for.
- **`notes/scripts/README.md`'s *Hard rule — figures do not move* extends
  here**, with the same trigger discipline: a commit that modifies **no**
  tracked driver cannot move a figure, and one that modifies a driver owes the
  baseline/re-run for it and its dependents.
- **Re-establishing a baseline after an M2 upgrade.** The version line *will*
  differ; that is the point. The procedure: re-run every invocation in
  `notes/scripts/README.md` §3's M2 table, confirm every line **except the
  version line** is byte-identical, and update the pin in this file and in the
  driver header **in the same commit**, recording the old and new versions.
  If any other line moves, that is a genuine figure change and it goes through
  the workbook, not through a README edit — and `notes/scripts/README.md` §4
  convention 5 (*don't rewrite history to match a correction*) applies as it
  does to the Python drivers.
- **Invocation paths are frozen here too.** Drivers are cited as
  `M2 --script notes/scripts/m2/<name>.m2`, run from the repo root. Do not move
  or rename a file, and do not change a flag.

**3. Placement.** M2 drivers live only in this directory. `notes/scripts/`'s
opening line describes the *Python* harness as stdlib-only; that remains true
of `escape/`, `kbare/`, `w4/` and the two shared modules, and this directory is
the stated exception. The *Divergences* discipline extends across the language
boundary: **every primitive reimplemented here is a divergence candidate.** A
primitive re-derived in M2 (the Plücker order, `hodge_star`, `klein`,
`cross4`, the bracket) is a *second implementation* of a `notes/scripts/README.md`
§1 row — it cannot be imported, so it is re-derived on purpose, and the
obligation is to (a) name the canonical Python home in a comment at the
definition, and (b) pin the convention with an explicit check inside the driver
rather than trusting that the two agree. `lambda1.m2`'s check (M0) is that
pin for the bracket dictionary, and (M1)'s `cross4(m,n,s) = cross4(s,m,n)`
check is that pin for the cofactor sign/argument order. If an M2 re-derivation
is ever found to *differ* from its Python original, it goes in
`notes/scripts/README.md` *Divergences* like any other same-name-different-
semantics pair — do not silently "fix" either side, because the Python figures
are frozen.

**4. Do not port existing drivers.** M2 is **additive**: it is for questions
the sampling harness cannot answer, never a re-implementation of one it
already answered. Figure invariance and the frozen invocation paths depend on
this — a "port" of a Python driver would either duplicate a recorded figure
(and then diverge from it silently) or replace it (and then move it). When an
M2 driver revisits a claim an existing driver established, the existing driver
and its figures stay exactly as they are, and the M2 result is recorded as an
*upgrade of the confidence verdict*, with both cited. `lambda1.m2` is the
worked example: `w4/lambda.py --witt` keeps its 23 frames and its recorded
output unchanged.

## Drivers

- **`lambda1.m2`** — **(Λ1)**, `notes/Pencil-informal.md` §(K-Λ) *Step 2*:

  > `(q·ω⁺)² · Φ_loc(λ) = −2 · B(ω⁺, ω⁻) · (λ·ω⁺) · (λ·ω⁻)`

  established as an **identity over the function field** of the length-4
  companion frame, replacing the per-frame evidence of
  `w4/lambda.py --witt` (23 sampled rational frames, factorization scalar
  exactly 1). Five checks, each printing one `OK` line per assertion:

  - **(M0)** the pairing dictionary `B(C(uv), C(pq)) = [u,v,p,q]`, four free
    points — pins the M2 re-derivation of the Plücker/Klein conventions
    against the Python harness's.
  - **(M1)** the **universal cofactor identity**
    `(q·ω⁺)·cof(λ) = (λ·ω⁺)·ω⁻ − (λ·ω⁻)·ω⁺`, with `m, n, q, s, λ` free
    covectors (20 indeterminates, no geometry, no gauge). This is the
    structural half of Step 2's proof, including the normalization
    `κ = −1/(q·ω⁺)`.
  - **(M2)** the **universal quadratic expansion** against a *free symmetric*
    Gram (30 indeterminates): squaring (M1) leaves exactly the two cross terms
    `Q(ω⁺)`, `Q(ω⁻)`, so those two are the identity's only geometric input.
  - **(M3)** the **α/β isotropy lemma**, gauge-free (four free points): the
    two triples `⟨C_ab, C_ac, C_aw⟩` and `⟨C_ab, C_ac, C_bc⟩` are totally
    isotropic and 3-dimensional over the function field, so anything
    `B`-orthogonal to one of them lies inside it — which is `Q(ω⁺) = Q(ω⁻) = 0`.
    (M1)+(M2)+(M3) together are a **gauge-free proof** of (Λ1).
  - **(M4)** (Λ1) **end-to-end**, both in its 4×4 matrix form (all 16 entries)
    and in the scalar form (Λ1) is stated in, on the gauge slice
    `b, x₁, x₂, x₃ = e₀, e₁, e₂, e₃` with `a, c, w` and the far covector `λ`
    free. Along the way it re-derives, now generically rather than per frame:
    the structural zeros `m₁ = n₄ = q₁ = q₄ = 0`, the banded Gram, `ω±` being
    nonzero line extensors, `ω⁺` passing through `pt(a)` and `ω⁻` lying in
    `plane(a,b,c)`, `q·ω⁺ ≠ 0`, `B(ω⁺,ω⁻) ≠ 0`, the factorization scalar
    being exactly 1, and hence `rank Φ_loc = 2`.

  **On the gauge in (M4).** Both sides are bracket polynomials, hence GL(4)
  relative invariants of the same weight (13; the count is in the driver's
  header comment). For a frame with `b, x₁, x₂, x₃` independent,
  `g = [b|x₁|x₂|x₃]⁻¹` is the *unique* element of GL(4) carrying them to the
  standard basis, so the slice meets every such orbit exactly once and
  vanishing on the slice gives vanishing on a Zariski-dense subset of the full
  28-coordinate configuration space — hence identically. (M1)–(M3) need no
  gauge at all, so the gauge argument is a convenience for the end-to-end form,
  not a load-bearing step of the proof.

  **Feasibility, measured.** The ungauged end-to-end expansion has degree 52 in
  28 point indeterminates and does **not** finish: killed at 600 s inside
  `cross4` on the ungauged bracket rows (2026-08-05). Anyone extending this
  layer should budget for that wall — the local frame is viable symbolically,
  a whole-graph placement is not (`notes/Pencil-strategy.md` §5.3's closing
  paragraph). That probe is recorded as **measured, script not retained**: it
  is (M4) with the gauge removed — replace `bv, x1, x2, x3 = ev 0 .. ev 3` by
  four more free 4-tuples of ring generators — so it reconstructs from the
  committed file in a one-line edit, and it cannot be a driver here because it
  does not terminate.

  **What (Λ1) does and does not need.** `a`, `c`, `w`, `λ` are free in (M4), so
  the identity uses **none** of (Λ0)'s genericity clauses and none of the panel
  / meet-line data — in particular `pt(a)` is *not* constrained to the meet
  line `M`. (Λ0) is what makes the identity's ingredients nonzero and
  meaningful (`ω± ≠ 0`, `q·ω⁺ ≠ 0`, `B(ω⁺,ω⁻) ≠ 0`), and the driver shows each
  of those is nonzero *as a polynomial*, i.e. on a dense open set.

  Reproduce: `M2 --script notes/scripts/m2/lambda1.m2` (~1 s). Prints one
  `OK` line per assertion and a final `PASSED` line; a failing `assert` exits
  non-zero.

- **`lambda0.m2`** — **(Λ0)** and the **`a`-line spans**, `notes/Pencil-informal.md`
  §(K-Λ) *Standing notation* + *Step 3*, established at the **generic point of
  the local frame**. This is `notes/Pencil-strategy.md` §5.3's *first* item: the
  one argument in the arc whose logical form is *generic-point computation ⟹
  uniform over the class*, and the reason the layer was built. It upgrades
  `w4/lambda.py --span` (164 sampled frames over 38 strata).

  Headline — the span criterion is an **identity**, and it is **wider than the
  recorded one**. With `g13 = B(C₁,C₃)`, `g14 = B(C₁,C₄)`, `g24 = B(C₂,C₄)` the
  three surviving entries of the banded Gram:

  > `span_t ω⁺(t) = 3` ⟺ `p⁺₂ · p⁺₃ · g13 · g14 · g24 ≠ 0`
  > `span_t ω⁻(t) = 3` ⟺ `q₂ · q₃ · g13 · g14 · g24 ≠ 0`

  (Λ0f) as recorded carries only the first two factors of each. `g13·g24 ≠ 0`
  is `rank Q|_S = 4` (the driver checks `det Gram = (g13·g24)²`), asserted
  elsewhere in the harness but never linked to the span; **`g14 ≠ 0` was
  asserted nowhere** until 2026-08-06, when re-baselining slice S3 coded the
  full (Λ0f′) into `lambda.omega_curves` (`../README.md` *Harness debt* item
  2). Block (P5) settles that this is a correction rather than
  pedantry: it degenerates `C₄`'s direction onto `C₁`'s (`v2 = λu2, v3 = λu3`),
  which kills `g14` while **every** recorded (Λ0) clause — (Λ0a) `rank{C_i}=4`,
  (Λ0b) `S ∩ T = 0`, (Λ0c) `rank[m;n] = 2`, (Λ0e) `C(M) ∉ S`, and all four
  `p⁺`/`q` middle brackets — still holds, and both spans drop.

  Seven blocks: **(P1)** closed forms `p⁺ = (0, −u₁y₀, −y₁v₀, 0)`,
  `q = (0, u₃y₂−u₂y₃, y₃v₂−y₂v₃, 0)` with their structural zeros, `m₁ = n₄ = 0`,
  and the banded Gram; **(P2)** every (Λ0) clause exhibited as a *nonzero
  polynomial*, hence generic — this is what replaces "certified generic by exact
  witnesses in 38 strata"; **(P3)** the two containments
  `p⁺·ω⁺(t) ≡ 0`, `q·ω⁻(t) ≡ 0` as identities, with `deg_t ω⁺ = 3`,
  `deg_t ω⁻ = 2` exactly; **(P4)** the span criterion, via `cross4` of every
  coefficient triple; **(P5)** the degeneration above; **(P6)** the
  class-uniformity bridge; **(P7)** the core re-run without the `P_b`/`P_c`
  normalization (20 indeterminates), so the part of the gauge that assumes
  (Λ0d) is shown not to be load-bearing.

  **On the gauge, and on `t`.** GL(4) is transitive on ordered pairs of
  independent covectors, so `ν_b = e₀*`, `ν_c = e₁*` — whence
  `Π(b) = {X₀=0}`, `Π(c) = {X₁=0}`, `M = ⟨e₂,e₃⟩` and `pt(a(t)) = e₂ + t e₃`.
  The residual group still moves `P_b` inside `Π(b)` and `P_c` inside `Π(c)`,
  so *given (Λ0d)* put `P_b = e₁`, `P_c = e₀`; 14 coordinates survive. Two
  things worth carrying forward: the gauge **consumes (Λ0d)** (which is why
  (P7) exists), and the `a`-line parameter `t` **does not** join the
  indeterminates — `ω⁺(t)` is cubic and `ω⁻(t)` quadratic in `t` *structurally*,
  so their coefficient vectors come from finite differences of 4 resp. 3
  integer evaluations, and the span of a polynomial curve is the span of its
  coefficients. That is what keeps this at ~0.1 s rather than at the wall
  `lambda1.m2` measured.

  Reproduce: `M2 --script notes/scripts/m2/lambda0.m2` (~0.1 s).
