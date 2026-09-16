# `notes/attacks/smark/drivers/` — controls for the smark attack

Exact ℚ (`fractions.Fraction`), stdlib only, every random draw seeded
(`random.Random(20260915)`), every command run with an explicit timeout from
the directory named. These are **controls** for statements in
`notes/pencil/workbook/attack-smark.md`; the deliverable is the proof there.

## `orbits/` — the gauge group `S(ϕ)` on `P⁵` (workbook S1, S4)

Coordinates `x = (x₀; x_u; x_v; x_∞)` = the workbook's `(x_M; x_u; x_v; x_L)`;
group `(a, b, C)` acting by `(ab·x₀; aCx_u; bCx_v; det C·x_∞)`. Run from
`notes/attacks/smark/drivers/orbits/`:

| command | figure it reproduces |
|---|---|
| `timeout 300 python3 task12_orbits.py` | S1(ii): orbit dimension = stratum dimension at 3 exact representatives of each of the 19 strata (`Gen(I)` at `I ∈ {2, −3, 1/2, 1}`); prints `mismatches: none` |
| `timeout 300 python3 task3_semiinvariants.py` | S1(i): the semi-invariant quadratic forms — `span{Q₁, Q₂}` for `χ = ab·det C`, and `x₀²`, `x_∞²` for `a²b²`, `(det C)²`; no others |
| `timeout 300 python3 task45_parity.py` | S4: `dim(star(p) ∩ g·star(p′)) = 1` at 20 pairs × 30 group elements (task 4) and the 16 block defects `≤ 0`; `dim(star(p) ∩ g·Λ²π) = 0` at 20 × 30 (task 5) |
| `timeout 300 python3 task4_genericity_addendum.py` | which of the 20 task-4 pairs deviate from the generic defect vector and why (a zero first/second coordinate of `p` or `p′`) |

Caps, disclosed: representatives and points have numerators in `[−6, 6]` and
denominators in `{1, 2, 3}`; the group sweep is 30 draws per pair, so task 4's
"always 1" is a witness at each draw and task 5's "0 attained" is a witness; the
inequality `dim(A ∩ gB) ≥ 1` for *every* `g` in task 4 is the parity **theorem**
(workbook S4), not the sweep.

## `sideprof.py` — block profile of a side's `ρ̄` at a prescribed generic flag pair (workbook S5, S8)

Run from the repository root. Reuses the corpus samplers and profile code
(`bdecor.sample_by_branches` with `fixed=` flags, `bimage.sample_flags('nonadj')`,
`bimage.rho_bar_of`, `bunif.profile` / `bunif.lam2_mat`, `bdecor.d3` / `weld_d3`);
`tail` (a degree-1 pendant path) goes through a pendant-aware skeleton that calls the
same three `bdecor` primitives, because `bdecor.hubs_and_branches` raises on degree-1
vertices. The 16 block sums are printed in the corpus order with `L` = the line
`p_u p_v` (the workbook's `⟨M⟩`) and `ell` = the line `π_u ∩ π_v` (the workbook's `⟨L⟩`).

| command | figure it reproduces |
|---|---|
| `timeout 900 python3 notes/attacks/smark/drivers/sideprof.py --side all --seed 20260915 --draws 6` | the S5 control table: 11 sides × 6 draws, `ρ = δ` and attaining at 66/66, one profile per side except one `theta34` draw |
| `timeout 600 python3 notes/attacks/smark/drivers/sideprof.py --side theta34 --seed 1 --draws 24` | `theta34`: one profile at 24/24 (the seed-`20260915` deviation is draw-level) |
| `timeout 1800 python3 notes/attacks/smark/drivers/sideprof.py --side all2 --seed 20260915 --draws 6` | the session-2 widening (workbook S8, state file *Tried*): 12 sides × 6 draws — `theta344/444/445/555` and `theta4444` (hub terminals, side-degree 3–4), `hubpend`, `hubpend2` (side-degree 3 at `u`, 1 at `v`), `hubcyc` (3 at `u`, 2 at `v` on a rigid 5-cycle), `cross44`, `cross55` (two interior hubs), `theta45`, `theta55`; `ρ = δ` and attaining at 72/72, one profile per side, **no excess anywhere except `Π_v: 1` on `hubpend`, `hubpend2`** (the side-degree-1 hinge) |

Caps, disclosed: flag pair and interior points drawn with `s = 20` (numerators in
`[−20, 20]`), 40 tries per branch draw. **Reading (workbook S7(vi), S8):** every draw
is an exact witness, so each row is a *theorem* for the irreducible component of
`Y°(H; ϕ)` through the draw — attainment, welded attainment and the upper bounds
`c(U) ≤ value` (upper semicontinuity); for sides without interior hubs (ears, thetas)
the fibre is irreducible and the row is the profile of the whole fibre. The lower
bounds are the count `max(0, ρ + dim U − 6)` and the terminal-hinge incidences. The
population is still the 23 named sides: "no excess at a hub terminal" is *not found
in these 23 sides*, not a theorem about hub terminals.

## `earone.py` — the `ear1` composition criterion (workbook S9) and the bar count (S7)

Run from the repository root; imports `sideprof.py` for sampling and coordinates.
Per side and draw it computes `A' = ρ̄ ∩ (Π_u ⊕ Π_v)`, its `Q₂`-Gram rank and ruling
family, `dim(T ∩ ⟨M, L⟩)` for the transmissible-wrench space `T = ρ̄^⊥`, asserts the
S9 identity `dim A' = ρ − 2 + dim(T ∩ ⟨M, L⟩)` and S7's `dim A' = dim M(H + bar M + bar L)
− dim M(H/uv)`, then compares S9's **predicted** verdict with the **actual** one: the exact
rank of the composed pencil configuration `G = H + x` (`p_x` on `L = π_u ∩ π_v`) against
`6|V(G)| − 6 − def₃(G)`, at `--px` random points of `L`; `def₃(G) = f + 2 − min(δ + 2, 6)`
is asserted (the brief's composition formula).

| command | figure it reproduces |
|---|---|
| `timeout 3000 python3 notes/attacks/smark/drivers/earone.py --side both --seed 20260915 --draws 6 --px 3` | 23 sides × 6 draws × 3 `p_x`: predicted = actual at **138/138** draws (`MISMATCH at 0`), all 138 attaining and welded-attaining; `dim(T ∩ ⟨M,L⟩) ≠ 0` only on `ear1` (2), `ear2` (1), `cycletail` (1), `dumbbell` (1) — the four sides with `dist(u, v) ≤ 3` — and `0` on the 19 sides with `dist(u, v) ≥ 4`; no `A'` of the excluded family `y ∧ W` |

Caps, disclosed: the same `s = 20` draws; `p_x` has coefficients in `[−20, 20]` on the
basis of `L`. A `p_x` draw is generic with probability 1 minus a finite set, so
"actual" is a witness per draw; "predicted = actual at 138/138" is a control on S9's
*proof* (its "what would change this" is one mismatch), not on S9's truth, which is
the argument in the workbook. `dist ≥ 4 ⟹ T ∩ ⟨M, L⟩ = 0` is a **measured law on 19
sides**, not a theorem (state file, *Where it breaks*).

## `earcompose.py` — S10 end-to-end: ear_m composed with a hub-terminal side (workbook S12(ii))

Run from the repository root; imports `sideprof.py` (and `adversarial.py` for the K4
sides). Composes side 1 = a battery side with side 2 = `ear_m` at the hub 2-cut `{w, v}`,
asserts the 2-cut deficiency law `def₃(G) = f₁+f₂ − min(δ₁+δ₂,6)`, and compares S10's
predicted verdict (gluing law + S3 block criterion) against the **exact rank** of the
combined pencil configuration.

| command | figure it reproduces |
|---|---|
| `timeout 1800 python3 notes/attacks/smark/drivers/earcompose.py --seed 20260916 --draws 6 --ears 2,3,4 --side hub` | S12(ii): 14 hub-terminal sides × 3 ears × 6 draws = **252/252**; 2-cut law ok, S3 criterion ⟺ actual attainment, predicted = actual, `MISMATCH 0`, `draws with c1 over S10 bound 0` |
| `timeout 400 python3 notes/attacks/smark/drivers/earcompose.py --seed 20260916 --draws 3 --ears 2,3 --side sk4_d3` | the K4-minor consumed shape attains: `sk4_d3 ∪ ear_{2,3}` at 6/6, S3 crit ⟺ actual |

Caps, disclosed: the `s = 20` flag/interior draws of `sideprof.py`; 6 draws per (side, ear).
`HUB_SIDES` is the 14 side-degree-`≥2`-at-both-terminals members. Each draw is an exact
witness, so "attains" is a theorem for the component through it (S7(vi)); "no side over the
S10 bound" is *not found over these sides/draws*, not a theorem about the class.

## `adversarial.py` — the K4-minor / prism profile frontier (workbook S12(iii))

Run from the repository root; imports `sideprof.py`. Samples the block profile of
girth-`≥7` sides with a **K4 minor** (topological `K4`, `sk4_d{2,3,4}` at `δ = 2,3,4`) or a
subdivided triangular prism (`prism`, `δ = 3`) — the "3-connected chunk" the 23-side battery
lacked — and flags any `c′(Π_w) ≥ 2`, `c′(Π_v) ≥ 2`, or `c′(Π_w⊕Π_v) ≥ 3` (a refutation of
S10's `m = 2` clean form).

| command | figure it reproduces |
|---|---|
| `timeout 1200 python3 notes/attacks/smark/drivers/adversarial.py --seed 20260916 --draws 6 --side all` | S12(iii): `sk4_d2` → `c′ = (0,0,0)`; `sk4_d3`, `prism` → `(1,1,2)` (**S10 bound, tight**); `sk4_d4` → `(1,1,2)`; **no draw exceeds the bound** |

Caps, disclosed: the same `s = 20` draws, 60 flag tries; the population is the four named
K4/prism sides. "`c′(Π_w) ≤ 1` never violated" is *not found above 1* over these sides and
draws (each row a theorem for its component, S7(vi)) — **not** a theorem about K4-minor
sides in general.
