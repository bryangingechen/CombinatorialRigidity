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

## `pencilline.py` — which pencil line, and by which motion (workbook S13(i))

Run from the repository root; imports `sideprof.py` and `adversarial.py`. For the K4-minor /
prism sides it computes the line `ρ̄′ ∩ Π_u` exactly, matches it against the hinge lines at `u`,
and exhibits the motion `m` with `m(u) = 0`, `m(v) =` that line (inactive hinges, vertices
co-moving with `v`); it also prints `(f, g, δ)` of the side minus its direct `u`–`v` branch.

| command | figure it reproduces |
|---|---|
| `timeout 600 python3 notes/attacks/smark/drivers/pencilline.py --seed 20260916 --draws 2` | S13(i): at 6/6 draws over `sk4_d3`, `sk4_d4`, `prism` the line is `L_{u x}` toward `v` along the direct branch, that branch's other hinges are inactive and its vertices co-move with `v`; the side minus the branch has `(f, g, δ) = (6, 0, 6)` — the frontier sides are ears in parallel with a fully flexible remainder |

Caps, disclosed: the `s = 20` draws of `sideprof.py`, 2 draws per side. Each draw is an exact
witness; the *explanation* is S13(ii) (`ρ̄ = ∩` over pieces), not the sweep.

## `census.py` — the single-piece census (workbook S13(vi))

Run from the repository root; imports `sideprof.py`. Builds girth-`≥ 7` sides from thirteen
skeleton families (`K4-e`, `K4-tail`, `K4-e-tail`, `K33`, `K33-e`, `prism-same-tri`,
`prism-diff-tri`, `cube-d2`, `cube-d3`, `V8`, `K5-e`, `W5`, `Pet`) by subdividing every
skeleton edge with a seeded length in `--lens`, keeps those with girth `≥ 7`, `dist(u, v) ≥ 4`,
`δ ∈ {2, 3, 4}`, `|V| ≤ --maxV`, at most `--per` per `(skeleton, δ)`, samples each at generic
flags and prints the block profile; a row is `**`-flagged if it exceeds S10's `m = 2` bound.

| command | figure it reproduces |
|---|---|
| `timeout 1200 python3 notes/attacks/smark/drivers/census.py --seed 20260916 --draws 2 --per 3 --maxV 32` | S13(vi): `ROWS: 200`, `FLAGGED: 0`; single pieces with side-degree `≥ 2` at `u` have `c(Π_u) = 0` at every `δ ≤ 3` row and no excess at any block; `c(Π_u) = 1` only at `dist = δ = 4` (a path span) and at the bridge sides `K4-tail`, `K4-e-tail`; 52 rows (8 skeletons) are instances of (O4″) — `dist ≥ 6`, `δ ≤ 3` — all with `c(Π_u) = 0` |

Caps, disclosed: lengths in `{2, 3, 4}`, 200 seeded length vectors per skeleton (enumerated
when fewer exist), `|V| ≤ 32`, 3 sides per `(skeleton, δ)`, 2 draws each, the `s = 20` draws
of `sideprof.py`; Petersen has no member under the caps. All lengths are `≥ 2`, so by S13(iv)
each fibre is irreducible and **each row is a theorem for its side** (S7(vi)); "no excess" is
*not found in this population*, not a theorem about single pieces.

## `specialcfg.py` — special configurations of the minimal uncovered piece (workbook S13(vii))

Run from the repository root; imports `sideprof.py` and `census.py`. On `K4-e (4,2,3,4,2)`
(`|V| = 14`, `dist = 6`, `δ = 3`) it pins the interior hubs `p, q` to nine special incidences
with the terminal flags and reports `c(Π_u)`, attainment and welded attainment.

| command | figure it reproduces |
|---|---|
| `timeout 900 python3 notes/attacks/smark/drivers/specialcfg.py --seed 20260916 --draws 3` | S13(vii): `c(Π_u) = 0`, attaining and welded at families (a)–(h); at (i) `π_p = π_q = π_u` the side stops attaining (`ρ = 4`), welded still attains, `c(Π_u) = 1`; `Π_u` is never contained |

Caps, disclosed: 3 draws per family, `s = 20`, 200 flag tries per draw; special points are
drawn inside the pinned loci with the same numerator range. Each row is an exact witness *at a
special point*; the pointwise reading (no component genericity) is what it controls.

## `splitoff.py` — the split-off antecedent supplies the consumed block list (workbook S14)

Run from the repository root; imports `sideprof.py`, `earcompose.py`, `adversarial.py`,
`census.py`. For side 1 = `H′` (the 14 hub-terminal battery sides plus `sk4_d2/d3/d4`, `prism`)
and `m ∈ {2, 3, 4}`, at a prescribed generic flag pair it samples `H′`, `ear_{m−1}` and `ear_m`
once each, computes the exact ranks of `G₋ = H′ ∪ ear_{m−1}` and `G = H′ ∪ ear_m` against their
targets, `dim(ρ̄′ ∩ ρ̄(ear_k))`, the S10 block list for `m` on `H′`'s profile, and asserts
S14(i)'s implication at every draw (`G₋` attains and `δ′ + m ≤ 6` ⟹ welded attainment,
`ρ̄′ ∩ ρ̄(ear_{m−1}) = 0`, block list; `δ′ + m > 6` ⟹ `H′` attains, `ρ̄′ + ρ̄(ear_{m−1}) = Λ²K⁴`).
Item (6) prints, for `B = ρ̄(ear_m)` (`m = 2, 3`) and its Klein complement `T_B`, the exact
Gram ranks of `Q₁, Q₂, Q` and the traces on the three coordinate hyperplanes with
`expected/got` per entry — the (X1)–(X4) avoidance computed by hand in S14(iii). **Label
caveat:** the output labels the hyperplanes by coordinates, `'<L>^perp={x_L=0}'` and
`'<M>^perp={x_M=0}'`; under the Klein form `{x_L = 0}` is `⟨M⟩^⊥` and `{x_M = 0}` is `⟨L⟩^⊥`
(swapped names, same two sets; the verdict is unaffected).

| command | figure it reproduces |
|---|---|
| `timeout 1800 python3 notes/attacks/smark/drivers/splitoff.py --seed 20260917 --draws 3 --ears 2,3,4` | S14(iii) control: 18 sides × 3 ears × 3 draws = **162 draws**, `G₋` attains 162, `G` attains 162, `H′` attains and welded-attains 162, S10 list holds 162, **`claim_violations=0`, `gram_mismatches=0`** (every expected Gram entry met at every draw); ~200 s |
| `timeout 900 python3 notes/attacks/smark/drivers/splitoff.py --seed 20260917 --draws 3 --special` | S14(v)'s gap witness: `K4−e (4,2,3,4,2)` at special family (i) (`π_p = π_q = π_u`), 3/3 draws: `δ′ = 3`, `ρ′ = 4`, `H′` does **not** attain (rank 74/75), welded attains, `c(Π_u) = 1`; **`H′ ∪ ear₁` attains (84/84, `ρ̄′ ∩ R_y = 0`) while `H′ ∪ ear₂` does not (89/90, `dim(ρ̄′ ∩ ρ̄₂) = 1`)** |

Caps, disclosed: the `s = 20` draws of `sideprof.py`, 60 flag tries per draw (200 in `--special`),
3 draws per `(side, m)`; the population is the 18 named sides. The implication in item (5) is a
theorem (S14(i)); the run controls the *bookkeeping* (`a′_w`, `a′`, the `≤ 6` split) and the
hand Gram entries, not the theorem's truth. Each draw is an exact witness (S7(vi)); the
`--special` rows are pointwise facts at the pinned configurations.

## `earspan.py` — the hinge lines of a long ear span `Λ²K⁴`, at incident flags too (workbook S16(iii)(c))

Standalone (stdlib `fractions` only). For `ear_m` with `x₁ ∈ π_w`, `x_m ∈ π_v`, interior points free,
it takes the exact rank of the `m + 1` Plücker vectors at two flag regimes — `generic` (the `w ≁ v`
case) and `incident` (`p_v ∈ π_w`, `p_w ∈ π_v`, `π_w ≠ π_v`: the flags forced when `w ~ v`, possible at
`m ≥ 5`). One rank-6 draw is a certificate for the generic ear at that regime (lower semicontinuity
over the irreducible ear moduli).

| command | figure it reproduces |
|---|---|
| `timeout 120 python3 notes/attacks/smark/drivers/earspan.py --seed 20260922 --draws 20` | S16(iii)(c): `m = 5` (6 lines) and `m = 6` (7 lines) at rank `6` at **20/20** draws in both regimes; control `m = 4` (5 lines) at rank `5` at 20/20 |

Caps, disclosed: integer coordinates in `[−20, 20]`, 20 draws per `(m, regime)`, the two named
regimes. The population is one ear at prescribed flags; the statement certified is about the
generic ear at each regime, nothing about sides.

## `planefirst.py` — the hub hypergraph and the two combinatorial lemmas of S17 (pure combinatorics)

Run from the repository root: `timeout 900 python3 notes/attacks/smark/drivers/planefirst.py`.
For each side (`Z :=` degree-`≥ 3` vertices plus the terminals, `E_y := N[y] ∩ Z`) it prints
`s_max`, the hub-graph maximum degree, girth, the habitat count on the side, the girth-7
overlap facts, and the minimum slack of Lemma P (`3|A| − 4 − J_A` over all `A ⊆ Z`, `|A| ≤ 6`)
and Lemma L (`2(|L| − 2) − 1 − J_line(L)` over all `L ⊆ Z`, `|L| ≤ 6`). Population: the 23
`sideprof` sides; the 13 `census` skeletons subdivided into 3 and, seeded `20260923`, three
length tuples in `{2,3,4}` and four in `{1,2,3,4}` containing a length-1 (hub–hub) edge, each
kept at girth `≥ 7`; hub paths `P₃..P₆` and a hub 7-cycle with pendant paths; three `sk4` sides.
**Figure (2026-09-23): `ROWS: 135`, girth-`≥ 7` rows `132`, overlap violations `0`, min Lemma-P
slack `0`, min Lemma-L slack `0`, Case-1 rows `131/135`.** Caps: subsets of `Z` of size `≤ 6`
only; the population is the named one — "never negative" is a statement about these 132 rows,
the lemmas' proofs are in S17(iii). The four `s_max = 4` rows all fail the habitat count.

`earspan.py` gained three regimes (S17(v)): `coinc-pt` (`p_w = p_v`), `coinc-pl` (`π_w = π_v`),
`coinc-both` (equal flags). `timeout 120 python3 notes/attacks/smark/drivers/earspan.py --seed
20260923 --draws 20 --ms 5,6,7 --regimes coinc-pt,coinc-pl,coinc-both` prints rank `6` at
`20/20` draws in all nine cells; the original two regimes at seed `20260922` are unchanged.

## `starcheck.py` — exhaustive small-case check of (★) (workbook S17(iv), O7d; helper-written, 2026-09-23)

Run from the repository root: `timeout 900 python3 notes/attacks/smark/drivers/starcheck.py`.
For nine built-in girth-`≥ 7` graphs (hub paths `P₃..P₆`, a hub 7-cycle, two hub paths joined
by a length-4 path, a theta with an extra hub, `K₄` and `K_{3,3}` subdivided into length-3
branches) it enumerates every rank pattern on the marked set `Z` (set partition × partial
linear space on the classes), computes the total jump `J` combinatorially, and lower-bounds
each pattern's codimension soundly by `3(|Z| − q) + ρ`, `ρ` the Jacobian rank of the
collinearity minors at an exact random realisation (tangent dimension `≥` local dimension;
`ρ` taken mod `2⁶¹ − 1`, `≤` the rational rank). **Figure (base seed `20260923`): PASS on every
non-vacuous graph, all patterns processed; hub 7-cycle: 877 partitions, 19 217 patterns with
`J ≥ 1`, 11 159 realised and checked, 28 not realised (the labelled Fano planes, unrealisable
over `ℚ`); the maximum of `(J + 1) − (3(|Z| − q) + ρ)` over realised patterns is exactly `0`,
attained only at one collinear size-3 hyperedge (`J = 1`, `ρ = 2`) and one adjacent parallel
pair (`J = 2`, codim `3`); total 12.9 s.** Caps: `|Z| ≤ 7`, coordinates in `[−30, 30]`, up to
120 then 720 placement orders per line-structure, 600 s. A PASS is a check on these graphs
over `ℚ`, not a proof of (★); `K₄`/`K_{3,3}` subdivided are vacuous (`J ≡ 0`).

## `earspan_modp.py` — the ear-span certificates in characteristic `p` (review 3, 2026-09-23; workbook S18(ii), O11)

Run from the repository root: `timeout 300 python3 notes/attacks/smark/drivers/earspan_modp.py`. Re-draws
`earspan.py`'s cells (seed `20260922` for `generic`/`incident` at `m = 5, 6`; seed `20260923` for the three
coincidence regimes at `m = 5, 6, 7`; same rng sequence, same `s = 20`), clears denominators from each Plücker
vector, and ranks the `m + 1` integer vectors over `F_p`, `p ∈ {2, 3, 5, 7, 11, 13}`, next to the exact ℚ-rank.
**Figure (2026-09-23):** ℚ-rank `6` at 20/20 in every cell; `F₂`-rank `6` at between **2/20** (`m = 5`: `incident`,
`coinc-pt`, `coinc-pl`) and **11/20** (`m = 7`, `coinc-pt`); `F₃` between 4/20 and 16/20; `F₁₃` between 14/20 and
20/20. Caps: the same integer draws; six primes; a reduced draw's flag pair may lie in a more degenerate
`PGL₄`-orbit than the cell's name (not classified — a certificate at a more degenerate orbit covers the less
degenerate ones, S17(v)). **Reading:** a ℚ-certificate proves the spanning in characteristic 0 and at every prime
not dividing its `6 × 6` minor, nothing more; the S16(iii)(c)/S17(v) certificates therefore do not travel to small
characteristics by themselves, but every cell has at least one `F₂`- and one `F₃`-certificate among its 20 draws, so
O11 is one exhibited draw per prime dividing the chosen ℚ-certificate's minor, at the equal-flags cell.

## `starcomb.py` — link-by-link check of the S19 proof of (★) in Case 1 (session 8, 2026-09-23; workbook S19, O7d)

Run from the repository root: `timeout 900 python3 notes/attacks/smark/drivers/starcomb.py` (options
`--seed 20260923 --graphs 60 --maxZ 7`). Imports `starcheck.py`'s pattern enumeration and nine graphs, adds
random habitat sides (hub skeleton of maximum degree `≤ 2` with edges subdivided into paths of length `1..5`,
`≤ 3` extra hub–hub paths of length `2..5`, a cycle closure only at `|Z| ≥ 7`, pendant paths of length `2` to
hub degree `3`, up to two extra marked degree-2 vertices modelling `w, v`; `|Z| ∈ [3, 7]`, `|V| ≤ 24`, 400 tries
per side), and **verifies every side** for girth `≥ 7`, Case 1, unmarked degree `≤ 2` and the habitat count
`5e(S) ≤ 6(|S| − 1)` on every vertex subset (exact: the maximum excess sits on the 2-core and is a sum over
its chains, `6 − L` per chain of length `L`). For every rank pattern with `J ≥ 1` it computes the sequential
codimension `cost = 3(|Z| − q) + LC` with `LC` an exact subset DP over all placement orders, and checks the
four links of S19 separately — class surplus `σ_A − F_A ≥ [not a bad pair]` and the `|Y_A|` bound; per-line
surplus `≥ 0` with equality exactly at type-(3) lines; the loss inequality; the final bound — plus `cost ≥ J + 1`
on the full line set and the two structural facts (a flat vertex on one line; a flat singleton never a
neighbour class elsewhere). **Figure (seed `20260923`, 9 + 60 graphs): `112 261` patterns, `64 325` with
`J ≥ 1`, all links hold everywhere; `min(cost − J − 1) = 0` at `197` full-pattern shapes (the Lemma P/L
extremals and their unions); `831` type-(3) lines, `447` bad pairs seen; `8.8` s. Seeds `1`, `2` (80 sides
each): `73 969` / `55 831` patterns with `J ≥ 1`, PASS.** Caps: `|Z| ≤ 7`; the generator's shapes above (its
fenced constants: `TOTAL_CAP = 600`, `maxV = 24`, `tries = 400`, the length menus `[1,1,2,3,4]` / `[2,3,4,5]`);
`cost` is the sequential lower bound on codimension, not the codimension itself (`starcheck.py`'s Jacobian is
the geometric control). Pure integer combinatorics, no geometry, no characteristic. **`--case2 L`** (S19(viii)) builds
the Case-2 side `K_{1,3}` of hubs with leaf-to-leaf paths of length `L` and reports girth, the count (max excess over
edge-carrying subsets; `0` = a tight, hence rigid, subgraph, so a legal `H′` needs `≤ −1`), and the big hub: `L = 6` gives
`|V| = 19`, `|E| = 21`, girth `8`, excess `−1` — O7e is non-vacuous; `L = 5` is tight (`90 = 90`), exit `1`.
The random population is checked against the **non-strict** count (what S19 uses), so it is a superset of the legal sides.

## `unitcert.py` — unit-minor integer certificates: spanning and independence in every characteristic (session 8, 2026-09-23; workbook S20, O11 and O10(i))

Run from the repository root: `timeout 120 python3 notes/attacks/smark/drivers/unitcert.py` (options `--seed 20260923
--tries 200000`). Seeded random integer points with coordinates in `[−2, 2]`, exact integer arithmetic (Bareiss
determinant), first hit reported. **(A)** an `ear₅` at *equal flags* (`p = e₁`, `π = {x₄ = 0}`, `x₁, x₅ ∈ π`): the `6 × 6`
Plücker determinant of its six lines is `−1` — found at try 1794, points `(1,0,0,0), (2,1,1,0), (2,−2,−2,−1),
(−2,1,−2,1), (−1,0,1,0), (−2,−1,0,0)`; **(B)** a pentagon whose `6 × 5` Plücker matrix has a `5 × 5` minor `−1` (rows
`0,1,2,4,5`; try 313); **(C)** an unconstrained hexagon with determinant `+1` (try 1184). At every witness all
consecutive point triples have `gcd` of `3 × 3` minors `1` and all adjacent pairs `gcd` of `2 × 2` minors `1`. **Reading:**
a unit determinant is nonzero in every field, so (A) proves *the six lines of this ear span `Λ²K⁴` over every field*,
(B) *five independent lines over every field*; with S20(i)'s semicontinuity and orbit-closure steps, (A) covers every
`ear_{m ≥ 5}` at every flag pair and every cycle through a flag — the whole of O11 — and (A)/(B) the cycle base cases
of O10(i). Caps: the search alphabet and try count (a found witness is a proof; only a *failure* would be capped).
Independent re-check of (A)'s determinant by Fraction elimination: `−1`.

## `case2m2.py` — Macaulay2 component count of the reduced incidence variety on Case-2 hub graphs (session 9, 2026-09-23; workbook S21(vi), O7e)

Run from the repository root: `timeout 900 python3 notes/attacks/smark/drivers/case2m2.py --timeout 280` (one case:
`--case T2`). Needs `M2` on the path. For each named hub graph `Γ` (marked set `Z`) with connectors, builds the reduced
closed incidence variety — a flag `(p_c, π_c)` per marked vertex, `p_d ∈ π_c` and `p_c ∈ π_d` per Γ-edge, one point on
`π_a ∩ π_b` per connector — fixes the flag of the first marked vertex and uses standard charts (points `x₀ = 1`, normals
`n₃ = 1`) on the other blocks, and prints the number and dimensions of the minimal primes over `ZZ/32003` (exact; no
randomness — `--seed` is unused). Faithfulness of the charts: every component is `PGL₄`-invariant, the flag stabiliser is
connected, and each of its invariant closed subsets of `P³` / `P³*` meets the chart. PASS = one prime of the expected
dimension `5|Z| − 2|E(Γ)| + #conn − 5`. **Figure:** C1, C1c (Case-1 controls), T1, T1c, T3, T2, T6, T7, T8 PASS (T8 in
`39` s, the others `< 2` s); the negative controls N3, N4, NK4 (hub triangle, 4-cycle, `K₄`: outside the habitat) show
`3`, `2`, `3` primes; T10, T11 (cycles through a big vertex) time out at `280` s; T9 (spider, `k_c = 4`, `|Z| = 10`) PASS in `1098` s
(`--case T9 --timeout 1650`). Caps: ten hand-built Case-2 graphs with `|Z| ≤ 9` — *not* a population, no cycle case finished; one
characteristic; primes over `F_{32003}`, not its closure. A single prime is evidence for, not a proof of, irreducibility.
