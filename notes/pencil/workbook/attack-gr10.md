# Attack `gr10` — workbook (the characteristic-2 probe)

Owner: attack `gr10` (`notes/attacks/gr10/`; brief and state there). Discipline:
`notes/pencil/workbook/README.md`. This file is the one place the attack appends
proved statements with their full hypotheses; the informal state of the attack
lives in `notes/attacks/gr10/state.md`.

**No labels minted.** No label prefix is assigned, so results are numbered **S1,
S2, …** (the brief's §A3 says "P1, P2, …"; `HARNESS.md` *Attack track* and the
`/attack` command say S-numbers, which bind) and are cited by this file's path.

Lean pointers are by declaration name, read at HEAD `84f60e2d` (Lean tree
unchanged since `084ee4ff`). Driver: `notes/attacks/gr10/drivers/char2chart.py`.

---

## S1 — the transfer: a nonzero chart minor at one `GF(2^k)` point proves `hK`'s conclusion over every infinite field of characteristic 2

**Statement.** Let `G` be a finite graph with `G.Simple`, `V(G)` nonempty,
`|closedHubNbhd v| ≤ 3` for every `v`, no triangle, and `G.deficiency 3 = 0`. Let
`hubSel` satisfy `IsFin3SelectorOf (G.closedHubNbhd w) (hubSel w)` for every `w`,
and let `s` be a set of indices `(e, t₁, t₂)` with every `e ∈ E(G)` and
`|s| = 6(|V(G)| − 1)`. Suppose that at some point `q₀` with coordinates in
`GF(2^k)` the family `pencilRow hubSel G.endsOf q₀` restricted to `s` is linearly
independent over `GF(2^k)`. Then `HasGenericPencilRealization K 3 G` holds for
every infinite field `K` of characteristic 2.

**Proof.**
(a) *Polynomiality.* In the basis of `α → ScrewSpace K 2` dual to
`Pi.basis (fun _ => screwBasis 2)`, the row `pencilRow hubSel ends q (e, t₁, t₂)`
with `ends e = (u, v)` has coordinate `C_{t₁}` at `(u, t₂)`, `−C_{t₂}` at
`(u, t₁)`, the negatives at `v`, and `0` elsewhere (`hingeRow_apply`,
`annihRow_apply`; `u ≠ v` since `G` is loopless, so nothing cancels). Here
`C_t = (p_u)_i (p_v)_j − (p_u)_j (p_v)_i` for `t = {i < j}` (the exterior-power
basis coordinates of `extensor ![p_u, p_v]`), and
`p_x = pencilChartPoint (PencilSeed.ofCoord q) hubSel x = cross₃` of the three
`hubSlotNormal`s, whose `i`-th coordinate is `det[a; b; c; e_i]`, a signed `3 × 3`
minor of seed coordinates (`cross₃` represents `w ↦ det[a; b; c; w]`). So every
coordinate is the image of one fixed polynomial of `ℤ[q]`, of degree `≤ 6`, the
same polynomial over every field. (This is the brief's G7 "no denominators"; the
Lean mirror is `pencilAnnihRowPoly`.)
(b) *Nonzero mod 2.* Linear independence of the `|s|` rows over `GF(2^k)` gives a
column set `c` with `|c| = |s|` and `Δ(q₀) ≠ 0`, where `Δ ∈ ℤ[q]` is the `s × c`
minor, `deg Δ ≤ 6|s|`. Evaluation at `q₀` factors through `ℤ[q] → F₂[q]`, so the
reduction `Δ̄ ∈ F₂[q]` is nonzero.
(c) *Any infinite `K` of characteristic 2.* `F₂ → K` is injective, so `Δ̄` is a
nonzero polynomial over `K`; over an infinite field a nonzero multivariate
polynomial has a non-root (`MvPolynomial.funext`). At such a `q₁ : α × Fin 4 × Fin 4 → K`
(coordinates at bodies outside `V(G)` arbitrary) the `s × c` minor is nonzero,
so `fun i : s => pencilRow hubSel G.endsOf q₁ i` is linearly independent over `K`.
(d) *The bridge.* `hasGenericPencilRealization_of_independent_pencilRow_target`
(`Escape.lean`; `[Inhabited α] [Finite α] [Finite β] [Infinite K]`, no
characteristic) with `hGne`, `hcard`, `htf` as assumed and
`hEsc := ⟨hubSel, q₁, s, selector, genuine edges, card, LI⟩`; the card conjunct is
`|s| = screwDim 2 · (|V| − 1) − G.deficiency 3 = 6(|V| − 1)`. Its conclusion is
`HasGenericPencilRealization K 3 G`. ∎

**Remarks.** (i) Orientation: `G.endsOf e` is a `Classical.choice` of the two
orientations (`endsOf`); swapping `(u, v)` negates the row, so independence does
not depend on which is chosen and the driver's stored orientation suffices.
(ii) The driver checks every hypothesis per shape except the identification of
`G.deficiency 3` with its count-matroid form: `nogood_subdiv.deficiency` computes
`6(|V| − 1) − rank` of the union of six graphic matroids on `5G`, which is `0`
iff `5G` has six edge-disjoint spanning trees iff (Nash-Williams 1961, Tutte 1961)
every partition `P` has `5·|crossing(P)| ≥ 6(|P| − 1)`, i.e. every `partitionDef`
`≤ 0`, i.e. `G.deficiency 3 = 0` (`deficiency`, `partitionDef` in
`Molecular/Deficiency.lean`). (iii) S1 uses nothing about `hK`'s antecedents; it
is a statement about `hK`'s conclusion only (brief §A4).

---

## S2 — (P) holds at every one of the 907 census shapes

**Statement.** For each of the 907 shapes of `grid.census_shapes()` (the
`kslidecomb` class-shape pool: three tight thetas, the exhaustive `K4` stratum,
seeded `|V°| ≤ 5` and `|V°| = 6` draws; |V| ∈ {11, 16, 21, …, 51}, 879 of them at
|V| = 16), and every infinite field `K` of characteristic 2,
`HasGenericPencilRealization K 3 G`.

**Proof.** S1, with the hypotheses supplied per shape by
`char2chart.py --sweep`: `check_shape` asserts no loop, no parallel edge,
`hcard_ok`, no triangle, `deficiency = 0`; `hub_selector` builds `hubSel v` as
`closedHubNbhd v` in sorted order, padding `none`, and asserts member / cover /
injective; the rows are the Lean `pencilRow` family (transcription listed in the
driver's docstring) at a seed `q₀` drawn over `GF(2^20)` (modulus
`x^20 + x^3 + 1`, primitivity asserted); greedy elimination selects `s`, and
`verify_cert` rebuilds the rows at `s` from scratch and re-ranks them by an
independent dense elimination. **Result: 907/907 hits, every one on its first
seed** (seed `20260923`, cap 3 seeds/shape never reached; ~34 s). A hit is an
exhibited certificate, so no Schwartz–Zippel bound is needed for the figure. ∎

**Controls.** `--control --cap 907`: the same matrix over `GF(2^31 − 1)` and
`GF(10007)` has rank `6(|V| − 1)` at 907/907 shapes (O1's control: the matrix is
the one whose ℚ-rank is the landed exact-point rank). Negative controls (probe,
script not retained beyond the driver's functions): at a random `GF(2^20)` seed
the same code gives rank 10 of 12 on `P₃`, 40 of 42 on `C₈`, 24 on `C₅`, and never
more than `6(|V| − 1)` without early stopping on the three thetas.

**Certificate for one hit** (`--cert 'theta(2, 5, 5)'`): edges
`[(0,10),(10,1),(0,12),(12,13),(13,14),(14,15),(15,1),(0,17),(17,18),(18,19),(19,20),(20,1)]`
(hubs 0 and 1); `hubSel` is `[x, none, none]` at each hub `x` and at each body
adjacent to exactly one hub (listing that hub), `[0, 1, none]` at body 10, all
`none` elsewhere; `s = {(e, {0,1}, t₂) : e ∈ E, t₂ ∈ the five 2-subsets after {0,1}}` —
per hinge, the five `annihRow`s pairing the first Plücker index with the others;
rank 60 = 6·10.

---

## S3 — (P) holds on the (GR-26) cubic population: 40 742 labelled shapes, 1 967 isomorphism classes

**Statement.** For every class shape of the `D = 0` cubic stratum at `n_hub ∈ {2, 4, 6}`
as `gisland.leg_island` enumerates it (every hub multigraph up to isomorphism; every
length tuple at `n_hub ≤ 4`, at most one length-1 branch at `n_hub = 6`; kept when
`gridcol.class_shape` accepts it), and every infinite field `K` of characteristic 2,
`HasGenericPencilRealization K 3 G`.

**Proof.** S1 at one representative per isomorphism class (`gisland.stratum`), with
`check_shape` asserting `Simple`, `hcard`, triangle-freeness and `def₃ = 0` at each
(so the bridge's shape hypotheses, "unchecked" for this population in brief §B4, hold
at all of it), and `verify_cert` re-ranking every certificate. A labelled member is the
image of its representative under a vertex relabelling, which carries seed, selector and
`s` along and permutes rows and columns of the minor. `char2chart.py --cubic` (seed
`20260924`, ≤ 3 seeds/class, ~4 min): `n_hub = 2`: 3/3 classes (10 labelled);
`n_hub = 4`: 80/80 (1 284); `n_hub = 6`, `|Λ| ≤ 1`: 1 884/1 884 (39 448). **1 967/1 967
hits, 40 742 labelled shapes** (equal to the labelled count of `gisland.scan_shape`'s
(GR-26) population, recomputed in the same run); no shape needed a second seed. ∎

**Population caps, travelling with the figure.** `n_hub ≤ 6`, cubic hub graphs only;
`|Λ| ≤ 1` at `n_hub = 6`. It overlaps the 907 census (S2) only in part: the census
also carries non-cubic `K4`-stratum and seeded `|V°| ≤ 6` shapes.

---

## S4 — report to the PI (brief §A3, O5)

**Population and caps.** (a) The 907-shape census `grid.census_shapes()` (S2). (b) The
(GR-26) cubic stratum, 40 742 labelled shapes in 1 967 isomorphism classes, caps as in
S3. Field `GF(2^20)` (modulus `x^20 + x^3 + 1`); seeds `20260923` (a) and `20260924` (b);
at most 3 seeds per shape, and never more than 1 used. Controls: the same matrix over
`GF(2^31 − 1)` and `GF(10007)` at rank `6(|V| − 1)` on all 907 census shapes; negative
controls `P₃`, `C₈` short as expected (S2).

**Hit/miss table.**

| population | shapes | char-2 hits | misses |
|---|---|---|---|
| census (S2) | 907 | 907 | 0 |
| (GR-26) cubic, isomorphism classes (S3) | 1 967 (40 742 labelled) | 1 967 | 0 |

**Certificate for one hit.** `theta(2, 5, 5)`, S2's last paragraph;
`PYTHONHASHSEED=0 python3 notes/attacks/gr10/drivers/char2chart.py --cert 'theta(2, 5, 5)'`
prints seed-derived selector, rank and `s`.

**Verdict: characteristic 2 limits the *method* only — at every shape tested.** At each of
these shapes `hK`'s conclusion `HasGenericPencilRealization K 3 G` holds over every infinite
field of characteristic 2 (S1), so nothing observed calls for `[NeZero (2 : K)]` on the
reduction. The grid route's need for characteristic ≠ 2 (the quadric, (AC-8)) is a property
of that route, not of the target, at these shapes.

**What this does not settle** (brief §A4). It is per-shape: no uniform statement over the
infinitely many tight shapes, so it does not decide the field range of `hK`'s conclusion at
def = 0 in general — only that the probe found no evidence for a restriction. It says nothing
about `hK` as an implication, about `hbareSplit`, or about def > 0. It moves no gap-map row.
It agrees with smark's record that route R2 uses no characteristic (smark state, S20(i)),
which it does not check.
