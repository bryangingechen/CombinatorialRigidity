# NONDEG workbook

Results of the NONDEG track, numbered S1, S2, … and cited by number (`HARNESS.md` *Attack track*).
Appending is right here; a result found wrong is struck through with a pointer to the result that
corrects it. Notation is the brief's (§2–§3): grade `k`, `d = k + 1`, `V = K^{d+1}`,
`D = C(d+1, 2)`; a pencil realization `(F, b, Π)` (`HasPencilPlaneRealization`); `N[v]` the closed
neighbourhood (`Graph.closedNbhd`), `H[v]` the closed hub-neighbourhood (`Graph.closedHubNbhd`), a hub
a body of degree at least 3 (`Graph.PencilHub`). `def_d(G)` is the deficiency at `D`
(`G.deficiency` at `n = d`; `def_2` is the planar one, at `D = 3`). On the polar side N1–N3 read:
- **N1(b)**: `b_u, b_v` independent at every link; **N3(b)**: `b` independent on `N[v]` at every
  non-hub `v`;
- **C2(f)**: for every `v ∈ V(G)` and `S ⊆ H[v]` with `|S| ≥ 2`, `dim ⋂_{w∈S} Π_w ≤ f_d(G, v, S)`.

The candidates: **C1** = N1 ∧ N3; **C2-same** = C1 ∧ C2(`f_d = 4 − |S|`, every `d`); **C2-vac** = C1 ∧
(at `d = 3`) C2(`4 − |S|`), i.e. `f_d = 3` for `d ≥ 4`; **C2-gp** = C1 ∧ C2(the general-position
dimension of `|S|` 3-spaces through one vector, `1 + max(0, 2|S| − (|S| − 1)d)`); **direct** = the
direct transcription of brief §2.

---

## S1 — the consumer diff (session 1, 2026-10-30)

**Statement.** At `97a631ba` the brief's §1 matches the Lean hypothesis by hypothesis, read from the
definition bodies: `HasPencilPanelRealization` (`Pencil/Statement.lean`), `HasCoplanarPanelRealization`
(`AlgebraicInduction/Theorem55.lean`), `IsNondegPencilRealization`, `PencilNondegFeasible`,
`HasGenericPencilRealization`, `PencilPair`, `Graph.closedHubNbhd`, `Graph.closedNbhd`, `Graph.PencilHub`
(`Pencil/Motive.lean`), `HasPencilPlaneRealization`, `ExtensorThroughSubspace`, `dotPerp`,
`HasGradedDistinctPencilRealization`, `hasGradedDistinctPencilRealization_two_iff`
(`Pencil/Grade/Realization.lean`), `X0Gen` (`Pencil/X0.lean`), `hasGenericPencilRealization_of_IH` and
`x0Gen` (`Pencil/MainComponent/Statements.lean`). N2 is `∀ v ∈ V(G), LinearIndepOn K normal
(G.closedHubNbhd v)`, at every body, hub or not, and `closedHubNbhd v` contains `v` only when `v` is a
hub. The polarity lemma `hasPencilPanelRealization_mapExtensor_screwComplementIso` sends
`(F, normal, point)` to `(F.mapExtensor screwComplementIso, point, normal)`, and
`hasGradedDistinctPencilRealization_two_iff` applies it once in each direction, existentially.
(F1) is `HasPencilPlaneRealization.normal_mem_plane_of_mem_closedNbhd`, which needs no independence.

**One addition to §1.** The Lean derives the distinct conjunct from the generic one at one place:
`pencilPair_of_ncard_le_two` (`Pencil/Pair.lean`) gets `HasDistinctPencilRealization` on at most two
bodies from `hasGenericPencilRealization_of_ncard_le_two` through `hasDistinctPencilRealization_of_generic`.
It is a convenience (the generic witness there needs no feasibility), not a dependency of the
distinct conjunct's induction. No mismatch to report to the PI.

## S2 — Q0: what consumes the `P³` generic conjunct (session 1)

**Statement.** (i) In the Lean, at `97a631ba`, the declarations naming `IsNondegPencilRealization`,
`PencilNondegFeasible` or `HasGenericPencilRealization` all lie under `Molecular/Molecule/Pencil/`
(fifteen files, `grep -rlE` over `CombinatorialRigidity/`). Their consumers of the generic conjunct
are its own induction: route B (`hasGenericPencilRealization_of_IH`, which reads `hIH`'s first
conjunct at the smaller graphs), the cut arms (`Pencil/Pair.lean`, `Pencil/Pair2.lean`, the first
conjunct of `hIH` at both sides), and the headline statements `X0Gen`, `x0Gen`, `pencilPair_of_nonempty`,
`pencil_realization_theorem`. No file outside `Pencil/` names the API; `Nonvacuity.lean`'s two pencil
witnesses read the distinct conjunct (`.2.1`); `Molecule/Application.lean` (KT Corollary 5.7) does not
name the pencil. (ii) The blueprint: outside `pencil.tex`, `main-component.tex` and `pencil-d.tex` the
word "nondegenerate" means nonzero hinges (`generic-lift.tex`, `algebraic-induction.tex`), not this
notion. (iii) `formalization.yaml`: the `pencil_realization_theorem` description states the conjunct
("a nondegenerate one at that rank when it also has a nondegenerate pencil realization");
`pencilPair_of_nonempty`'s calls `x0Gen` a corollary. (iv) The molecule reading (panel = the plane of
an atom's bonds, point = its centre): N1 says bonded atoms have distinct centres, N3 that a non-hub
atom's centre and its neighbours' are not collinear, N2 that the bond planes of the hub atoms around
each atom are independent.

**What each change loses.** Dropping the conjunct from the `Pᵈ` headline loses no downstream Lean
consumer at `d = 3` or above: its only consumers are its own induction and the statements of (i), and
the one use by the distinct conjunct (S1) has a direct replacement. Keeping only N1 and N3 (C1)
changes the antecedent too: by S3 every graph with an admissible picture is C1-feasible in every `d`,
`K₄` included (S4), so C1's conjunct is "the distinct conjunct plus N3", not Phase 39's at `d = 3`.

## S3 — the C1 conjunct is a corollary of attaining (brief §4's first reading; session 1)

**Statement.** Let `q` be an admissible picture of `G` (`def:pencil-admissible-picture`), `z¹, …,
z^{d−2} ∈ L(q)`, `b = (q, z)` and `Π_v` the span of `b` on `N[v]`, `d ≥ 3`. Then `b` satisfies N1 and
N3. Hence wherever the general configuration of `G` attains in dimension `d`
(`def:pencil-d-x0-attains`), `G` has a C1-generic realization in dimension `d`: at every `d` on
Tier 0 (`thm:pencil-d-deficiency-two-le-three`), and at `d = 3` on the main component
(`thm:pencil-x0-coverage`).

**Proof.** N1 is `lem:pencil-d-config-realization`. On `N[v]`, `b_w = A_v(x_w, y_w, 1)` for one
injective linear `A_v : K³ → K^{d+1}` (that lemma's proof), so `b` is independent on `N[v]` iff the
homogeneous picture points are. A non-hub `v` has `|N[v]| ≤ 3` (its at most two neighbours and itself),
and admissibility puts three members of `N[v]` with independent homogeneous points in it, so
`|N[v]| = 3` and all of `N[v]` is independent: N3. An attaining configuration has the rank, and
`lem:pencil-d-config-realization` makes it a pencil realization with `Π` as stated. ∎

**Remark.** Admissibility needs `|N[v]| ≥ 3` at every body, so S3 is a main-component statement; the
reduction's other cases (cuts, few bodies) are not covered by it. At `d = 3` this is the first paragraph
of `lem:pencil-x0-conjunct-three`'s proof, as the brief says. Reading confirmed.

## S4 — `K₄` and the readings of `f_d` (brief §4's second reading; session 1)

**Statement.** Let `G = K₄`, `d ≥ 3`, and `(F, b, Π)` a pencil realization with N1. Then exactly one of:
(i) `dim span b = 3` and `Π_v = span b` for every `v`; (ii) `span b = L` has dimension 2, `L ⊆ Π_v`
for every `v`, all six hinges are multiples of one extensor, and the rank is at most `3D − 3`.
`def_d(K₄) = 0`, so the target is `3D`. Consequently, for a C2 candidate with `H[v] = V` at every
`v`, and `c_j := min f_d(K₄, ·, S)` over `|S| = j`:
- some `f_d(S) < 2`: `K₄` is infeasible (both cases have `dim ⋂_S Π_w ≥ 2`);
- all `f_d(S) ≥ 2` and some `f_d(S) < 3`: feasible only by (ii), so its conjunct is **false**;
- all `f_d(S) ≥ 3` (C1, C2-vac at `d ≥ 4`): feasible by (i), and the conjunct is true in every `d`
  (S3, as `def_2(K₄) = 0`, so `K₄` is on Tier 0 and its configurations are case (i)).
C2-same (`f = 4 − |S|`, so `f = 0` at `|S| = 4`) makes `K₄` infeasible in every `d`, as at `d = 3`.

**Proof.** `N[v] = V` at every `v`, so by (F1) `span b ⊆ Π_v`, of dimension at most 3, and at least 2
by N1. In case 3, `span b = Π_v`. In case 2, every pair `b_u, b_v` spans `L`, and every hinge is a
nonzero multiple of `C(b_u, b_v)` (`lem:pencil-d-point-configuration` (2)), the extensor of a basis
of `b_u^⊥ ∩ b_v^⊥ = L^⊥`, one subspace for all six pairs, so one extensor `C` up to scalars. The assignments `S_v = S₀ + t_v C` are
motions (each `S_u − S_v ∈ K·C`), a space of dimension `D + 4 − 1`, so the rank, `4D` minus the motion
dimension, is at most `3D − 3`. `def_d(K₄) = 0`: a partition into `p ≥ 2` parts of `K₄` crosses at
least `3(p − 1)` edges (`p = 2`: 3; `p = 3`: 5; `p = 4`: 6), so its value is
`D(p − 1) − (D − 1)·e(P) < 0` at `D ≥ 3`, and `{V}` has value 0. The three regimes: each `S ⊆ V`
has `⋂_S Π_w ⊇ L` (dim ≥ 2) in (ii) and `= span b` (dim 3) in (i). `def_2(K₄)`: the singleton
partition has value `3·3 − 2·6 < 0`, and as above every partition is nonpositive. Every admissible
picture of `K₄` has the four points not collinear, so `b = A(q̂)` with one injective `A` spans 3. ∎

**Remark.** The brief's reading holds with one correction: "forced by the shared points", read with the
realization's own span of shared `b`'s, allows case (i) and so keeps `K₄`'s conjunct true; the conjunct
fails only for an `f_d` that allows the meet `L` and forbids equal planes. C2-same and Phase 39 avoid
both by `|H[v]| ≤ 3`.

## S5 — two hubs with three common neighbours, polar form (brief §4's third reading; session 1)

**Statement.** Let `d ≥ 3`, `a ≠ b` hubs with common neighbours `x, y, z`, and `(F, b, Π)` a pencil
realization with `b_x, b_y, b_z` independent. Then `Π_a = Π_b = span(b_x, b_y, b_z)`. So every
candidate with `f_d(G, x, {a, b}) ≤ 2` (C2-same, C2-gp; Phase 39 at `d = 3`) rejects it, and rejects
every configuration over a picture with `q_x, q_y, q_z` not collinear: R-C fails there in every `d`.
At a realization with `dim(Π_a ∩ Π_b) ≤ 2` (C2-same, C2-gp), `b_x, b_y, b_z` are dependent: they lie
in `Π_a ∩ Π_b`.

**Proof.** `x, y, z ∈ N[a] ∩ N[b]`, so (F1) puts their `b`'s in `Π_a` and in `Π_b`, both of dimension
3; three independent vectors in both make them equal to their span. `{a, b} ⊆ H[x]`, as both are hubs
adjacent to `x`, so the candidate's `|S| = 2` condition at `x` bounds `dim(Π_a ∩ Π_b)`. Over a
picture, `(b_x, b_y, b_z) = A_a(q̂_x, q̂_y, q̂_z)` with `A_a` injective (S3's proof), independent iff
`q_x, q_y, q_z` are not collinear. ∎ Reading confirmed. (N1 does not separate `b_x, b_y`, which are
not adjacent; at `d ≥ 4` they may coincide, so "on a line" is not forced.)

## S6 — the steer in polar form (brief §4's fourth reading, row 22; session 1)

**Statement.** `lem:pencil-generic-steer`'s parametrization takes the hub normals `m_h` as free
parameters and sets `p_v = y₁ × y₂ × y₃`, the vectors `m_w` for `w ∈ H[v]` completed by auxiliaries
(`main-component.tex`, the proof's first paragraph). In polar form, with `Π_h = m_h^⊥`, it puts
`b_v` in `⋂_{w∈H[v]} Π_w`. At free (general) `Π`'s that meet has dimension
`max(0, 3j − (j − 1)(d + 1))` for `j = |H[v]|`: `j = 2` gives `max(0, 5 − d)`, `j = 3` gives
`max(0, 7 − 2d)`. So the free parametrization gives a nonzero `b_v` at every body in `d = 3`; at `d = 4`
exactly at the bodies with `|H[v]| ≤ 2`; at `d ≥ 5` exactly at those with `|H[v]| ≤ 1`. The one-ear
step's `b_x ∈ Π_a ∩ Π_b`, for non-adjacent hubs `a, b` with no common neighbour in `G − x`, has the
same `j = 2` count, zero from `d = 5` on.

**Proof.** `j` general 3-spaces of `K^{d+1}` meet in the expected dimension `max(0, 3j − (j−1)(d+1))`.
The steer's cross product is orthogonal to its three factors, so polar `b_v` lies in every `Π_w`,
`w ∈ H[v]`. In the one-ear lemma, `a, b` are not adjacent (else `x a b` is a triangle with two hubs,
infeasible, `lem:pencil-feasible-hub-conditions`). ∎

**Remark.** Row 22's "steer fails for `d ≥ 4`" is exact at `d ≥ 5`; at `d = 4` it fails only where some
`|H[v]| = 3` (a hub with two hub neighbours). Every realization still has `b_v ∈ ⋂_{H[v]} Π_w` (F1),
so the polar condition is necessary in every `d`; what fails is that free hub planes reach it.
Reading confirmed, with that refinement.

## S7 — the candidates against (a), (b), (c) and the embedding (session 1)

**Statement.** With `G` finite:
| candidate | (a) at `d = 3` | (b) N1 on `b` | (c) open | survives `ι` (`d′ ≤ d`) |
|---|---|---|---|---|
| C1 | fails: `K₄` (S2, S4) | yes | yes | yes |
| C2-same | yes | yes | yes | yes |
| C2-vac | yes | yes | yes | yes |
| C2-gp (with `|H[v]| ≤ 3`) | yes | yes | yes | fails at adjacent hubs, `d ≥ 4` |
| direct | existentially only | no | yes | fails: N1 on flats is void from `d = 4` |

**Proof.** (a) At `d = 3` put `Π_v = q_v^⊥`, `q_v ≠ 0`. For finite `S`, `⋂_{w∈S} q_w^⊥ =
(span q_S)^⊥` has dimension `4 − dim span q_S`, which is `≤ 4 − |S|` iff `q` is independent on `S`.
Over all `S ⊆ H[v]` with `|S| ≥ 2`, with `q_w ≠ 0` from the realization, this is `LinearIndepOn K q
(H[v])`: N2 of the polar framework. N1 and N3 on `b` are N1 and N3 of the polar framework, whose
points are `b`. So `Nondeg_3(G, F, b, q^⊥)` gives `IsNondegPencilRealization G F′ q b` by
`hasPencilPlaneRealization_two_iff` and the polarity lemma, and conversely a nondegenerate `(F′, q, b)`
gives `Nondeg_3(G, F′.mapExtensor σ, b, q^⊥)`, at the same rank (`finrank_span_rigidityRows_mapExtensor`):
the form of `hasGradedDistinctPencilRealization_two_iff`. C2-gp's `1 + max(0, 2|S| − (|S|−1)·3)` is
`4 − |S|` for `|S| ≤ 3`; the clause `|H[v]| ≤ 3` supplies `|S| = 4`, where the formula gives 1. C1 has
no condition on `Π` and admits `K₄` (S4 (i)), which `PencilNondegFeasible` excludes (`|H[v]| = 4`). The
direct transcription is Phase 39's on one framework (normals `b`, points `q`), so it agrees as an
existential statement through the rank-preserving polarity, not realization by realization.
(b) Each C2 and C1 contains N1 on `b`; the direct one puts N1 on the flats `Π^⊥`.
(c) N1, N3: a nonzero minor of `[b_u, b_v]`, of `b` on `N[v]`. C2: `⋂_S Π_w = (Σ_S Π_w^⊥)^⊥`, so
`dim ⋂_S Π_w ≤ m` iff the stacked bases of the `Π_w^⊥` have rank `≥ d + 1 − m`, a nonzero minor.
(Embedding) `ι` is injective linear, so it keeps independence and `ι(⋂ Π_w) = ⋂ ιΠ_w`: every span and
meet keeps its dimension. A C2 condition survives iff `f_d ≥ f_{d′}` on the same `(G, v, S)`: true for
C2-same (equal) and C2-vac (`f_d = 3` at `d ≥ 4`); false for C2-gp, whose `f_4 = 1` at `|S| = 2`
while a hub `v` adjacent to a hub `w` has `dim(Π_v ∩ Π_w) ≥ 2` in every `d` (F2), so every `d = 3`
realization with adjacent hubs leaves C2-gp when embedded. The direct N1 asks `Π_u^⊥ ∩ Π_v^⊥ = 0`, and
by (F2) the two `(d − 2)`-dimensional flats meet in dimension `≥ d − 3 ≥ 1` inside the hinge's span. ∎

**Remark.** C2-gp at `d ≥ 4` forbids adjacent hubs outright, and forces the common neighbours of two
non-adjacent hubs onto one point (`Π_w ∩ Π_{w′} = ⟨b_v⟩`): a control, not a contender.

## S8 — the generic conjunct transfers from `P³` where the deficiency is stable (session 1)

**Statement.** Let `Nondeg_d` be C2-same or C2-vac, `d ≥ 3`, `K` infinite, `G` finite, simple and
connected with `PencilNondegFeasible K G` and `def_3(G) = def_d(G)` (for instance `def_2(G) ≤ 3`,
`lem:deficiency-stable` at `d′ = 3`). Then `Generic_d(G)`: a `Nondeg_d` realization in dimension `d`
whose rows span `D(|V(G)| − 1) − def_d(G)`.

**Proof.** `pencilPair_of_nonempty` gives `HasGenericPencilRealization K 3 G`: `(F′, n, p)`
nondegenerate, rank `6(|V| − 1) − def_3(G)`. By S7 (a), `(F′.mapExtensor σ, p, n^⊥)` is a `Nondeg_3`
realization at that rank. `lem:pencil-d-embed-realization` (`G` connected) makes
`(φF, ιp, ιn^⊥)` a pencil realization in dimension `d` of rank `D(|V| − 1) − def_3(G) =
D(|V| − 1) − def_d(G)`, and S7's embedding column keeps `Nondeg`. ∎

**Remark.** This is Tier 0 for the generic conjunct, under any candidate that survives the embedding
and agrees at `d = 3`. Its gap is the content range, `def_3(G) > def_d(G)`, and (for C2-vac) the graphs
that are C2-vac-feasible but not `P³`-feasible, `K₄` among them (S4: there C2-vac's conjunct holds).

## S9 — under C2-same, feasibility does not depend on `d` (session 1; claimed, one reader)

**Statement.** Let `K` be infinite, `G` finite and `d ≥ 3`. `G` has a C2-same realization in
dimension `d` iff `PencilNondegFeasible K G`.

**Proof.** (⇐) S7 (a), then the embedding (S7, S8's proof without the rank).
(⇒) Let `(F, b, Π)` be C2-same in dimension `d ≥ 4`. We find a linear surjection `π : K^{d+1} → K⁴`
keeping C2-same; then `(πb, πΠ)` with the hinges `C(πb_u, πb_v)` is a C2-same realization in dimension
3 (`lem:pencil-d-point-configuration` (1): N1 survives, and `b_w ∈ Π_v` gives `πb_w ∈ πΠ_v`), and
S7 (a) gives a nondegenerate one. Each requirement below is a nonvanishing minor in `π`'s entries, so
it suffices that each holds at some `π`; then a common `π` exists (`K` infinite). Write
`π` as a composite of projections from one point at a time, `P^m ⇢ P^{m−1}`, `m = d, …, 4`; a
property kept by a general point projection at each stage is kept by some `π`.
- N1, N3, `dim πΠ_v = 3`: independence of at most three vectors, kept when the centre avoids their
  span (a proper subspace, `m ≥ 4 > 3`).
- `|S| = 2` (`Π_w ≠ Π_{w′}`): `Π_w + Π_{w′}` has dimension `≥ 4`, and a projection from a centre off
  it, or onto all of `K^m` from it, keeps a sum of dimension `≥ 4`, so the images differ.
- `|S| = 3`: pass to `P^{m−1}_b := P(K^{m+1}/b)` (the centre off `b`). There `Π_i` are lines `L_i`,
  pairwise distinct, with no common point. The projection from `c` makes the images concurrent iff a
  line through `c` meets all three `L_i` (a transversal), and makes two images equal iff `c` lies in
  the plane of two meeting `L_i`. The transversals of three pairwise distinct lines with no common point
  sweep a set of dimension at most 2: if `L_1, L_2` are skew, those meeting both form a 2-dimensional
  family and meeting `L_3` cuts it (or `L_3` lies in a quadric of transversals, at `m − 1 = 3`, swept
  set a surface); if `L_1, L_2` meet at `y`, the transversals lie in the plane `⟨y, L_3⟩` or the plane
  `⟨L_1, L_2⟩`. So for `m − 1 ≥ 3` a general centre keeps both properties, down to `P²`, where three
  pairwise distinct lines with no common point are three planes of `K⁴` with independent normals. ∎

**Remark (what it buys).** Under C2-same, `Feasible_d = PencilNondegFeasible` in every `d`, so the
`Pᵈ` generic conjunct reads `G.Simple → PencilNondegFeasible K G → Generic_d(G)`, with Phase 39's
antecedent verbatim. With S8, only its content range (`def_3 > def_d`) is open. The `|S| = 3` step's
transversal count is the one point a reader should check; a driver control is S10's task.

## S10 — the candidates at general and collinear pictures; S9's control (session 1)

**Statement (measured).** `python3 notes/attacks/nondeg/drivers/nondeg.py --seed 1` draws, per graph
of the brief's population and `d = 3, 4, 5`, a configuration over a general picture (`gen`) and, where
two hubs share three or more neighbours, one over a picture putting those neighbours on a line
(`col`, S5's locus); `ring6` (24 bodies) is listed, not drawn (`MAX_N`; it has `|H[v]| = 4`).
- **Every draw satisfies C1 and reaches `D(n − 1) − def_d(G)`** (57 draws, 12 graphs): C1's, so
  C2-vac's, generic conjunct is certified at these graphs in `d = 4, 5` (and C1's at `d = 3`), `K₄`
  included (S4 (i)).
- **C2-same fails at every general picture of `K_{2,3}`, `θ(2,2,2,k)` (`k = 5..10`) and D's witness**,
  in every `d` (S5; D's witness's general configurations are planar, `dim L = 3`), and **holds at every
  collinear picture**, at the deficiency rank (21 draws). At `θ(2,2,k)` (two hubs, two common
  neighbours) the general picture is already C2-same (9 draws), and `dim L` does not jump.
- `dim L(q)` at general against collinear pictures: `K_{2,3}` 3 / 4, `θ(2,2,2,k)` `k` / `k + 1`.
- **S9's control:** each of the 20 C2-same draws at `d ≥ 4` projects to a C2-same realization at `d = 3`
  under one of `PROJ_TRIES = 3` seeded integer `4 × (d+1)` matrices (exit status 0).
- C2-gp holds at `d = 3` wherever C2-same does and at no draw with `d ≥ 4` (S7's remark).
Population and caps: the 12 graphs drawn, one draw per cell and picture, seed 1, `COORD = 1000`,
`PROJ_COORD = 50`; a rank below target would certify nothing, and none occurred.

## S11 — Q3 on the population: C2-same reaches the deficiency rank at every feasible graph (session 1)

**Statement (measured; each `=` cell an exact certificate).** `python3
notes/attacks/nondeg/drivers/nondeg.py --steer --seed 1` draws, per graph, one point of the polar
steer family at `d = 3` (the driver's docstring), writes it as a configuration `(q₀, z¹)`, and at
`d = 3, 4, 5` redraws the `d − 2` heights in `L(q₀)`. On the 13 graphs of `graphs()` (`K₄`, `K_{2,3}`,
`θ(2,2,2,k)` for `k = 5..10`, `θ(2,2,k)` for `k = 4, 7, 10`, D's witness, `ring6`): `K₄` and `ring6`
have `|H[v]| = 4` (infeasible in every `d` under C2-same, S9 and `lem:pencil-feasible-hub-conditions`);
at the other 11, in each of `d = 3, 4, 5`, the draw satisfies C2-same and its rank equals
`D(n − 1) − def_d(G)` (33 cells). As the target bounds every realization
(`lem:relative-deficiency-rank-bound`), each is an exhibited C2-same realization at the deficiency
rank: C2-same's generic conjunct holds at these graphs in `d = 3, 4, 5`. `dim L(q₀)` is one above
the general-picture value where S10 measured both (`K_{2,3}`: 4 against 3; `θ(2,2,2,5)`: 6 against 5;
D's witness: 4 against 3): the nondegenerate realizations lie over special pictures there.
In particular `θ(2,2,2,10)` at `d = 4` (130/130) and `d = 5` (195/195), where `def_3 = 4 > def_4 = 0`
(content range; T4's forced miss was of `G − x` on the locus `Π_a = Π_b`, which C2-same excludes),
and D's witness is `PencilNondegFeasible` (the brief's "feasibility unchecked"), by the `d = 3` row and
S7 (a). Population, caps: the 13 graphs above, one draw per cell, seed 1, `COORD = 1000`.

## S12 — C1 and C2-vac feasibility (session 1)

**Statement.** Over an infinite `K`, every finite loopless `G` has a C1 realization in every `d ≥ 3`;
so C2-vac's `Feasible_d` is "loopless" for `d ≥ 4`, and its conjunct there asks every simple `G` for a
realization at the deficiency rank with N1 and N3.

**Proof.** Put every `b_v` in one 3-space `P`, pairwise independent and any three independent (general
position in `P`, `K` infinite), and `Π_v = P`. Then `b_w ∈ Π_v` always, so this is a pencil
realization (`lem:pencil-d-point-configuration` (1), N1 from looplessness); a non-hub has at most
three members in `N[v]`, independent. ∎ (At the deficiency rank this planar realization is the flat
configuration, rank `D(n−1) − def_2`-type; S3 and the coverage supply the rank at the main component.)

## S13 — R-L: lifting over a nondegenerate picture (session 1; claimed, one reader)

**Statement.** Let `K` be infinite, `G` finite, `d ≥ 3`, and `(b⁰, Π⁰)` a C2-same realization in
dimension 3 with `b⁰(N[v])` spanning `Π⁰_v` at every `v`. After a general linear automorphism of
`K⁴` it is the configuration `(q₀, z¹)` of an admissible picture `q₀` with `z¹ ∈ L(q₀)`. If some
`z ∈ L(q₀)^{d−2}` gives `(q₀, z)` the rank `D(n − 1) − def_d(G)`, then `Generic_d(G)` under C2-same.

**Proof.** A general automorphism keeps C2-same, N1 and the spans, puts every `b⁰_v` off `w = 0` and
every `Π⁰_v` off the point `e_z`. Projecting from `e_z` is then injective on each `Π⁰_v`, so the
picture points of `N[v]` span (admissible), and the height `z¹` is affine on each `N[v]`, so
`z¹ ∈ L(q₀)`. Over `q₀`, every `z ∈ L(q₀)^{d−2}` gives a pencil realization with N1
(`lem:pencil-d-config-realization`), with `Π_v` the span of three members of `N[v]` with non-collinear
picture points, so with Plücker coordinates polynomial in `z`. C2-same is then open on the vector space
`L(q₀)^{d−2}` (S7 (c)) and holds at `(z¹, 0, …, 0)`, whose configuration is `ι` of `(b⁰, Π⁰)` (S7,
the embedding). The rank is lower semicontinuous and reaches the target at `z`. A common point of the
two nonempty open sets exists. ∎

**Remark.** S11's `--steer` cells are exactly this hypothesis, checked at a general point of the steer
family, which parametrizes every nondegenerate realization (`lem:pencil-generic-steer`).

## S14 — C2-same pulls back along projections injective on the planes (session 1)

**Statement.** Let `(b, Π)` be a pencil realization in dimension `d` and `p : K^{d+1} → K^{d′+1}`
linear and injective on every `Π_v`. If `(pb, pΠ)` satisfies C2-same (resp. N1, N3), so does `(b, Π)`.
In particular a configuration `(q, z¹, …, z^{d−2})` satisfies C2-same whenever one truncation
`(q, z^i)`, a configuration in dimension 3, does.

**Proof.** `p` injective on `Π_w` keeps independence inside it, and maps `⋂_S Π_w` injectively into
`⋂_S pΠ_w`, so `dim ⋂_S Π_w ≤ dim ⋂_S pΠ_w ≤ 4 − |S|`; N1 and N3 pull back as independence of images
forces independence. For a configuration, the map keeping `(x, y, z^i, w)` restricts on `Π_v = A_v(K³)`
to `(ξ, η, ω) ↦ (ξ, η, a^iξ + c^iη + e^iω, ω)`, injective. ∎

**Corollary (case (i) of route B, in every `d`).** Let `G` satisfy the standing hypotheses of
`sec:main-component`, be `PencilNondegFeasible`, and have no planar-rigid set. If the general
configuration of `G` attains in dimension `d` (`def:pencil-d-x0-attains`), then `Generic_d(G)` under
C2-same. Proof: `thm:pencil-x0-base-generic`'s proof gives, over a general picture `q`, a nonempty
open set of `z¹ ∈ L(q)` with `(q, z¹)` nondegenerate, so C2-same in polar form (S7 (a)); by S14 every
`z ∈ L(q)^{d−2}` with first height there is C2-same, a nonempty open set, which meets the attaining
heights. So off the planar-rigid case C2-same's conjunct costs no more than the coverage, as C1's (S3).

## S15 — the reduction's arms under C2-same in `Pᵈ`: two lift, the cut edge needs a carrier (session 1)

**Statement.** Let `d ≥ 3`, `G` finite and simple, `D = C(d+1, 2)`, and suppose `Generic_d` (C2-same)
at every simple feasible graph on fewer bodies. (α) On at most two bodies `Generic_d(G)` holds outright.
(β) If `V(G) = V₁ ⊔ V₂` with no edge between and both nonempty, `Feasible_d(G)` gives `Generic_d(G)`.
(γ) If `uv` is the only edge between `V₁ ∋ u` and `V₂ ∋ v`, `|V₁|, |V₂| ≥ 2`, and `G₁⁺ = G[V₁ ∪ {v}]`,
`G₂⁺ = G[V₂ ∪ {u}]` have generic realizations whose glued union (below) is C2-same, it has rank
`D(n − 1) − def_d(G)`. The sides are feasible when `G` is (S9 and the `P³` arm's feasibility step).

**Proof.** (α) One body: any `b_v ≠ 0` and `Π_v ∋ b_v`, rank `0 = D·0 − 0`. Two bodies and an edge:
`b_u, b_v` independent, both planes through them; N3 is N1; rank `D − 1 = D − def`, `def = 1`. No edge:
rank `0`, `def = D`. (β) A part meeting both sides can be split without crossing an edge, raising the
value by `D`, so `def(G) = def(G₁) + def(G₂) + D`; the restriction of a C2-same realization of `G` to a
side is C2-same (closed neighbourhoods and degrees are unchanged), so the sides are feasible; generic
realizations of the sides, side by side, are C2-same (every condition is local to a side) and their
ranks add to `D(n − 1) − def(G)`. (γ) Glue by a linear automorphism `g` of side 2 taking its `b_u, b_v`
to side 1's (lines up to scale); the hinge `b_u ∨ b_v` is shared, `Π_u` comes from side 1 and `Π_v`
from side 2. A combination of rows supported on `{u, v}` lies in `uv`'s rows (the only rows at `v` in
`G₁⁺`), so `rank G = rank G₁⁺ + rank G₂⁺ − (D − 1)`. A cut edge gives `def(G) = def(G₁) + def(G₂) + 1`,
and `def(G_i⁺) = def(G_i) + 1` (the pendant body), so the targets satisfy `t(G) = t(G₁⁺) + t(G₂⁺) − (D − 1)`. ∎

**Where (γ) stops.** The glued union is C2-same only under open conditions across the cut (at `H[u] ∋ v`
when `v` is a hub of `G`, and symmetrically), on which a general `g` fixing the two points does most of
the work, but also at a hub `u` of `G` whose side `G₁⁺` has it of the same degree only because `v` is
included. The pendant arm (`V₂ = {v}`), where `u` may stop being a hub in `G − v`, needs the generic
realization of `G − v` to satisfy `G`'s conditions at `u`: two open conditions, one from the induction
(the rank) and one from a nondegenerate realization of `G` (S9), to be met at one point. In `P³` that
is `lem:pencil-generic-steer` (b), through the steer's irreducible parametrization; in `Pᵈ` it needs an
irreducible carrier of the C2-same realizations, which the steer no longer gives (S6). S13's family over
a general point of the `P³` steer family is a candidate carrier.

## S16 — Q2/Q3 on the `--d4` population (session 1)

**Statement (measured; each `=` cell an exact certificate).** `python3
notes/attacks/nondeg/drivers/nondeg.py --steer --pop d4 --seed 1` runs S11's draw on the 36 simple
graphs of `strata.py`'s `GRAPHS4` (its two multigraphs `2C4`, `2C5` left out, as the conjunct asks
`G.Simple`). 19 are infeasible by `lem:pencil-feasible-hub-conditions`, in every `d` under C2-same (S9):
`|H[v]| ≥ 4` at `K₄, K₅, K_{3,3}, W₅, W₇`, the prism, `ringK4x3`, `rnd8-11`, `rnd9-13`, the octahedron,
`strip8`, the cube and the Petersen graph; a triangle with two hubs at `rnd9-12`, the diamond,
`C6ears`, `triring4`, `C11ear`, `C9ears3`. At the other 17 (`C6`–`C9`, `C11`, `C12`, `K_{2,3}`, `K_{2,5}`,
the bowtie, `θ(3,3,3)`, `θ(2,3,3,3)`, `θ(4,4,4)`, `K23+1ear`, `K23+2ear`, `rnd8-10`, `friend3`,
`C5-C5`), all 51 cells at `d = 3, 4, 5` satisfy C2-same and reach `D(n − 1) − def_d(G)`. `C5-C5` has a
cut edge, so the certificate covers a non-main-component graph too. Population and caps: these 36
graphs, one draw per cell, seed 1, `COORD = 1000`. With S11: every feasible graph of the brief's
population and of `GRAPHS4` (27 distinct graphs, `K_{2,3}` in both; 84 cells drawn) has a C2-same generic realization in `d = 3, 4, 5`;
no candidate miss was found under that cap.

## S17 — the candidates table after session 1 (the brief's §6 deliverable, in progress)

| | (a) | (b) | (c) | embedding | `Feasible_d`, `d ≥ 4` | Q3 on the population | Q4 route |
|---|---|---|---|---|---|---|---|
| C1 | no (S4) | yes | yes | yes (S7) | loopless (S12) | rank at all 12 drawn (S10) | coverage at the main component (S3); N3 in the reduction |
| C2-same | yes (S7) | yes | yes | yes (S7) | `PencilNondegFeasible` (S9) | 27 feasible graphs, 84 cells, no miss (S11, S16) | coverage off planar-rigid sets (S14); Tier 0 (S8); else R-L (S13), open (S15) |
| C2-vac | yes | yes | yes | yes | loopless (S12) | as C1 at `d ≥ 4` | as C1 at `d ≥ 4`; Phase 39 at `d = 3` |
| C2-gp | yes | yes | yes | no (S7) | no adjacent hubs (S7) | fails C2 at every `d ≥ 4` draw (S10) | retired (`log.md`) |
| direct | existential | no | yes | no (S7) | edgeless (S7, F2) | — | retired (`log.md`) |
| C3 | — | — | — | — | — | — | S13's family `{q₀} × L(q₀)^{d−2}` over a general `P³` steer point is the C3 the route uses |

**Verdict so far.** Q0 settled (S2). Q1: C2-same and C2-vac both meet (a)–(c); C2-same is the one whose
feasibility is Phase 39's in every `d`. Q2: settled for C2-same by S9, for C1/C2-vac by S12. Q3: no miss
on the population under C2-same, every cell an exact certificate (caps in S11, S16). Q4: C2-same's
conjunct costs the coverage plus an irreducible carrier for graphs with a planar-rigid set and for the
pendant and cut-edge arms (S15); C2-vac's costs the coverage plus N3 through the reduction (a reading,
not checked arm by arm).
