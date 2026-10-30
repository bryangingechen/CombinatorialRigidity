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

---

Session 2 (2026-10-30): C2-same is the definition (the PI's word, brief header). Consumer diff
re-run at `5c9948e2`: the Lean of S1's declarations is unchanged since `97a631ba` (only
`Induction/SparseDeficiency.lean` moved, COUNT-A's `n`-general siblings, none named by the brief);
the definition bodies and `hasGenericPencilRealization_of_IH` re-read, no mismatch. Below,
`t_d(G) := D(|V(G)| − 1) − def_d(G)`, `m := d − 3`, and "general" means off the zero set of a
polynomial that is nonzero somewhere on the set in question.

## S18 — the carrier: lifts over a nondegenerate `P³` realization, and the motive `RL_d`

**Setting.** `K` infinite, `G` finite and simple. `𝒩(G)` is the set of C2-same realizations in
dimension 3: `(b⁰, Π⁰)`, `b⁰_v ∈ K⁴ ∖ 0`, `Π⁰_v = n_v^⊥` a 3-space, `b⁰_w ∈ Π⁰_v` for `w ∈ N[v]`,
N1, N3, C2(`4 − |S|`). By S7 (a) and `lem:pencil-d-agrees-three` these are Phase 39's nondegenerate
realizations with normals `n` and points `b⁰`, the hinge of `uv` the line through `b⁰_u, b⁰_v`.

**(i) An irreducible carrier at `d = 3`.** `lem:pencil-generic-steer`'s parametrization (its
proof's first three paragraphs) is a polynomial map `σ_G` from an affine space `Γ(G)` to points and
normals: hub normals are parameters, `b⁰_v` is the triple product of `H[v]`'s normals completed by
auxiliary vectors, a non-hub's normal the product of its closed neighbourhood's points (completed
by auxiliaries when `|N[v]| ≤ 2`: my reading of "any nonzero vector orthogonal to their points").
Nondegeneracy of `σ_G(s)` is a finite list of nonvanishing conditions, so holds on an open
`U(G) ⊆ Γ(G)`, nonempty iff `G` is feasible; and every member of `𝒩(G)` is some `σ_G(s)` up to a
nonzero scalar at each point and normal (the steer's converse). "A general point of `𝒩(G)`" means
`σ_G(s)` for general `s ∈ Γ(G)`; a polynomial condition on points and normals, homogeneous in each,
is scale-invariant and so is read on `𝒩(G)` itself.

**(ii) The lift space.** For `r⁰ = (b⁰, Π⁰) ∈ 𝒩(G)` let `L¹(r⁰)` be the space of `(ζ, φ)`,
`ζ ∈ K^{V(G)}` and `φ_v` a linear functional on `Π⁰_v`, with `ζ_w = φ_v(b⁰_w)` for every `v` and
`w ∈ N[v]`. At `λ = (λ¹, …, λ^m) ∈ L¹(r⁰)^m` the lift `R(r⁰, λ)` has `b_v = (b⁰_v, ζ¹_v, …, ζ^m_v)`
and `Π_v = {(p, φ¹_v(p), …, φ^m_v(p)) : p ∈ Π⁰_v}` in `K^{d+1}`. The trivial lifts `ζ_v = ψ(b⁰_v)`,
`φ_v = ψ|_{Π⁰_v}` (`ψ ∈ (K⁴)*`) lie in `L¹(r⁰)`. **Claim:** every `R(r⁰, λ)` is a C2-same
realization in dimension `d` with hinges `C(b_u, b_v)`, and its rank depends on `b` alone.
*Proof.* `Π_v` is a graph over `Π⁰_v`, so 3-dimensional; `b_w ∈ Π_v` for `w ∈ N[v]` is the
defining equation; `b_u, b_v` are independent since their images `b⁰_u, b⁰_v` are. So
`lem:pencil-d-point-configuration` (1) makes it a pencil realization with the panel-hinge rows of
`b`. Forgetting the last `m` coordinates is injective on each `Π_v` and maps `(b, Π)` onto
`(b⁰, Π⁰)`, which is C2-same; S14 pulls C2-same back. ∎

**(iii) Pendant planes do not matter.** At a body with `|N[v]| ≤ 2` (degree at most one) every
choice of `(ζ_w)_{w ∈ N[v]}` extends to some `φ_v` (at most two conditions at independent vectors of
the 3-space `Π⁰_v`), and `Π⁰_v` enters no C2 condition (`H[·]` holds hubs only) and no N3 condition
of another body. So whether `r⁰ ∈ 𝒩(G)`, the `ζ`-parts of `L¹(r⁰)` and the ranks of the lifts do
not depend on the planes of bodies of degree at most one.

**(iv) The motive.** `RL_d(G)`: at a general `r⁰ ∈ 𝒩(G)` a general `λ ∈ L¹(r⁰)^m` gives `R(r⁰, λ)`
rank `t_d(G)`. By (ii), `RL_d(G)` gives `Generic_d(G)` under C2-same. **`RL_3` holds at every simple
feasible `G`** (`m = 0`): `pencilPair_of_nonempty` gives a generic realization, `σ_G(s*)` up to
scalars, which keep the rank (the steer's proof); a `t_3(G)`-minor of the rows is a polynomial in
`s` nonzero at `s*`, and `t_3(G)` bounds every rank (`lem:relative-deficiency-rank-bound`).

**(v) One witness suffices, and the pointwise form.** Let `L̃(r⁰)` allow `φ̃_v ∈ (K⁴)*`; then
`L¹(r⁰) = L̃(r⁰)/⊕_v K·n_v`, and `L̃` is the kernel of a matrix `A(b⁰)` polynomial in the points
alone: the planes enter only the quotient, so the `ζ`-parts and the lifts' ranks are functions of `b⁰`. Let `N` be the least `dim L̃` on `𝒩(G)`. Suppose some `r* ∈ 𝒩(G)` with `dim L̃(r*) = N` and
some `λ*` give `R(r*, λ*)` rank `t_d(G)`. Fix a nonzero maximal minor `M` of `A(r*)`; where
`M ≠ 0` on `𝒩(G)`, `rank A ≥ rank A(r*)` and `dim L̃ ≥ N` force `dim L̃ = N`, and Cramer's rule on
`M`'s rows gives a kernel basis `k_1, …, k_N` polynomial in `b⁰` after scaling by `M`. With
`λ = Σ c_i k_i`, a `t_d(G)`-minor of `R`'s rows is a polynomial `P(r, c)` with `P(r*, c*) ≠ 0`; let
`Q_G` be `M` times a `c`-coefficient of `P` nonzero at `r*`, a polynomial in the points alone. **Every `r⁰ ∈ 𝒩(G)` with
`Q_G(r⁰) ≠ 0` has its general lift at rank `t_d(G)`**, and `Q_G` is nonzero at `r*`, hence at a
general point of `𝒩(G)` (pull back along `σ_G`; `Γ(G)` is irreducible). So `RL_d(G)` holds as soon
as one such witness exists. Conversely `RL_d(G)` supplies such a `Q_G` (take `r*` general). ∎

**Remark (S13's form).** When `r⁰` is the configuration `(q₀, z¹)` over an admissible picture, a
lift is `ζ ∈ L(q₀)` (each `φ_v` is the affine function of `ζ` on `N[v]`, the planes being graphs
over the picture), so `L¹(r⁰) = L(q₀)` and `RL_d(G)` is S13's hypothesis at the picture of a general
point of `𝒩(G)`. S11's and S16's `--steer` cells are draws of `R(r⁰, λ)`: their `=` cells certify
`Generic_d`, not `RL_d` (a draw does not certify `dim L̃ = N`).

## S19 — the transfer: a general lift of `G` restricts to a general lift of `H`

**Statement.** Let `G` be simple and feasible, `d ≥ 4`, and `H = G[V′]` with `V′ ≠ ∅`. Restriction
`ρ` keeps the points and planes of the bodies of `H`; at `r⁰ ∈ 𝒩(G)`, `ρ(r⁰)` is a pencil
realization of `H` in dimension 3, and `λ ↦ λ|_H` maps `L¹_G(r⁰)` into `L¹_H(ρ r⁰)` (`N_H[v] ⊆
N_G[v]`, and `Π⁰_v` contains `b⁰(N_G[v])`). Suppose
- **(T1)** there is a polynomial `E` in `H`'s points and normals, homogeneous in each and nonzero
  somewhere on `𝒩(H)`, such that every `r_H ∈ 𝒩(H)` with `E(r_H) ≠ 0` agrees with `ρ(r)` for some
  `r ∈ 𝒩(G)`, except perhaps at the planes of bodies of degree at most one in `H`;
- **(T2)** at a general `r⁰ ∈ 𝒩(G)`, the `ζ`-part of `λ ↦ λ|_H` maps `L¹_G(r⁰)` onto that of
  `L¹_H(ρ r⁰)`.

Then `H` is feasible, and if `RL_d(H)`, at a general `r⁰ ∈ 𝒩(G)` a general `λ ∈ L¹_G(r⁰)^m` gives
`R(r⁰, λ)|_H = R(ρ r⁰, λ|_H)` the rank `t_d(H)`.

**Proof.** Feasibility: `E ≠ 0` somewhere on `𝒩(H)`, so `𝒩(H) ≠ ∅`. Take `Q_H` from S18 (v) and
`s′ ∈ U(H)` with `(E·Q_H)(σ_H s′) ≠ 0` (`Γ(H)` is irreducible and both are nonzero somewhere on
`σ_H(U(H))`). By (T1), `σ_H(s′)` agrees with `ρ(r)` for some `r ∈ 𝒩(G)` off the planes of bodies of
degree at most one, and `r = σ_G(s)` up to scalars. By S18 (iii) and homogeneity,
`ρσ_G(s) ∈ 𝒩(H)` and `Q_H(ρσ_G(s)) ≠ 0`, as `Q_H` reads the points only (S18 (v)). Both conditions on `s` are open in `Γ(G)` (each a nonvanishing of a
polynomial in `s`, `ρσ_G` being polynomial), and hold at `s`, so at a general `s`. There the set of
`ζ`-parts of `λ_H ∈ L¹_H(ρσ_G s)^m` whose lift attains is a nonempty open subset of a vector space,
and its preimage under the linear surjection of (T2) is a nonempty open subset of `L¹_G(σ_G s)^m`. ∎

**How a step uses it.** If also `R(r⁰, λ)` has rank at least `rank R(r⁰, λ)|_H + c` at a general
lift and `t_d(G) ≤ t_d(H) + c`, then `R(r⁰, λ)` attains `t_d(G)` at a general point of `G`'s family
(where `dim L̃_G` is least, an open condition met at a general `r⁰`), and S18 (v) gives `RL_d(G)`.
For two restrictions at once (S21) apply the proof to each and intersect the open sets.

## S20 — `RL_d` at few bodies, at the triangle, and across a disconnection

**Statement.** Let `d ≥ 4` and `G` simple and feasible. (α) If `|V(G)| ≤ 2`, `RL_d(G)`. (τ) If `G`
is a triangle, `RL_d(G)`. (β) If `V(G) = V₁ ⊔ V₂`, both nonempty, with no edge between, and
`RL_d(G[V_i])` for `i = 1, 2`, then `RL_d(G)`.

**Proof.** In each case every lift is checked directly (S18 (v): one witness at a point where
`dim L̃` is least suffices, and here the rank is the same at every lift, so at that point too).
(α) One body: rank `0 = t`. Two bodies and an edge: N1 keeps `b_u, b_v` independent at every lift,
rank `D − 1`, and `def_d = 1` (the singletons: `D − (D − 1)`), so `t = D − 1`. No edge: rank `0`,
`def_d = D`, `t = 0`. (τ) No body is a hub, so N3 keeps `b_1, b_2, b_3` independent at every lift;
the hinges `b_i ∧ b_j` are three joins of independent vectors, independent in `Λ²`, so the cycle is
rigid (`lem:cycle-realization-rigid`'s argument: a motion has `t₁₂C₁₂ + t₂₃C₂₃ + t₃₁C₃₁ = 0`), rank
`2D`; `def_d = 0` (singletons `2D − 3(D − 1) < 0`, two parts `D − 2(D − 1) < 0`). (β) Every closed
neighbourhood and closed hub-neighbourhood lies in one side, so `𝒩(G) = 𝒩(G₁) × 𝒩(G₂)`,
`L¹_G = L¹_{G₁} × L¹_{G₂}` and the rows split; the ranks add, and `def_d(G) = def_d(G₁) + def_d(G₂) +
D` (S15 (β)), so `t_d(G) = t_d(G₁) + t_d(G₂)`. With `Q_{G₁}·Q_{G₂}` (S18 (v)) a general point of each
side attains. The sides are feasible: a C2-same realization of `G` restricts to one of each. ∎

## S21 — `RL_d` across a cut edge with two sides of at least two bodies

**Statement.** Let `d ≥ 4`, `G` simple and feasible, `uv` the only edge between `V₁ ∋ u` and
`V₂ ∋ v`, `|V₁|, |V₂| ≥ 2`, and `G₁ = G[V₁ ∪ {v}]`, `G₂ = G[V₂ ∪ {u}]`. If `RL_d(G₁)` and
`RL_d(G₂)`, then `RL_d(G)`.

**Proof.** *Restriction to a side is nondegenerate.* Of the bodies of `G₁`, only `v` changes degree,
to one; it is not a hub of `G₁`, its N3 is N1, and `H_{G₁}[u] ⊆ H_G[u]`; every other body keeps its
closed neighbourhood and closed hub-neighbourhood. So `ρ₁` maps `𝒩(G)` into `𝒩(G₁)`.
*(T1).* Given any `r₁ ∈ 𝒩(G₁)`, `r₂ ∈ 𝒩(G₂)`, the `P³` cut arm (`lem:pencil-pair-loop-base-cut`'s
proof, as `lem:pencil-cut-case`) moves `r₂` by an automorphism `g` fixing the lines of `b⁰_u, b⁰_v`
and avoiding finitely many subspaces, and joins: `u`'s plane from `r₁`, `v`'s from `g r₂`. That
proof takes the two sides' realizations as given, so it applies to every pair; the result is in
`𝒩(G)` and agrees with `r₁` on `G₁` except at the plane of `v`, of degree one in `G₁`. So (T1) holds
with `E = 1`, for each side.
*(T2).* Given `λ₁ ∈ L¹_{G₁}(ρ₁ r⁰)`, take the trivial lift of a `ψ ∈ (K⁴)*` extending `λ₁`'s `φ_v`
(a functional on `Π⁰_v` of `r⁰`, which `G₁` constrains only at `b⁰_u, b⁰_v`) on `V₂ ∪ {u}`, and
replace its `φ_u` by `λ₁`'s (`G₂` constrains `φ_u` only at `b⁰_u, b⁰_v`, where both agree). Glued,
this is in `L¹_G(r⁰)`: each closed neighbourhood of `G` is one of `G₁` (bodies of `V₁`) or of `G₂`
(bodies of `V₂`). So `L¹_G(r⁰) → L¹_{G_i}(ρ_i r⁰)` is onto, `i = 1, 2`.
*Rank.* By S19 for each side, a general lift of a general `r⁰ ∈ 𝒩(G)` restricts to rank `t_d(G_i)`
on both (two nonempty open subsets of the irreducible `L¹_G(r⁰)^m`). The row spaces `R_i` of `G_i`
meet in the rows of `uv`: a combination of `R₁` supported on the columns of `u, v` is a multiple of
`uv`'s rows plus a combination of `G[V₁]`'s rows supported on `u`'s column alone, which is zero (each
row has opposite blocks at its two ends). So `rank G = rank G₁ + rank G₂ − (D − 1)`, N1 giving the
edge rank `D − 1`, and `t_d(G) = t_d(G₁) + t_d(G₂) − (D − 1)` (S15 (γ)). ∎

## S22 — `RL_d` across a pendant body

**Statement.** Let `d ≥ 4`, `G` simple and feasible on at least three bodies, `v` of degree one with
neighbour `u`, and `G₁ = G − v`. If `RL_d(G₁)`, then `RL_d(G)`.

**Proof.** *(T1).* `v` is not a hub and is the only neighbour `G₁` takes from any body, so
`lem:pencil-generic-steer` (a) gives `r ∈ 𝒩(G)` with `ρ(r) ∈ 𝒩(G₁)`. Let `E` be the product of
`G`'s conditions that read only bodies of `G₁` — C2 at the sets containing `u` when `u` is a hub of
`G` but not of `G₁` — as minors (S7 (c)); `E(ρ r) ≠ 0`. Given `r₁ ∈ 𝒩(G₁)` with `E(r₁) ≠ 0`, extend:
`b⁰_v` general in `Π⁰_u`, and `Π⁰_v` any 3-space through `b⁰_u, b⁰_v`. If `u` has at least two
neighbours in `G₁`, `Π⁰_u` is `r₁`'s plane (for a non-hub of `G₁`, N3 makes it the span of its three
closed-neighbourhood points); if one, `u` is a non-hub of `G` with `N_G[u] = {u, v, w}` and its plane
becomes `span(b⁰_u, b⁰_v, b⁰_w)`, a change at a body of degree one in `G₁`. N1 at `uv` and N3 at `v`
and at a non-hub `u` hold for general `b⁰_v`; `v` enters no `H[·]`; the C2 conditions at `u`'s plane
are `E`. *(T2).* Given `λ₁`, set `ζ_v := φ_u(b⁰_v)` (if `u` has one neighbour in `G₁`, `ζ_v` is free
and `φ_u` is the functional with the values of `ζ` at `b⁰_u, b⁰_v, b⁰_w`), and `φ_v` any functional
on `Π⁰_v` with the values `ζ_u, ζ_v` at `b⁰_u, b⁰_v`. Onto. *Rank.* `uv`'s `D − 1` rows are the only
ones reading `v`'s column, so `rank G = rank G₁ + D − 1`; `def_d(G) = def_d(G₁) + 1`
(`lem:deficiency-cut-vertex` at `u`, `def_d(K₂) = 1`), so `t_d(G) = t_d(G₁) + D − 1`. S19 finishes. ∎

## S23 — `RL_d` across a pendant triangle

**Statement.** Let `d ≥ 4`, `G` simple and feasible, with adjacent `x₁, x₂` of degree two both joined
to `c` of degree at least four, and `H = G − {x₁, x₂}`. If `RL_d(H)`, then `RL_d(G)`.

**Proof.** *(T1).* Only `c` can stop being a hub, and the neighbours it loses are not hubs, so
`lem:pencil-generic-steer` (a) gives `r ∈ 𝒩(G)` with `ρ(r) ∈ 𝒩(H)`; `E` is the product of `G`'s C2
conditions at the sets containing `c` (minors in `H`'s planes, nonzero at `ρ(r)`). In `G`, `Π⁰_c`
contains `b⁰(N_G[c]) ⊇ b⁰(N_H[c])`, which spans `H`'s plane of `c` (as a hub, or by N3 if `c` has
degree two in `H`); so `G` and `H` give `c` one plane. Given `r_H ∈ 𝒩(H)` with `E ≠ 0`, put
`b⁰_{x₁}, b⁰_{x₂}` general in `Π⁰_c` and `Π⁰_{x_i} = Π⁰_c`: N3 at `x_i` (`b⁰_c, b⁰_{x₁}, b⁰_{x₂}`
independent) and N1 hold, `H[x_i] = {c}` asks nothing, and the rest is `E` or `H`'s own conditions.
*(T2).* Given `λ_H`, `ζ_{x_i} := φ_c(b⁰_{x_i})` and `φ_{x_i} := φ_c`; the conditions at `x₁, x₂`
(closed neighbourhood `{x₁, x₂, c}`) and the new ones at `c` hold. Onto (indeed bijective).
*Rank.* At every lift `b_c, b_{x₁}, b_{x₂}` are independent (their images are), so the triangle's
three hinges are independent and it is rigid (S20 (τ)); its bodies move with `c`, the motion spaces
of `G` and `H` agree, and `rank G = rank H + 2D`. `def_d(G) = def_d(H) + def_d(K₃) = def_d(H)`
(`lem:deficiency-cut-vertex` at `c`; S20 (τ)), so `t_d(G) = t_d(H) + 2D`. S19 finishes. ∎

## S24 — `RL_d` across a good ear: the lifts of `G` are a hyperplane `ker μ`, free when `μ = 0`

**Setting.** `d ≥ 4`; `G` simple, feasible, two-edge-connected on at least four bodies, with a
planar-rigid set; `x` of degree two with hub neighbours `a, b` and `def_3(G − x) ≤ def_3(G)`, as
`lem:pencil-rigid-good-ear` gives; `H = G − x`. Then `a ≁ b` (else `xab` is a triangle with two
hubs, `lem:pencil-feasible-hub-conditions`).

**Statement.** (1) `def_d(H) = def_d(G)`, so `t_d(G) = t_d(H) + D`. (2) (T1) holds. (3) For
`r⁰ ∈ 𝒩(G)`, restriction identifies `L¹_G(r⁰)` with `ker μ ⊆ L¹_H(ρ r⁰)`, where
`μ(λ) := φ_a(b⁰_x) − φ_b(b⁰_x)`. (4) If `μ = 0` on `L¹_H(ρ r⁰)` at a general `r⁰`, then
`RL_d(H) ⟹ RL_d(G)`. (5) `μ = 0` at a general `r⁰` whenever `a` and `b` have two common
neighbours in `H` (the case **E2**; **E1**, **E0**: one, none).

**Proof.** (1) The good-ear lemma's proof finds `X ⊆ V(H)` with `a, b ∈ X`, `|X| ≥ 3`, `s(X) ≤ 1`
and `s(Z) ≥ 1` for `Z ⊆ X`, `|Z| ≥ 2`. Then `def_3(G[X]) = 0` (`lem:deficiency-tight-rigid`),
`def_d(G[X]) = 0` (`lem:deficiency-rigid-higher`), `def_d(H; a, b) = def_d(H)`
(`lem:deficiency-merge-rigid` (2), `D ≥ 1`), and `def_d(H) ≤ def_d(G)` (`lem:deficiency-ear-merge`,
`k = 1`). Conversely every partition of `V(G)` has value at most its restriction's: with `x` alone,
lower by `2(D − 1) − D`; otherwise no fewer crossing edges. So `def_d(G) ≤ def_d(H)`.
(2) As in `lem:pencil-generic-one-ear`'s proof: an end of degree three is not a hub of `H` and
loses only `x`, not a hub, so `lem:pencil-generic-steer` (a) gives `r ∈ 𝒩(G)` with `ρ(r) ∈ 𝒩(H)`.
`E` collects, as minors in `H`'s points and planes, `G`'s C2 conditions at the sets containing `a`
or `b`, `Π⁰_a ≠ Π⁰_b`, and "`b⁰_a ∉ Π⁰_b` or `b⁰_b ∉ Π⁰_a`" (the one-ear proof's
`p_a·n_b ≠ 0` or `p_b·n_a ≠ 0`); `E(ρ r) ≠ 0`. `G` and `H` give `a` one plane (`b⁰(N_H[a])` spans
`H`'s, as a hub or by N3), and `b`. Given `r_H` with `E ≠ 0`, `Π⁰_a ∩ Π⁰_b` is 2-dimensional and
meets `span(b⁰_a, b⁰_b)` in dimension at most one; put `b⁰_x` general in it and
`Π⁰_x = span(b⁰_a, b⁰_x, b⁰_b)`: N3 and N1 at `x`, and `H[x] = {a, b}` asks `Π⁰_a ≠ Π⁰_b`.
(3) A lift of `G` restricts to one of `H`, and `ζ_x = φ_a(b⁰_x) = φ_b(b⁰_x)` forces `μ = 0`.
Conversely, given `λ ∈ ker μ`, `ζ_x := φ_a(b⁰_x)` and `φ_x` the functional on `Π⁰_x` with values
`ζ_a, ζ_x, ζ_b` meet the conditions at `a`, `b` (`x ∈ N_G[a], N_G[b]`) and `x`. Injective, as `λ`
fixes `ζ_x` and `φ_x`.
(4) With `μ = 0`, (T2) holds, and S19 gives `R(r⁰, λ)|_H` rank `t_d(H)` at a general lift of a
general `r⁰`. The restriction of motions `M(G) → M(H)` is injective, as `S_x` lies in
`S_a + K·C(b_a, b_x)` and `S_b + K·C(b_b, b_x)`, two independent lines of directions (`b_a, b_x,
b_b` are independent, their images are). So `rank G ≥ rank H + D = t_d(H) + D = t_d(G)` by (1).
(5) Let `y, w` be common neighbours of `a, b` in `H`. `b⁰_x, b⁰_y, b⁰_w ∈ Π⁰_a ∩ Π⁰_b`, of dimension
two. At a general `r⁰`, `b⁰_y, b⁰_w` are independent: `y ≁ w` (a non-hub `y` has `N(y) = {a, b}`, and
a hub `y ~ w` makes `ayw` a triangle with two hubs), so `b⁰_w` does not read `y`'s steer parameters,
while these (`y`'s auxiliaries if `H[y] = {a, b}`; `y`'s normal if `H[y] = {y, a, b}`) move `b⁰_y`
over a dense subset of `Π⁰_a ∩ Π⁰_b`; the open set where they are independent meets `U(G)`. Then
`b⁰_x = αb⁰_y + βb⁰_w` and `φ_a(b⁰_x) = αζ_y + βζ_w = φ_b(b⁰_x)`. ∎

**What is left at a good ear.** When `μ ≠ 0` (E0, E1), `R(r⁰, λ)|_H` ranges over `(ker μ)^m`, a
proper subspace of `L¹_H^m` of codimension `m`: the lifts of `H` in which `Π_a ∩ Π_b` contains a
point over `b⁰_x`. `RL_d(H)` speaks of the general point of `L¹_H^m`, not of `(ker μ)^m`. This is
ONE-EAR's motive (design doc §2.3), inside the C2-same family. S27 states it.

## S25 — `RL_d` without a planar-rigid set, from the coverage

**Statement.** Let `d ≥ 4` and `G` satisfy the standing hypotheses of `sec:main-component` (simple,
connected, minimum degree at least two), be feasible, and have `def_2(G[Y]) ≠ 0` for every `Y` of
at least two bodies. If the general configuration of `G` attains in dimension `d`
(`def:pencil-d-x0-attains`), then `RL_d(G)`.

**Proof.** Let `𝒯` be the configurations `(q, z¹)`, `q` admissible and `z¹ ∈ L(q)`; `𝒩_c ⊆ 𝒯` those
in `𝒩(G)` (open in `𝒯`); `B ⊆ 𝒯` those with `dim L(q)` least, `3 + def_2(G)` (Jackson–Jordán,
`thm:pencil-jj-equality`): open in `𝒯` by semicontinuity, and irreducible, a bundle of linear spaces
of constant dimension over an open set of pictures. `thm:pencil-x0-base-generic`'s proof puts a
configuration over a general picture in `𝒩_c`, so `B ∩ 𝒩_c` is nonempty and open in both, hence
dense in both. A general change of coordinates of `K⁴` makes every `b⁰_v` meet `w ≠ 0` and every
`Π⁰_v` miss `e_z`, keeping `𝒩(G)`, lifts and ranks; then `r⁰` is the configuration of its picture
(`z¹` is affine on each `N[v]`, `Π⁰_v` being a graph over `(x, y, w)`). So a polynomial condition
nonzero somewhere on `B ∩ 𝒩_c` holds at a general point of `𝒩(G)`. At `(q, z¹) ∈ B`,
`L¹ = L(q)` (S18's remark) and the lifts are the configurations `(q, z¹, ζ¹, …, ζ^m)`,
`ζ ∈ L(q)^m`. The pairs `(q, z)`, `z ∈ L(q)^{d−2}`, at rank `t_d(G)` are open in the bundle over `B`'s
pictures and, by the coverage, nonempty over every picture off a nonzero polynomial; their
projection forgetting `z², …, z^{d−2}` is a nonempty open subset of `B`, and at its points some lift
attains. Such a point with `dim L̃` least is a witness for S18 (v). ∎

**Remark.** This is S14's corollary in the motive's form; the coverage itself is the bare and
distinct conjuncts' business (42d), not this track's.

## S26 — the reduction: `RL_d` everywhere, given the coverage and the costly ears

**Statement.** Let `K` be infinite and `d ≥ 4`. Suppose
- **(A)** the general configuration attains in dimension `d` at every graph satisfying the
  standing hypotheses with no planar-rigid set, on at least four bodies; and
- **(B)** at every `(G, x)` as in S24 with `μ ≠ 0` at a general `r⁰` (E0, E1), `RL_d(G − x) ⟹
  RL_d(G)`.

Then `RL_d(G)`, hence `Generic_d(G)` under C2-same, at every simple feasible `G` with a body: the
`Pᵈ` generic conjunct, with Phase 39's antecedent (S9).

**Proof.** Strong induction on `|V(G)|`, following `pencilPair_of_IH`'s case split; every smaller
graph used is simple and, by (T1) in each step, feasible. At most two bodies: S20 (α). Disconnected:
S20 (β). Connected, not two-edge-connected, at least three bodies: a cut edge `uv`; both sides with
at least two bodies, S21; else one side is a single body of degree one, S22. Two-edge-connected and
simple: three bodies, a triangle (each body has degree two), S20 (τ); at least four bodies and no
planar-rigid set, (A) and S25 (two-edge-connected gives the standing hypotheses, as in
`thm:pencil-generic-step`); otherwise `lem:pencil-rigid-good-ear`, whose hub hypotheses are
`lem:pencil-feasible-hub-conditions` (S9: `G` is `P³`-feasible), gives a pendant triangle (S23) or a
good ear `x`: `μ = 0`, S24 (4), including every E2 ear (S24 (5)); `μ ≠ 0`, (B). ∎

**What it settles.** O6b: every arm of the reduction lifts under C2-same at every `d`, once the
motive is `RL_d` rather than `Generic_d` (S20–S23); `RL_d` is the strengthening S15 asked for, an
irreducible carrier (S18 (i)) with the lifts as fibres. O6a: route B's case (ii) lifts except at
the costly good ears (B); case (i) is the coverage (A). `RL_3` holds everywhere (S18 (iv)).

## S27 — the outer step: `RL` rises with `d` where the deficiency does not drop

**Statement.** Let `G` be simple, feasible and connected, `3 ≤ d′ ≤ d`, `def_{d′}(G) = def_d(G)`.
Then `RL_{d′}(G) ⟹ RL_d(G)`. So `RL_d(G)` holds whenever `def_3(G) = def_d(G)` (S8 in the motive's
form), and, by an outer induction on `d`, S26's (B) is needed only at `(G, d)` with
`def_{d−1}(G) > def_d(G)` (call it **(B′)**).

**Proof.** At a general `r⁰`, a general `λ′ ∈ L¹(r⁰)^{d′−3}` attains `t_{d′}(G)`. As `0 ∈ L¹(r⁰)`,
`λ = (λ′, 0, …, 0)` is a lift in dimension `d`, and `R(r⁰, λ)` is the image of `R(r⁰, λ′)` under
the embedding `ι` (zero coordinates appended). By `lem:pencil-d-embed-realization` (`G` connected)
its rows span `t_{d′}(G) + (D − D′)(|V(G)| − 1) = D(|V(G)| − 1) − def_{d′}(G) = t_d(G)`. One lift of a
general `r⁰` attains, so S18 (v) applies. In S26's induction at dimension `d`, a costly ear at `G`
with `def_{d−1}(G) = def_d(G)` is then settled by `RL_{d−1}(G)`, the outer hypothesis. ∎

## S29 — at the lemma's own ear, `μ` reads only `X`, and vanishes when `X` lifts trivially

**Setting.** `(G, x, a, b)` as in S24, with `x, a, b` in a minimal planar-rigid set `W₀`
(`s(W₀) ≤ 0`, `s(Z) ≥ 1` for `Z ⊊ W₀`, `|Z| ≥ 2`; `s = s_2`), as `lem:pencil-rigid-good-ear`'s proof
chooses its ear (its `y` is our `x`); `X := W₀ ∖ {x}`. Call this a **`W₀`-ear**.

**Statement.** (1) `a` and `b` each have at least two neighbours in `X`; `G[X]` has minimum degree at
least two, `s(X) = 1` and `def_2(G[X]) = 1`. (2) At a general `r⁰ ∈ 𝒩(G)`, `span b⁰(N_{G[X]}[a]) =
Π⁰_a` (and at `b`), so `μ(λ) = μ_X(λ|_X)` with `μ_X(λ′) := φ′_a(b⁰_x) − φ′_b(b⁰_x)` on
`L¹_X := L¹_{G[X]}(r⁰|_X)`, `φ′_a` determined by `ζ′` on `N_{G[X]}[a]`. (3) `μ_X` vanishes on the
trivial lifts, which have dimension 4 in `L¹_X`. Hence **if `dim L¹_X = 4` at a general `r⁰`, the
ear is free** (`μ = 0`) and S24 (4) gives `RL_d(G − x) ⟹ RL_d(G)`. The condition is open on
`𝒩(G)`, so one `r ∈ 𝒩(G)` with it suffices. Call it **(W)**: *at a general point of `𝒩(G)`, the
restriction to `X` lifts to `P⁴` only trivially.* In picture form, `dim L_{G[X]}(q₀|_X) = 4 =
3 + def_2(G[X])`: the picture of `X` is not special for `G[X]`.

**Proof.** (1) Every body of `W₀` has at least two neighbours in `W₀` (the lemma's proof). If `a` had
only `x` and one more, `a′`, then `x` and `a` would be adjacent bodies of `W₀` each with at most one
neighbour in `W₀ ∖ {x, a}` (`b` and `a′`), and the lemma's triangle argument makes `W₀` the
triangle `{x, a, b}`, against `a ≁ b`. So `a` has at least three neighbours in `W₀`, at least two in
`X`; likewise `b`; the other bodies of `X` keep their `W₀`-neighbours, as `x`'s are `a, b`. Removing
`x` and its two edges raises `s` by `−3 + 4`, so `s(X) = s(W₀) + 1 ≤ 1`, and `s(X) ≥ 1` by
minimality. `def_2(G[X])`: the singletons give `s(X) = 1`; a partition with a part `Z`,
`2 ≤ |Z| < |X|`, has value at most `s(X) − s(Z) ≤ 0` (`lem:deficiency-singleton-bound`); `{X}`
gives `0`. (2) Let `y, y′` be neighbours of `a` in `X`. `y ≁ y′` or neither is a hub (a triangle
`ayy′` has at most the hub `a`), so neither point reads the other's steer parameters, and these move
`b⁰_y` (resp. `b⁰_{y′}`) over a dense subset of `S_y := Π⁰_a ∩ ⋂_{h ∈ H[y] ∖ {a, y}} Π⁰_h`, which
is `Π⁰_a` or a 2-space missing `b⁰_a` (a hub `h ∈ H[y]` adjacent to `a` would close a triangle `ayh`
with two hubs). A general `b⁰_y ∈ S_y` is independent of `b⁰_a`, and `S_{y′} ⊄ span(b⁰_a, b⁰_y)`
(it is 3-dimensional, or a 2-space missing `b⁰_a`), so a general `b⁰_{y′}` completes an independent
triple: an open condition meeting `U(G)`. Then `φ_a` on `Π⁰_a` is fixed by `ζ` on `N_{G[X]}[a] ⊆ N_H[a]`, and
`λ|_X ∈ L¹_X` as `N_{G[X]}[v] ⊆ N_H[v]`. (3) A trivial lift has `φ_a = φ_b = ψ`. The points of `X`
span `K⁴`: were they in one 3-space, it would be `Π⁰_a` and `Π⁰_b` (each spanned by points of
`N_{G[X]}[·]`, by (2)), against C2 at `x`; so `ψ ↦ (ψ(b⁰_v))_{v ∈ X}` is injective. If
`dim L¹_X = 4`, `L¹_X` is the trivial lifts and `μ_X = 0`. Openness: `dim L̃_{G[X]}` is upper
semicontinuous in the points (S18 (v)), and `dim L¹_X ≥ 4` always. ∎

**Remark.** The trivial lifts are, in picture form, the affine heights and `z¹|_X`; so (W) says
`L_{G[X]}(q₀|_X) = Aff ⊕ ⟨z¹|_X⟩`, and `μ_X(z¹) = 0` is `q_x` on the line where `Π_a` and `Π_b` meet:
in `P³`, the one constraint `W₀` puts on a nondegenerate picture. What could break (W) is the rest of
`G` making `X`'s picture special, e.g. a hub outside `W₀` with four neighbours in `X`, which puts
four points of `X` in one plane (a condition on `q|_X` through `z¹`); whether such a locus lies in
`G[X]`'s jump locus is the open question.

## S30 — (W) holds at every `W₀`-ear of the populations, certified; costly ears are never `W₀`-ears

**Statement.** `oneear.py` (`notes/attacks/nondeg/drivers/`), each run with `PYTHONHASHSEED=0`:
`--pop brief --seed 1`, `--pop d4 --seed 1`, `--pop geng --n 5 6 7 8 --seed 1`,
`--pop geng --n 9 --seed 1`. The case-(ii) graphs (simple, two-edge-connected, at least four
bodies, hub conditions, a planar-rigid set) are 8, 6, 46 and 128 (of `geng -c -d2`'s 8021
graphs on 5–8 vertices and 197772 on 9, one per isomorphism class; `K_{2,3}` is in three of the
four). At each, one steer draw `r⁰` is C2-same, checked exactly (no draw degenerate), so all 188
are feasible. Then:
- **(W) holds at every `W₀`-ear, for every minimal `W₀` through it: 24, 12, 102 and 340 ears.**
  Each is `dim L_{G[X]}(q₀|_X) = 4` at the draw, the least value possible (S29 (3)); as (W) is open
  and one point suffices (S29), **each is an exact certificate** that the ear is free at a general
  `r⁰`, so `RL_d(G − x) ⟹ RL_d(G)` there at every `d ≥ 4`.
- Good ears in all: 24, 12, 107, 375 (E0 1/0/2/49, E1 2/0/21/123, E2 21/12/84/203). **Costly at
  the draw** (`dim L_G(q₀) < dim L_H(q₀|_H)`): 0, 0, 5, 35, **none a `W₀`-ear**; all have `κ` of
  rank 1 (`κ(λ) := (φ_a − φ_b)|_{Π⁰_a ∩ Π⁰_b}`, whose value at `b⁰_x` is `μ`; trivial on E1's `b⁰_y`) except two E0 ears at `n = 9` (rank 2). Costly-at-a-draw is measured, not certified (each
  dimension is read from above).
- Every graph has a free choice (a pendant triangle or a certified-free `W₀`-ear), so no `(G, d)`
  cell needed (B′), and the driver drew none.

**Consequence.** With S26, S29 and the good-ear lemma (which always offers a `W₀`-ear or a pendant
triangle): at every simple feasible graph on at most nine bodies, `RL_d`, hence `Generic_d` under
C2-same, holds at every `d ≥ 4` given (A) on at most nine bodies. The induction meets only smaller
graphs; those with a planar-rigid set that are two-edge-connected are in the enumeration, and the
arms (S20–S23) are proved in general. Population and caps: as listed, one draw per graph, seed 1,
`COORD = 1000`.

## S31 — how the rest of `G` meets a minimal planar-rigid set

**Statement.** Let `G` be feasible (hub conditions) and `W₀` a minimal planar-rigid set of `G` in
which every body has at least two neighbours (as in the good-ear lemma's proof). Every body `u` of `G`
outside `W₀` has at most two neighbours in `W₀`, and they are hubs; every body of `W₀` with a
neighbour outside `W₀` is a hub. In particular no body outside `W₀` puts four points of `X` in one
plane, S29's remark's danger.

**Proof.** A neighbour `w ∈ W₀` of `u` has its two neighbours in `W₀` and `u`, so degree at least
three. If `u` had three neighbours in `W₀`, all hubs: a hub `u` would have `|H[u]| ≥ 4`, and a
non-hub has degree at most two. ∎

**Remark.** So `G − W₀` meets `W₀` only through hub planes, at most two per outside body, and
those incidences (`b⁰_u ∈ Π⁰_w ∩ Π⁰_{w′}`) are satisfiable at any realization of `W₀` with
`Π⁰_w ≠ Π⁰_{w′}`. A proof of (W) would extend a realization of `G[W₀]` that is general for `G[X]`
(with `x` on the line `Π⁰_a ∩ Π⁰_b`) to a nondegenerate realization of `G`; S31 removes the
obvious closed obstruction, but the outside may hold planar-rigid sets of its own that share hubs
with `W₀`, whose special pictures (S10) could pull `X`'s along. That extension is the open step.
