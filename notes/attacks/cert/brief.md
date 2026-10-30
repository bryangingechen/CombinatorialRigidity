> **Cleared for session 1 on the PI's word, 2026-10-30** (the question put: how CERT proceeds
> given R1; the answer: "Clear it; session 1 checks R1", whose option read "Session 1 verifies R1's
> four steps and lands them with a driver at d <= 9; if R1 holds, CERT closes, possibly in one
> session"). Session 1 therefore reads and lands §5's R1 (i)–(iv) first, then §6's driver.
> Written 2026-10-30 by an agent (Claude
> Opus 5.5) against the tree at `947fa75d`, from the owning sections: `notes/Phase42-design.md`
> §2.1 rows 10–12 and its second read of row 12, §2.3 CERT; `notes/Strata.md` Result 21;
> `notes/attacks/short-core/state.md` with workbook S35 and S52–S56; the subsections of
> `blueprint/src/chapter/main-component.tex` on ears and cycles and on open ears with two to four
> interior bodies; `blueprint/src/chapter/pencil-d.tex` on configurations; and the Lean of §1, read
> from declaration bodies. Its claims are the writer's readings; an attack re-derives what it builds
> on (`HARNESS.md` *Evidence*). Rewritten only at milestones (`/review-attack`) or by the PI.
>
> **Where it runs.** Dispatched session by session by the central session `/coordinate-tracks
> 42d`, each session in an isolated git worktree. No `lake build` and no Lean server: read the Lean
> as text, and work by hand and in exact Python. Nested subagents are blocked, so a sweep runs in
> the session's own background shell with a per-run output file. Results are numbered S1, S2, … in
> `notes/attacks/cert/workbook.md`; drivers go in `notes/attacks/cert/drivers/`.

# CERT: independent joins for the cycle and ear steps, in every `Pᵈ`

## 0. Where this sits

PENCIL-D (Phase 42) asks whether the pencil realization theorem holds in every `Pᵈ`; 42d aims at
an informal proof at every `d`. Three of Phase 40's steps (the cycle, the long ear, the ear whose
smaller side has no larger deficiency) carry over given formal work and one input: a configuration
at which some joins are independent. The inputs are measured at `d ≤ 6`, the top one proved at even
`d`. At `d ≥ 7` they are open, and with them SHORT-CORE's answer that the coverage never needs its
`k = 3` row, which parks its last open part, G1.

## 1. The consumer

No `Pᵈ` Lean exists for these steps. The `P³` steps take the certificate through two entry points.
Write `MC/` for `CombinatorialRigidity/Molecular/Molecule/Pencil/MainComponent/`.

**`Graph.X0Attains.of_cycle_of_certificate`** (`MC/Chain.lean`), called by `Graph.X0Attains.of_cycle`:
- `[Infinite K] [Finite α] [Finite β]`: ambient.
- `hk : 1 ≤ k`, `hcover : V(G) = {a, b} ∪ Set.range x`, `hinj`, `hxa`, `hxb`, `hab`,
  `hf : G.IsLink f a b`, `hpath`, `honly` (every link off the path is `f`): `G` is the cycle
  `a − x₁ − ⋯ − x_k − b − a` on `m = k + 2 ≥ 3` bodies.
- `hcard : Fintype.card ι = min (k + 2) 6` and `hg : ∀ i, G.IsLink (g i) (u i) (w i)`: `min(m, 6)`
  links of `G`, by an index `ι`.
- `q₀ : α × Fin 2 → K`, `zs : α → K`: any picture, admissible or not, and any heights.
- `hli`: the joins `pointJoin (pencilConfigPoint q₀ zs (u i)) (pencilConfigPoint q₀ zs (w i))` are
  linearly independent. **The certificate.**
- Conclusion: `G.X0Attains K`; every height is the cycle's (closed neighbourhoods of three).

`of_cycle` places the bodies on the integer points `certPt` (`MC/Ear.lean`): the closed `m`-gon on
`Y₀, …, Y_{m−1}` for `m ≤ 5`; for `m ≥ 6` the closed hexagon, with `x₄, …, x_k` all at `Y₄`.

**`Graph.X0Attains.of_openEar_of_cert`** (`MC/Ear.lean`), called by `Graph.X0Attains.of_openEar`
(`k ≥ 5`, `MC/Chain.lean`) and `Graph.X0Attains.of_openEar_two` (`k = 2`, `MC/Short.lean`):
- `[Infinite K] [Finite α] [Finite β]`: ambient.
- `hG : G.IsX0Graph`: from the structure's body, simple, connected, every body of degree ≥ 2.
- `hk : 2 ≤ k`, `hcover : V(G) = V₁ ∪ Set.range x`, `hinj`, `hxV₁`, `ha`, `hb`, `hab : a ≠ b`,
  `hpath`, `hsep`: an open ear `a − x₁ − ⋯ − x_k − b` on `V₁`; nothing excludes an edge `ab`.
- `h₁ : (G.induce V₁).X0Attains K`.
- `n`, `u v : Fin n → α`, `j : Fin n → Fin (k + 1)`, `hl`: `n` edges of the ear, with their ends.
- `q₀`, `zs : α → K`; `hcert`: their joins at `(q₀, zs)` are independent. **The certificate.**
- `hzs : ∀ q, G.IsAdmissiblePicture q → zs ∈ G.liftingSpace q`, discharged by
  `Graph.mem_liftingSpace_of_ear` (`zs` affine in the picture on the closed neighbourhood in `G` of
  each body of `V₁`, which holds `x₁` at `a` and `x_k` at `b`): the callers take `zs` zero on
  `V₁ ∪ {x₁, x_k}`.
- `hcount : k + 1 + def₆(G[V₁]) ≤ n + def₆(G)` (Lean's `deficiency 3`): (⋆), `n` for `dim(ρ + Λ)`.
- Conclusion: `G.X0Attains K`.

`of_openEar` takes `n = 6` (`hcount` by `Graph.deficiency_induce_add_le_of_ear`, stated at every
dimension), every body of `V₁` (so `a` and `b`) at `Y₀`, `x₁, x₂, x₃` at `Y₁, Y₂, Y₃`, `x₄, …,
x_{k−1}` at `Y₄`, `x_k` at `Y₅`, heights 1 at `x₂, x₃` and 0 elsewhere. `of_openEar_two` takes `n = 3`
(`hcount` from `def₆(G[V₁]) ≤ def₆(G)`), `a, x₁, x₂, b` at `Y₄, Y₅, Y₀, Y₁`, all heights 0.

**The `Pᵈ` consumer.** The write-up track's future blueprint node(s) for rows 10–12 at every `d`,
stating (C1)–(C3) of §3 and feeding the `Pᵈ` forms of both entry points: points
`b_v = (q_v, z¹_v, …, z^{d−2}_v, 1)` (`pencilConfigPointGrade`), each height in `L(q)`, joins in
`Λ²K^{d+1}` (`normalsJoin`), target `D(|V| − 1) − def_D`, `D = C(d + 1, 2)` (`Graph.X0AttainsGrade`),
and `D` for `6` in `hcard` and `hcount`. Join independence is open in the picture and in the heights
in every `d` (`pencil-d.tex`); the hinge form is PD-STEPS's formal work (design doc §3).

**The diff, (C1)–(C3) against what the arguments consume.**
1. *Affine points.* The carrier's points have last coordinate 1. A normalization, not a
   constraint: rescaling a point rescales its joins, and over an infinite field independent joins
   survive moving every point off `{last = 0}` (independence is Zariski-open).
2. *Heights zero where.* Cycle: nowhere. Ears: on `V₁ ∪ {x₁, x_k}`, all `d − 2` heights, of which
   only `a, x₁, x_k, b` enter the joins; nothing at `x₂, …, x_{k−1}`. A constant height is a
   translation. (Design doc §2.3's "long ear with its ends at height zero" means all four, as Result
   21's three consecutive points with `a = b` show.)
3. *Field.* Every infinite field, any characteristic: the steps assume `[Infinite K]`, never
   characteristic 0. An integer certificate valid over every field is more than needed.
4. *Which joins.* Cycle: `min(m, D)` of its `m`. Long ear (`k ≥ D − 1`): `D` of its `k + 1`. Ear row
   (`2 ≤ k ≤ D − 2`, `f = def_D(G[V₁]) ≤ def_D(G)`): all `k + 1`, as `hcount` needs
   `n ≥ k + 1 + f − def_D(G)` and the second read of row 12 gives `def_D(G) ≤ f` for `k ≤ D − 1`.
5. *Coincidences.* The certificate's picture need not be admissible; joined points differ, others
   may coincide (`of_openEar` puts `a` and `b` at one point).

**The domain.** Cycles with `3 ≤ m ≤ D`, and `m > D` by collapsing bodies as `of_cycle` does. Long
ears with `k = D − 1`, and `k ≥ D` by collapsing `x_{D−2}, …, x_{k−1}`. Ear rows at `k = 2` (four
points at height zero, three joins in a 3-dimensional `Λ²`) and `3 ≤ k ≤ D − 2`. `a, b` adjacent or
not (`ab` is no ear edge). Even and odd `d`. Every characteristic (an integer certificate needs unit
Smith form, not just a nonzero determinant). `G[V₁]`, `ρ` and the base data enter only through
`hcount`, so they are not cases. Not a consumer: SHORT's argument at `k ≥ C(d − 1, 2) + 3` (design
doc §2.3) uses CERT's `D_{d−2}`-gon, but S35 proves every `k ≥ 4` without it (the writer's reading).

## 2. Setting

Fix `d ≥ 3`, `D = C(d + 1, 2)`. A point of `K^{d+1}` is *affine* if its last coordinate is 1; its
*heights* are its coordinates `z¹, …, z^{d−2}`; it is *at height zero* if all vanish, that is, it
lies in the 3-space `F` of points `(x, y, 0, …, 0, t)`. A *closed `m`-gon* `Y₀, …, Y_{m−1}` has the
`m` joins `Y_i ∧ Y_{i+1}`, indices mod `m`. `star(y) = y ∧ K^{d+1}`. The *unimodular basis* is
`P₀ = (0, …, 0, 1)` and `P_i = e_i + P₀` (`1 ≤ i ≤ d`): affine, `P₀, P₁, P₂` at height zero, and
the joins `P_i ∧ P_j` (`i < j`) a basis of `Λ²` over the integers.

## 3. The statement

**CERT.** For every `d ≥ 3` and every infinite field `K`:
- **(C1)** for every `3 ≤ m ≤ D`, a closed `m`-gon of affine points with linearly independent joins;
- **(C2)** affine points `p_a, p₁, …, p_{D−1}, p_b`, at height zero at `p_a, p₁, p_{D−1}, p_b`, whose
  `D` joins `p_a∧p₁, p₁∧p₂, …, p_{D−1}∧p_b` are linearly independent;
- **(C3)** for every `3 ≤ k ≤ D − 2`, affine points `p_a, p₁, …, p_k, p_b`, at height zero at
  `p_a, p₁, p_k, p_b`, whose `k + 1` joins are linearly independent.

Joined points differ; others may coincide, `p_a = p_b` included. The strong form gives one integer
certificate per `(d, m)` or `(d, k)` with unit Smith form, independent over every field. By §1,
(C1) gives the cycle step for every `m`, (C2) the long-ear step for every `k ≥ D − 1`, and (C3), with
the flat triangle at `k = 2`, the ear step at `2 ≤ k ≤ D − 2` where `f ≤ def_D(G)`.

## 4. What is known

- **Measured** (Result 21, T2; `python3 notes/scripts/strata/strata.py --content --seed N`, its T2
  lines seed-independent): at `d = 3..6`, by search in `{−1, 0, 1}`, closed `m`-gons for
  `3 ≤ m < D` and open ears for `2 ≤ k ≤ D − 2` at height zero at `a, x₁, x_k, b`, each with
  invariant factors all 1. Fences: `d ≤ 6`, `CERT_TRIES = 1000`; a determinant-2 negative control.
- **The `D`-gon** (Result 21, `cert_top`): a closed walk on the unimodular basis through
  `P₁, P₀, P₂` (the long ear's `x_k`, `a = b`, `x₁`). Even `d`: an Euler circuit of `K_{d+1}`, its
  joins the basis up to sign, **proved**. Odd `d`: a circuit of `K_{d+1}` minus a perfect matching,
  one detour `R = P_j + P_k − P_i` per matching edge `ij` at a step `i → k`, checked at `d = 3, 5`
  only; the writer's probe found it unimodular at `d = 7, 8, 9` (measured, script not retained).
- **Embedding** (design doc §2.3, by hand): a certificate at `d′` is one at every `d ≥ d′` (zero
  heights inserted; `Λ²` of an injective map is injective), so only `D_{d−1} ≤ k + 1 ≤ D_d − 1` is new.
- **Trails** (design doc §2.3; a reader's search, measured, script not retained): trails in
  `K_{d+1}` on the basis, first and last edges inside `{P₀, P₁, P₂}`, give every
  `k + 1 ∈ [4, D − 1]` at `d = 3, 4, 6`. At odd `d` all degrees are odd, so a trail has at most
  `D − (d − 1)/2` edges. The writer's probe agrees, `k + 1 = 14` at `d = 5` the one gap below `d = 7`
  (measured, script not retained).
- **Who waits on it.** SHORT-CORE's S53 answers the need question "no" given CERT's open ears at `d`
  (the `long` and `ear` rows of chains with `k ≥ 4`); G1 (`k = 3`, `d ≥ 7`) is parked with the
  revival trigger "CERT's open ears fail at some `d ≥ 7`" (`state.md`, S56).

## 5. A route (session 1 chooses; `HARNESS.md` binds)

- **R1, generic, every infinite field** (the writer's sketch, read by no one else; its probe ran
  (iv) to the closed `D`-gon at `d = 3..9` over the rationals, measured, script not retained).
  - (i) Three consecutive points of a closed polygon with independent joins are independent:
    otherwise two consecutive joins are proportional, or one vanishes.
  - (ii) So a linear automorphism of `K^{d+1}` sends them to `P₁, P₀, P₂`; it keeps the joins
    independent. Openness moves the other points off `{last = 0}`; rescale. Any closed polygon
    with independent joins becomes affine, with three consecutive points at height zero.
  - (iii) With `p_b = p_a`, an open ear's `k + 1` joins are those of the closed `(k + 1)`-gon
    `p_a, p₁, …, p_k`, and the height-zero points are three consecutive ones. So (ii) turns (C1) at
    `m = k + 1` into (C3) at `k` and (C2) at `k = D − 1`. The consumer allows `p_a = p_b` (§1, item 5).
  - (iv) (C1) by induction on `m` from a triangle of independent points. Let `W` be the span of the
    `m < D` joins. Some vertex `y` has `star(y) ⊄ W`: if the points span `K^{d+1}`, the stars span
    `Λ²`, which exceeds `W`; otherwise `W ⊆ Λ²S` for their span `S`, which no star lies in. Replace
    an edge `y y′` by `y, y + tu, y′` with `y ∧ u ∉ W`; for some `t ≠ 0` the `m + 1` joins span
    `m + 1` dimensions. That is the chapter's insertion lemma with `ρ = 0`, whose proof uses no
    dimension.

  If (i)–(iv) stand, CERT is formal work at every `d`. Session 1 reads and lands them first.
- **R2, explicit, every field.** Trails on the unimodular basis (distinct edges, distinct basis
  joins), with detours through non-basis points at odd `d`, as the odd `D`-gon's. Closed trails do
  not give (C1): at `d = 4` no circuit of `K₅` has 8 or 9 edges, as its complement in the 4-regular
  `K₅` would have even degrees. Worth it only if PD-STEPS wants certificates over every field.
- **R3, KT, at the cycle.** A cycle's pencil condition is empty (three points span a plane), so its
  general configuration is a general affine point tuple. KT Theorem 5.6, formalized in every
  dimension over every infinite field for simple graphs, gives `C_m` the rank
  `D(m − 1) − max(0, m − D)`, so by the cycle's ear rank formula its `m` hinges span `min(m, D)`.
  **So KT covers (C1) at every `d`**, as formal work (the witness moved to affine points by openness),
  and the cycle step could skip the certificate. With (ii)–(iii) it also gives (C2) and (C3): R3
  can replace (iv), not (i)–(iii).
- **Controls.** At `d = 3` the construction must reproduce the three `P³` placements of §1, and
  every driver re-asserts Result 21's certificates at `d ≤ 6` and the negative control.

## 6. Deliverable, and what it settles

The deliverable is a proof by hand of (C1)–(C3) at every `d ≥ 3`, landed as workbook results each
as soon as it holds, saying over which fields it holds. With it, a committed exact driver under
`drivers/` (seeded, exact; unit Smith form where a claim is over every field) checks the
construction at every `d ≤ 9` at least: every `3 ≤ m ≤ D`, every `2 ≤ k ≤ D − 1`, and the
collapsing placements at `m = D + 1` and `k = D`. It reuses `notes/scripts/strata/strata.py`
read-only (`cert_top`, `closed_joins`, `placed`, `elementary_divisors`) and names its population.

**The verdict on G1's revival trigger.** If (C2) and (C3) hold at every `d`, the trigger "CERT's open
ears fail at some `d ≥ 7`" cannot fire: G1 has no consumer at any `d`, and S53's "no" keeps only its
other conditions (S35 with S20's factoring, row 9's formal work). The session records this and
stops for the PI, who decides whether G1 is retired. A failure is also a result: a `(d, k)` with a
proof that no certificate exists over some infinite field, reviving G1 at that `d` (`state.md`) and
naming R1's false step. A secondary target, only on the PI's word: R2's integer certificates at
every `d`. CERT does not settle the hinge form, the ear rank formula at `D`, or PD-STEPS's other
formal steps.

## 7. Pointers

- Plan and evidence: `notes/Phase42-design.md` §2.1 (rows 10–12, the second read of row 12), §2.3
  (CERT, SHORT), §3 (PD-STEPS's deferred hinge form); `notes/Strata.md` Results 15 (embedding), 21.
- The `d = 3` proofs, `main-component.tex`: *Ears and cycles* (`lem:pencil-chain-span-certificates`,
  `thm:pencil-x0-cycle`, `thm:pencil-x0-open-ear`); *Open ears with two, three or four interior
  bodies* ((⋆), `thm:pencil-x0-open-ear-two`, `lem:pencil-insertion`); `lem:block-rank-ear`.
- Lean (as text), beyond §1's: `exists_insertion_gain` (`MC/Lines.lean`, at `Λ²K⁴`);
  `CombinatorialRigidity/Molecular/Molecule/Pencil/Grade/Carrier.lean` and `JoinIndependence.lean`
  there; KT Theorem 5.6, `PanelHingeFramework.rankHypothesis_of_theorem_55_gen`
  (`CombinatorialRigidity/Molecular/AlgebraicInduction/Theorem55.lean`).
- SHORT-CORE: `notes/attacks/short-core/state.md` (G1, its trigger), workbook S35, S53, S56.
- Driver: `notes/scripts/strata/strata.py`, `mode_content`'s T2 (`cert_search`, `cert_ear`, `cert_top`).
