> **Session 1 started on the PI's word, 2026-10-29; §3's reduction sentence and §5's O1 and O2
> corrected that day on the PI's direction, after session 1's consumer diff (workbook S2).
> Re-aimed at review 1, 2026-10-30, on the PI's word (workbook S25): §3 takes base data general
> in S21's sense, §6 makes the secondary target the next deliverable, and §1's carrier and the
> Lean paths are brought up to date. Re-aimed at review 2, 2026-10-30, on the PI's word (workbook
> S50): §6 makes the need question N the next deliverable and holds G1 until N is answered; §6's
> counterexample sentence follows S41; §4 records 42c's deficiency lemma.**
> Written 2026-10-29 by an agent (Claude
> Opus 5.5) against the tree at `fa295157`, from the owning sections: `notes/Phase42-design.md`
> §2.1 rows 12–13, §2.3 SHORT and §2.4 T3; `notes/Strata.md` Result 24; the short-ear subsection
> of `blueprint/src/chapter/main-component.tex`; and the Lean of §1, read from definition bodies.
> Its claims are the writer's readings; an attack re-derives what it builds on (`HARNESS.md`
> *Evidence*). Rewritten only at milestones (`/review-attack`) or by the PI's direction.
>
> **Where it runs.** In its own worktree on branch `attack-short-core`, beside PENCIL-D's Lean in
> the main checkout. Read the Lean there as text: run no `lake build` and no Lean server in the
> worktree, since the machine takes one build at a time. The work is by hand and in exact Python.

# SHORT-CORE: putting the second body back into a short ear, in `P⁴`

## 0. Where this sits

PENCIL-D (Phase 42) asks whether Phase 40's induction proves the pencil realization theorem in
every `Pᵈ`. Its research sub-phase found the induction's steps dimension-general given formal
work, except four. One of them, the open-ear step at short ears whose smaller graph has the larger
deficiency, is the only new mathematics the coverage (the case analysis that picks a step for each
graph) still needs at `d ≥ 4`. A construction settles it from `C(d − 1, 2) + 3` interior bodies on.
This brief's statement is what is left at `d = 4`: three, four or five interior bodies. Without it
the coverage fails, for instance at the Petersen graph with every edge a 4-path.

## 1. The consumer

PD-STATE (Phase 42b, on master) lays the `Pᵈ` carrier: `def:pencil-d-x0-attains` in
`blueprint/src/chapter/pencil-d.tex` (planned `X0AttainsGrade K m G`), heights in `L(q)^{d−2}`.
The step that consumes this lemma belongs to PD-STEPS. The model is Phase 40's `P³` step
`Graph.X0Attains.of_openEar_three`
(`CombinatorialRigidity/Molecular/Molecule/Pencil/MainComponent/Short.lean`; `k = 4` is
`of_openEar_four`, and both run through `Graph.X0Attains.of_openEar_splitOff`). Its hypotheses, one
per line (Lean names the interior bodies `x 0, x 1, x 2`; the prose writes `x₁, x₂, x₃`):

- `[Infinite K] [Finite α] [Finite β]`: ambient.
- `hG : G.IsX0Graph`: the standing hypotheses. From the structure's body: simple, connected, every
  body of degree at least 2.
- `hcover : V(G) = V₁ ∪ Set.range x`, `hinj : Function.Injective x`, `hxV₁ : ∀ i, x i ∉ V₁`,
  `ha : a ∈ V₁`, `hb : b ∈ V₁`, `hab : a ≠ b`: the bodies of an open ear `a − x₁ − x₂ − x₃ − b`.
- `hpath : ∀ i : Fin 4, G.IsLink (e i) (pathVertex a x b i.castSucc) (pathVertex a x b i.succ)`:
  its edges `e 0, …, e 3` in order. Nothing excludes an edge `ab`.
- `hsep : ∀ f u w, G.IsLink f u w → (∀ i, f ≠ e i) → u ∈ V₁ ∧ w ∈ V₁`: every other edge lies in
  `V₁`.
- `h₁ : (G.induce V₁).X0Attains K`: `G[V₁]` attains.
- `h₂ : (G.splitOff (x 1) (x 0) (x 2) (e 1)).X0Attains K`: `G''` attains, where `G''` is `G` with
  `x₂` suppressed and its label `e 1` relinked to `x₁ − x₃`.
- Conclusion: `G.X0Attains K`.

`G.X0Attains K` (`Carrier.lean`, from the body): for some nonzero polynomial `P` in the picture,
every picture `q` off its zero set is admissible, and the heights `z ∈ L(q)` at which the
configuration has rank `6(|V| − 1) − def[6](G)` (Lean's `G.deficiency 3`) contain the non-roots in
`L(q)` of a polynomial that has one.

**The `P⁴` consumer, as the step table reads it (row 13).** The same hypotheses, with
`k = 3, 4, 5` interior bodies and "attains" read in `P⁴`: two heights in `L(q)`, points
`b_v = (q_v, z¹_v, z²_v, 1) ∈ K⁵`, hinges `b_u ∧ b_v ∈ Λ²K⁵`, target `10(|V| − 1) − def[10](G)`.
The `P³` step assumes no deficiency bound, and the `P⁴` one should not either. §3 lists the cases
the statement does not cover and where each is settled; session 1 checks that list.

## 2. Setting

Fix `d = 4`. Screws live in `Λ²K⁵`, of dimension `D = 10`, and `def[D]` is the deficiency at
screw dimension `D`. For a point `y`, `star(y) = y ∧ K⁵` is the span of the lines through `y`, of
dimension 4. For independent `y, y'`, `star(y) + star(y')` has dimension `2d − 1 = 7` and
codimension `C(d − 1, 2) = 3`.

The step runs in two stages, the `P³` step's scheme, dimension-general by rows 1–4 and 12:
- **Base data.** A general picture and heights of `G''`, at which `G[V₁]` and `G''` attain. They
  fix the points on `V₁`, among them `p_a` and `p_b`; the 3-spaces `Π_a, Π_b ⊂ K⁵` of `a` and `b`
  (the points of a closed neighbourhood span at most three dimensions); and the relative screws
  `ρ = {S(b) − S(a) : S a motion of G[V₁]} ⊆ Λ²K⁵`.
- **Ear data.** Over the base, a polynomial family of configurations of `G` and of `G''`. In the
  ear `a − x₁ − x₃ − x₄ − ⋯ − x_k − b` of `G''`, the point `y₁` lies in `Π_a` and `y_k` in `Π_b`,
  each over a free picture point, and the others are free affine points. At `k = 3`, `y₃ = y_k`
  lies in `Π_b`.

Let `W = ρ + span(p_a ∧ y₁, y₁ ∧ y₃, y₃ ∧ y₄, …, y_k ∧ p_b)`: `ρ` plus the `k` joins of `G''`'s
ear. Write `f = def[D](G[V₁])`. The ear rank formula
(`BodyHingeFramework.finrank_span_rigidityRows_ear_eq`, every `D`) gives two things:
- `G` attains once (⋆) holds: `dim(ρ + Λ) ≥ k + 1 + f − def[D](G)`, where `Λ` is the span of
  `G`'s ear joins.
- Where `G''` attains, `dim W ≥ k + f − def[D](G'')`.

Putting `x₂` back on a line through `y₁` (or `y₃`) that is not in `W` raises the span by one; the
argument of `exists_insertion_gain` uses no dimension.

## 3. The statement

**SHORT-CORE (X3 at `d = 4`, `k = 3, 4, 5`).** Let `G` satisfy the standing hypotheses, with an
open ear `a − x₁ − ⋯ − x_k − b` on `V₁`, `3 ≤ k ≤ 5`, and let `G''` be `G` with `x₂` suppressed.
Over base data at which `G[V₁]` and `G''` attain in `P⁴`, general in the sense of workbook S21
((P) `p_a` and `p_b` independent; (B) `la ≠ lb`, or `ρ ⊆ Λ²Π_a`), at a general ear datum:

> if `W ⊇ star(y₁) + star(y₃)`, then `W = Λ²K⁵`.

With it, the `P⁴` step at these `k` follows by the `P³` scheme, though not through the `P³`
factoring verbatim, whose insertion hypothesis ranges over every subspace `ρ` (O1 below). The step
chooses its own base data and can meet (P) and (B) (S20, S21), so the form at every attaining base
datum is not needed. It is needed only at
**danger cells**, where `f > def[D](G) = def[D](G'')` and `7 ≤ dim W ≤ 9`. Elsewhere (⋆) closes
without it:
- when `def[D](G'') < def[D](G)`, by the count;
- when `dim W ≤ 6`, by the insertion, since `W` cannot then hold both stars;
- when `dim W = 10`, trivially;
- when `f ≤ def[D](G)`, by the two-body ear's argument with independent joins (row 12).

On danger cells `dim ρ ≥ 7 − k`, since `W` is `ρ` plus `k` joins.

**The quotient form.** Let `π : Λ²K⁵ → Λ²(K⁵/⟨y₁, y₃⟩) ≅ K³`, or equivalently
`c ↦ c ∧ y₁ ∧ y₃ ∈ Λ⁴K⁵`. Its kernel is `star(y₁) + star(y₃)`, which contains the joins
`p_a ∧ y₁`, `y₁ ∧ y₃` and `y₃ ∧ y₄` (`y₃ ∧ p_b` at `k = 3`). So a `W` containing both stars is
`π⁻¹(π(W))`, and it is the whole space exactly when

  `π(ρ) + span(π(y₄ ∧ y₅), …, π(y_k ∧ p_b)) = Λ²(K⁵/⟨y₁, y₃⟩)`.

The `k − 3` remaining joins supply at most `k − 3` of the three dimensions; `ρ` must supply the
rest: all three at `k = 3`, two at `k = 4`, one at `k = 5`. So the statement holds wherever this
sum is everything, which is what T3 measured at every danger cell (§4). Otherwise `W` must miss a
star. At `k ≥ 6` the joins alone fill the quotient, by a closed triangle of CERT placed in it
(design doc §2.3); that case is proved and is not this brief's.

**The `d = 3` model** (the proof of `of_openEar_three`). There the quotient has dimension
`C(2, 2) = 1`, `π` is the Klein pairing `c ↦ ⟨c, y₁ ∨ y₃⟩`, and the proof splits on `ρ` before
choosing ear data:
- If every `c ∈ ρ` pairs to zero with every line `u ∨ v` (`u ∈ Π_a`, `v ∈ Π_b`), then `c = 0` when
  `Π_a ≠ Π_b`, and `c ∈ Λ²Π_a` when they agree. So `dim W ≤ 3 < 5`, and `W` cannot hold both stars.
- Otherwise some `c ∈ ρ` pairs to a nonzero value with some `u₀ ∨ v₀`. The map
  `(u, v) ↦ ⟨c, u ∨ v⟩` is bilinear and not zero, so it is nonzero at a pair of affine points,
  hence at general ear data, and then `π(c) ≠ 0` fills the quotient.

At `d = 4`, `k = 3`, the analogue is the trilinear map `ρ × Π_a × Π_b → Λ⁴K⁵`,
`(c, u, v) ↦ c ∧ u ∧ v`. At `k ≥ 4`, `y₃` is a free point rather than a point of `Π_b`. The
question is the rank of `c ↦ c ∧ y₁ ∧ y₃` on `ρ` at general ear data. There are three dimensions
to fill, not one, so the dichotomy becomes a stratification by that rank.

## 4. What is known

- **Measured, with no obstruction** (T3, `Strata.md` Result 24): `python3
  notes/scripts/strata/strata.py --short --seed N`, `N = 1, 2, 3`; the cells are
  seed-independent.
  - The population is 72 danger cells at `d = 4` and 126 at `d = 5`, at most 40 bodies, every
    deficiency certified by a partition and a generic rank.
  - Six families: `G[V₁]` is a cycle; or a theta whose hubs are `a, b`, or with `a, b` inside two
    paths, inside one, or at a hub and a path body; or a necklace of diamonds.
  - At every cell, `W` contains neither star, `π(ρ)` has dimension `min(dim ρ, 3)`, the joins'
    image has dimension `min(k − 3, 3)`, and `π(W)` is everything.
  - The 24 cells at `d = 3` assert the chapter's theorem; they are the control.
  - Each cell is one seeded draw, so each rank is a lower bound at that cell, not a proof.
- **Claimed proved by hand** (design doc §2.3; read the proof before building on it): X3 for
  `k ≥ C(d − 1, 2) + 3` at every graph, and the reduction to danger cells.
- **Why it is needed** (T5, Result 26): at `d = 4`, the Petersen graph with every edge a 4-path is
  carried only by `k = 3` ears in this range, so the coverage at `d = 4` needs this statement.
- **Not reached by 42c's lemma** (workbook S50). `Graph.Connected.deficiency_eq_of_deficiency_two_add_three_le`
  (master) gives `def_{D′}(G) = def_D(G)` for connected `G` and `def₃(G) + 3 ≤ D′ ≤ D`. So, given
  the tier below, a graph needs new mathematics at `d` only if `def₃(G) ≥ C(d, 2) − 2`. A danger
  cell has `def₃(G) ≥ 2d − 3` (S50), so every danger cell at `d = 4` (`def₃ ≥ 5`) needs this
  statement. T3's cells have `def₃` from 12 to 28 at `d = 4`.

## 5. A route (session 1 chooses; `HARNESS.md` binds)

- **O1, the reduction in `P⁴`.** The `P⁴` step at `k = 3, 4, 5` follows from §3, given:
  - the ear rank formula at `D = 10`;
  - `def[D](G'') ≤ def[D](G)` (`Graph.splitOff_deficiency_le_of_eq_left`, read at `D`);
  - `def[D](G) ≥ f + k + 1 − D`, since an ear adds `k` parts and `k + 1` crossing edges, so (⋆)
    never asks for more than `D`;
  - the insertion in `Λ²K⁵`;
  - the polynomial-family argument;
  - an insertion hypothesis that names the actual `ρ`. `of_openEar_splitOff` takes the insertion
    (`hins`) for every base datum `(q, z, la, lb)` and every subspace `ρ`. At `d = 4` that form is
    false (workbook S2: `k = 3`, `Π_a = Π_b = Π`, `ρ = Π ∧ K⁵`, where `W = ρ` holds both stars
    and every join of `G`'s ear lies in `ρ`). The `P⁴` factoring passes `ρ` as the relative
    screws of `G[V₁]` at base data where `G[V₁]` and `G''` attain, with the danger numbers.

  Consumed because the step's conclusion is what PD-STEPS takes. The design doc claims this
  reduction; nobody has written it out.
- **O2, the domain.** The cases the base data admit:
  - `dim(Π_a ∩ Π_b) ∈ {1, 2, 3}`. General position gives 1 at `d = 4`; an edge `ab` or shared
    neighbours may force more. The `d = 3` proof's `Π_a = Π_b` case is the precedent.
  - `k ∈ {3, 4, 5}`.
  - `a` and `b` adjacent or not.
  - `Π_a` spanned by points of `G[V₁]`, or chosen by the base data when `a` has one neighbour
    in `V₁` (likewise `Π_b`).
  - `a` and `b` in different components of `G[V₁]`, where `ρ = Λ²K⁵` and `W` is everything.

  Every case is in the sketch or is an obligation (`HARNESS.md` *Evidence*). By S2 the case
  `Π_a = Π_b` at `k = 3` is one where the proof must use that `ρ` is the actual one.
- **O3, the crux, per case.** Either `π(ρ) + π(joins)` is everything at one ear datum, and then at
  a general one by openness, or `W` misses a star for a structural reason, as in the `d = 3` first
  case. A natural first question: how does `ρ` sit relative to `Λ²Π_a` and `Λ²Π_b`, which hold
  every hinge at `a` and at `b`?
- **O4, genericity.** That one ear datum suffices. The condition is a rank bound polynomial in the
  ear data: read the `P³` openness lemmas (`exists_mvPolynomial_le_finrank_ofNormals_bind` and
  its neighbours in `lem:pencil-ear-data-open`) for any dependence on the dimension. The base data
  are general too, so `ρ` moves with them.
- **O5, controls.** The argument at `d = 3`, `k = 3` must reproduce the chapter's proof, and every
  new driver checks itself on T3's 72 cells at `d = 4`.

## 6. Deliverable, and what it settles

The deliverable is a proof of §3 at `d = 4` by hand, landed in the workbook as numbered results
(S1, S2, …), each as soon as it holds. Drivers go under `notes/attacks/short-core/drivers/`,
seeded and exact, and reuse `notes/scripts/strata/` read-only.

The secondary target is a `d`-general argument, `3 ≤ k ≤ C(d − 1, 2) + 2`, checked on T3's 126
cells at `d = 5`. The every-`d` tier needs it wherever the coverage at `d` uses it. At `k = 3`
its statement names the actual `ρ` wherever `κ ≥ 7 − d`, where the every-`ρ` form fails
(workbook S26), as at `d = 4`, `κ = 3`. At `k = 3`, `d ≥ 7` the use is not shown, which is N.

**The next deliverable (review 2, workbook S50): N, the need question at `d ≥ 7`.** Is there a
graph satisfying the standing hypotheses (`Graph.IsX0Graph`), past the coverage's rows 1–5, with
`def₃(G) ≥ C(d, 2) − 2` (42c's range, §4), at some `d ≥ 7`, whose only row not free of new
mathematics is SHORT-CORE's `k = 3` row at a danger cell (§3's sense)? Read "free" as T5 does
(`cov_tag`, design doc §2.4), updated by what this attack has proved. `short` rows with `k ≥ 4` are
free (S35, with S20's factoring). R1's base row, `def_{C(d,2)}(G) = def_D(G)`, is free given the
tier below, and 42c's lemma gives it wherever `def₃(G) ≤ C(d, 2) − 3`. Row 12 and the long ears rest
on CERT's open ears, unsettled at `d ≥ 7` (design doc §2.3). So N is asked given CERT and the tier
below, and its answer says so.
- *By hand first.* T5's second argument (design doc §2.4, "Where ONE-EAR can be load-bearing";
  claimed proved by one session, so read it before building on it) shows that a graph with no free
  row has a chain with `k ≥ 3`, or is ONE-CLASS. With S35, a chain with `k ≥ 4` gives a free row,
  so every chain left has at most three bodies. T5's count for chains of at most two bodies,
  `s_D(V₁) ≤ e(3 − D/3) − 3 < 0`, is the model. Try it for three-body chains, where `D/3 > 4`
  from `d = 5` on, together with S45's structure: every cycle of `F/P` is at least `D` long, and
  `f ≥ 2d − 4`.
- *Measured, if the hand argument stalls.* Write a driver under `drivers/` that extends
  `strata.py`'s coverage (`cov_population`, `cov_cell`, `cov_tag`; fenced at `COV_DIMS = 3..6` and
  `COV_LMAX = 4`) to `d = 7, 8`. It uses the content range `def₃ ≥ C(d, 2) − 2`, treats the
  `short` rows as above, refined to `short_danger`'s danger test at `k = 3`, counts R1's base row,
  and allows paths longer than four edges where the count needs them. Name the population and
  the caps; a "none found" carries them.
- *Outcome.* If no graph needs a `k = 3` danger row, G1 has no consumer. That holds whether N is
  proved or only measured, in which case the population and caps go with the conclusion. Record
  it, park G1 as an obligation of the every-`d` tier, and stop for the PI. If a graph needs one,
  it is G1's population. G1 then resumes at S47's identity at `d ≥ 8`, restricted to motions with
  `S_b − S_a ∈ H∧V` (`state.md`), before any further `d = 7` family: that step decides whether
  S45–S48 work in every `d`.

Until N is answered, no session works on G1a's `d = 7` families (the theta no-coloop step, the
necklaces).

A counterexample is also a result: a danger cell where `W` holds both stars and is proper at
general data, certified exactly. By S41 (read by S42), where `G[V₁]` and `G''` attain, that is
exactly `G` failing `def:pencil-d-x0-attains`, so it would refute the `Pᵈ` statement at `G`, not
only redirect the coverage. T3's graphs and S43's 41 graphs all attain.

A proof settles the coverage's last new mathematics at `d = 4`, with ONE-CLASS (Result 27). It
does not settle the formal steps, CERT's open ears at `d ≥ 7`, or the generic conjunct (GENERIC).

Workbook: `notes/attacks/short-core/workbook.md`. This placement is proposed for the PI to
confirm: the earlier attacks kept theirs in Phase 39's corpus, `notes/pencil/workbook/`, which
PENCIL-D does not use.

## 7. Pointers

- Plan and evidence: `notes/Phase42-design.md` §2.1 (rows 12–13, the second read of row 12), §2.3
  (SHORT, CERT, CARRIER), §2.4 (T3, T5); `notes/Strata.md` Results 13 (the `Pᵈ` configuration),
  21 (CERT), 24 (T3), 26 (T5), 27 (ONE-CLASS); `notes/Phase42a.md`.
- The `d = 3` proofs: `main-component.tex`, the subsection on open ears with two, three or four
  interior bodies (`thm:pencil-x0-open-ear-three`, `-four`; `lem:pencil-two-stars`,
  `lem:pencil-bilinear`, `lem:pencil-insertion`, `def:pencil-ear-data`); the ear rank formula
  `lem:block-rank-ear` and `def:relative-screws` in `rigidity-matrix.tex`.
- Lean (read as text), under `CombinatorialRigidity/Molecular/Molecule/Pencil/MainComponent/`:
  `Short.lean` (`of_openEar_three`, `-four`, `-splitOff`, `exists_insertion_three`);
  `Carrier.lean` (`Graph.X0Attains`); `Cut.lean` (`Graph.IsX0Graph`); `Bridge.lean`
  (`Graph.exists_mvPolynomial_finrank_liftingSpace_eq`, `thm:pencil-jj-equality`).
- The `Pᵈ` carrier: `blueprint/src/chapter/pencil-d.tex` and `notes/Phase42b.md`, on master.
- 42c's lemma, on master: `Graph.Connected.deficiency_eq_of_deficiency_two_add_three_le`
  (`CombinatorialRigidity/Molecular/Deficiency.lean`; `lem:deficiency-stable` in `pencil-d.tex`).
- Driver: `notes/scripts/strata/strata.py` (`short_danger`, `short_cell`, `mode_short`; for N, the
  coverage: `cov_population`, `cov_cell`, `cov_tag`, `mode_coverage`).
