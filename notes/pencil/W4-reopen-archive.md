# W4 reopened — the archived hand-off text (frozen 2026-09-25)

**Not read on load; frozen verbatim.** This is `notes/pencil/W4-reopen.md` exactly as it stood at
`73ea85a3`, when the live hand-off was compressed to its forward part. Section references
elsewhere in the corpus of the form "`W4-reopen.md` *START HERE*", "P1, the 2026-09-24 paragraph",
"P2"–"P5", "*Unranked*", "T0"–"T4", "*Where you are working*", "*Why reopen*" resolve **here**. The
live hand-off is `notes/pencil/W4-reopen.md`; the verbatim PI calls are `notes/pencil/adjudications.md`.

---

# W4 reopened — hand-off for the next session (2026-09-23)

**Read this first, then `notes/Phase39.md` *Status*, then `notes/pencil/workbook/W4.md`'s
header and the sections named below.** Written at the end of attack gr10 session 1 at the PI's
request, against the tree at `b0d76407` (master) + `3773c022` (branch `attack-gr10`). Lean
pointers are by declaration name; Lean unchanged since `084ee4ff`. Revised after
`/review-attack gr10` and its close commit `3d769296` (2026-09-23): the worktree and merge notes, T0's gr10 items (done), and T2's optional char-2 leg. Revised again by the T0 commit (T0 marked DONE; the worktree bullet made path-free).
**Revised a third time at the end of the same session (2026-09-23): the START HERE section (a
prioritized direction list, which now sets the order), T1's partial findings, the corrected
*Open on W4*, T2 re-aimed, T3 held.**
**Current next-task source (2026-09-24, after Step MC21 landed): *Next session* below, then P1's
*third session* paragraph.**

**Where things stand.** The **coverage theorem (MC-89) is proved modulo Jackson–Jordán, and both
halves are second-read**. It holds in characteristic 0, and over any infinite field modulo
(MC-33)(i), since Step MC20 removed every computational certificate. Every finite simple connected
graph of minimum degree ≥ 2 has `X₀` attaining, so (MC-10)(a) holds. With Step MC19's (MC-133),
not yet second-read, every *feasible* such graph has `HasGenericPencilRealization`. Both statements
are in §(K-main) Steps MC15–MC20. Step MC21 (not yet second-read) adds a second proof of (MC-89)'s
in-𝒮 half by EAR alone (MC-148), and narrows the last ear cell to "Case II-cyclic" (MC-154), which
coverage does not need.

**Next session, in order.**
1. **Second readers**, one dispatch each. Tracks A–J have all landed (Steps MC15–MC21).
   - Step MC19, first (MC-123), (MC-129), (MC-130) and (MC-133);
   - Step MC15's (MC-62)–(MC-67), the part the coverage proof does not use;
   - Steps MC17–MC18 and Step MC20;
   - Step MC21: first the second route (MC-143), (MC-146)–(MC-148), then (MC-150)–(MC-153). That
     route also rests on Step MC17's (MC-105): read Step MC17 first, or in the same dispatch.
2. **PI calls, now ripe.**
   - *Architecture.* The census's A′ row said "P3 becomes 'prove the rank on `X₀`', an architecture
     change". That proof now exists, modulo Jackson–Jordán. Should the W4/`hK` Lean plan move to
     the `X₀` induction? What stops: `kres` (held), the contraction kernels, smark's O7e?
   - *Jackson–Jordán.* Cite it or formalize it; the project formalizes everything it uses.
   - *Characteristic.* The Lean target is over any infinite field. Since Step MC20, the only
     characteristic-0 dependence is Jackson–Jordán, whose field-general proof is `[INFORMAL]`
     (MC-33)(i).
3. *Structural chore:* `K-main.md` is about 6 000 lines, one section. Consider splitting it by step.

**The decision (user, 2026-09-23, verbatim):** *"OK, I'd like to reopen W4."* — and on where to
run it: *"I'll probably run it in this same worktree as the smark agent is still proceeding in
the main one."*

**Gate G0 — SETTLED (user, 2026-09-23): a staged lift.** Asked whether the 2026-08-05 Lean hold is
lifted for the whole **W4 build** item or only for T1's wrapper, the agent recommended lifting it
now for (i) T1's W4 wrapper (a new declaration carrying (K-res), and any other unsettled piece, as
hypotheses; no `sorry`; no edit to smark's consumer) and (ii) **W4-L4b**
(`exists_degree_two_of_co1_rigid`, a pure graph lemma, pinned and spike-elaborated, independent of
(K-res) and (α)), keeping **W4-L1/L2/L3′/L5 parked** until T1 (question (b), the residual L7a
sibling re-traced against the 2026-09-16 `hK`) and T2 (placement step or kernel) report, then
one more call. The user said: *"OK, sounds good."* Record this verbatim in T0's adjudication entry
and in `notes/Phase39.md` *Blockers* (hold lifts are recorded per item).

## START HERE — directions after the 2026-09-23 strategy discussion, prioritized

**Why this section exists (user, 2026-09-23, verbatim).** After the T1 findings below, the PI
asked: *"I get the sense that often times we try narrowing down what's going on on some family of
graphs but then we find exceptions that we try to characterize, which then lead to more
complicated exceptions, and the results don't seem to be closing in on the proof. For the attacks
that we're thinking about in this session, do those also seem likely to spiral out more
attacks?"* — then *"Are there other potential high-level proof strategies we should try pursuing
(even if we have to give up our work in progress)? Alternatively: ways to find counterexample
candidates that could narrow the viable approaches."* — then *"OK, let's write these up as
potential directions in the handoff doc and prioritize them according to your judgment. I guess
we'll want to kick this off in a fresh session?"* The ranking below is the agent's judgment,
delegated; **nothing below is commissioned** beyond that. **It supersedes the order of *Tasks, in
order* further down**, which is kept for each task's scope.

**The diagnosis (the agent's reading; the PI should check it).**
- *The pattern is in the record.* The W4 residual arc: each successor conjecture fell to a larger,
  more specific witness (`W19` → `S29` → `T32` → `R20`) and was replaced by a weaker one. smark's
  obligation count across sessions ran 4 → 3 → 1 → 2 → 4 → 4 (the last rise partly a counting
  change at review 5), and its latest state says the stratification depth is unbounded (workbook
  S40(v)). The retired arc: 127 directions, "`hK` is not closer".
- *The mechanism (a reading, not a theorem).* Every motive is existential. Carrying "some good
  point" across an induction step needs an explicit construction, or irreducibility/density of
  the right configuration space. Where that is unknown, attacks fall back on stratum-by-stratum
  ledgers over infinite families, and each classification exposes a new stratum.
- *Forecast for the queued work.* The Lean wrapper and W4-L4b: no spiral risk (engineering from
  landed bricks). The (α) recon: low as a recon. **`kres`: high, with a predictable failure
  point** — smark's route rests on girth `≥ 7` (short cycles are rigid, so the no-rigid habitat
  excludes them), while a residual has a proper rigid subgraph by definition and every residual
  examined has a short-cycle core (`W19`/`S29` `C₄`, `R20` `C₅`, `NT21c3` `C₆`); R2 most likely does not transfer verbatim, and its natural
  repair re-enters the coplanarity/coincident-flag arm the girth restriction deleted. The
  contraction pair (K-c)/(K-bare-c): medium-high — the 2026-07-30 plan for (K-c) is
  "per-boundary-pattern witnesses", classification-shaped.
- *Hypothesis, unverified:* smark's O7, (K-res) via R2, (K-c) via specialization, and (α)'s
  un-coinciding each reduce to one closure/irreducibility statement about the nondegenerate
  pencil locus — the same geometric question attacked four times by combinatorial stratification.

**The reformulation behind P1 — derived in-session 2026-09-23; elementary, NOT yet written up or
checked by a second reader or a driver.** The pencil configuration is the smark brief's §1 object
(`p : V → P³`, adjacent points distinct, every closed neighbourhood `N[v]` coplanar). In an affine
chart write `p_v = (q_v, z_v)`, a planar position and a height.
- **(F1)** For fixed `q`, "every `N[v]` coplanar" is **linear in `z`**: `z` restricted to `N[v]` is
  the restriction of an affine function of the `q`-positions, wherever `q(N[v])` is not collinear.
  So the configuration space is `X(G) = {(q, z) : z ∈ L(q)}` with `L(q)` a linear space — the
  scene-analysis lifting space of the planar picture `q` with the closed stars as faces.
- **(F2)** The **main component** `X₀` (the closure of the part over generic `q`) is irreducible —
  a vector bundle over an open subset of `(K²)^V` — and contains the **flat configurations**
  `z = 0`, where the smark brief's §3(a) gives rank `6(|V|−1) − def₂` by Jackson–Jordán's
  pin-collinear theorem (published, unformalized; unverified beyond `ℝ`, `notes/Phase39-design.md`
  field-hypothesis recon, row S5).
- **(F3)** Hinge Plücker vectors `p_u ∧ p_v` are **affine in `z`** (no `z_u z_v` term), so over a
  fixed `q` the rigidity matrix is `A₀(q) + A₁(z)`, `z ∈ L(q)`: the Klein quadric is absorbed by
  the parametrization.
- *So:* the conjecture on `X₀` says **the linear subspace `L(q)` is not contained in the
  rank-deficient locus of the molecular (Katoh–Tanigawa) rigidity matrix**. The Lean motive is
  existential, so attaining at `X₀`'s generic point proves the whole conjecture — with **no**
  irreducibility of `X(G)`, no IH-as-certificate, no jump-locus analysis. Not in the corpus as far
  as grep shows (smark's S17 fibres over the hub planes, a different base). The difficulty moves
  to the generic rank of an affine matrix family, gap `def₂ − def₃` from the flat point — and the
  flat point is maximally degenerate (`strategy.md` §2.4: *"degenerate enough to compute, and you
  break the thing you are computing"*).
- *A by-product for (α):* wherever `def₂ = def₃` the flat configuration already attains **with
  adjacent points distinct** (generic `q`), so it supplies the distinct motive there — `K4`
  included (3-connected; smark brief §3(a)/(c)) — under the Jackson–Jordán caveat above.

**P1 — the main-component census. FIRST; docs + driver, bounded; can run in this worktree,
independent of smark.** **DONE 2026-09-23 — outcome A′, awaiting the PI's call.** The write-up is
`notes/pencil/workbook/K-main.md` §(K-main), tag `MC-`, and the driver is
`notes/scripts/w4/maincomp.py`. (F1)–(F3) are (MC-1)–(MC-3), checked. Four results go beyond the
hand-off:
- (MC-4), the flat rank is exact: `6|V| − 3 − dim L(q)`, with `dim L(q) ≥ 3 + def₂`. So "`X₀` flat
  ⇒ `def₂ = def₃`" is proved without Jackson–Jordán ((MC-5)(iii)).
- (MC-6), the first-order term at the flat point is a symmetric form `β` on the lifting space.
- (MC-7)/(MC-8), the census, spec committed first (`9e8aaec2`): `X₀` attains at all 10 252 members,
  every simple 2EC graph on ≤ 8 vertices included, with 0 `SHORT`s, and first order alone suffices
  at every drawn point.
- (MC-9), the exception, which decides row A′ over row A: `K_{2,3}` and 27 other small feasible
  graphs, all with a proper rigid subgraph, where `X₀` is degenerate (conjunct 3). There the
  generic motive lives on a jump component.

The class statements are (MC-10), conjectured. **Next: the PI's call on the table's A′ row.** The
agent's suggestion is an adversarial census first (larger random graphs, n = 9–14, biased to
2-cuts and large `def₂ − def₃`), then P3 in two tracks with a stop rule. Track 1 is (MC-10)(b),
the plane-framework form. Track 2 is nondegeneracy on `hK`'s habitat. Stop and report if either
needs more than about three structural cases. The by-product below needs Jackson–Jordán at `G`
(§(K-main) *Step MC5*).

**2026-09-24 — P3 run without the adversarial census, at the PI's direction.** The PI (verbatim):
*"Let's continue work on P1 in @notes/pencil/W4-reopen.md, however, let's see if we can make
progress on the math without a new census first. Feel free to dispatch subagents to help."* The
census is deferred, not cancelled. Everything is written up in §(K-main), *After the census*,
Steps MC7–MC10, (MC-11)–(MC-27).
- **Track 1 reformulated.** (MC-11): the gain is exact, not first-order. So (MC-10)(a) ⟺ (b),
  and the conjecture at an admissible chart is a plane-framework statement. The 3D flexes of the
  molecular framework at `(q, z)` are `H(ℓ(q)) ∩ H(a(z))`: two planar pin frameworks sharing their
  angular velocities, with the heights entering linearly. **(MC-10)(a) is exactly: the linear
  family `T_q(z)`, which attains on `K^V` by the molecular theorem, keeps its generic rank on the
  subspace `L(q)`** ((MC-11)(vi)). The obstruction is a vector area ((vii)).
- **Track 2 done, modulo Jackson–Jordán.** (MC-14): `X₀` is nondegenerate iff `hcard` holds and no
  `def₂`-rigid subgraph holds two hubs of a common `closedHubNbhd`. That settles (MC-10)(c), with
  its converse, and agrees with the census on all of `exh8`. (MC-15): `hK`'s habitat has no
  `def₂`-rigid subgraph. So **on `hK`'s habitat (MC-10)(a) alone would give `hK`'s conclusion**,
  with no antecedent and no IH.
- **The ear step on `X₀`** (Step MC10, a forked agent's work, checked by the coordinator; not yet
  second-read).
  - Closed ears and open ears with `k ≥ 5` are unconditional. `k = 4` is proved under strong
    induction.
  - **Every θ-graph attains on `X₀`** ((MC-21)), the first infinite class.
  - Open ears with `k ≤ 3` are open ((MC-27); the stop rule fired). So is the relative-dof
    conjecture (MC-23), `r = δ`, which is (K-c)'s question in `X₀` form, certified on ≤ 7 vertices.
    *Later that day most of (MC-27) closed (Step MC13, below).*
- **Literature.** The pencil statement is not found anywhere; Jackson–Jordán is verified (the full
  rank function, over `ℝ`, generic over `ℚ`); citations are recorded in §(K-main).
- **The honest limit.** Pencil ⊆ panel, so (MC-10)(a) implies the molecular theorem for simple
  graphs of minimum degree ≥ 2; no short proof should be expected. An ear-only induction can
  never reach graphs of minimum degree ≥ 3. Those need a chord or contraction step on `X₀`, and
  that step is where "the pencil pin destroys the combinatorial ingredient" bites.

**Next (PI's call).** The smallest useful commits, in the agent's order:
1. A second reader on Step MC10. *(Done in part 2026-09-24: Step MC13's reader re-read (MC-16),
   (MC-17), (MC-22), (MC-26).)*
2. Either (MC-27) at `k = 2, 3` (the placement lemma, bounded by the stop rule), or a design recon
   of the chord/contraction step on `X₀` — whether `X₀(G)` relates to `X₀(G − e)` or `X₀(G/H)`
   at all. *(Both done 2026-09-24: Step MC13 and Step MC12, below.)*
3. The adversarial census, once there is a statement for it to test.

**2026-09-24 (later) — the three unranked directions assessed; their findings being landed.** The
PI (verbatim): *"I'd like to explore the feasibility of the unranked directions below P5 in
@notes/pencil/W4-reopen.md. Feel free to spin up subagents if they could help."* Three read-only
recons ran in scratch (one per direction; verdicts in *Unranked* below). Then, after this
session's P3 commit landed: *"Please take a look and then plan how to incorporate the findings from
this session into the repo."* and, on the plan: *"Sure, please proceed through each of these. Feel
free to stop when you think we should proceed in a fresh session (and make sure that we're
prepared to handoff what we have then)."* The plan, one commit per step, each driver ported to
`notes/scripts/w4/`:
- **Steps 0 and 1 — LANDED:** Step MC13 ((MC-43)–(MC-51), `w4/earante.py`, `m2/earbad.m2`). A
  second reader of the hybrid recon's ear step *with the antecedent*: under strong induction `X₀(G′ + ear_{k−1})` attains, and by (MC-22)'s "iff" that gives both
  (R_{k−1}) and (P_{k−1}) at `X₀(G′)`'s generic point ((MC-24) extracts only (R)). Every
  `ρ ⊇ Pen(p_a, π_a)` that (MC-27) names as bad at `k` is bad at `k − 1` too, so the antecedent
  excludes it. Verdict: `k = 3` closes in every orbit (MC-45); `k = 2` where the generic flags are in
  orbit (i)/(ii) and `dim U ≠ 1` (MC-46); the chord `G′ + ab` gives every (R_k) (MC-44), superseding
  (MC-24)'s last bullets; `k = 1` at `δ ≥ 5` (MC-49), (MC-31). Open: (MC-51)(a) `k = 2`, `dim U = 1`;
  (b) `k = 2`, orbit (iv), mod Jackson–Jordán; (c) `k = 1`, `δ ≤ 4`, reduced to one condition at the
  chord point (MC-50), met at every tested instance. On `hK`'s habitat only (c) remains (MC-48).
- **Step 2 — LANDED:** Step MC12, the contraction step on `X₀` ((MC-34)–(MC-42),
  `w4/coreshrink.py`), from the multi-scale recon: for a proper rigid `W` with `G/H` simple,
  `X₀(H)` and `X₀(G/H)` attaining give `X₀(G)` attaining under two per-graph linear-algebra
  conditions (MC-39), open as class statements (MC-41); the multi-scale durable negatives (MC-42).
  Re-derived by a second agent; a second reader of (MC-37) is owed.
- **Step 3 — LANDED:** Step MC11, the split-off step on `X₀` ((MC-28)–(MC-32), `w4/splitext.py`),
  and *Jackson–Jordán beyond ℝ* ((MC-33), `w4/jjchar.py`), from the Jackson–Jordán recon, each
  re-derived by a second agent.
- **Step 4 — LANDED:** Step MC14 ((MC-52)–(MC-61), `w4/x0arms.py`), which counts what an induction
  with motive (MC-10)(a) reaches using only landed steps: cut vertices and bridge chains are fibre
  products (MC-52), (MC-53); an open ear with `k ≤ 4` at `δ = 0` needs no antecedent (MC-54), which
  closes (MC-51)'s cells there; a `def₂`-rigid core needs no per-graph contraction certificate,
  modulo Jackson–Jordán (MC-59), so every `K₄` necklace attains on `X₀` (MC-60). **Every tested
  graph is covered** — all 7 980 simple 2EC graphs on ≤ 8 vertices ((MC-57), exhaustive), every
  member of every census population with Step MC13's cells ((MC-58)), `N(3..8)` — **but this is a
  measurement, not a coverage theorem** (MC-61). The hybrid recon's 48-graph "REST" and "887/888"
  were artifacts of its step set and of a first-arm-only recursion.

**Next (PI's call) — the open directions, for a fresh session.** All five steps have landed. The
`X₀` induction covers every tested graph, but **there is no coverage theorem** (MC-61). By (MC-56), a
theorem that every simple 2EC graph satisfying (H) is covered proves (MC-10)(a) by this strategy, so
it is the whole remaining problem here. Its two halves: the **structural half**, that every such
graph admits some step; and the **certificate half**, that each step's per-graph certificates hold
in general. The smallest commits first:
1. **Second readers**, read-only, one dispatch each, on the new load-bearing claims: (MC-37)/(MC-39)
   (the contraction step), (MC-45)/(MC-46) (the short ears), (MC-54), (MC-59) (the flat core),
   (MC-52)/(MC-53) (cut vertices and bridges), and Step MC14's reading that (MC-22)–(MC-25) need no
   `a ≁ b` (three `k = 4` covers rest on it). Each was derived by one agent and checked by one more at
   most. *(Done 2026-09-24 except (MC-45)/(MC-46): one reader re-derived (MC-34)–(MC-39), (MC-52)–(MC-55),
   (MC-59) and the `a ≁ b` reading. Nothing was wrong. It repaired (MC-22)'s statement and (MC-55)(iii)'s
   proof, and sharpened (MC-59)(c): at a `def₂`-rigid core Jackson–Jordán is needed only at `H` and
   `G/H`, so the `K₄` necklaces (MC-60)(b) need no citation.)*
2. **The adversarial census** — the cheapest test of the structural half — run through both `maincomp.py` (does `X₀`
   attain?) and `x0arms.py --ear23 antecedent` (does the induction reach it?): `n = 9–14`, biased to
   2-edge-cuts and large `def₂ − def₃`. A `SHORT`, or an uncovered graph, triggers the stop rule.
3. **The structural half, a recon on the combinatorics:** which simple 2EC graphs with `def₂ > def₃` admit no step?
   Candidates: a proper rigid set but none with a simple quotient (Katoh–Tanigawa's Lemma 6.5 case),
   and 2-edge-cuts with no degree-2 chain.
4. **The certificate half, as bounded attempts under the stop rule:** (MC-39)'s (i)/(ii) at a core with `def₂(H) > 0`
   (lifting-space linear algebra, where scene-analysis counts may apply); the open 1-ear at
   `1 ≤ δ ≤ 4` ((MC-51)(c), reduced to one condition at the chord point, (MC-50)); (MC-51)(a) at
   `δ ≥ 1`; and Jackson–Jordán, cited or formalized.
5. **Outside `X₀`:** the generic motive at A′ graphs, where `X₀` gives only the distinct motive
   ((MC-9), (MC-14)); none of Steps MC11–MC14 addresses it.

**2026-09-24 (third session) — the open directions, worked in parallel.** The PI (verbatim): *"Let's
work on the open directions for P1 there with up to 4 parallel subagents. I'd like to prioritize
proving theorems (even if informally) over collecting more numerical evidence for existing
conjectures."* Then: *"Let's keep launching subagents as they return until we hit a point where we
should start a fresh session."* Read-only agents, up to four at a time, each landed by the
coordinator:
- **D**, the second reading (item 1): landed (`e2c234c9`).
- **C**, the certificates as partition counts (item 4): landed as §(K-main) **Step MC15**,
  (MC-62)–(MC-74). Modulo Jackson–Jordán, `dim U = min(δ₂, 3)` and the flag orbit are combinatorial,
  and CONTRACT needs no certificate at a core with `def₂(G) = def₂(H) + def₂(G/H)`, which is automatic
  at a maximal proper rigid set with a simple quotient outside one exceptional case. A second reader
  is owed.
- **A**, the structural half (item 3): landed as §(K-main) **Step MC16**, (MC-75)–(MC-89), including
  the **coverage theorem (MC-89)** modulo Jackson–Jordán. The pieces:
  - a maximal `def₂`-rigid set has a simple quotient, which leaves the sparse class 𝒮;
  - in 𝒮, Theorem S gives a usable chain or a proper rigid core with a simple quotient, and every
    such core is additive, so (MC-71) applies;
  - `δ₂ = 1 ⟹ δ ≤ 1` (MC-88), which closes (MC-51)(a) for `a ≁ b`;
  - stuck necklace families exist (MC-83), (MC-84), so CONTRACT at cores with `def₂(H) > 0` is
    necessary.

  **Both second readings have landed, and neither found a gap.** H read (MC-75)–(MC-79) and (MC-82),
  G read (MC-80), (MC-87)–(MC-89) with (MC-68), (MC-69) and (MC-71). The repairs are minor; the
  largest is that (MC-81)'s (β′) bullet was false as worded (MC-121). G also gave an independent
  proof of (MC-87) (MC-119). **(MC-89) stands modulo Jackson–Jordán, in characteristic 0.**
- **J**, the one open ear cell (MC-117): returned after the session stopped for context, was staged
  verbatim (`e2ec9927`), and landed the next session as §(K-main) **Step MC21**, (MC-142)–(MC-156),
  not yet second-read. EAR alone covers 𝒮 (MC-148), a second proof of (MC-89)'s in-𝒮 half, still
  using (MC-68)(d) and Jackson–Jordán. The cell narrows to "Case II-cyclic" (MC-154), which coverage
  does not need. No agent is in flight.
- **I**, the certificate leaves: landed as §(K-main) **Step MC20**, (MC-134)–(MC-141), not yet
  second-read. Every computational certificate under (MC-89) has a hand proof over every infinite
  field, so (MC-89) rests on arguments and Jackson–Jordán alone. Guarding `--lamcap` and `--thetas`
  is harness debt, left for a deliberate driver-edit commit.
- **E**, the generic motive (item 5): landed as §(K-main) **Step MC19**, (MC-123)–(MC-133), not yet
  second-read. The A′ graphs add nothing. Feasibility is (F1) and (F2) (MC-123). The generic motive
  reduces to feasible graphs with no `def₂`-rigid subgraph (MC-130), so with (MC-89): **every
  feasible simple connected graph of minimum degree `≥ 2` has `HasGenericPencilRealization`, modulo
  Jackson–Jordán, in characteristic 0 (MC-133).**
- **F** and **B**, the ear cells (off the critical path): landed as §(K-main) **Steps MC17** and
  **MC18**, (MC-90)–(MC-118), not yet second-read.
  - Relative deficiency is a minimum over induced subgraphs, so `δ₂ ≤ 2 ⟹ δ ≤ δ₂`.
  - For `a ∼ b` the triangle is the chord gadget, which closes Step MC16's cell (a′).
  - (MC-50)'s gap is closed, and its reduction is the theorem (MC-110).
  - Every ear cell closes except (MC-117): `k = 1`, `δ₂ = 3`, `δ ∈ {3, 4}`.
  - An **erratum to (MC-26)**: its `--lamcap` certificate was unguarded, but no landed claim uses the
    wrong cell.
- The PI, midway (verbatim): *"Let's drop the number of subagents to 2 as they come in."*

1. Write (F1)–(F3) up as a new workbook section with the derivation (reserve a label prefix
   first: `python3 notes/ledger.py --reserve`, `notes/pencil/labels.md`).
2. A seeded, exact driver (`notes/scripts/README.md` rules; `HARNESS.md` *Reproducibility*)
   sampling `X₀`: random `q`, a basis of `L(q)`, random `z ∈ L(q)`; report rank against
   `6(|V|−1) − def₃` (existing oracles), plus the rank at `z = 0` (must equal `6(|V|−1) − def₂`;
   the Jackson–Jordán sanity check), `dim L(q)`, and as a diagnostic the first-order gain at the
   flat point (flat-framework flexes paired with flat stresses through `A₁(z)`). Assert (F1)/(F3)
   per instance (coplanarity of every `N[v]` at the sampled point; affineness by interpolation).
3. Populations: smark's sweep populations; both kernels' habitats incl. θ-graphs; the residual
   pool (255; `W19`, `S29`, `T32`, `R20`); smark's Case-2 hub graphs (D3, E13, E15, E55, T10, …);
   W4 branch-2 graphs (`K4`, gate N8); the forced-coincident-flag peels.
4. **Decision table, written into the spec before any run:**
   - *`X₀` attains on every instance* → P3 becomes "prove the rank on `X₀`" (an architecture
     change); the `kres`, contraction and O7 programmes become unnecessary in principle; a PI call
     on what to stop.
   - *`X₀` fails at some `G` where the project's own charts attain* → witnesses live off the main
     component; every generic-point strategy dies; those `G` are the hard core, and P3 asks which
     component attains and why.
   - *`X₀` fails and no chart attains* → a counterexample candidate, checked on the special
     components (the planar positions `q` where `L(q)` jumps — a finite enumeration per graph).
   The census ends at the table: nothing follows without a PI call.

**P2 — the (α) recon, re-aimed and folded into P1's driver.** *Answered by P1 (2026-09-23): the
`def₂ > def₃` branch-2 list is NOT empty (928 peels, 10 `θ(1,2,k)`, 86 graphs on ≤ 8 vertices),
but `X₀` gives the distinct motive at every one — §(K-main) *The census — results*.* Population: **W4 branch 2** —
simple, 2-edge-connected, infeasible, with a proper rigid subgraph. By the by-product above, those
with `def₂ = def₃` are settled by the flat configuration; P1's driver lists the rest
(`def₂ > def₃`), which are (α)'s whole content. If that list is empty on the library, (α) is
probably a lemma, not a kernel. **The residual pool is the wrong population** (T1 finding 3).

**P3 — the follow-up recon, shaped by P1's outcome.** Either a direct rank argument on `X₀` —
perturbation from the flat point (the first-order term pairs flat-framework flexes with flat
stresses through the lifting), or an Edmonds-problem argument if `A₁` splits into rank-one pieces
(a matroid-intersection min-max would restore the combinatorial ingredient `strategy.md` §2.2 says
the pencil pin destroys) — or, on the second outcome, which component attains. Fold in the
common-crux question (do O7, (K-res), (K-c) and (α) reduce to one statement?). Literature to check
first, **citations unverified**: scene analysis (Whiteley's hypergraph matroid; Sugihara), Maxwell–
Cremona liftings, Lovász on singular spaces of matrices / Edmonds' problem. The 2026-07-30 hunt
(`notes/Phase39-design.md` § *(K) literature hunt*) targeted the stress crux, not this.

**P4 — T1's Lean (the residual-branch producer, W4-L4b): DEFERRED until P1 reports.** Cheap and
G0-authorized, but it pays only if the split/contract architecture continues. T1's scope question
(below, finding 6) stays open.

**P5 — T3 (`kres`) and a contraction attack ((K-c) + (K-bare-c)′): HELD until P1/P3.** If `kres`
runs, session 1 checks the R2 transfer, tests the girth prediction first, and stops at the first
break rather than characterizing residual subfamilies.

**Unranked — assessed 2026-09-24** (P1's later 2026-09-24 paragraph: three read-only recons, then
steps 0–4 of its plan). The line listed three directions: a multi-scale (tropical) construction
along an SPQR tree or tree packing; transferring Jackson–Jordán's proof technique; and a hybrid
keeping smark's 2-cut composition with the motive "attains at the generic point of `X₀`".
- **Multi-scale construction — it survives only as the contraction step.** Its one live form is the
  two-scale contraction of a proper rigid core: Katoh–Tanigawa's contraction case in `X₀` form
  (§(K-main) Step MC12, (MC-34)–(MC-42), `w4/coreshrink.py`). For a proper rigid `W` with `G/H`
  simple, `X₀(H)` and `X₀(G/H)` attaining give `X₀(G)` attaining under (i) core-free and (ii)
  no-jump (MC-39); at a `def₂`-rigid core both hold modulo Jackson–Jordán (MC-59), so every `K₄`
  necklace attains (MC-60). Durable negatives (MC-42): collapsing a flexible 2-cut side is lossy at
  leading order; gauge families at a 2-cut reduce to smark's S2; tree packing is (K-slide-comb)'s
  refuted route. Not a stand-alone strategy.
- **Jackson–Jordán's technique — a lemma source, not a route.** It gave the split-off step on `X₀`
  (Step MC11, (MC-28)–(MC-32), `w4/splitext.py`: rank exactly `+5` at the special point, which lies
  on `X₀`, so attaining when `δ ≥ 5` and within one otherwise) and the field-free reading of their
  theorem ((MC-33), `w4/jjchar.py`). The transfer fails at the two moves that carry their induction
  past degree-2 vertices: contraction-and-vertex-split (Claim 6.5 Case 2; `X₀`'s contraction comes
  from Katoh–Tanigawa instead, Step MC12) and the final 2-edge-cut gluing.
- **The `X₀` hybrid — it became the ear step with the antecedent, and the coverage count.** Under
  strong induction the gadget `X₀(G′ + ear_{k−1})` supplies (R_{k−1}) and (P_{k−1}) (Step MC13,
  (MC-43)–(MC-51), `w4/earante.py`, `m2/earbad.m2`): `k = 3` in every orbit, `k = 2` in orbits
  (i)/(ii) with `dim U ≠ 1`, and every (R_k) from the chord. smark's O7e is not needed in this
  induction. With cut vertices and bridge chains (fibre products), ears, split-off, the flat point
  and contraction, **every tested graph is covered** — measured, with no coverage theorem yet
  (Step MC14, (MC-52)–(MC-61), `w4/x0arms.py`):
  all 7 980 simple 2EC graphs on ≤ 8 vertices, every member of every census population, `N(3..8)`.
  The recon's "the uncovered class is infinite" and "887/888 habitat members reach it" were
  artifacts of its step set and of a first-arm-only recursion.

**Counterexample-candidate sources:** `X₀` failures, then the special components; and a dichotomy
worth trying to prove — *if `X₀` is forced flat then `def₂ = def₃`* (smark's hunt found no
forced-flat graph with `def₂ > def₃` to `n = 6`; flatness needs density, the gap needs 2-edge-cuts).

**For `/harness-review`, not for a research session:** make "getting in a rut" measurable — a
session either closes an obligation outright or shows its successors smaller in a stated measure;
a flat or rising count over a set number of sessions triggers the 2026-09-03 reprioritization.
(Incident line 2026-09-23.) **Bearing on smark, for the PI (no edit to smark's files):** on P1's
first outcome, smark's O7e programme is unnecessary in principle for the Lean target.

## Where you are working

- **The main checkout, on `master`.** Branch `attack-gr10` (the gr10 session-1 commits, the
  review-1 close `3d769296`, T0 and the strategy re-think) was **merged 2026-09-23** as a merge
  commit (`03f73e61`; PI: *"OK, smark is idle, let's merge and move to the main worktree."*), so the branch SHAs this file cites stay
  valid. The gr10 worktree is still on disk, merged and idle; removing it is the PI's call.
- **The shared-checkout commit rule is RETIRED (PI, 2026-09-24).** The PI (verbatim): *"smark is
  idle, let's retire that part of the harness and then commit."* This session may commit without
  first checking whether a smark session is running. File ownership is unchanged: never touch
  `notes/attacks/smark/` or `notes/pencil/workbook/attack-smark.md`. If smark resumes, it runs in
  its own worktree (`notes/Phase39.md` *Status*). Keep edits to the files both lines touch
  (`notes/Phase39.md`, `ROADMAP.md`, `notes/harness/incidents.md`) small and anchored.
- Commit rules: `CLAUDE.md` *Working* (author identity, `-F` for messages with backticks,
  no local paths).
- P1 needs no Lean. (The gr10 worktree has a working Lean build of `Escape.lean`, with
  `.lake/packages` symlinked to the main checkout's; the main checkout has its own `.lake`.)

## Why reopen (the mathematical reason the 2026-09-03 directive asks for)

W4 was parked on 2026-08-02 (route 3, packaging (b), "recorded as a decision, not built", because
its one remaining kernel **(K-res)** "and the pinned `hK` share their crux";
`notes/pencil/adjudications.md` § *Relocated 2026-09-03*). Since then:

1. **smark's `hK` side is closed informally.** smark `state.md`: "Case (iii), `hK`, all `m` —
   closed modulo O9 (written, S16(vi))". O9 (descent to a `K`-point) is not open: S16(vi) is
   proven-informally given irreducibility, irreducibility on `hK`'s arm is Case 1 (S17(vii)(b)),
   proved by S19; review 4 re-derived S19 end to end and S16(vi) (workbook S23(iv)), and S21(v)
   was confirmed at S24(ii). smark's four open pieces (O7e-b(a)–(c), O7e-c) are all `hbareSplit`,
   case (iii), `m ≤ 4` — the infeasible arm, which never occurs at a residual (residuals are
   feasible by (K-res)'s own hypothesis).
2. **(K-res) as written is stale.** `W4.md` § *widened kernels* *Step 4* states it in the
   pre-2026-09-16 shape of `hK`: no induction hypothesis, chart-form conclusion (∃ selector, seed,
   independent `pencilRow`s). Since checklist item 5, `hK` takes the IH and concludes
   `HasGenericPencilRealization K 3 G` directly (`notes/Phase39-design.md` § *Kernel restatement
   (2026-09-16)*). R2 uses exactly the IH and the split-off antecedent as certificates, so the
   stale form cannot even receive R2's argument.
3. **The grid route's criterion for residuals is refuted (method, not target):** (RS-5) fails at
   `R20` (gap map row §(K-res)/(RS-5); `python3 notes/gapmap.py --row '§(K-res)/(RS-5)'`). The
   same method-vs-target split gr10 just drew for characteristic 2 (workbook
   `attack-gr10.md` S4).

## What is already closed on W4 (do not redo)

From `W4.md`'s header and sections: route 3 packaging (b) adjudicated; (T) proved (§(SAFE-RES)
*Step TF5*); (E-loc) refuted and shown unnecessary (§widened kernels *Steps EL4–EL6*); (E-pair)
proved (*Steps PR1–PR6*, *GW1–GW6*) and (V) with it. The build is decomposed with gates
N8/N9/N10/N10b passed: `notes/Phase39-design.md` §§ *W4 decomposition recon (2026-07-30)* and
*W4-L4 identification recon (2026-07-30)*; leaf sequence in `notes/Phase39.md`'s **W4 build**
checklist item (W4-L4b `exists_degree_two_of_co1_rigid` first, then W4-L1/L2/L3′/L5; residual
carry `hnoGood'`, non-vacuous by a `|V| = 19` witness, so branch 4 needs content).

## Open on W4

*Corrected 2026-09-23 (T1 finding 1): this list first named only (K-res) and (α).*

- **Three research kernels, not one.** **(K-res)** — restated (T1), attack held (P5). **(K-c)
  `hKc`** and **(K-bare-c) `hbareContract`** — carried by the L3′ skeleton since 2026-07-30
  (`notes/Phase39-design.md` §§ *W4 decomposition recon*, *W4-L4 identification recon*), **never
  attacked**, and pinned in the pre-2026-09-16 shape (T1 finding 2). The three are logically
  independent (disjoint habitats); (K-c) and (K-bare-c) are one un-contraction problem at two
  genericity levels, (K-res) a split-arm problem whose nearest relative is `hK`.
- **The (α) obligation** — `W4.md` § *The (α) obligation — `hcontract` must un-coincide at
  parallel classes (2026-09-16, OPEN)*. It lands **entirely on (K-bare-c)**, in branch 2 (T1
  finding 3); re-aimed as P2.
- **The build** itself (T4), carrying W4-A (W4-L1) and `hremove` (W4-L5) as well.

## Tasks, in order

*Priority is now the P-list at the top (START HERE); this section keeps each task's scope. T0 is
done; T1 is a partial design pass whose Lean is deferred (P4); T2 is re-aimed (P2); T3 is held
(P5).*

**T0 — record the reopening — DONE (2026-09-23, the T0 commit).** `notes/pencil/adjudications.md`
§ *2026-09-23* (the decision, the three reasons, G0 and the three further calls, verbatim where
the user's words are known); `notes/Phase39.md` *Status* header, *Current state* (lead sentence,
the W4 sentence), the checklist preamble and the **W4 build** item (staged), *Blockers* (hold lift;
the (K-res) bullet), *Hand-off* and *Decisions made* (one line; the note rebalanced to stay under
its line cap); the ROADMAP Status cell; `W4.md`'s header; the `Phase39-design.md` arc index. The
gr10 sentences on those surfaces were kept; the gap map's (K-grid) row is untouched (gr10 brief
§A4). N1 is not commissioned; T2 carries the one characteristic-2 population that bears on a
live decision.

**T1 — design pass: (K-res) restated against today's `hK`, landed as a carried hypothesis.**
A `/coordinate-phase 39` recon or design commit (not an attack; there is no consumer yet —
producing one is the point). Starting draft, to be *checked*, not trusted:

```lean
(hKres : ∀ (G : Graph α β) (v a b : α) (eₐ e_b e₀ : β), G.Simple → 5 ≤ V(G).ncard →
  G.TwoEdgeConnected → PencilNondegFeasible K G →
  G.degree v = 2 → eₐ ≠ e_b → G.IsLink eₐ v a → G.IsLink e_b v b →
  (¬ G.PencilHub a ∨ ¬ G.PencilHub b) → e₀ ∉ E(G) →
  (∀ G' : Graph α β, V(G').Nonempty → V(G').ncard < V(G).ncard → PencilPair K 3 G') →
  HasGenericPencilRealization K 3 (G.splitOff v a b e₀) →
  HasGenericPencilRealization K 3 G)
```

i.e. `hK` of `pencilPair_of_splitOff_of_habitat` token for token with `hnoRigid` ↦
`PencilNondegFeasible K G`. Questions the pass must settle from the route-3(b) call site, not
from prose:
- (a) **Habitat antecedent** — left to this pass by the user (2026-09-23: "design pass
  decides"; the agent's suggested default was residuals only, matching packaging (b)). With no `∃ H, H.IsProperRigidSubgraph G 3` antecedent the
  statement also covers `hK`'s feasible habitat (packaging (a) in disguise); the minimal honest
  form restricts to residuals. Which does the dispatch supply? Are `f(V(G)) ≤ 4` and
  triangle-freeness available there for free (`W4.md` *Step 4* says they may be added)?
- (b) **The antecedent's source.** Under `hK`'s current consumer the split-off antecedent comes
  from the IH at `G.splitOff`, whose simplicity uses `hnoRigid`
  (`Graph.splitOff_simple_of_noRigid_of_card`). At a residual that step is the L7a sibling's
  (S3)/(S4)/(S5), supplied by (T) + (V) of §(SAFE-RES′). Re-trace it against the 2026-09-16
  structure of `pencilPair_of_splitOff_of_habitat` — the old L7a leaf shape predates the IH.
- (c) **Where it lives.** A new declaration (a W4 wrapper taking `hKres` and the other W4 leaves
  as hypotheses and producing `hcontract`'s statement), with **no edit** to
  `pencilPair_of_splitOff_of_habitat` or `pencil_conjecture_of_hcontract_hK_hbareSplit_of_card`
  (smark's consumer). Lean: the wrapper and W4-L4b only (G0).
- (d) **Blueprint.** Forward mode: a red node for (K-res) and the wrapper in `pencil.tex`, pinned
  by `\lean{...}` in the same commit (`blueprint/CLAUDE.md`).

**T1 findings so far (2026-09-23; the design pass is PARTIAL — no design commit, no Lean).**
Read from the landed Lean (`Escape.lean`, `Pair2.lean`, `Habitat.lean`, `Motive.lean`,
`Statement.lean`) and `notes/Phase39-design.md` §§ *W4 decomposition recon* / *W4-L4
identification recon*.
1. **The L3′ skeleton's branches and what each carries** (`hcontract` must give all three
   `PencilPair` conjuncts):
   0 — `¬ TwoEdgeConnected`: the landed cut arm `pencilPair_of_not_twoEdgeConnected`. 1 — `¬ Simple`:
   bare only, W4-A (W4-L1, buildable, parked). 2 — simple, **infeasible**: distinct + bare,
   **`hbareContract`** (K-bare-c). 3a — simple, feasible, co-1: generic, W4-L4b + `hremove`
   (W4-L5). 3b — …, a good contraction: generic, **`hKc`** (K-c) + W4-B (W4-L2). 3c — residual:
   generic, packaging (b)'s (SAFE-RES′) + the L7a residual sibling + **(K-res)**. W4's lane closed
   only 3c's non-kernel costs ((T), (E-pair), (V)); branches 2 and 3b were never touched.
2. **`hKc` and `hbareContract` are stale in the two ways the 2026-09-16 restatement fixed for
   `hK`/`hbareSplit`:** no IH (un-contraction glues a realization of `H` onto one of `G/H`, and
   only the IH supplies `H`'s), and the conclusion shape — `hKc` concludes the chart form (needing
   W4-B), `hbareContract` only the bare motive though branch 2's `G` is simple. *Recommended, not
   decided:* restate both — take the IH; `hKc′` concludes `HasGenericPencilRealization K 3 G`
   (retiring W4-B from the consumed path, as (d) retired L7b); `hbareContract′` concludes
   `HasDistinctPencilRealization K 3 G`; each carries its branch conditions, so the carried
   kernels' habitats partition (`hK` no rigid, `hremove` co-1, `hKc′` good contraction and no
   co-1, `hKres` residual, `hbareContract′` infeasible). A kernel-shape decision of the kind item 5
   was: the PI's.
3. **(α) lands entirely on `hbareContract`.** Branch 2 is the only branch with `G` simple that
   consumes the IH at a possibly non-simple `G/H`; at 3a–3c the distinct conjunct comes free from
   the generic one (`hasDistinctPencilRealization_of_generic`). Residuals are feasible, so the
   residual pool cannot show (α)'s friction — T2's original population was the wrong one.
4. **(a) the habitat antecedent — the pass's answer: residuals only.** `hKres` = `hK` token for
   token, with `hnoRigid` replaced by the full residual bundle (`∃` proper rigid, no co-1, no good
   contraction) plus `PencilNondegFeasible K G`, and (SAFE-RES′)'s outputs G triangle-free and
   `N(a) ∩ N(b) = {v}` — all free at the only call site; weakest precondition, and the partition
   of finding 2.
5. **(b) the antecedent's source, re-traced.** L7a (`hasGenericPencilRealization_of_splitOff_of_safe`)
   consumes `hnoRigid` at exactly two calls — `Graph.splitOff_triangleFree_of_noRigid` ((S4) +
   (S5)) and `Graph.splitOff_simple_of_noRigid_of_card` ((S3)); the 2026-09-16 change touched
   `hK`/`hbareSplit` only. The residual sibling replaces `hnoRigid` by (T) and `N(a) ∩ N(b) = {v}`;
   **(S3) `a ≁ b` follows from (T)** (an `ab`-edge closes `{v, a, b}`), so it is not a separate
   input. L6a-transfer (`ncard_closedHubNbhd_splitOff_le_three_of_safe`) and L6b are already
   `hnoRigid`-free: the sibling needs two small graph lemmas. At a residual the wrapper must also
   supply the split data from (SAFE-RES′) (informal theorem, Lean-unbuilt: carried), `5 ≤ |V|`
   (a small brick: a proper rigid subgraph of a simple graph has `≥ 3` vertices, and no co-1 adds
   two), and a fresh `e₀` (a simple-graph fresh-edge supply with larger `β` headroom, (EL-6)).
6. **(c) scope — OPEN, put to the PI 2026-09-23 and not answered:** a full L3′-successor wrapper
   producing `hcontract`'s statement (restating `hKc`/`hbareContract`; seven carried pieces), the
   residual-branch producer only (enough of a consumer for `kres`; respects G0's "L3′ parked"
   literally), or a design doc only. The agent's suggestion was staged: the residual producer
   first. Now deferred under P4.

**T2 — (α) recon (read-only, or a docs + driver commit).** *RE-AIMED 2026-09-23 (T1 finding 3;
now P2): the population below is the wrong one — residuals are feasible and get the distinct
conjunct free; (α)'s population is W4 branch 2 (simple, 2EC, infeasible, a proper rigid
subgraph), starting from `K4`/gate N8, and only its `def₂ > def₃` members are open.*
Question: at the contracted witness
the assembly starts from, which pairs coincide (exactly the parallel classes of `G/H`?), and can
un-contracting separate them while holding the rank? Deliverable: a verdict "placement step" or
"kernel", with a committed, seeded, exact driver (`HARNESS.md` *Reproducibility*) over a named
population — e.g. the residual pool behind `W4.md`'s witnesses (`W19`, `S29`, `T32`, `R20`, the
255 residual inhabitants `W4.md`'s sweeps ran on, censused as (RS-12) in `grid.md` §(K-res)). Templates to try first (`W4.md` *What would change
this* (ii)): `hasPencilRealization_of_not_twoEdgeConnected_core` and the distinctness clause of
`exists_reposition_cross_incidences`. Independent of smark; can run alongside T1.
*Optional char-2 leg (from the gr10 review, 2026-09-23):* gr10's evidence covers no residual,
because every gr10 shape has no proper rigid subgraph, so T1's `hKres` inherits no
characteristic-2 evidence. If the field binder matters to T1, run
`notes/attacks/gr10/drivers/char2chart.py`'s row construction on this same pool with target
`6(|V|−1) − def₃` in place of the hard-coded `6(|V|−1)`: a new mode, committed and seeded, where
the driver asserts the bridge's shape hypotheses per shape and reports failures.

**T3 — the (K-res) attack, after T1 lands the Lean declaration.** *HELD 2026-09-23 (P5): the
predicted break is girth — every residual examined has a rigid `C₄`–`C₆` core, smark's route
needs girth `≥ 7`; if it runs, session 1 tests that first and stops at the first break.* Create `notes/attacks/kres/`
per `notes/attacks/README.md`: a brief transcribing the T1 declaration's hypotheses one per line,
both sides, diffed against it (`HARNESS.md` *Evidence*, the consumer-diff rule — the reason to
wait for T1). Session-1 question: **does R2's proof of `hK` transfer to residuals, and if not, at
which use of `hnoRigid` does it break?** Inputs from smark, all closed (read, do not trust:
`HARNESS.md` "a `PROVED` tag is a claim by its author"): S14(iii), S16(vi), S17(v) and (vii)(b),
S19, S21(v). Reviewed: S19 and S16(vi) (S23(iv)), S21(v) (S24(ii)); **S14(iii)'s review status
not confirmed**. Where it most likely breaks: S19's three-way domain split and the strict
habitat count S19(viii), both derived under no proper rigid subgraph; `W4.md` adds that residuals
sit wholesale in the `dim R_a = 1` stratum (§widened kernels *Step 2*). Name: **`kres`**
(user, 2026-09-23). The PI approves the brief before session 1. Run it in its own worktree.

**T4 — the rest of the W4 build, when the PI commissions it.** Ordinary `/coordinate-phase 39`
work from the checklist's W4 build item; independent of smark and of (K-res), which the wrapper
carries as a hypothesis.

## Do not

- Edit `hK`, `hbareSplit`, `pencilPair_of_splitOff_of_habitat` or the headline theorem.
- Write the (K-res) brief before T1's Lean declaration exists.
- Launch `kres` or a contraction attack before P1 reports (P5); treat (F1)–(F3) as checked before
  P1's write-up and driver check them.
- Treat `W4.md`'s (K-res) statement or its cost estimates as current; both predate 2026-09-16.
- Ask smark for anything; the only optional request is a wording fix in its state line ("`hK`
  closed; O9 written, re-derived at review 4"), at its own pace, via the PI.
