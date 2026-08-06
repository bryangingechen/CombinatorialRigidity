# Phase 39 W4 (`hcontract`) recon — and the whole kernel-(K) continuation

**Start from `notes/scripts/README.md`** — the harness-wide primitive index,
layering map, full invocation table (including `kslidecl.py` / `kslidecomb.py`,
which this file does not describe), and conventions. This file is the
per-driver description list for this directory.

**The directory name is stale, deliberately so.** `w4/` was opened for the
`hcontract` (W4) arm, but it now also carries the kernel-(K) continuation —
`(K-tight)` (`repin.py`), `(K-pitch)` (`pitch.py`), `(K-slide)` (`kslide.py`),
`(K-slide-cl)` (`kslidecl.py`), `(K-slide-comb)` (`kslidecomb.py`), and the
three kernel-(K) research fan-out arcs — `(K-flank)` (`flanks.py`, direction A),
`(K-pure)` (`pure.py`, direction C), `(K-Λ)` (`lambda.py`, direction B). A
rename is churn until the (K) arc closes; see `notes/scripts/README.md`
*Deliberate non-goals*.

Exact-ℚ numerics for the W4 decomposition recon (2026-07-30); results and
the decomposition they feed are in `notes/Phase39-design.md`
§"W4 decomposition recon". The drivers here form a chain (each builds on the
previous arc's machinery), sitting on the two model layers
`../kbare/kbare_common.py` and `../escape/pencil_escape.py` and, under those,
the shared primitives in `../exactcore.py`.

- `hybrid_gates.py [nsamples]` — the four gates:
  - **N8** K4 via triangle contraction (the bare-kernel `(K-bare-c)` shape:
    coincident-cluster contracted realization, specialization-glued hybrid);
  - **N9** C4+x,y via vertex removal (the branch-(2b) 6.5-mirror at the W4
    discriminating instance, plus the first direct truth sample of the
    conjecture's target on its forced all-coplanar stratum), with a
    deliberate collinear control exhibiting the rank-29 in-stratum failure
    locus the output motive's fourth conjunct excludes;
  - **N10** C4+x+y+xy via C4 contraction (the `(K-c)` kernel shape: simple
    + feasible contraction, generic-triangle IH, two distinct-anchor
    boundary panels — the first sample beyond N3's single-cluster boundary
    pattern);
  - **N10b** C4+x~1,y~1,xy — the forced-boundary-panel pattern (boundary
    body with two outside anchors; no panel genericity survives there).

Reproduce: `python3 notes/scripts/w4/hybrid_gates.py 6` (seed fixed,
~1 min). All gates assert their targets; the run prints `ALL GATES PASSED`.

- `no_good_search.py [nrandom]` — the W4-L4 residual-branch inhabitant
  search (§"W4-L4 identification recon"): classifies structured families
  (cycle + hub gadgets, cycle + anchored pair, two-hub multi-path) and
  random sparse graphs against the residual habitat (simple, 2EC,
  provably feasible, ∃ proper rigid, no co-1 rigid subgraph, no provably
  Simple∧Feasible contraction), with a three-way feasibility proxy
  (landed-lemma-backed provably-good / provably-bad / middle-zone) and
  the `B#351` coarse-proxy regression check. Result (2026-07-30, two
  runs): **0 candidates** (strong or middle). ~10 min per run.
  **Superseded as evidence** by `nogood_subdiv.py` below — its `|V| ≤ 13`
  cap and `≤ 3`-interior gadget paths both sit below the Ear-Lemma
  threshold, so the habitat it swept was empty for structural reasons.

- `nogood_subdiv.py [--validate | --witness | --min]` — the follow-up
  search over **subdivision** families with arbitrarily long branches
  (2026-08-02). Replaces the `2^|V|` subset sweep by a branch-subset
  enumeration (a rigid `W` is its own 2-core, so it is a union of whole
  branches), and the deficiency oracle by the Lee–Streinu `(6,6)` pebble
  game (`def = 6(|V|−1) − rank_{(6,6)}(5G)`). Result: the `hnoGood'`
  **vacuity conjecture is REFUTED** — 96 inhabitants, smallest `|V| = 19`.
  - `--validate` (~4 min): pebble game vs `kbare_common.exact_deficiency`,
    400/400; `C_k` rigid iff `k ≤ 6`; the Ear-Lemma threshold; branch
    enumeration vs brute force on 120 random 2EC graphs.
  - `--witness` (~1 min): the canonical `|V| = 19` inhabitant, re-checked
    over all `2^19` subsets with both oracles, plus the two deficient
    variants.
  - `--min` (~3 min): 21455-instance minimality sweep + the short-branch
    probe behind the open (SAFE-RES) conjecture.
  - no flag (~4 min): families D/E/F.

  Argument state and consequences: `notes/Pencil-W4-informal.md`
  §"`hnoGood'` vacuity".

- `saferes.py [--validate | --witness | --search | --prime | --structure]` —
  the adversarial attack on the **(SAFE-RES)** conjecture (2026-08-02).
  `nogood_subdiv.py`'s families carry all their ear length in ONE long
  branch; the Ear Lemma constrains *ears*, not *branches*, so this script
  sweeps the blind spot — subdivided multigraphs whose branch interiors are
  all `≤ 2`, with the ear length carried by **hub chains**. Result:
  **(SAFE-RES) is REFUTED** by a `|V| = 29` residual with every branch at
  exactly `≤ 2` interior vertices, both feasibility verdicts
  landed-lemma-certified.
  - Second oracle: `treepack_deficiency`, matroid-union augmenting paths
    packing 6 edge-disjoint spanning forests in `5H`. Polynomial, so unlike
    `kbare_common.exact_deficiency` (`2^|V|`) it runs at `|V| = 29`.
  - `--validate` (~2 min): all THREE oracles (partition / pebble game /
    tree packing) agree on 250 random graphs; `C_k`, the Ear Lemma
    threshold, and sparse subdivisions up to `|V| ≈ 30`.
  - `--witness` (~2 min): the `|V| = 29` refutation, every branch-subset
    candidate and every `G − v` re-checked on both oracles.
  - `--search` (~15 min): structured + random short-branch sweeps, plus the
    ultra-short (`≤ 1` interior) probe.
  - `--prime` (~1 min): coverage for the successor conjecture (SAFE-RES′)
    over every residual inhabitant both scripts produce.
  - `--structure` (~10 s): coverage for the *argument's own* steps — (C7),
    the (C8) dichotomy, the (E-κ) count, the (V) branch characterization.

  Argument state, the successor (SAFE-RES′), and consequences for W4:
  `notes/Pencil-W4-informal.md` §"(SAFE-RES)".

  **Recorded-figure correction (2026-08-02, re-run by the widened-kernel
  recon).** `--prime` reports **255** residual inhabitants, of which **216**
  carry a deep split vertex, so **39** refute (SAFE-RES) — the workbook's
  original "281 / 65" was a transcription error, corrected there. Every other
  figure reproduces exactly (`--search` 1989/39/584/343, `--structure`
  338/59/59/0/59); `saferes.py` itself is unchanged since it landed.

- `widened.py [--validate | --witness | --pool | --sample | --ebound]` —
  the **widened-kernel** probe (2026-08-02). W4 routes 1/3 dispatch residual
  graphs to the split arm, whose carried kernel `hK` takes `hnoRigid` as an
  antecedent, so the kernel has to widen; this script measures what that costs.
  Exact-ℚ, on top of `../escape/`'s rigidity machinery. New geometry:
  `place_pencil_general`, a pencil-generic placement handling **hub-hub
  adjacency** (`escape/place_pencil` samples every hub plane independently —
  valid only for the double-subdivision families, where no two hubs are
  adjacent; every residual has hub edges).
  - `--validate` (~1 min): reproduces the N9a record (θ(4,4,3): `s₀ = 0`,
    `dim R_a = 2`, escaping seeds 8/8) and the tight both-ends-hubs control
    (dbl-subdivided `K4`: `dim R_a = 1`, escaping seeds 11/12); checks the
    identity `dim R_a = 5 + def(G′) − def(G−v)` on all 4192 pool pairs.
  - `--witness` (~2 min): W19 and S29 — the pencil target rank is attained at
    both; every split-usable vertex has `s₀ = 2`, `dim R_a = 1`; escaping
    seeds 8/8, on-line placements fail 16/16 resp. 14/14.
  - `--pool` (~1 min): the 255-residual combinatorial sweep (`s₀`, `dim R_a`,
    the `def × dim R_a` cross-tab, 2-connectedness).
  - `--sample` (~4 min): stratified exact-ℚ escape rate, 94/96 escaping seeds.
  - `--ebound` (~1 min): the **(E) re-route** probe — 255/255 residuals carry a
    degree-2 vertex `v₀` with `E(G − v₀)` count-independent, which is exactly
    the property `edgeBound_of_noRigid_of_degree_two` extracts from `hnoRigid`.

  Argument state: `notes/Pencil-W4-informal.md` §"widened kernels (routes 1/3)".

  **Escape-figure correction (2026-08-02, the (K-tight) re-pin).** The
  non-escaping seeds behind `--validate`'s 11/12 (incl. seed 442) and
  `--sample`'s 94/96 are **placement-sampler artifacts**: `localtest.py`'s
  `plane_basis` returns two *parallel* in-plane directions whenever the
  normal's third coordinate is `0`, so those seeds' "in-plane placements"
  all sat on one line through `pt(b)`, freezing `hinge(vb)`. With a robust
  sampler every target-rank seed probed escapes — see `repin.py` below.
  `widened.py` is left unchanged as the record of what was measured.

- `repin.py [--control | --theta | --witness | --stratum | --pointwise]` —
  the **carrier-aware KT pp. 684–691 boundary-load re-pin** (2026-08-02):
  validates the corrected escape criterion of `notes/Pencil-informal.md`
  §(K-tight) (attainment ⟺ two functionals independent on the obstruction
  space `U`; `dim U = dim R_a + 1` forced; route-A/B uniform failure ⟺
  `r ⊥ Λ²Π̂(b)` / `r ⊥ Λ²Π̂(c)`; combined failure ⟺ `★r ∥ C(meet line)`).
  Exact-ℚ, on top of `widened.py` / `../escape/`.
  - `--control` (~10 min): dbl-subdivided `K4`, seeds 440–479 — criterion
    exact 34/34 (routes A, B, and A|B); seed-442 post-mortem (escapes with
    the robust sampler; bad-line generator = `★C(meet line)`); the second
    failure line `P′` exhibited (off-line placement failing by exactly 1);
    the pencil-restricted M2 predictor refuted (32/34, seeds 442/473).
  - `--theta` (~2 min): θ(4,4,3), `dim R_a = 2` — `dim U = 3 = dim R_a + 1`,
    all seeds escape both routes.
  - `--witness` (~8 min): `W19` (3 split shapes) and `S29` (`s₀ = 2`) —
    criterion exact 12/12 and 4/4.
  - `--stratum` (~10 min): the `(def 0, dim R_a 1)` pool stratum — 24/24
    agreement, 0 genuine failures (the two `--sample` failures reproduce as
    seeds 5000/5001 of one pair, both with `nrm[b][2] = 0`).
  - `--pointwise` (~8 min): the per-placement biconditional (attainment ⟺
    rank-2 of the `U`-functional matrix), 80/80 at the control and `W19`.

  Argument state: `notes/Pencil-informal.md` §(K-tight).

- `pitch.py [--control | --witness | --stratum | --sweep | --theta336]` —
  the **(K-pitch)** development (2026-08-04): the null-wrench test's
  motion-side transfer. Validates, per target-rank seed on the
  `dim R_a = 1` hard stratum: **(T1)** the transmitted load `r` spans the
  Euclidean perp of `V_bc ⊕ ⟨C_ab, C_ac⟩`, `V_bc` = the relative twist
  system of the chain ends through `H = G − v − a` (stress-free);
  **(T2)** the sign law `Q(r)·Q(z) < 0` (or both zero) against the
  reciprocal twist `z`; **(T3)** the motion form of the full escape
  criterion (escape ⟺ some `H`-motion pairs non-trivially with the meet
  line) against `repin.py`'s validated per-route criteria; **(T4)** the
  `pt(a)`-sweep quartic `q(t) = Q(z(t))` with `a`-free leading coefficient.
  Exact-ℚ, on top of `repin.py` (robust sampler inherited).
  - `--control` (~4 min): dbl-subdivided `K4` + the tight thetas
    θ(3,4,5)/θ(3,3,6) — (T1)–(T3) hold on all 16 seeds; pitch nonzero 16/16.
  - `--witness` (~4 min): `W19` (free-end shape) + `S29` (both-hubs) —
    5/5 residual seeds, pitch nonzero 5/5.
  - `--stratum` (~4 min): 4 pool splits × 2 seeds — 8/8, pitch nonzero 8/8.
  - `--sweep` (~6 min): the quartic at 4 habitats — degree ≤ 4 exact,
    `q₄ = Q(z_∞) ≠ 0`, sign law re-checked against recomputed stresses.
  - `--theta336` (~1 min): the **companion-chain closed form** — at
    θ(3,3,6), `V_bc = ⟨C(bx), C(xy), C(yc)⟩` and
    `Q(z) = 2[x,y,a,b][b,x,a,c][y,c,a,b][x,y,a,c][b,x,y,c]`, a bracket
    monomial; validated exactly (4/4 seeds), incl. the pairing–bracket
    dictionary `B(C(uv), C(pq)) = [u,v,p,q]`.
  - `--companion4` (~5 min, 2026-08-04 second pass): the **Λ-compression
    (T5)** — at a length-4 companion the far data enters only through the
    annihilator covector `λ` of `V_bc` in the companion span, and
    `Q(z) = Φ_loc(λ)`, an explicit local quadratic. Validated at
    θ(3,4,5) (3 seeds, with the far-arc `ν` cross-check) and at **NT21**,
    a non-theta tight habitat built here (`def = 0` and
    no-proper-rigid-branch-union certified over all `2⁷` subsets).
  - `--slide` (~10 min, 2026-08-04 second pass): the **slide-in
    degeneration** (the corrected collinear collapse) — panel-constrained
    interiors slide into their hub points (chart-legal); hub-incident
    hinge lines are constant, interior–interior hinges become hub chords.
    Tracks `V_bc`, `z`, `Q(z)` at `ε` down to `1/1024` plus the projective
    limit system: motion rank persists (9 → 9), `V_bc(ε)` converges to
    the limit plane at `O(ε)` (normalized Plücker distance), and the limit
    twist is **pitched** at dbl-subdiv `K4` (simple `G°`, 3/3) but
    **null** at θ(3,4,5) (parallel-edge `G°`, 2/2 — the order-0
    evaluation fails exactly where the companion forms take over).

  Argument state: `notes/Pencil-informal.md` §(K-pitch).

- `kslide.py [--k4 | --battery [0-3] | --mixed | --flanks]` — the
  **(K-slide)** attack (2026-08-04, third pass): the slide-transfer
  theorem's per-habitat `ε = 0` witnesses. Validates, per member: the
  transfer certificate ((T1)–(T3) + `Q(r) ≠ 0` at one target-rank
  `dim R_a = 1` seed, via `pitch.transfer_probe`) and hard limit
  witnesses (W1) `dim mot = 6|V_H| − 5|E_H|`, (W2) `dim V_bc(limit) = 3`,
  (W3) `z(limit)` defined, (W4) `Q(z_limit) ≠ 0` — by (S1) one such
  witness proves the pitch `≢ 0` on the habitat's chart. Exact-ℚ, on top
  of `repin.py` / `pitch.py`.
  - `--k4` (~1 min): dbl-subdivided `K4` — 3 witnesses, plus the (S2)
    hub-level serial-chain `V_bc` cross-check (interior elimination).
  - `--battery [0-3]` (~2–6 min each): `W4` wheel (rim; spoke, both
    ends), `K5 − {01, 23}` (split `02`), prism+diagonal (split `01`,
    both ends) — 2 witnesses per split-class, all pitched.
  - `--mixed` (~2 min): `K4` with lengths `(3,4,2,3,3,3)` — flank (i),
    both split ends; serial-4-chain + meet-line-pair carriers
    cross-checked at hub level.
  - `--flanks` (~4 min): the hub-hub-edge member (flank (ii), both ends,
    WITNESSED) and the parallel non-`bc`-edge member `P21` — order-0
    obstructed in both slide supports; the limit stress's chain support
    and line rank exhibited (full support: the parallel pair, 6 edges
    rank 5; reduced: the theta sub-multigraph, 12 edges rank 6).

  Argument state: `notes/Pencil-informal.md` §(K-slide).

- `kslidecl.py [--k4 | --battery [0-3] | --mixed | --hubhub | --scope]` — the
  **tetrahedral collapse** (2026-08-04, fourth pass): the WW87 Thm-2.18
  specialization inside the decoration variety that factors the `(K-slide)`
  limit system into six scalar forest systems, reducing `(K-slide-cl)` to the
  combinatorial `(K-slide-comb)`. Per member it asserts `def = 0`, the
  per-edge chain-span dimension, independence of the assigned basis lines, the
  transversal identities `klein(L, C) = 0`, then (W1)–(W4) with the `V_bc`
  structure and Gram identities. `--scope` validates both
  dictionary-completeness lemmas (the `def = ℓ − 6` exemplar; the exhaustive
  length-6 sweep, 5848/5848). Exact-ℚ, on top of `repin.py`/`pitch.py`/
  `kslide.py`. Per-mode assertion list: `notes/Pencil-informal.md`
  §(K-slide-cl) *Verification*.

- `kslidecomb.py [--battery | --pack | --k5 | --acyclic | --flanks | --dict4 |
  --relaxed | --k4full | --sweep]` — the **combinatorial residue**
  (2026-08-05, fifth pass), which **REFUTES `(K-slide-comb)` class-wide**: the
  colouring premise fails at 5-chromatic `G°` and at acyclicity-obstructed
  `G°`. Surviving positive content: `--pack` proves **(C6)** (the unrestricted
  6-fold base packing exists at every class shape, Edmonds matroid partition)
  and `--dict4` proves **(C7)** ((C2)'s length-4 "forced" entry is wrong,
  12/12 exact witnesses). Every shape is re-certified by `shape_ok` = tight
  count + `def = 0` + `hnoRigid`. Exact ℚ/ℤ, on top of the whole chain.
  Per-mode assertion table: `notes/Pencil-informal.md` §(K-slide-comb)
  *Verification*.

- `flanks.py [--conj | --degen | --strata | --split | --allsplits | --pitch |
  --rzero | --limit]` — the **adversarial rank test at the uncovered flanks**
  (2026-08-05, sixth pass; research fan-out direction A), which computes the
  *geometry* at the shapes §(K-slide-comb) *Step D5* and §(K-slide) *Step 5*
  left with a combinatorial description only. It keeps two questions apart:
  half 2 (does the **pencil conjecture** hold there — a failure would disprove
  the phase's target theorem) and half 1 (does the pinned kernel `hK` hold —
  a failure would force a re-pin). Result: **no disproof** — half 2 holds at
  every flank shape by an exact `∃`-witness, and `hK` needs no re-pin. Every
  sampled configuration carries the four-conjunct `IsNondegPencilRealization`
  check **and** a star-rank genericity guard (the `plane_basis` precedent);
  exact ℚ throughout, on top of the whole chain. Run with `PYTHONHASHSEED=0`.
  - `--conj` (~10 s): half 2 at the 8 named shapes — class + habitat
    certification (`def = 0`, tight, 2EC, `hcard`, triangle-free), then an
    exact nondegenerate configuration at the Tay target, 8/8.
  - `--degen` (~4 s): the sampler control at the 5-chromatic flank — 27/27
    generic samples at the target; 11 guard-rejected samples, each short by
    exactly the number of collapsed closed stars.
  - `--strata` (~85 s): half 2 over whole strata by `rank_modp = #rows`
    certification with an exact-ℚ recheck per stratum — `K5` 210/210, 6v/11e
    155/155, `K222` 40/40 (seed 20260805), the **exhaustive** menu-blocked
    `K4` stratum 438/438: **843 shapes, 0 failures**.
  - `--split` (~193 s): half 1 at both `e₀` ends of all 8 shapes — antecedent
    witnessed and nondegenerate, hard-stratum invariants, criterion =
    observation, both KT routes escape, each escape re-certified as a half-2
    witness (16/16).
  - `--allsplits` (~176 s): half 1 at **every** eligible split of the
    5-chromatic flank — the `∀ (v, a, b)` in `hK` — 26/26.
  - `--pitch` (~65 s): (T1)–(T3) + `Q(r) ≠ 0` at all 16 flank splits, so
    (K-pitch) closes at each individually (16/16).
  - `--rzero` (~84 s): the `dim R_a = 0` stratum exhibited at last, at `P21` —
    30/5/5 seeds, `dim U = 1`, 8/8 placements fail at each jump seed (so a
    **∀-realization** escape form is REFUTED), and the jump stress's theta
    sub-multigraph support (12 edges, line rank 6).
  - `--limit` (~762 s): the (K-slide) **full-support** limit carrier at the
    flanks, 40 generic non-aligned decorations per shape, with a
    first-failing-conjunct tally — witnesses at `W5`, `W7` and the
    menu-blocked `K4` (seed 101), **none** at any of the four structural
    flanks.

  Argument state and per-mode assertion table: `notes/Pencil-informal.md`
  §(K-flank).

- `pure.py [--chord | --flanks | --support | --pure | --parallel]` — the
  **pure condition of the slide-in limit carrier, un-specialized** (2026-08-05,
  sixth pass; research fan-out direction C), which asks whether the
  class-uniform escape can be settled by a non-vanishing theorem for
  White–Whiteley 1987's pure condition instead of by the tetrahedral collapse.
  Result: **NO, and the reason is a mismatch of invariants** — the pure
  condition is a *rank* certificate (WW87 Cor. 2.7), which for the limit
  carrier is (W1) ∧ (W2), while the escape's obstruction at the uncovered
  flanks is **(W4)**, a question about the Klein *quadric*. Positive residue:
  **(PC-Z)** (`Q(z) = 0` ⟺ `V_bc` meets `α(a)` or `Λ²π̂`) and
  **(PC1)–(PC3)/(PC-OBS)**, the arc's first *proven* identically-vanishing-pitch
  theorem, governed by `R_3`-dependence of the hub-point framework; plus the
  slide **support** as the lever, which rescues 5 of the 6 probed flank shapes.
  Exact ℚ throughout, on top of `repin.py`/`pitch.py`/`kslide.py`/
  `kslidecomb.py`; every limit system is built from an honest `repin.seed_probe`
  chart seed (a hand-rolled decoration need not be chart-realizable, so it would
  not transfer under (S1)). Run with `PYTHONHASHSEED=0`.
  - `--chord` (~45 s): **(PC1)** as a length/support rule against the *measured*
    `C_uw ∈ R_P` (90 `G°`-edge instances over 6 shapes); **(PC2)**+**(PC3)** by
    assembling the chord stress as an explicit row combination of the actual
    limit rows and checking its covector is a nonzero multiple of the `C_bc`
    load; then the **census** — over the 23 candidate hub graphs with
    `|V°| ≤ 6`, `R_3`-dependence ⟺ Maxwell-overbraced (5 dependent, 18
    independent; smallest `K5`, `|E°| = 10 > 9`).
  - `--flanks` (~385 s): full-support (W1)–(W4) verdicts at 13 shapes (2
    pitched controls, 5 `K5`, the 6v11e and `K222` flanks, 3 menu-blocked `K4`,
    θ(3,4,5)), each with the chord predictor asserted against the verdict.
  - `--support` (~384 s): the 5-support menu (full; no slide at `c`; at `b`; at
    both; nowhere) at 3 `K5` shapes, 6v11e, `K222`, θ(3,4,5) — rescue = `≥ 1`
    full witness at a **nonempty** support, which is what (S1) consumes;
    `Σ = ∅` is reported separately as the `ε = 1` chart (where (S1) is vacuous)
    and then closed by the transfer certificate ((T1)–(T3) + `Q(r) ≠ 0`).
  - `--pure` (~187 s): the invariant mismatch — (W1) ∧ (W2) at every valid seed
    while `Q(z) = 0` at every one, at 4 class shapes (14/14, 12/12, 12/12,
    11/11); plus the **free-bar contrast** showing WW87 Thm 2.18 cannot transfer
    to the decoration variety (θ(3,4,5), `P21`, `K5`).
  - `--parallel` (~4 s): the corrected parallel-`G°`-edge row — at θ(3,4,5)
    (W1) and (W2) hold and the obstruction is the chord stress at (W4), not
    (S5) at (W1); and `def(C_k) = 0 ⟺ k ≤ 6`, so `hnoRigid` forces
    `ℓ₁ + ℓ₂ ≥ 7` on a parallel pair (which puts the (S5) `(3,3)` mechanism
    outside the tight class).

  Argument state and per-mode assertion table: `notes/Pencil-informal.md`
  §(K-pure).

- `lambda.py [--witt | --span | --dichot | --habitat | --l56 | --adv]` — the
  **(T5) Λ-compression's quadric** (2026-08-05, sixth pass; research fan-out
  direction B), which asks whether **(K-Λ)** — "one projective point `λ` off one
  local quadric `{Φ_loc = 0}`" — closes uniformly over the class. Result: **the
  framing was wrong and (K-Λ) is REFUTED as an *independent* gap.** `Φ_loc` is
  never the zero form and never full rank: it is always a **rank-2** form, the
  product of two distinct rational linear forms in `λ` ((Λ1)), so the quadric is
  a pair of hyperplanes; and after using (T4)'s `a`-line freedom the bad far
  covectors shrink to **two points**, which are exactly the genuine (T3) escape
  failure and a configuration where route A escapes outright — so at a
  length-4-companion split (K-Λ) is *equivalent* to **(K-wit)**. Positive
  residue: the length-3 bracket monomial gets a two-line proof, and its closed
  form extends to `ℓ = 4` as a product of two bracket-linear forms.
  Exact ℚ throughout, on top of `pitch.py` (and `repin.seed_probe` for habitat
  frames); every sampled object rank/dimension asserted; all rng seeded. Run with
  `PYTHONHASHSEED=0`. Note this file's basename is a Python keyword, so its
  primitives (`span_meet`, `pluck_of`) are not reachable by `import lambda` —
  `notes/scripts/README.md` §1.
  - `--witt` (~13 s): the Witt structure — `T` totally isotropic, `T^{⊥B}/T` a
    hyperbolic plane, `{Q = 0} ∩ T^{⊥B} = α_a ∪ β_{π_a}` (**(Λ0′)**) — then
    `dim N = 2`, `rank Q|_N = 2`, `ω±` line extensors spanning `S ∩ α/β`, and
    **(Λ1) with the scalar exactly 1** on all 16 matrix entries. 23 frames.
  - `--span` (~20 s): the two `a`-line curves `ω⁺(t)`, `ω⁻(t)` — degrees
    `≤ 3`/`≤ 2`, both spans `= 3` (**not** 4 — the pass's decisive negative
    measurement), identified as `S ∩ C(M)^{⊥B}` / `S ∩ C(bc)^{⊥B}` with
    annihilators `⟨p⁺⟩`/`⟨q⟩`, and the bracket equivalence **(Λ0f)** in both
    directions. **164 frames** over 38 local-chart strata + 4 habitats, uniformly
    `(3,3,3,2)`.
  - `--dichot` (~1 s): **(Λ2)** — `Q(z(t)) ≡ 0` exactly at `λ ∝ p⁺` / `λ ∝ q`,
    with a generic `λ` giving `≢ 0` — and **(Λ3)** `★r ∝ C(bc)` with
    `C(bc) ∉ Λ²Π̂(b)`, so route A escapes in that branch. 18 frames, 9 strata.
  - `--habitat` (~25 s): end-to-end at θ(3,4,5), NT21 and the two new
    class-certified non-theta shapes **NT24** / **NT30** — the Λ-compressed `z`
    against `pitch.z_from`, the (T2) sign law against an independently computed
    stress, (T3) agreement `escape ⟺ ¬(λ ∝ p⁺)` — plus the `ℓ = 3` corollary at
    θ(3,3,6).
  - `--l56` (~0 s): `dim(S ∩ α_a) = k − 3` for `k = 3,4,5,6` and `C(M) ∈ S ⟺
    k = 6`; at `k = 5` the Plücker reduction `(dim W, dim W^⊥,
    rank Q|_{W^⊥}) = (3,3,3)` on **both** the α/`C(M)` and β/`C(bc)` sides — a
    smooth conic, so the (F-A) bad locus gains a second equal-dimensional
    component and **`ℓ = 5,6` is refuted through this frame** (the argument
    shape, not the conjecture).
  - `--adv` (~536 s): the refutation hunt over 1497 frames (357 real habitat
    seeds + 1140 local frames) — `λ ∝ p⁺` / `λ ∝ q` / `Q(z) = 0` / `C(M) ∈ S`
    all **0**. **Denominators, corrected 2026-08-06** (§(K-out) *Step O8*): the
    first three are computed **only inside the habitat loop**, so their `0` is
    over `≤ 400` frames (4 habitats × seeds 200–299), **not** 1497 — the 1140
    local-strata frames leave the far covector free and carry no `λ` at all;
    `C(M) ∈ S` and the span histogram *are* counted in both loops, so those
    figures keep the 1497 denominator. Plus the **(Λ0d)** panel-incidence
    witness (θ(3,4,5) seed 345,
    `span ω⁻` collapsing `3 → 1`) and the two **constructed** (Λ0f) necessity
    witnesses (`p⁺₃ = 0 ⟹ span ω⁺ = 2`, `q₃ = 0 ⟹ span ω⁻ = 2`, 4/4 each).

  Argument state and per-mode assertion list: `notes/Pencil-informal.md`
  §(K-Λ).

- `dominance.py [--cap | --jac | --far | --validate]` — the **C1 dominance
  spike** (2026-08-05, ninth pass; `notes/Pencil-strategy.md` §4-C1, the one
  candidate the arc had never run). Question: is the map
  `H ↦ V_bc` into `Gr(3,6)` **dominant**? If it were, the escape would follow
  for generic reasons, because by **(PC-Z)** the failure locus is two Schubert
  `σ₁` conditions of codimension 1. This driver computes the **rank of the
  differential** at exact rational seeds and measures it against
  `dim Gr(3,6) = 9`. Result: **rank 9 (dominant) at every class habitat probed
  — and provably ≤ 4 at every length-3-companion habitat**, which `hnoRigid`
  puts outside the class but which `hK`'s (K-res) sibling carries; the far graph
  contributes at most `3(k−3)` to the rank, so C1's *inductive* claim ("the
  image grows with the far graph") is refuted. Method: `V_bc` is the image of
  the kernel of an **augmented linear system** (`m_x − m_y − ω_e C_e = 0`) whose
  entries are polynomial in the chart coordinates, so each directional
  derivative is implicit differentiation of that kernel — a derived exact-ℚ
  solve, no CAS. The chart tangent is the kernel of the differentiated pencil
  condition `⟨n_u, pt(w) − pt(u)⟩ = 0`, so the derivative never leaves the
  stratum; `pt(a)`, `pt(b)`, `pt(c)`, `Π(b)`, `Π(c)` are frozen so the bad locus
  stands still (asserted). Exact ℚ throughout, sitting on `repin`/`pitch`/
  `kslide` (and `flanks.star_span_ranks` as the `plane_basis` genericity
  guard); every sampled object rank/dimension asserted. Run with
  `PYTHONHASHSEED=0`.
  - `--cap` (~20 s): the structural ceiling, before any numerics. Path-sum
    containment asserted at **every** `b`–`c` path of `H` (21 seeds, 7
    habitats); at companion length `k = 3` the containment is an *equality*, so
    `rank Q|V_bc = 2` (asserted, and `= 3` at `k ≥ 4`) and `V_bc` sits in the
    discriminant hypersurface of `Gr(3,6)`. Also the `C_{3+k}` dichotomy — the
    split chain plus the companion is rigid iff `k ≤ 3` — cross-checked against
    `kslide.no_rigid_branch_union`, so **`hnoRigid` forces `k ≥ 4`**; and
    `V_bc ∩ α(a) = V_bc ∩ Λ²π̂ = 0` at all 21 seeds, i.e. the escape holds
    everywhere measured, including where the rank is capped.
  - `--jac` (~57 s): the rank table, 3 seeds × 7 habitats × 3 scopings (FIXED =
    the dominance measure; FREE and UNPINNED diagnostic). `k = 3`: **4** of 9,
    exactly the proven cap, and **6** with the pencil pin dropped — so the
    deficiency is path-sum containment, not the pin. `k ∈ {4,5,6}`: **9** at
    every habitat (θ(3,4,5), NT21, NT16k5, `K4` and `K5−M` double
    subdivisions), so the map is dominant there.
  - `--far` (~28 s): the far-graph block. Restricting the chart tangent to
    directions moving only vertices off the shortest companion gives rank
    `0, 3, 6, 9` at `k = 3,4,5,6` — exactly the **(T5)** bound `3(k−3)`,
    asserted and attained. At `k = 3` every far direction is in `ker dV`.
  - `--validate` (~19 s): the machinery, three ways — `V_bc` from the rigidity
    matrix (`pitch.H_motions_vbc`), from the augmented system and from the
    cycle kernel all agree; the augmented-system and cycle-kernel
    **differentials agree entry by entry**; and an exact secant quotient on a
    chart-exact ray converges to the computed differential.

  Argument state and per-mode assertion list: `notes/Pencil-informal.md`
  §(K-dom).

- `outer.py [--geom | --habitat | --sweep | --tangent | --patterns]` — the
  **outer companion bracket** `g₁₄ = [b, x₁, x₃, c] = B(C(bx₁), C(x₃c))`, the
  one factor of the (Λ0f′) span criterion (`m2/lambda0.m2`) that the harness
  asserted nowhere. Answers §(K-Λ) *What would change this* item (vi): **can a
  class habitat force `g₁₄ = 0` on its whole pencil chart**, which would give
  (Λ2) a third branch and force the Λ-completeness theorem to be restated?
  Sampling settles this one exactly, since the question is identical vanishing:
  one exact chart point with `g₁₄ ≠ 0` refutes forcing at that habitat. Sits
  beside `dominance` as a `w4/` leaf; **reads** `lambda.py` through `importlib`
  (keyword name) and never modifies it. Run with `PYTHONHASHSEED=0`.
  - `--geom` (~26 s): **(Λ0g)** — `C₁ ⊆ Π(b)` and `C₄ ⊆ Π(c)`, both panels
    contain `M`, so each outer line *always* meets `M` and
    `g₁₄ = 0 ⟺ C₁ ∩ M = C₄ ∩ M` (asserted both ways, 12 pairs). Then the
    construction: slide `pt(x₁)` inside `Π(b)` onto the line `b–(C₄ ∩ M)`,
    producing at **all four** habitats an exact pencil realization with
    `g₁₄ = 0`, every other (Λ0) clause intact, both spans `3 → 2`, and still
    **target-rank with `dim R_a = 1`**. `lambda.omega_curves`' coded (Λ0f)
    equivalence raises there — caught and reported, never repaired.
  - `--habitat` (~45 s): the named inventory (`lambda`, `dominance`, `flanks`)
    — 7 shapes carry a length-4 companion; 48 (split, seed, companion) triples
    at hard-stratum target-rank seeds, `g₁₄ ≠ 0` at every one.
  - `--sweep` (~18 s): the systematic class-shape sweep — exhaustive over the
    θ family, `G° = K4` (lengths ≤ 5) and `K4` + a parallel `bc` edge
    (lengths ≤ 6), capped at 25 per `|V°| = 5` hub graph. **1357** class
    shapes, **4280** (split, companion) pairs, all placed exactly, `g₁₄ = 0`
    at **none**; plus the **(Λ0i)** coverage split (3628 covered by the
    free-end criterion, 652 residual, all the `x₂`-a-hub pattern).
  - `--tangent` (~45 s): `d g₁₄ ≠ 0` along `dominance.build_chart`'s pencil
    tangent space (scoping FIXED) at **684/684** chart points, including all
    652 (Λ0i)-uncovered companions — so `{g₁₄ = 0}` is a proper hypersurface
    of the chart, not the whole chart.
  - `--patterns` (~299 s): the coverage boundary itself — which of the 8 hub
    patterns `(x₁, x₂, x₃)` a class companion can have, at a widened length
    bound. **4 of 8** realized; the four with ≥ 2 hubs on the companion
    interior appear in no swept family, and the driver prints that as a
    boundary rather than a theorem. *Re-run and confirmed by the coordinator,
    2026-08-05.* **Do not read its companion counts against `--sweep`'s**: the
    two modes run over different denominators (7002 vs 4280 pairs), so
    `--patterns`' 1006 `(0,1,0)` companions and `--sweep`'s 652 uncovered pairs
    are not comparable — expected, but **unreconciled**
    (`notes/scripts/README.md` *Harness debt*).

  Argument state and per-mode assertion list: `notes/Pencil-informal.md`
  §(K-Λ) *Step 3a*.

- `sigma.py [--transport | --adv | --nondeg | --fixed | --hunt]` — the **projective
  polarity `σ`** (`screwComplementIso`) as a symmetry of the split, and
  **route σ**: route A run at the *dual* seed `σu`. The whole driver works in
  **homogeneous** data — a body carries a point `P[w]` and a panel normal
  `N[w]` in `ℚ⁴` with `P[w]·N[w] = 0`, and `σu` is literally
  `(points, normals) := (N, P)` — which is why two of its helpers are
  *Divergences* rows against their affine originals (`lambda2_perp` vs
  `repin.lambda2_plane`; `nondeg_conjuncts_hom` vs `flanks.nondeg_conjuncts`).
  Sits beside `dominance`/`outer` as a `w4/` leaf. Run with `PYTHONHASHSEED=0`
  (verified byte-identical under two different hash seeds, so no printed
  collection depends on hash order).

  **One pinned seed pool for the first four modes**: two splits of the tight
  control (the double-subdivided `K4`, `|V| = 16`, target 90 / `G′` target 84),
  seeds 440–479 at chain 0 and 500–529 at chain 1, of which **34 + 29 = 63** are
  valid — i.e. survive the guards *and* land on the hard stratum (`s₀ = 0`,
  `dim R_a = 1`). Each of those modes asserts every counter equals that pool and
  asserts the pool size itself, so a sampler change that silently moved the
  pool fails the run. **`--hunt` runs on three pools of its own** (random
  1000–1059, coplanar-chain 2000–2029, (Λ0d) 3000–3019, per split), printed in
  its header and deliberately disjoint from the 63 — it exists to reach
  configurations the pinned pool cannot contain. **Do not quote a figure from
  one pool over the other.**
  - `--transport` (~87 s): **(σ4)** `ν_u ∧ ν_w ∝ ⋆(p̂_u ∧ p̂_w)` on every edge —
    "σ replaces every body's point by its own panel normal"; `rank`, `s₀`,
    `dim R_a` transported; **(σ6)** the criterion transport
    `crit_A(σu) ⟺ r ⊥̸ α_{pt(b)}` together with `r(σu) ∝ ★r(u)`; the
    six-dimensional span `β_{Π b} + β_{Π c} + α_{pt b} = K⁶` of the
    σ-completeness theorem; and route σ's witness, pulled back into `u`'s frame,
    exhibited as the `pt(v) = pt(b)` family with `pt(a)` sliding on
    `Π(a) ∩ Π(c)`.
  - `--adv` (~87 s): the adversarial half — `dim(α_{pt b} + α_{pt c}) = 5` with
    perp `★C(bc)`; `dim(β_{Π b} + β_{Π c}) = 5` with perp `★C(M)` and
    `C(M) ∦ C(bc)`; the `predA` census (**`predAfalse = 0/63`**, so (σ6)'s
    failure direction is *unwitnessed*); pullback legality; and the observation
    that routes A/B at `u` **already** escape at all 63 seeds. Also probes two
    `W19` splits (the (K-res) residual habitat) over seeds 600–619 and finds
    **0** valid hard-stratum seeds — asserted to stay empty, so a successor who
    makes it nonempty is forced to update the workbook.
  - `--nondeg` (~43 s): all four `IsNondegPencilRealization` conjuncts
    (`Motive.lean:110-115`) at `u`, at `σu` (reported **per conjunct**, because
    that is the obligation), and at the route-σ witness; plus the chart's
    binding point equations at both. `σu` nondegenerate is **observed 63/63,
    not proven** — the conjuncts are not self-dual.
  - `--fixed` (~1 s): σ-**equivariant** seed recipes are dead. Over ℝ with the
    project's definite polarity there is no σ-fixed pencil configuration at all;
    for a **null** correlation `J` every hinge line is forced into `J`'s linear
    line complex, giving a self-stress per cycle. Measured on tight `C₆`:
    **deficit exactly 1 at 6/6** placements, with `⋆S ⊥` every hinge asserted.
  - `--hunt` (~135 s, added 2026-08-05): **obligation 1**, in five legs. **H0**
    the shape's *conjunct arithmetic* (no hub–hub edge, so dual conjunct 3 is
    implied by the primal ones); **H1** a fresh random pool — **0 failures in
    107** hard-stratum draws, i.e. the failure locus is a proper subvariety and
    a random hunt cannot reach it; **H2** the **constructive** failure — the
    coplanar-chain degeneration gives **53** legal, target-rank, `s₀ = 0`,
    `dim R_a = 1`, **primally nondegenerate** seeds at which dual conjuncts 2
    and 4 FAIL at `σu`, so *Step σ4*'s 63/63 was genericity and **not** an
    implication; **H3** the **steering** — on an explicit chart line the
    offending bracket is `τ·bracket(1)` *identically* (affine in `τ`, zero at
    `τ = 0`), so the failure locus meets the line in exactly one point, and at
    every `τ ≠ 0` the seed is hard-stratum with primal and dual 4/4; **H4/H5**
    the (Λ0d) side condition — one-sided failure is reachable on the hard
    stratum (35/35, and the failing scalar *is* dual conjunct 2 on the edge
    `ac`), while forcing **both** halves leaves the split's middle body with no
    panel at all (39/39), which is the witness for **(σ7)**: primal conjunct 4
    forbids the two-sided failure, so *Step σ3*'s side condition is free.
    Uses `localtest.meet_line` behind the sanctioned **caller-side** guard
    (*Harness debt* 1), and re-imposes the sampler's own legality + star-rank
    guards on every hand-degenerated placement.

  Argument state, the four obligations and the per-mode assertion list:
  `notes/Pencil-informal.md` §(K-σ). **Route σ is a CANDIDATE offered for
  adjudication — it moves no gap-map row.**

- `closure.py [--fixed | --sweep | --shapes | --flanks | --pool | --parity |
  --collapse | --char2 | --validate]` — the polarity **over an algebraically
  closed field**. The **only** driver in the harness whose scalars are not ℚ: it
  works over the Gaussian rationals **ℚ(i)** (exact, `Gauss` = a pair of
  `Fraction`s; no floating point, no rng, so nothing to seed), because ℚ(i) is
  the smallest extension of ℚ carrying a nonzero solution of `∑ xᵢ² = 0` — and
  that single fact is the whole difference the §(K-clos) question is about. It
  uses the harness's **own** `⋆` (`repin.hodge_star`), rigidity rows
  (`hybrid_gates.build_rigidity_extensors`) and nondegeneracy checker
  (`flanks.nondeg_conjuncts`) unchanged; only the field is enlarged. Sits beside
  `dominance`/`outer`/`sigma` as a `w4/` leaf. Run with `PYTHONHASHSEED=0`
  (verified byte-identical under two different hash seeds).
  - `--fixed` (~2 s): the control **AC-C0** (no ℚ-isotropic vector in `[−3,3]⁴`;
    an explicit ℚ(i) one; the `⋆` eigenspaces `3 + 3`, ℚ-rational and mutually
    orthogonal; both rulings realizing both `⋆`-signs; the conjugacy law
    `p ⬝ᵥ p′ = 2[s,s′][u,u′]`), then **AC-E**: a σ-fixed pencil configuration of
    the tight control `ds-K4` with all four `IsNondegPencilRealization`
    conjuncts, every star of rank 3, and rank **90 = the Tay target**. So
    §(K-σ) *Step σ6*'s "the fixed locus is degenerate" is **refuted for the
    symmetric correlation** (it stands for the null one, a different locus).
  - `--sweep` (~19 s): **AC-S**, the full `ds-K4` census — all **64** ruling
    colourings satisfy `rank = rank₊ + rank₋` (a test, not a restatement: the
    two eigen-blocks are built independently of `build_rigidity_extensors`);
    every target-rank colouring is balanced with both ruling classes forests and
    both blocks isostatic at `3|V|−3 = 45`; every unbalanced one falls short.
  - `--shapes` (~7 s): **AC-U**, the 13-shape table, all colourings.
  - `--flanks` (~15 s): **AC-X**, the eight §(K-flank) flank shapes. **The `hit`
    column SATURATES at the probe cap of 6 and is not a fraction of `pass`** —
    the driver prints that caveat above the table, and the load-bearing column
    is `best`.
  - `--pool` (~21 s): **AC-Q**, the pinned 21-shape pool = exactly the union of
    the two tables above, tallied into three **disjoint** groups — tight
    (`def = 0` **and** `5|E| = 6(|V|−1)`) **15/15**, rigid-but-not-count-tight
    (`W19` alone) **1/1**, not rigid **2/5**, overall **18/21** — then every
    miss attributed against `hK`'s own hypotheses (`hnoRigid`, plus the landed
    *necessary* feasibility conditions). **This is the only leg an aggregate may
    be quoted from**; it is computed from the same rows, so it cannot drift from
    them (the `63/63`-across-inconsistent-pools defect, `notes/dispatch-log.md`).
  - `--parity` (~1 s): **AC-R2**, the one identified structural obstruction —
    over `C3…C14` the shapes admitting no colouring are exactly the **odd** ones
    `[3,5,7,9,11,13]`, and all 19 non-cycle pool shapes admit one. A tight shape
    has hubs, so it is never a bare cycle: **parity cannot be the tight-stratum
    obstruction.**
  - `--collapse` (~1 s): **AC-F**, at a σ-fixed seed route σ's uniform-failure
    criterion and route A's coincide **as subspaces** of each eigenspace,
    32/32 (16 bodies × 2 eigenspaces) — a basis-wise check would not settle an
    iff.
  - `--char2` (~1 s): **AC-2c**, `x ⬝ᵥ x = (∑xᵢ)²` on all 16 vectors of `𝔽₂⁴`
    (the fixed quadric is a double plane) and the two rank tables showing `Λ²`
    does not split; then **AC-P**, a mod-`p` table on one rational target-rank
    `ds-K4` configuration, printed as an explicitly labelled **proxy** for the
    char-`p` question — it is a statement about one seed, not about the minor.
  - `--validate` (~43 s): all eight legs.

  Argument state and per-leg assertion list: `notes/Pencil-informal.md`
  §(K-clos). **(AC-6) is REFUTED as a class statement** (`C11`, a bare odd cycle
  in `hK`'s habitat) **and open only on the tight stratum** — do not read the
  15/15 as a class result.

- `annih.py [--stress | --rate | --supp | --recipe | --census | --validate]` —
  **the annihilator as a self-stress of the contracted framework.** Exact ℚ,
  stdlib only, no CAS; a `w4/` leaf beside `dominance`/`outer`/`sigma`/`closure`,
  and the one that reimplements nothing — every primitive is imported (see
  `notes/scripts/README.md`'s layering map for the full list), with the
  `star_span_ranks` genericity guard riding in through `dominance.base_seed` and
  all rng seeded through `repin.seed_probe`. Run with `PYTHONHASHSEED=0` (all six
  modes verified byte-identical under two different hash seeds).
  - `--stress` (~30 s): **(ANH-1)** — the screw-circulation space of `H` supported
    inside the companion, compared **as a subspace** with the motion-side
    annihilator `nullspace(π_P Z)` at 18 seeds over 9 habitats, `k = 3..6`. Also
    asserts `dim = k−3`, `dof(H/P) = def(H/P) = 0` (rigidity at the pencil
    placement *and* combinatorially), the count `5|E(H/P)| − 6(|V|−1) = k−3`, and
    that `H` itself carries no self-stress.
  - `--rate` (~20 s): **(ANH-2)** the reciprocity identity
    `dλ(π_P ω) = Σ_e ω_e B(τ_e, δC_e)`, checked direction by direction and `ω` by
    `ω` against an **independent** implicit differentiation of `ker N` — 276
    far-chart directions × 828 motions; the locality of `dC`; **(ANH-3)** the
    collapsed one-Klein-pairing form at 192 single-vertex moves (zero-pitch `ρ_y`
    at **0/192**, which is why the section says *one pairing*, not *one bracket*);
    and **(ANH-5)** as a **subspace identity**, not a coincidence of booleans.
  - `--supp` (~81 s): **(ANH-4)**'s realized side. `C_pen ⊆ C_gen` with `C_gen`
    from `count_matroid_rank` on `5(H/P)` and `C_pen` computed **twice** (full
    solve, and a stress space rebuilt on the reduced edge list); 16 seeds, equality
    at all, and `|C_pen| = |E(H/P)|` at **14/14 class seeds** — the support is the
    whole far edge set, so the named move needs no support-location step. Also
    prints the far block of `rank dλ` (3 / 6 / 9 at `k = 4/5/6`), reproducing
    §(K-dom) *(D2)* through the annihilator. The **off-class control**
    `θ4(3,4,5,6)` (tight, `def = 0`, `hcard`, triangle-free, but `hnoRigid`
    **false**, asserted at load) is what makes the off-support tests non-vacuous:
    its circuit is a proper 5-cycle, and `dV = 0` at all 13 single-vertex moves off
    it.
  - `--recipe` (~37 s): **(ANH-7)** at 56 (length-5 branch, free middle body)
    sites over 2 named exemplars, 6 swept `K4` shapes nobody hand-picked, and the
    control — `κ_β` 1-dimensional, `τ_β ∝ κ_β`, the equivalence
    `κ_β ∝ C(w₁w₃) ⟺ [w₁,w₃,w₄,w₅] = 0`, and the general `(V_y ∧ U_y)^{⊥B}`
    criterion alongside the closed form. 56/56 correct, 32 sites at `dim U_y = 2`
    and 24 at `dim U_y = 1`.
  - `--census` (~23 s): 4296 (shape, split, length-4 companion) triples —
    `girth(H/P) ≥ 6` unless `|E(H/P)| = 5` (8 cases, all θ(3,4,5)); the circuit
    certificate at 400 of them (budgeted); the branch-length histogram capped at
    **5**, which is the *Shared dictionary*'s **(SD-6)**; and the same generators
    re-run past length 6 (θ families to 12, `K4`/`K4+par` to 7) as an (SD-6) stress
    test. Coverage of the closed form: **3820/4296 = 89 %**.
  - `--validate` (~8 s): the machinery — the Hodge dictionary
    `⟨★τ, C⟩ = B(τ, C)`, `λ` annihilating `π_P(Z)`, `λ ∈ row(N)`, transmissibility
    off `P`, and `V_bc` reconstructed from `Z` in the `C`-basis, at 4 habitats.

  Argument state, the F11 claim→mode table and the confidence verdict:
  `notes/Pencil-informal.md` §(K-ann). **The recipe's kernel is class-uniform;
  its two inputs are not** — quote (ANH-7) only with **(ANH-R1)** (`τ_β ≠ 0` at
  the pencil placement, **open**, relocation #4) attached.

- `outerline.py [--comb | --pool | --shapes | --build]` — **(OUT)'s hypothesis,
  measured.** Answers §(K-Λ) *What would change this* item (viii) and *Step 5a*'s
  "never evaluated anywhere in the arc": `lambda.py --adv` computes `λ` but
  reports only the two proportionalities, never `λ₁` and `λ₄` separately, and
  `λ₁ = 0 ⟺ C₁ ∈ V_bc` is exactly (OUT)'s first disjunct failing. Exact ℚ,
  stdlib only; a `w4/` leaf beside
  `dominance`/`outer`/`sigma`/`closure`/`annih`, importing only catalogued §1
  primitives and **modifying nothing** (`lambda.py` and `outer.py` are read).
  Run with `PYTHONHASHSEED=0` (all four modes verified byte-identical under two
  different hash seeds). **Each mode prints its pool, and no figure is
  aggregated across two pools.**
  - `--comb` (~14 s): **(OC-2)** over **POOL-C** (deterministic, no rng: the 4
    habitats, `outer.named_inventory()`, every `outer.sweep_shapes()` family) —
    **4296** (split, companion) pairs, all with `χ = 0`, `def(H/X) = def(H/Y) =
    0` and `(μ, dim R, A) = (1, 5, 0)` on **both** sides, plus the `5χ` count
    identity for `H/X` per pair. **This is the *ambient*-generic count
    (`nogood_subdiv.deficiency`) and it does NOT discharge (OUT)**: the pencil
    chart is a proper subvariety, which is the whole point of `--build`.
  - `--pool` (~358 s): **POOL-G** = the 4 `lambda.habitat_specs` habitats ×
    placement seeds 200–299, **357 frames** (16 no placement, 27 star-span
    rejects), with (Λ0d) failures **kept and reported**. **(OC-1)** the welded
    relative-twist chain (`λᵢ = 0 ⟺ C_i ∈ V_bc ⟺ dim W_i = 1 ⟺ C_i ∈ R_i`)
    asserted at 46 frames; **(OC-5)** the distribution `322/17/17/1`, (OUT)'s
    hypothesis at 356/357 and its **conclusion** separately at 356/356, plus the
    codimension-1 rates of every (Λ0) bracket over the same pool; **(OC-7)** the
    sampler diagnostics. `λ` cross-checked against `lambda.habitat_frame` at 20
    frames. **Quote its rates over the 318 coincidence-free frames, never the
    raw 357** (*Harness debt* 4).
  - `--shapes` (~322 s): **(OC-6)** over **POOL-S** — 41 class shapes (the
    19-shape named inventory + the first 4 of each sweep family), every eligible
    split, seeds 1–39, ≤ 3 frames per split: **270 frames over 90 splits**,
    hypothesis 270/270, **0** (split, companion) pairs with no available frame.
    **POOL-S is disjoint from POOL-G and its figures are never summed with
    POOL-G's.**
  - `--build` (~10 s): **POOL-B** — the 4 habitats × seeds 200–259, slides from
    a fixed list. **(OC-3)** on-chart (`dim R = 5`, `dim(R ∩ L) = 1`, never 2)
    and **(OC-4)** the construction: slide `pt(x₁)`/`pt(x₃)` onto their marked
    directions and land, at all four habitats, an exact chart point with
    `λ₁ = λ₄ = 0` — **(OUT) SILENT** — keeping every (Λ0) clause, the target
    rank, `dim R_a = 1` and all four `IsNondegPencilRealization` conjuncts, with
    `deg_t Q(z(t)) = 4` so the escape still holds. **3 of the 4 carry no
    coincident hinge line**, which is what makes the locus real rather than an
    artifact of *Harness debt* 4.

  Note `outerline` imports `localtest.plane_basis` **as a diagnostic only**
  (aliased `DEGENERATE_PLANE_BASIS`) — it never samples with it; (OC-7) needs to
  know when the degenerate basis fires.

  Argument state, the pool definitions and the per-mode assertion list:
  `notes/Pencil-informal.md` §(K-out). **The headline is the NEGATIVE (OC-3) —
  the bad locus is nonempty on every class shape's chart, so no counting
  argument can ever deliver (OUT)'s hypothesis; what the pools establish is
  availability, MEASURED, not proven.**
