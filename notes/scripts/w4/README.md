# Phase 39 W4 (`hcontract`) recon — and the whole kernel-(K) continuation

**Start from `notes/scripts/README.md`** — the harness-wide primitive index,
layering map, full invocation table (including `kslidecl.py` / `kslidecomb.py`,
which this file does not describe), and conventions. This file is the
per-driver description list for this directory.

**The directory name is stale, deliberately so.** `w4/` was opened for the
`hcontract` (W4) arm, but it now also carries the kernel-(K) continuation —
`(K-tight)` (`repin.py`), `(K-pitch)` (`pitch.py`), `(K-slide)` (`kslide.py`),
`(K-slide-cl)` (`kslidecl.py`), `(K-slide-comb)` (`kslidecomb.py`). A rename is
churn until the (K) arc closes; see `notes/scripts/README.md` *Deliberate
non-goals*.

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
