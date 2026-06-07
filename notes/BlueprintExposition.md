# Blueprint exposition ledger — hard nodes deserving a fully detailed account

**Purpose.** One of the project's deliverables is a *fully detailed,
self-contained exposition* of Katoh–Tanigawa's most intricate arguments —
spelling out the steps a research paper reasonably compresses (and the details
formalization forces explicit), so each crux is followable end-to-end by a
reader without the authors' context. This **complements** KT's necessarily
terse research exposition; it is not a verdict on KT's clarity. (Where
formalizing did surface a genuine gap or slip, the relevant entry records that
factually — routine in formalization work, not a knock on the paper.) The
blueprint stays terse-by-default (carleson style, 1–3 sentence proofs —
`blueprint/CLAUDE.md` *Proof verbosity*), but **crux nodes earn full, followable
exposition**. This file is the cross-phase *ledger* of which nodes have earned
that treatment and whether the exposition has landed.

It is a **capture-now / write-later** mechanism (agreed with the project owner,
2026-06-04):

- **Capture (cheap, while fresh).** When a node initially scoped as one commit
  turns out to be much harder and gets rerouted / reworked / decomposed, add a
  one-line entry here naming the *stable* mathematical insight the reroute
  surfaced — the case structure KT states compactly, why a strengthening is
  forced, where the real difficulty sits. "Thought-one-commit → rerouted" is the
  primary trigger and is recoverable from git history for retroactive entries.
- **Write (at phase-close, once the argument is `sorry`-free).** The expanded
  blueprint prose lands in the phase-close end-to-end blueprint pass, *not*
  during the churny recon — the clean argument (and any simplification toward
  KT's own style) is only known once the result is final. That pass is
  broadened from "collapse formalization asides" to *also* "add the detailed
  exposition for that phase's ledgered nodes."

**Out of scope** (these stay terse / excluded, per the existing rules):
Lean-*modelling* narration ("basis-free", "Layer 4b reshaped …") and
mathlib-standard background. The carve-out is for *mathematical difficulty*,
not Lean verbosity.

**Inclusion criterion (sharpened 2026-06-04).** The difficulty must be
**source-side** — genuinely in *KT's mathematics* — not **project-side** (our
formalization setup). (These two terms, *source-side* / *project-side*, are used
throughout the ledger for the in-scope vs. excluded distinction.) **Exclude**
entries whose trigger was a project-side mistake/misunderstanding about something
KT was
actually clear on — e.g. an early draft that proved the wrong (weaker) theorem
because a constraint wasn't yet encoded. The "thought-one-commit → rerouted"
signal is *suggestive, not sufficient*: a reroute caused by our own setup error
does not earn an entry. (Calibration: the Phase-21 panel-coplanarity re-scope is
excluded — KT is clear the conjecture is the *hinge-coplanar* case; our first
draft just hadn't encoded coplanarity.)

**Codification status (updated 2026-06-06, after 22d).** The **capture/tracking
side is now codified**: this ledger is referenced from the standing process docs
— `notes/CLAUDE.md` (the directory file list), top-level `CLAUDE.md` *When this
commit closes a phase* (the blueprint re-read step now also writes ledgered
nodes), `blueprint/CLAUDE.md` *Proof verbosity* (the crux-node carve-out), and
`notes/MolecularConjecture.md`. The format, the sharpened inclusion criterion
(KT-math, not project-side setup), and the `(a)/(b)/(c)` flavors are stable.
**The write stage has now begun:** the first expositions landed at 22b-close (the
`lem:claim-6-4` three-brick assembly) and 22d-close (the `lem:case-III-claim-6-11`
Gap-2→3→1 chain, this commit). The write-late timing held up — both were written
once the argument was `sorry`-free, so the clean account was stable. The
remaining `pending` entries write at their own phase-close (Lemma 2.1 + Prop 1.1
when Case III completes; Phase-20 forest-surgery on its next touch).

## Format

One entry per node, grouped by destination blueprint chapter:

> `label / Lean name` — [status] **(flavor)** trigger; **stable insight to expose** — pointer

where `status ∈ {pending, done (<commit>)}` and **flavor** is one of:

- **(a) compressed step** — a step KT states compactly (or, where formalizing
  found one, a genuine gap or slip) that the formalization expands in full /
  makes explicit. The core of the deliverable, and the prototypical *source-side*
  difficulty the ledger exists to surface.
- **(b) KT-simplification** — the formalization found a shorter / more direct
  route than KT's; an alternative presentation, not a filled gap.
- **(c) hard-but-not-rerouted** — load-bearing and genuinely hard, but landed as
  first scoped. Lower priority; included because the goal is making the hard
  parts followable, not only the rerouted ones.

## Ledger

### `extensor.tex` — Phase 17 (Grassmann–Cayley / Lemma 2.1)

- **Lemma 2.1 (`omitTwoExtensor_linearIndependent`)** — [pending] **(c)** landed
  as scoped (no reroute); flagged for difficulty. **Stable insight:** the
  independence of the `D = (d+1 choose 2)` many `(d−1)`-extensors of `d+1`
  affinely independent points — join-on-the-left kills the off-diagonal terms,
  the `pairAppend` bijection handles the diagonal. The deepest single
  linear-algebra fact in the program; Case III (Phases 22b+/23) bottoms out on
  it. Pointer: `notes/Phase17.md`.

### `rigidity-matrix.tex` — Phase 18 (R(G,p), rank Lemmas 5.1–5.3)

- **`prop:rigidity-matrix-prop11` (KT Prop 1.1)** — [pending] **(a)** scoped to
  18 → deferred to 19 → relocated forward to 21+. **Stable insight:** Prop 1.1
  is *two genuinely separate halves* KT presents as one — the **matroidal**
  `def = corank M(G̃)` (combinatorial, JJ09 min–max) and the **analytic**
  `rank R(G,p) = D(|V|−1) − def(G̃)` (generic, needs the genericity device).
  Closing the matroidal half does not touch the analytic half. Pointer:
  `notes/Phase18.md` *Hand-off*; `notes/Phase19.md` *Hand-off*.

### `deficiency.tex` — Phase 19 (M(G̃), deficiency, k-dof)

- *Scanned 2026-06-04, no candidate.* Every node landed as scoped, including the
  full axiom-free `thm:def-eq-corank`. The one forward-looking finding (Prop
  1.1's two halves) is filed under `rigidity-matrix.tex` above.

### `molecular-induction.tex` — Phase 20 (combinatorial induction, Thm 4.9)

- **KT Lemma 4.1 / forest-surgery track (`kt_lemma_41_overquantified`,
  `lem:forest-surgery-split` family)** — [pending] **(a)**, the richest entry.
  Planned hard core; turned out over-quantified, rerouted onto
  deficiency-counting. **Stable insight (KT-non-erring framing):** (1) Lemma 4.1
  as-quantified is *false* — it quantifies over independent sets but
  `|I'| = |I|−D` needs bases. (2) Its base case silently assumes the chosen
  `D`-forest packing is *balanced at `v`* (every forest meets `v`), unjustified
  in KT; recovered via a pendant/bridge finite-descent (no `D ≥ 3`
  counterexample — a gap, not an error). (3) The induction needs only
  `def(G̃ᵥᵃᵇ) ≤ def(G̃)`, by partition-count through `def = corank`, routing
  around the surgery entirely. Pointer: `notes/Phase20.md` *Findings*.
- **`lem:removal-deficiency` (KT 4.4, `removeVertex_deficiency_ge`)** — [pending]
  **(b)**. **Stable insight:** a shorter deficiency-count route than KT's `h'=0`
  unsplit-forest argument (which is itself sound): the `−(D−1)·d` sign in
  `partitionDef` makes dropping the crossing-count `d` the *helpful* direction,
  and in the part-losing case `v`'s two neighbours are *forced* into distinct
  blocks, so `c=2` — the `+2(D−1)` crossing-drop pays for the `−D` part-loss
  exactly when `D ≥ 2`. Pointer: `notes/Phase20.md` *Findings*.
- **`lem:reduction-step` (KT 4.7–4.8, `splitOff_isMinimalKDof`)** — [pending]
  **(b)** *(borderline toward bookkeeping)*. **Stable insight:** KT's iterated
  fundamental-circuit swap is bypassed by one rank count — KT 4.10 makes
  `E(G̃_v)` a base of `M(G̃_v)`, so with KT 4.7 (`def > 0`) a single cardinality
  split of any fiber-avoiding base contradicts `isBase_ncard_add_deficiency_eq`;
  no matroid minor, no swap induction. Pointer: `notes/Phase20.md`; FRICTION
  *[matroid] Transporting circuits …*.

### `meet.tex` — Phase 21a (meet / projective duality)

- **`def:meet-complement-iso` / `complementIso`** — [pending] **(b)**. **Stable
  insight:** the regressive product (meet) needs only the *nondegeneracy* of the
  wedge pairing `⋀ʲV × ⋀^(N−j)V → ⋀ᴺV ≅ ℝ`, not the oriented `j ↔ N−j` sign —
  the pairing matrix is a signed-permutation matrix and `complementIso` reads off
  only "diagonal ≠ 0"; the orientation/sign bookkeeping KT carries is deferrable
  to a consumer that actually reads an oriented meet. Pointer:
  `notes/Phase21a.md` *Decisions* + *Blockers*.

### `algebraic-induction.tex` — Phases 21 / 21b / 22a (Thm 5.5, Cases I/II/III, genericity device)

- **`lem:case-I-realization` (N6 composer)** — [pending] **(a)** thought 1 commit
  → reconned into N6-G1/G2/G3 (2026-06-04). **Stable insight:** KT §6.2 Case I is
  a *trifurcation* (Lemmas 6.2 non-simple, 6.3 `G/E′`-simple, 6.5 degree-2 vertex
  removal), not a uniform contraction recursion; and the realization motive must
  be *strengthened to general position* on the inductive legs (the composer's
  per-leg adapter consumes `HasGenericFullRankRealization`, while the induction
  threads only the bare motive). Pointer: `notes/Phase22-realization-design.md`
  §1.5–1.6; `notes/Phase22a.md`.
- **conditioned motive `Pc := (G.Simple → GP) ∧ bare` (`theorem_55_generic`;
  folds into `lem:case-I-realization` prose)** — [pending] **(a)** G2a
  (`f35be5d`). **Stable insight:** the generic motive must be *conditioned on
  simplicity* — KT's "nonparallel, if `G` is simple" (printed p.669);
  unconditional general position is *false* at the parallel-`K₂` base. Pointer:
  `notes/Phase22-realization-design.md` §1.6.
- **contraction simplicity `rigidContract_simple` / `map_simple` (folds into
  `lem:case-I-realization` prose)** — [pending] **(a)** G2b (`b9000ef`). **Stable
  insight:** vertex-relabelling (`map`) is the *one* graph op that breaks
  `Simple` — it can manufacture both loops (collapse an edge's endpoints) and
  parallel edges (collapse two edges onto one pair), so unlike `↾`/`＼`/`-`/induce
  it has no unconditional `Simple` instance. This is *why* Case I trifurcates:
  `G/E′` simple is a genuine *case hypothesis* (Lemma 6.3), its failure routed to
  Lemma 6.5's vertex-*removal* (which does preserve simplicity). Pointer:
  `notes/Phase22-realization-design.md` §1.6; `notes/Phase22a.md`.
- **`lem:case-III` / `theorem_55.hsplit` (Case-naming + one-row shortfall)** —
  [pending] **(a)**. **Stable insight (the decisive distinction):** KT's cases key
  on the dof `k`, *not* the graph operation — **Case II (Lemma 6.8) is `k>0`**
  (`+(D−1)` rows suffice for the lower target `D(|V|−1)−k`), while the **`k=0`
  split is Case III**: eq. (6.12) reaches only `D(|V|−1)−1`, *one rigidity row
  short*, the missing row being the redundant-edge / `M(G̃)`-base argument of
  Lemma 6.10/6.13. Labelling by surface analogy ("degree-2 split ⇒ Case II") hid
  the single hardest sub-proof in KT. Pointer: `DESIGN.md` *Phase Case-naming
  must match KT's k-bookkeeping*; `notes/Phase21b.md` *Finding B*.
- **`lem:case-III-claim-6-11` / the redundant `ab`-row — where the real difficulty
  sits (Gap-2→3→1, Phase 22d)** — [done (`case-iii.tex`, 22d-close)] **(a)**. **Stable
  insight:** KT's discharge of the redundant `ab`-row factors as (Gap 2) a matroid-base
  fact (`ãb ⊄` some base of `M(G̃_v^{ab})`), (Gap 3) eq. (6.22) computing the rank of the
  *specific* restricted realization `R(G_v, q|_{E_v})`, and (Gap 1) a pigeonhole turning
  the matroid redundancy into a linear one. The research-shaped **kernel is Gap 3's eq.
  (6.22), which bottoms on KT footnote 6**: *one nonparallel realization attaining the
  rank ⟹ all generic ones do, and the already-chosen seed `q` restricted to `E_v` inherits
  algebraic independence, so it is itself generic and attains the rank.* This is a
  **rank-of-a-given-seed** statement — a different object from the *existence* of a
  full-rank realization (the form the project's IH motive `HasFullRankRealization`
  supplies), and the Phase-21b genericity device runs the opposite direction (one-point
  independence ⟹ existence of a good point) — which is why it forced the project's first
  algebraic-independence use (footnote 6: "*this* seed", not "*∃* a seed"; tracker
  `notes/AlgebraicIndependence.md`). So Gaps 3+1 share one kernel — "the rigidity matrix at
  the inductively-fixed seed attains the rank `M(G̃)` predicts" — the genuinely-new
  analytic content. **Whole chain green + axiom-clean at 22d-close:**
  `lem:case-III-claim-6-11-base` (Gap 2), `lem:case-III-gap3-minimalKDof` (Gap 3
  combinatorial), the seed-rank kernel (`lem:case-III-seed-rank-bridge` `def=0` rigidity
  transfer + `-seed-rank-upper` `def>0` upper bound + `-rank-attainment` exact rank), and
  the pigeonhole + row-set identity feeding `lem:case-III-claim-6-11` (Gap 1, the
  eq.-(6.18)/(6.22)⟹(6.23) discharge). **Written** (22d-close, this commit): the
  `case-iii.tex` proofs spell the Gap-2→3→1 argument out in full, including the
  footnote-6 rational-`Q`/alg-indep-non-root step and the row-set identity that instantiates
  the abstract pigeonhole at `G_v^{ab}` / `G_v`. What stays *open* (deferred successor) is
  not Claim 6.11 but the **candidate-completion** that converts its redundant `ab`-row into
  the missing `+1` full-rank row (eq. (6.24)→(6.29)) + the Claim-6.12 disjunction. Pointer:
  `notes/Phase22d.md`; ROADMAP §22d; KT pp. 684–685, eq. (6.22) + footnote 6.
- **`lem:case-III-candidate-row` / `lem:case-III-columnop` — the eq. (6.27) transport's off-`v`
  vanishing is the eqs. (6.14)–(6.16) *column operation*, not the seam + eq. (6.43)** — [pending]
  **(c)** (Phase 22e capture — a reroute correcting a mis-identified mechanism). **Stable insight:**
  KT eqs. (6.27)→(6.28) claim the transported row `w`'s `V∖{v}` part vanishes; a Phase-22e recon
  found *which* fact makes it vanish was mis-read. The transported row collapses (using the eq.-(6.24)
  decomposition `g = 0`) to `w = hingeRow v a ρ_g` with `ρ_g = Σⱼ λ_{(ab)j} r_j ≠ 0`, supported on
  *both* columns `v` and `a`: in the natural frame `w S = ρ_g(S v − S a) = −ρ_g(S a) ≠ 0` at
  `S v = 0`, so it does **not** vanish off `v` on its own. The vanishing is KT's eqs. (6.14)–(6.15)
  column operation `col_a += col_v`, modelled as the `≃ₗ` automorphism `Φ S = update S v (S v + S a)`
  (`columnOp`): `w(Φ S) = ρ_g((S v + S a) − S a) = ρ_g(S v)`, pure `v`-column. eq. (6.43) (the
  `a`-block of the eq.-(6.24) vanishing combination is `0`) is a *Claim-6.12* (`M3`-case) fact, not
  this one — the project briefly wired it as the candidate-row input before the recon corrected it.
  **Construction-core simplification (22e, `lem:case-III-candidate-row-construction`):** the
  combination needs no per-row `λ`-expansion — the redundant row's *common* element `wGv`
  (its `G_v`-row part `= r i* − wOther`) is a single `ab`-block element, hence `hingeRow a b ρ`
  for one `ρ ∈ r(p(e₀))` (by `span_panelRow_edge_eq`); the whole transport collapses at that one `ρ`
  to `w = hingeRow v a ρ`, with `hingeRow v b ρ` the genuine transported `(vb)i*` rigidity row.
  Pointer: `notes/Phase22e.md` *Decisions*; KT pp. 683–686 (eqs. 6.14–6.16); `lem:case-III-columnop`
  + `lem:case-III-candidate-row` proof + `lem:case-III-candidate-row-construction`.
- **`lem:case-II-realization` / eq. (6.12) degenerate placement** — [pending]
  **(a)**. **Stable insight:** KT's construction (Lemma 6.8, eq. 6.12) is
  *row-side with a degenerate placement* — `p1(vb) = q(ab)` places `v`'s new
  hinge *at the* `e₀=ab` *hinge of the inductive realization*, so column ops make
  `R(G,p1)` block-triangular with the `vb`-row reproducing the `e₀`-row; a slight
  rotation (Lemma 5.2 semicontinuity) lifts to nonparallel. The motion-side route
  KT gestures at ("a motion constant on `V(G)∖{v}`") is unsound — a `G`-motion
  need not be (`G−v` isn't rigid). **Stratum-1 Lean refinement (Phase 22c):** the
  reproduction is the *shear in one panel-normal slot* — placing `v`'s normal at
  `n_a + t·n_b` makes the `vb`-extensor `=` the `ab`-extensor *for any `t`* (the
  `n_b∧n_b=0` term, `panelSupportExtensor_add_smul_right`), while `t≠0` keeps the
  `va`-extensor `= (-t)·` the `ab`-extensor `≠0` (`_left`) — so the `t=0` placement
  `v=a` is the trap (zeros the `va`-line, a degenerate candidate), and KT's genuine
  eq. (6.12) candidate needs `t≠0`. The `+(D−1)` lower bound is then the pin-a-body
  `Sum.elim` of the new edge's `D−1` rows and the IH-transported old block.
  Pointer: `notes/Phase21b.md` *Finding A*; `notes/Phase22c.md` (stratum 1).
- **`lem:case-I-realization` realization mechanism — KT eq. (6.3) block-triangular
  rank-ADDITION** — [pending] **(c)** *(landed via a block-triangular reframe; the
  reroute that preceded it was project-side, see note)*. **Stable insight:** Case I's
  realization is KT eq. (6.3)'s block-triangular **rank-addition**: the rigid-block
  rows (edges `E(H)`) occupy *only* the `V(H)` columns (the matrix's top-right `0`),
  so at *one* placement the rigid-block rank `D(|V(H)|−1)` and the surviving-edge
  (`E(G)∖E(H)`) rank `D(|s_c|−1)` **add** to `D(|V(G)|−1)`, and the genericity device
  reads rigidity off that independent-row *count*. The two row-blocks are made jointly
  independent by the **exterior-column projection** onto `V(G)∖V(H)` (where the
  rigid-block rows vanish — the row-side of the top-right `0`); crucially there is
  **no** need for a common placement on which *both* legs are simultaneously rigid.
  *Project-side reroute note (excluded from the source-side core per the inclusion
  criterion):* an earlier draft formalized this as a motion-space **common-seed splice
  glue** (one `q₀` rigid on both legs) — a re-expression of KT's clear block-triangular
  structure that the project's motion-space rigidity model made the *natural*
  composition; it type-checked but kept demanding undischargeable bridge hypotheses
  (`hcrig`→`hpinc`→`htransportGP`→`∀`-GP), and was abandoned for the row-addition above.
  That divergence is a *process* lesson — project-side, not a source-side
  difficulty → `DESIGN.md` *Match the source's argument structure, not just its
  conclusion*. Pointer:
  `notes/Phase22-realization-design.md` §1.13–§1.16; `notes/Phase22a.md`.
- **`lem:case-I-realization` N6-G3 / Claim 6.4 — the splice's contraction leg is
  `G ＼ E(H)`, not the relabelled contraction; the collapse is placement-side** —
  [pending] **(a)** thought "pure leg-data geometry" → reconned into G3a/G3b/G3c
  (2026-06-05). **Stable insight:** KT's Case-I block matrix (eq. 6.3) splices the
  rigid block `R(G′,p1)` against `R(G,p; E∖E′, V∖V′)` — the *parent restricted to
  the surviving edges* `E(G)∖E(H)`, i.e. `G.deleteEdges E(H)` (a genuine subgraph),
  **not** the abstract relabelled contraction `G/E′`. The vertex-collapse `V′↦v∗`
  is entirely a *placement* operation (eq. 6.7's `p_{E∖E′}`, with `v∗` realized as
  a `d`-dimensional body rather than a panel), and **Claim 6.4** (eq. 6.9) is the
  rank-transport that the surviving-edge realization of `G ＼ E(H)` attains the
  contraction's rank — riding on the algebraic-independence (general position) of
  the joint `p1`/`p2` coefficients. The "contract the graph then splice it back"
  reading conflates a graph operation with a placement one; the formalization is
  forced to keep the splice leg `≤ G` and carry the collapse on the seed.
  **Sharpened at G3a (`a…`, 2026-06-05):** the math-first pass confirmed Claim 6.4
  is *irreducible* — the natural Lean lever (the motion space sees only linking-edge
  support extensors) does **not** discharge it, because `collapseTo r V(H)` redirects
  each surviving edge's *endpoints*, so its support extensor
  `panelSupportExtensor (q u) (q v)` uses *different normals* in `G/E′` vs.
  `G ＼ E(H)` and the spans differ — recovering the rank at the un-collapsed endpoints
  is exactly the algebraic-independence content. So the rank-transport across the
  relabel is genuinely new analytic content (not a structural rename), and G3a carries
  it as the explicit hypothesis `htransport` (green-modulo). **Final form (block-triangular
  reframe, §1.13–§1.16):** the residual is now the red node `lem:claim-6-4` = the surviving
  block's *exterior-column-projected row-independence* (`(extProj V(H)).dualMap`, the
  `V∖V′`-restricted rank `D(|s_c|−1)` of eq. (6.9)), carried by `case_I_realization` in the
  `Qc`-non-root form (`∃ Qc ≠ 0, ∀ q, eval q Qc ≠ 0 → …`) — *not* the `∃`-form `htransport`,
  and *not* a `∀`-general-position statement. (The `∀`-GP-vs-generic-locus distinction — KT's
  "generic" is a Zariski-open *locus* / rank-poly non-roots, never "every GP placement" — was
  itself a recurring project-side trap; process lesson in `DESIGN.md` *Match the source's
  argument structure …*.) Pointer: `notes/Phase22-realization-design.md` §1.7, §1.13–§1.16;
  `notes/Phase22a.md` *Decisions*; `notes/Phase22b.md` (the discharge).
  **Sharpened at U3b (§1.22, 2026-06-05):** the exterior-projection rank-preservation reduces
  (mathlib dual API) to `Z ⊔ range(extProj V(H)) = ⊤`, whose one real-content fact is the
  rigid-block **pin-count** `finrank(pinnedMotionsOn V(H)) = D(|scᶜ| + 1 − |V(H)|)`. **Stable
  insight (the §1.21 correction):** a framework rigid on a *proper* vertex set `V(F) ⊊ α` does
  **not** have a zero residual after pinning a body — its null space carries `D·|V(F)ᶜ|` free
  *isolated-body* dimensions (one free screw per body outside the graph). So the clean `D(|sc|−1)`
  projected rank of Claim 6.4 survives by an **exact free-isolated-body cancellation** between the
  row-space gain and the projection's column loss, certified by the pin-count — not by a
  zero-rank-loss pin. The pin-count itself is `pinnedMotionsOn t = pinnedMotionsOn (V(F) ∪ t)`
  (rigidity propagates `S r = 0` over `V(F)`) ⇒ exact free count `D·|(V(F)∪t)ᶜ|` ⇒ incl.–excl. on
  `|V(F) ∩ t| = 1`. Pointer: §1.22; `Pinning.lean`
  `finrank_pinnedMotionsOn_of_isInfinitesimallyRigidOn_vertexSet_inter_eq_singleton`.
  **Sharpened at U3a/route-(i) (§1.23–§1.24, 2026-06-05):** the rank-transport needs the
  contraction's generic realization *rigid at the relabel selector* `endsᵐ = f ∘ ends`, but
  the IH motive `HasGenericFullRankRealization` carries a *free* endpoint selector with no
  link-recording invariant — so the rigidity does not transport to `endsᵐ` (the same gap is the
  `H`-leg's `hswap`). **Stable insight:** a panel-hinge realization's hinge constraint reads
  `supportExtensor e = panelSupportExtensor (normal (ends e))`, so the motion space *depends on
  the selector*; transporting rigidity across a relabel needs both selectors to record the same
  graph's links (then they agree up to swap and the motion spaces coincide). The honest fix is to
  **strengthen the motive** to carry "the realization's `ends` records its own graph's links",
  which then derives the relabel-leg transport *and* the `H`-leg alignment. **Written (22b-close,
  this commit):** the `lem:claim-6-4` blueprint proof now spells out the three-brick assembly
  (U3a alignment / U3b zero-rank-loss / U2-at-U1 collapse-relabel reproduction) — `done`. The first
  exposition to land, so the *Proof verbosity* write-stage codification (lines 57–63) can now be
  revisited.
- **`lem:case-I-realization` N6-G3-G3c / the two splice legs live on *different*
  body sets, `V′` and `V∖V′ ∪ {v∗}`** — [pending] **(a)** thought "pure green-brick
  assembly (`buildable`)" → reconned into G3c-i/ii/iii (2026-06-05). **Stable
  insight:** KT eq. (6.3)'s second block is `R(G,p; E∖E′, V∖V′)` — the parent
  restricted to surviving edges *and surviving bodies* `V∖V′`; the rank bookkeeping
  `D(|V′|−1) + D(|V∖V′ ∪ {v∗}|−1) − k = D(|V|−1)−k` is a sum over **two distinct body
  sets**, the rigid block's `V′` and the contraction's `V∖V′ ∪ {v∗}`. The contraction
  leg is rigid *only* on `V∖V′ ∪ {v∗}` (the surviving edges leave the interior `V′∖{v∗}`
  free), not on the parent's full `V`. KT's own splice respects this body-set split;
  the formalization's earlier (all-of-`V`-leg) couplings had collapsed `sc := V(Gc)`
  because every prior leg *was* rigid on its full vertex set — the contraction is the
  first leg that is not, which exposes the collapse and forces the witness-transfer
  producers (rank polynomial, coupling) to thread a per-leg body set `sH`/`sc` and
  finish on the honest base glue `isInfinitesimallyRigidOn_of_splice` (which always
  supported arbitrary body sets). *(Borderline by the sharpened inclusion criterion:
  the body-set restriction is something KT states in eq. (6.3); our coupling just
  hadn't encoded it. Kept because the `V∖V′`-body bookkeeping is load-bearing KT
  content the splice rank-count rests on, and the "splice contraction = rigid on all
  of `V`" reading is a natural mis-step the formalization forced open.)* Pointer:
  `notes/Phase22-realization-design.md` §1.8; `notes/Phase22a.md` *Decisions*.
- **`lem:case-I-realization` N4 union↔contraction crux
  (`rigidContract_isMinimalKDof`)** — [pending] **(a), model-induced**. **Stable
  insight:** `Matroid.Union` does *not* commute with contraction, so
  `M((G/E(H))̃) = M(G̃)/E(H̃)` is not a rename — it holds only because the `D`-fold
  union *rank-saturates* on a rigid subgraph's fibers, reached via the *count*
  condition, not a matching re-decomposition (an arbitrary decomposition of
  `I ∪ J` is not factor-aligned). *(The most infrastructure-flavored of the (a)s
  — the difficulty is partly induced by the project's `D`-fold-union model of
  `M(G̃)`.)* Pointer: `notes/Phase22a.md` *Decisions* (N4c …).
- **`lem:case-I-realization` / Claim 6.4 — rank-genericity vs. general position
  (one condition in KT, two in Lean)** — [pending] **(a)** general position had to
  be split out of KT's single "generic" hypothesis during the N6b/N6c + G2c
  coupling build. **Stable insight:** KT's §5.1 "generic" (KT 2011, p. 668)
  bundles *two* conditions under one "vertex coordinates algebraically independent
  over ℚ" hypothesis — configuration **non-degeneracy** (KT's *nonparallel*:
  every panel pair meets in a `(d−2)`-flat) and **rank-maximality** — and Claim
  6.4 (p. 675, inside Lemma 6.3's splice) reads *both* off that single assumption,
  with no separate general-position check and no intersection of loci. KT never
  writes "general position" (0 occurrences), and footnote 4 (p. 668) shows the
  algebraic-independence definition is a *deliberate* fusion ("to make our proof
  simpler"). The formalization is forced to separate them: the genericity device
  certifies only the rank/corank (Gram-determinant) polynomial, while general
  position is the *separate* `(G2)` factor `exists_generalPosition_polynomial`
  (off-diagonal product of leading `2×2` minors), and the coupling
  `hasFullRankRealization_of_couple_ofNormals` takes a shared non-root of the
  *product* (per-leg rank polynomial × GP factor). Pointer:
  `notes/Phase22-realization-design.md` §0, §1.1; `notes/Phase22a.md` *Decisions*
  — (G2) / N6b–N6c.
- **`lem:case-III-claim612-p3-placement` — the third candidate via the graph iso
  `Gᵥᵃᵇ ≅ Gₐᵛᶜ` (KT eqs. (6.31)–(6.41))** — [pending] **(a)** (Phase 22e capture). **Stable
  insight:** Claim 6.12's third candidate `p₃` exists *because `a` is also a degree-2 vertex* — KT
  splits off at `a` along `vc`, and `Gₐᵛᶜ` is isomorphic to `Gᵥᵃᵇ` (via `ρ(v)=a`, `ρ(u)=u`), so the
  whole eq.-(6.29) candidate-completion machine reruns at the swapped roles. KT compresses this into a
  half-page of matrix manipulations (eqs. (6.35)→(6.41): a column op `col_a += col_c`, the
  substitutions `p₃(va)=q(ac)`, `p₃(vb)=q(ab)` of eq. (6.34), and a row reduction mirroring `R(G,p₁)`)
  whose end state is the block-triangular eq. (6.41) with the `M₃` top-left block. The formalization
  must make the graph-iso transport explicit (the `ofNormals` graph-swap defeq trap, the project's
  recurring `IsInfinitesimallyRigidOn`-`convert` timeout). KT's densest single step in §6.4.1. Pointer:
  KT pp. 687–689, eqs. (6.31)–(6.41); `notes/Phase22e.md` *Lemma checklist* N7.
- **`lem:case-III-claim612-eq644` — eq. (6.44) routes `M₃` onto the same `r`** — [pending] **(a)**
  (Phase 22e capture). **Stable insight:** the three candidates `M₁/M₂/M₃` only collapse to a *single*
  contradiction because they all test the **same** vector `r`. `M₁/M₂` share `r := Σⱼ λ_{(ab)j} rⱼ(q(ab))`
  by construction; `M₃`'s row is `Σⱼ λ_{(ac)j} rⱼ(q(ac))`, a priori different. Eq. (6.44) identifies it as
  `−r`, and the mechanism is precisely *that `a` is degree-2*: in `Gᵥᵃᵇ` only `ab` and `ac` are incident
  to `a`, so the `a`-column block of the eq.-(6.24) redundant-row vanishing (eq. (6.43), green
  `lem:case-III-acolumn-zero`) has only two surviving sums, giving `Σⱼ λ_{(ab)j} rⱼ(q(ab)) + Σⱼ λ_{(ac)j}
  rⱼ(q(ac)) = 0`, i.e. `M₃`'s row `= −r`. The degree-2-at-`a` hypothesis is doing real work here, not just
  enabling `p₃`. Pointer: KT p. 691, eqs. (6.43)–(6.44); `notes/Phase22e.md` *Lemma checklist* N8.
- **`lem:case-III-claim612-line-in-panel-union` — the point-join↔panel-meet duality bridge** —
  [done] **(c)** (Phase 22e capture, N3 design pass; landed Phase 22f, blueprint prose final).
  **Stable insight:** the span-(6.45) finish
  silently uses Grassmann–Cayley *projective duality*, the genuinely-new content the original single
  N3 had buried. A projective line `L` in `⋀²ℝ⁴` has *two* extensor presentations of the same
  1-dimensional subspace: as a **point-join** `pᵢ∨pⱼ` of two points on it (the span side, what
  Lemma 2.1 feeds via `omitTwoExtensor`) and as a **panel-meet** `C(L) = panelSupportExtensor n_u (·)
  = complementIso(n_u ∧ ·)` of two hyperplanes through it (the annihilated side, what the row-space
  criterion N4 tests). When `L ⊂ Π(u)` these agree up to a nonzero scalar, so `r⊥C(L) ⟹
  r(pᵢ∨pⱼ)=0` — the bridge that lets the contrapositive's annihilation (panel-meets) reach Lemma
  2.1's spanning family (point-joins). *Phase-22f design-pass (route settled):* the "agree up to
  scalar" step is exactly that both presentations live in the **1-dimensional** exterior square `⋀²W`
  of `W = {n_u, n'}^⊥`. The clean realization avoids any Hodge-star API: both extensors lie in the
  1-dim `Ω = ` the `b.toDual`-orthogonal complement (in `⋀²ℝ⁴`) of the 5-dim shared-direction span
  `Φ̃ = n_u ∧ ℝ⁴ + n' ∧ ℝ⁴`. The meet `complementIso(n_u ∧ n') ∈ Ω` is the green step (i); the join
  `w₀ ∧ w₁` (`w_i ∈ W`) is in `Ω` because the coordinate pairing `b.toDual(w₀ ∧ w₁)(n_u ∧ t)` expands
  (reconciliation `b.toDual = pairingDual ∘ map toDual`) as the **Gram determinant**
  `det [[w₀·n_u, w₀·t],[w₁·n_u, w₁·t]]`, vanishing by the column of zeros `w_i · n_u = 0`. The
  exposition crux: `⋀²ℝ⁴` carries **two distinct bilinear forms** — the coordinate inner product
  `b.toDual` (Kronecker / Gram-determinant) and the volume/wedge pairing `vol(· ∧ ·)` — coinciding
  *only* through `complementIso`; the bridge runs on the coordinate one. Irreducible new infra: the
  reconciliation lemma (no Hodge/decomposable-dual API). Pointer: KT p. 691, eq. (6.45); `meet.tex`
  `def:meet`/`def:meet-complement-iso`; `notes/Phase22f.md` *Current state* + *Membership route —
  settled verdict*.
- **`lem:case-III-claim612` / the span-(6.45) + Lemma-2.1 finish** — [pending] **(c)** (Phase 22e
  capture; load-bearing, expected to land as scoped). **Stable insight:** the disjunction's
  contrapositive closes on a clean dimension count: if all three blocks fail, `r ⊥` every supporting
  2-extensor `C(L)` over all lines `L ⊂ Π(a)∪Π(b)∪Π(c)`. KT then picks **four** affinely-independent
  points realizing the `Π`-triple-intersection incidence pattern (`p₁∈Π(a)∩Π(b)∩Π(c)`, etc.), so each
  of the `(4 choose 2)=6` connecting lines lies in `Π(a)∪Π(b)∪Π(c)` and its 2-extensor is in the union
  (6.45); Lemma 2.1 (`omitTwoExtensor_linearIndependent` at `e=2`) makes those six independent, hence a
  basis of `⋀²ℝ⁴ ≅ ℝ⁶`, so `r ⊥` a spanning set ⟹ `r = 0`, contradicting `r ≠ 0`. The deepest
  linear-algebra fact of the program (Lemma 2.1) discharges the hardest case's final step. Pointer:
  KT p. 691, eq. (6.45); `notes/Phase22e.md` *Lemma checklist* N1–N9.

## Retroactive coverage

- **Molecular program (Phases 17–22a): scanned 2026-06-04** — candidates folded
  into the chapter sections above. *Excluded as project-side issues, not
  source-side:* the Phase-21 panel-coplanarity re-scope (early draft proved the
  body-hinge theorem — KT is clear the conjecture is the hinge-coplanar case);
  the Phase-20 N4b binder-paraphrase correction (formalization-rescue, recorded
  in FRICTION/DESIGN only); and the 22a "device-output-is-not-GP" note (project
  device-API confusion from our recon mis-plan — project-side, not source-side —
  preserved in `DESIGN.md`, and *superseded* by the Claim-6.4 entry above, which
  captures the genuine KT bundling that sits underneath it); and the 22a **common-seed-splice →
  block-triangular reroute** (2026-06-05) — the reroute itself was a project-side
  divergence (the motion-space rigidity model re-expressed KT's clear eq.-(6.3)
  block-triangular rank-addition as a common-seed glue), a *process* lesson in
  `DESIGN.md` *Match the source's argument structure …*; the genuine KT crux it sits
  on (the block-triangular rank-addition) is folded into the corrected
  `lem:case-I-realization` realization-mechanism entry above, and the now-wrong
  common-seed framing in the prior N5 entry was corrected in the same pass.
- **Non-molecular phases (1–16): not yet scanned.** TODO (unscheduled): the
  Phase 5 blocker argument is a likely candidate; run as a cleanup-style round,
  candidate list producible on demand from `notes/PhaseN.md` + `git log`.
