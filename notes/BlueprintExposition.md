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
`blueprint/AUTHORING.md` *Proof verbosity*), but **crux nodes earn full, followable
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
nodes), `blueprint/AUTHORING.md` *Proof verbosity* (the crux-node carve-out), and
`notes/MolecularConjecture.md`. The format, the sharpened inclusion criterion
(KT-math, not project-side setup), and the `(a)/(b)/(c)` flavors are stable.
**The write stage has now begun:** the first expositions landed at 22b-close (the
`lem:claim-6-4` three-brick assembly), 22d-close (the `lem:case-III-claim-6-11`
Gap-2→3→1 chain), and 22h-close (the triangle floor). The write-late timing held
up — each was written once the argument was `sorry`-free, so the clean account was
stable. **At 22k-close** the carry family discharged (`h622` in L7, `hsplit`/`h65`
in L8/L9), so the Case-III assembly family's accounts are now final: their detailed
expositions live in the `case-ii.tex` / `case-iii.tex` node+proof prose (written
incrementally 22c–22h and stable since each became `sorry`-free), and the
`prop:rigidity-matrix-prop11` / `thm:theorem-55-6-d3` two-halves account landed in
`panel-layer.tex` (22k L10d) — those markers are flipped to `done` below. **The
molecular-conjecture program closed 2026-07-07** (Phase 26 / Cor 5.7); Phases 24–26
each closed with a recorded no-entries judgment (nothing met the KT-math criterion).

**Accounting reconciled (D2a, 2026-07-07).** This header's "two remain pending"
line had gone stale: the ledger had grown to 13 `[pending]` / 16 `[done]`
markers (29 entries total) without a matching re-check. The reconciliation
pass found the **post-Phase-23 blueprint readability rewrite** (R1–R9,
`ee705e06`..`caa99f96`, 2026-07-02–05 — a separate cleanup round that rewrote
most of the algebraic-induction chapters for prose quality) had, as a side
effect, already written the full followable exposition for **nine** of the
thirteen pending entries, with nobody flipping the corresponding marker here:
Lemma 2.1 (`extensor.tex`, R9), the whole KT-Lemma-4.1/forest-surgery family
together with `lem:removal-deficiency` and `lem:reduction-step`
(`molecular-induction.tex`, written in Phase 20 itself and polished by R5),
`def:meet-complement-iso` (`meet.tex`, R8), and three of the Case-I entries —
the N6 trifurcation composer, the motive's simplicity-conditioning, and the
eq.-(6.3) block-triangular rank-addition mechanism (`case-i.tex`/
`panel-layer.tex`, R1/R6) — plus Claim 6.4's three-brick assembly, whose own
entry already said "done" in its closing sentence without the top marker
agreeing. Each is flipped to `done` below with its landing pointer. **Result:
4 pending / 25 done** (of 29). The four still-pending entries are genuinely
unwritten — no discussion beyond the bare (correct) formalized statement: the
contraction-simplicity mechanism (why vertex-relabelling alone breaks
`Simple`), the two-distinct-body-sets splice framing, the
matroid-union-vs-contraction non-commutativity crux, and KT's
single-hypothesis two-conditions bundling (Claim 6.4's genericity vs. general
position). They write at their own next touch, same as before.

**Phase-27 close (2026-07-08).** The four then-pending Case-I entries were
written at the post-program crux-node exposition phase — contraction
simplicity, the two-body-set splice, the matroid-union-vs-contraction
non-commutativity crux, and Claim 6.4's genericity-vs-general-position
bundling — each landing a fuller account in `case-i.tex` (their markers below
flipped to `done`). One new worked-case entry was added and written: the d=3
Case-III three-candidate dispatch (`lem:case-III-candidate-dispatch-d3`), an
accessible on-ramp to the general Lemma 6.13. **Result: 0 genuinely-pending /
30 done** (of 30) — the exposition ledger is fully written.

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

- **Lemma 2.1 (`omitTwoExtensor_linearIndependent`)** — [done (`extensor.tex`,
  R9 readability rewrite `caa99f96`)] **(c)** landed as scoped (no reroute);
  flagged for difficulty. **Stable insight:** the independence of the
  `D = (d+1 choose 2)` many `(d−1)`-extensors of `d+1` affinely independent
  points — join-on-the-left kills the off-diagonal terms, the `pairAppend`
  bijection handles the diagonal. The deepest single linear-algebra fact in
  the program; Case III (Phases 22b+/23) bottoms out on it. **Written**
  (R9, 2026-07-05, found by the D2a reconciliation 2026-07-07): the
  `lem:extensor-independence` proof spells out the join-on-the-left/
  alternation argument and the reindexing bijection in full. Pointer:
  `notes/Phase17.md`.

### `rigidity-matrix.tex` — Phase 18 (R(G,p), rank Lemmas 5.1–5.3)

- **`prop:rigidity-matrix-prop11` (KT Prop 1.1)** — [done (`panel-layer.tex`,
  22k-close)] **(a)** scoped to 18 → deferred to 19 → relocated forward to 21+.
  **Stable insight:** Prop 1.1 is *two genuinely separate halves* KT presents
  as one — the **matroidal** `def = corank M(G̃)` (combinatorial, JJ09 min–max)
  and the **analytic** `rank R(G,p) = D(|V|−1) − def(G̃)` (generic, needs the
  genericity device). Closing the matroidal half does not touch the analytic
  half. The analytic half is *itself* pinned by two inequalities of opposite
  character: a **genericity-free** lower bound on the motion space (`hub`, the
  Phase-19 partition machinery — *every* realization has at least `D + def`
  motions) and a **generic** upper bound (`hgen`, supplied by Theorem 5.5 +
  re-add monotonicity — a generic point attains at most that many). The
  `def > 0` feed (`thm:theorem-55-6-d3`, 22k) is the one that needed the
  spanning-strip lift; the `def = 0` feed landed in 22h. The full two-by-two
  account is in the `prop:rigidity-matrix-prop11` and `thm:theorem-55-6-d3` prose
  of `panel-layer.tex`. Pointer: `notes/Phase18.md` / `notes/Phase19.md`
  *Hand-off*; `notes/Phase22k.md`.

### `deficiency.tex` — Phase 19 (M(G̃), deficiency, k-dof)

- *Scanned 2026-06-04, no candidate.* Every node landed as scoped, including the
  full axiom-free `thm:def-eq-corank`. The one forward-looking finding (Prop
  1.1's two halves) is filed under `rigidity-matrix.tex` above.

### `molecular-induction.tex` — Phase 20 (combinatorial induction, Thm 4.9)

- **KT Lemma 4.1 / forest-surgery track (`kt_lemma_41_overquantified`,
  `lem:forest-surgery-split` family)** — [done (`molecular-induction.tex`
  `rem:kt-lemma-41`; landed Phase 20, polished by the R5 readability rewrite
  `d589fa64`)] **(a)**, the richest entry. Planned hard core; turned out
  over-quantified, rerouted onto deficiency-counting. **Stable insight
  (KT-non-erring framing):** (1) Lemma 4.1 as-quantified is *false* — it
  quantifies over independent sets but `|I'| = |I|−D` needs bases. (2) Its
  base case silently assumes the chosen `D`-forest packing is *balanced at
  `v`* (every forest meets `v`), unjustified in KT; recovered via a
  pendant/bridge finite-descent (no `D ≥ 3` counterexample — a gap, not an
  error). (3) The induction needs only `def(G̃ᵥᵃᵇ) ≤ def(G̃)`, by
  partition-count through `def = corank`, routing around the surgery
  entirely. **Written** (Phase 20; found by the D2a reconciliation
  2026-07-07): `rem:kt-lemma-41`'s three-layer enumeration states exactly
  this, and the balanced-packing descent (`lem:base-vfiber-count` through
  `lem:balanced-forest-packing`) spells out the gap's repair in full.
  Pointer: `notes/Phase20.md` *Findings*.
- **`lem:removal-deficiency` (KT 4.4, `removeVertex_deficiency_ge`)** — [done
  (`molecular-induction.tex` `rem:kt-lemma-44`/`lem:removal-deficiency`; landed
  Phase 20, polished by the R5 readability rewrite `d589fa64`)] **(b)**.
  **Stable insight:** a shorter deficiency-count route than KT's `h'=0`
  unsplit-forest argument (which is itself sound): the `−(D−1)·d` sign in
  `partitionDef` makes dropping the crossing-count `d` the *helpful* direction,
  and in the part-losing case `v`'s two neighbours are *forced* into distinct
  blocks, so `c=2` — the `+2(D−1)` crossing-drop pays for the `−D` part-loss
  exactly when `D ≥ 2`. **Written** (Phase 20; found by the D2a reconciliation
  2026-07-07): `rem:kt-lemma-44` spells out the partition-count comparison and
  the forced-`c=2` argument in full. Pointer: `notes/Phase20.md` *Findings*.
- **`lem:reduction-step` (KT 4.7–4.8, `splitOff_isMinimalKDof`)** — [done
  (`molecular-induction.tex` `lem:reduction-step`; landed Phase 20, polished by
  the R5 readability rewrite `d589fa64`)] **(b)** *(borderline toward
  bookkeeping)*. **Stable insight:** KT's iterated fundamental-circuit swap is
  bypassed by one rank count — KT 4.10 makes `E(G̃_v)` a base of `M(G̃_v)`, so
  with KT 4.7 (`def > 0`) a single cardinality split of any fiber-avoiding base
  contradicts `isBase_ncard_add_deficiency_eq`; no matroid minor, no swap
  induction. **Written** (Phase 20; found by the D2a reconciliation
  2026-07-07): the lemma's proof spells out the rank-count argument
  ("a rank count replaces KT's iterated fundamental-circuit swap …") in full.
  Pointer: `notes/Phase20.md`; FRICTION *[matroid] Transporting circuits …*.
- **`lem:chain-cycle-dichotomy` (KT Lemma 4.6, `chainData_or_cycleData_of_noRigid`)** —
  [done (23g-close, the node's proof prose)] **(a)** (Phase 23g E2 / design §(4.107),
  retroactive capture at close). **Stable insight**, two source-side facts the formalization
  forced explicit: (i) KT's dichotomy is *tight* — the chain branch yields a chain of length
  **exactly** `d` (never shorter), and the cycle branch is **unavoidable** at general `d`
  (minimal `0`-dof cycles on `4 ≤ m ≤ d` vertices admit no length-`d` chain), so Lemma 5.4 is
  load-bearing; the `d = 3` formalization dodged the cycle family only because `m ≤ 3` collides
  with the ambient `|V| ≥ 4`. (ii) KT's compact counting (4.6)–(4.9) unpacks as a charging
  argument over capped interior-degree-2 walks: walk determinism (two walks sharing their first
  vertex + edge are prefix-comparable) makes the per-incidence charge well-defined, the lollipop
  case is excluded by "a cycle on `≤ D` vertices is `0`-dof" (the boundary-index injection of
  partition classes into crossing edges), and the linking identity `i(n−2)+2 ≤ (D−1)(i−2)`
  (KT's display above (4.9)) is the *entire* chain-length↔dimension relation — no hidden floor.
  **Written** (23g-close): the `lem:chain-cycle-dichotomy` / `lem:chain-data-extract` proof
  prose (`molecular-induction.tex`). Pointer: `notes/Phase23-design.md` §(4.107)/(4.107.G);
  `notes/Phase23g.md`.

### `meet.tex` — Phase 21a (meet / projective duality)

- **`def:meet-complement-iso` / `complementIso`** — [done (`meet.tex`, R8
  readability rewrite `2f4d9fc9`)] **(b)**. **Stable insight:** the regressive
  product (meet) needs only the *nondegeneracy* of the wedge pairing
  `⋀ʲV × ⋀^(N−j)V → ⋀ᴺV ≅ ℝ`, not the oriented `j ↔ N−j` sign — the pairing
  matrix is a signed-permutation matrix and `complementIso` reads off only
  "diagonal ≠ 0"; the orientation/sign bookkeeping KT carries is deferrable to
  a consumer that actually reads an oriented meet. **Written** (R8, 2026-07-05;
  found by the D2a reconciliation 2026-07-07): the `def:meet-complement-iso`
  proof spells out the signed-permutation-matrix argument, ending "the exact
  grade-swap sign is not needed for the isomorphism and is deferred to where an
  oriented meet consumes it." Pointer: `notes/Phase21a.md` *Decisions* +
  *Blockers*.

### `algebraic-induction.tex` — Phases 21 / 21b / 22a (Thm 5.5, Cases I/II/III, genericity device)

- **`lem:case-I-realization` (N6 composer)** — [done (`case-i.tex`
  `lem:case-I-dispatch`/`lem:case-I-realization`; R6 readability rewrite
  `87e81442`)] **(a)** thought 1 commit → reconned into N6-G1/G2/G3
  (2026-06-04). **Stable insight:** KT §6.2 Case I is a *trifurcation* (Lemmas
  6.2 non-simple, 6.3 `G/E′`-simple, 6.5 degree-2 vertex removal), not a
  uniform contraction recursion; and the realization motive must be
  *strengthened to general position* on the inductive legs (the composer's
  per-leg adapter consumes `HasGenericFullRankRealization`, while the
  induction threads only the bare motive). **Written** (R6, 2026-07-05; found
  by the D2a reconciliation 2026-07-07): `lem:case-I-dispatch`'s proof narrates
  the three-way case split verbatim, and `lem:case-I-realization`'s statement
  requires "generic realizations of both" inductive legs explicitly. Pointer:
  `notes/Phase22-realization-design.md` §1.5–1.6; `notes/Phase22a.md`.
- **conditioned motive `Pc := (G.Simple → GP) ∧ bare` (`theorem_55_generic`;
  folds into `lem:case-I-realization` prose)** — [done (`panel-layer.tex`
  `thm:theorem-55` statement + `fmlnote` at line ~441; R1 readability rewrite
  `a85e849c`)] **(a)** G2a (`f35be5d`). **Stable insight:** the generic motive
  must be *conditioned on simplicity* — KT's "nonparallel, if `G` is simple"
  (printed p.669); unconditional general position is *false* at the
  parallel-`K₂` base. **Written** (R1, 2026-07-03; found by the D2a
  reconciliation 2026-07-07): `thm:theorem-55`'s statement carries the
  "moreover, if `G` is simple, generic" conjunction, and the following
  `fmlnote` states the parallel-`K₂` base admits no generic realization
  explicitly. Pointer: `notes/Phase22-realization-design.md` §1.6.
- **contraction simplicity `rigidContract_simple` / `map_simple` (folds into
  `lem:case-I-realization` prose)** — [done (`case-i.tex`, Phase-27 C1 exposition)]
  **(a)** G2b (`b9000ef`). **Stable
  insight:** vertex-relabelling (`map`) is the *one* graph op that breaks
  `Simple` — it can manufacture both loops (collapse an edge's endpoints) and
  parallel edges (collapse two edges onto one pair), so unlike `↾`/`＼`/`-`/induce
  it has no unconditional `Simple` instance. This is *why* Case I trifurcates:
  `G/E′` simple is a genuine *case hypothesis* (Lemma 6.3), its failure routed to
  Lemma 6.5's vertex-*removal* (which does preserve simplicity). **Written**
  (Phase 27, this commit): a two-paragraph connective passage before
  `lem:case-I-realization` in `case-i.tex` sets out, source-side, that
  contraction is the one Case-I operation that identifies vertices (hence can
  create a loop from a surviving edge with both ends in `V(H)`, or a parallel
  pair from two surviving edges collapsing onto one end-pair), unlike the
  subgraph operations that preserve simplicity automatically — so `G/E(H)`
  simple is a genuine hypothesis — and maps the resulting three-way split onto
  KT Lemmas 6.2 (`G` non-simple), 6.3 (simple contraction), and 6.5 (Claim 6.6
  degree-2 vertex removal, itself simplicity-preserving). Pointer:
  `notes/Phase22-realization-design.md` §1.6; `notes/Phase22a.md`; KT
  pp. 673--676.
- **`lem:case-I-dispatch` / Claim 6.6 (the Lemma-6.5 arm) — the maximal rigid
  subgraph must be edge-saturated (Phase 22k L8a)** — [done (`case-i.tex`
  `lem:case-I-dispatch` + this ledger insight; flipped 22k-close)] **(a)** the
  L8a-step-2 build surfaced it (2026-06-15). **Stable insight (a benign gap in
  KT-as-written):** KT's Lemma 6.5 / Claim 6.6 takes a *vertex-inclusionwise
  maximal* proper rigid subgraph `G'` and reads the degree-2 vertex `v` off the
  non-simplicity of the contraction `G/E(G')`. But contraction-non-simplicity has
  *two* modes (`rigidContract_not_simple`): a **parallel pair** — two surviving
  edges collapsing together, ⟹ the wanted `v ∉ V(G')` with two edges into
  `V(G')` — and a **loop** — a single `G`-edge with both ends in `V(G')` that
  survived `＼E(G')`, i.e. `G'` is *not* edge-saturated (an internal non-edge of
  `G'`). KT asserts the parallel conclusion directly, *silently assuming* `G'` is
  edge-saturated; the loop mode is reachable precisely because a rigid subgraph
  (`IsRigidSubgraph := H ≤ G ∧ H.IsKDof 0`) need not be induced. The faithful fix
  makes the saturation explicit: take `G'` *induced* — `G.induce V(G₀)` for the
  cardinality-maximal `G₀` — which kills the loop mode (`induce` carries exactly
  the internal edges, `IsLink.mem_induce_iff`), at the cost of one extra fact,
  *deficiency is antitone under edge addition at a fixed vertex set*
  (`deficiency_le_deficiency_of_le_vertexSet_eq`), to keep the induced subgraph
  rigid. Pointer: `notes/Phase22-realization-design.md` §1.70(c′);
  `notes/Phase22k.md`.
- **`lem:case-III` / `theorem_55.hsplit` (Case-naming + one-row shortfall)** —
  [done (`DESIGN.md` *Phase Case-naming…* + `case-iii.tex`; flipped 22k-close)]
  **(a)**. **Stable insight (the decisive distinction):** KT's cases key
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
  vanishing is the eqs. (6.14)–(6.16) *column operation*, not the seam + eq. (6.43)** — [done
  (`case-iii.tex`, prose final since 22e; flipped 22k-close)]
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
- **`lem:case-II-realization` / eq. (6.12) degenerate placement** — [done
  (`case-ii.tex` / `case-iii.tex`, prose final since 22h; markers flipped 22k-close)]
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
  rank-ADDITION** — [done (`case-i.tex` `lem:case-I`; R6 readability rewrite
  `87e81442`)] **(c)** *(landed via a block-triangular reframe; the
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
  conclusion*. **Written** (R6, 2026-07-05; found by the D2a reconciliation
  2026-07-07): `lem:case-I`'s proof states the block-triangular rank-addition
  and the exterior-column-projection argument in full, working from a single
  seed with no simultaneous-rigidity requirement on both legs. Pointer:
  `notes/Phase22-realization-design.md` §1.13–§1.16; `notes/Phase22a.md`.
- **`lem:case-I-realization` N6-G3 / Claim 6.4 — the splice's contraction leg is
  `G ＼ E(H)`, not the relabelled contraction; the collapse is placement-side** —
  [done (`case-i.tex` `lem:claim-6-4`; landed 22b-close `8b375212`, polished by
  the R6 readability rewrite `87e81442`; marker corrected by the D2a
  reconciliation 2026-07-07 to match this entry's own "Written" line below)]
  **(a)** thought "pure leg-data geometry" → reconned into G3a/G3b/G3c
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
  body sets, `V′` and `V∖V′ ∪ {v∗}`** — [done (`case-i.tex`, Phase-27 C2 exposition)]
  **(a)** thought "pure green-brick
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
  of `V`" reading is a natural mis-step the formalization forced open.)*
  **Written** (Phase 27, this commit): the expanded connective passage after
  `lem:case-I-splice-seed` in `case-i.tex` spells out, source-side, the two
  body sets `V′ = V(H)` (rigid block) and `s_c = (V∖V′) ∪ {r}` (contraction);
  why the contraction leg is rigid on `s_c` alone and not on all of `V` (the
  surviving edges `E∖E′` never touch the interior bodies `V(H)∖{r}`, which are
  therefore left free); and how the rank count balances (KT's top-right zero
  block makes the two families disjoint, and the shared body `r` — counted once
  from each side — gives `(|V′|−1)+(|s_c|−1)=|V|−1`, so
  `D(|V′|−1)+D(|s_c|−1)−k = D(|V|−1)−k`, KT's closing line of Lemma 6.3). The
  surviving block's rank is reconciled to the contraction's rank on `s_c` by the
  pin-a-body Lemma 5.1 (KT eqs. (6.5)/(6.9)). Pointer:
  `notes/Phase22-realization-design.md` §1.8; `notes/Phase22a.md` *Decisions*;
  KT pp. 673--675, eq. (6.3).
- **`lem:case-I-realization` N4 union↔contraction crux
  (`rigidContract_isMinimalKDof`)** — [done (`case-i.tex`, Phase-27 C3 exposition)]
  **(a), model-induced**. **Stable
  insight:** `Matroid.Union` does *not* commute with contraction, so
  `M((G/E(H))̃) = M(G̃)/E(H̃)` is not a rename — it holds only because the `D`-fold
  union *rank-saturates* on a rigid subgraph's fibers, reached via the *count*
  condition, not a matching re-decomposition (an arbitrary decomposition of
  `I ∪ J` is not factor-aligned). *(The most infrastructure-flavored of the (a)s
  — the difficulty is partly induced by the project's `D`-fold-union model of
  `M(G̃)`.)* **Written** (Phase 27, this commit): the expanded proof of
  `lem:rigidContract-isMinimalKDof` in `case-i.tex` spells out, source-side, that
  the contraction identity `M((G/E(H))̃) = M(G̃)/E(H̃)` is not a bookkeeping rename
  — contraction does not distribute over the `D`-fold cycle-matroid union
  (union-of-contractions ≠ contraction-of-union) — and holds here only because the
  contracted-out fibers `E(H̃)` *rank-saturate* the union: rigidity (`def(H̃)=0`)
  forces `rank M(H̃) = D(|V(H)|−1) = D·r_cyc(E(H̃))`, so the fibers pack into `D`
  edge-disjoint spanning trees on `V(H)` — precisely KT's own Lemma-3.5 claim (3.1),
  which the graph collapse of `V(H)` needs and a non-rigid `H` fails. The
  coincidence is reached through the `(D,D)`-count condition (submodularity +
  monotonicity of the cycle rank), not a factor-aligned re-decomposition. Source
  verified: KT Lemma 3.5 + eq. (3.1), p. 658. Pointer: `notes/Phase22a.md`
  *Decisions* (N4c COUNT route).
- **`lem:case-I-realization` / Claim 6.4 — rank-genericity vs. general position
  (one condition in KT, two in Lean)** — [done (`case-i.tex`, Phase-27 C4 exposition)]
  **(a)** general position had to
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
  *product* (per-leg rank polynomial × GP factor). **Written** (Phase 27, this
  commit): a three-paragraph connective passage after `lem:case-I-realization` in
  `case-i.tex` states, source-side, the two conditions KT fuses under §5.1's one
  "algebraically independent over ℚ" hypothesis — configuration non-degeneracy
  (KT's *nonparallel*, `def:panel-general-position`) and rank-maximality — and
  that Claim 6.4 (p. 675) reads both off it with no separate check, footnote 4
  (p. 668) flagging the fusion as a deliberate simplification; then how the
  formalization separates them into the rank/corank polynomial (the genericity
  device, `lem:genericity-device`) and the *separate* general-position polynomial
  (the product over distinct body pairs of the leading `2×2` minor, nonzero at a
  Vandermonde/moment-curve seed, `lem:moment-curve-general-position`), coupled by
  a shared non-root of the product of the two per-leg rank polynomials with the
  GP factor. Source verified: KT §5.1 + footnote 4, p. 668; Claim 6.4, p. 675.
  Pointer: `notes/Phase22-realization-design.md` §0, §1.1; `notes/Phase22a.md`
  *Decisions* — (G2) / N6b–N6c.
- **`lem:case-III-claim612-p3-placement` — the third candidate via the graph iso
  `Gᵥᵃᵇ ≅ Gₐᵛᶜ` (KT eqs. (6.31)–(6.41))** — [done (`case-iii.tex`, prose final since 22h;
  marker flipped 22k-close)] **(a)** (Phase 22e capture). **Stable
  insight:** Claim 6.12's third candidate `p₃` exists *because `a` is also a degree-2 vertex* — KT
  splits off at `a` along `vc`, and `Gₐᵛᶜ` is isomorphic to `Gᵥᵃᵇ` (via `ρ(v)=a`, `ρ(u)=u`), so the
  whole eq.-(6.29) candidate-completion machine reruns at the swapped roles. KT compresses this into a
  half-page of matrix manipulations (eqs. (6.35)→(6.41): a column op `col_a += col_c`, the
  substitutions `p₃(va)=q(ac)`, `p₃(vb)=q(ab)` of eq. (6.34), and a row reduction mirroring `R(G,p₁)`)
  whose end state is the block-triangular eq. (6.41) with the `M₃` top-left block. The formalization
  must make the graph-iso transport explicit (the `ofNormals` graph-swap defeq trap, the project's
  recurring `IsInfinitesimallyRigidOn`-`convert` timeout). KT's densest single step in §6.4.1.
  *Sharpened at 22g (§1.48–§1.49):* the `M₃` candidate is realized at the **same** inductive seed
  transported by the relabel `ρ = (a v)` — eq. (6.44) forces it (a second IH application would
  produce a different `r`) — and KT's Lemma 6.10 receives hypothesis (6.1) and invokes Lemma 4.6
  *itself* to choose the adjacent degree-2 pair, so the formalized induction must hand the `k=0`
  branch the full conditioned IH rather than pre-split data. Pointer:
  KT pp. 687–689, eqs. (6.31)–(6.41); `notes/Phase22e.md` *Lemma checklist* N7;
  `notes/Phase22-realization-design.md` §1.48–§1.49.
- **`lem:case-III-claim612-eq644` — eq. (6.44) routes `M₃` onto the same `r`** — [done (`case-iii.tex`,
  prose final since 22h; marker flipped 22k-close)] **(a)**
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
- **`lem:case-III-claim612` / the span-(6.45) + Lemma-2.1 finish — Claim 6.12 is a genuine
  existential over *free* lines, not a three-fixed disjunction** — [done (22g, the existential
  restate)] **(a)** (Phase 22e capture as (c); upgraded at the Phase-22g reroute). **Stable
  insight:** KT state Claim 6.12 as "at least one of `M₁, M₂, M₃` has full rank", which reads as a
  disjunction over three fixed candidate supports — but three fixed supports cannot carry the
  contradiction: three `2`-extensors span at most 3 of the 6 dimensions of `⋀²ℝ⁴`, so
  `r ⊥ C₁, C₂, C₃` alone never forces `r = 0`. The load-bearing quantifier is KT's "*for some
  choice of lines* `L ⊂ Π(a)`, `L' ⊂ Π(b)`, `L'' ⊂ Π(c)`" — the lines are **free**, and the honest
  form is the premise-free existential *for some pair `(i,j)` of the four witness points,
  `r̂(p̄ᵢ ∨ p̄ⱼ) ≠ 0`*, proved by the clean contrapositive: `r` annihilating all six joins
  annihilates the span (6.45) — Lemma 2.1 makes the six joins of four linearly-independent
  homogeneous vectors a basis of `⋀²ℝ⁴ ≅ ℝ⁶` — so `r = 0`, contradicting `r ≠ 0`. The deepest
  linear-algebra fact of the program (Lemma 2.1) discharges the hardest case's final step; the
  realization producer consumes the existential by building its candidate placement so its hinge
  line IS the witness join's line. **Written** (22g: the `lem:case-III-claim612` statement + proof
  prose carry the existential form and the why-not-three-fixed dimension count). Pointer: KT
  p. 691, eq. (6.45); `notes/Phase22-realization-design.md` §1.38–§1.39; `notes/Phase22g.md`.
- **`lem:case-III` `|V|=3` base — the `k=0` split recursion bottoms on a *direct* triangle
  realization** — [done (`case-iii.tex` *The triangle floor*, 22h-close)] **(a)** (Phase 22g
  capture, §1.46–§1.48). **Stable insight:** the `d=3` Case-III induction
  genuinely reaches the triangle (`|V|=3`), and there the split-off graph `G_v^{ab}` is the
  *non-simple* double-edge `K₂` (the surviving `ab`-edge plus the fresh `e₀`) — so the inductive
  motive's general-position conjunct ("nonparallel, *if simple*") is unavailable by any route, and
  with it the candidate placement's transversality input (`hgab`, the independence of the two
  split-leg normals). KT cover this floor compactly (a triangle is `0`-dof; its realization is the
  3-panel cycle of Lemma 6.7(i) / the Lemma 5.4 family); the formalization must realize the
  triangle *directly* — third-edge/vertex-pin counting, a 3-body sibling of the two-body base
  case, a cyclically-consistent basis seed, then the bare→generic upgrade — rather than recurse.
  **Written** (22h-close): the *triangle floor* prose block in `case-iii.tex` (preceding
  `lem:triangle-third-edge`) spells out why the floor exists and how the four leaves T1–T4
  assemble. Pointer: `notes/Phase22-realization-design.md` §1.46–§1.48 (T1–T4 signatures);
  `notes/Phase22g.md`.
- **`lem:case-III` general `d` (Lemma 6.13) — the `d`-chain dispatch + the `⋀^{d−1}(ℝ^{d+1})`
  duality finish (eq. 6.67)** — [done (`case-iii.tex` *The general-`d` chain dispatch* narrative +
  the restated `lem:case-III`, Phase-23 close)] **(c)** (Phase 23b/CHAIN-open capture 2026-06-17,
  sharpened across 23b–23f; owner-flagged 2026-06-18 "this exposition must be absolutely clear" —
  the Lean economizes, the prose must not). **Stable insight** (source-verified against KT §6.4.2
  eqs. (6.46)–(6.67)): KT's "exactly the same as `d=3`" (p. 692) compresses two genuinely-hard
  moves. (i) The `d` candidate frameworks are **re-views of ONE base** `(G₁,q₁)` — the single
  `v₁`-split (6.46) — tied by the index-shift isos `ρᵢ` (6.54–6.56, "exactly the same framework"),
  not `d` separate splits; and the **single redundancy `r` (Claim 6.11, applied once at the base)
  is carried `±`-ly across the `d` panels (6.60–6.66) by whole-matrix bookkeeping with `r` abstract
  and the member MOVING** (KT's (6.62) puts the redundant row on a *different* row of `R(G,pᵢ)` for
  each `i` — no fixed-functional transport exists; the natural-looking fixed-member-transport shape
  is a trap, the *member-mapping wall*). The per-step carry IS the degree-2 column-vanishing read
  of (6.44)/(6.52) iterated along the chain, and the spliced candidate panel is no harder than any
  other — the panel block is read off the seed alone, graph-independent
  (`baseRedundancy_perp_interior_reproduced_panel`). Each candidate's (6.64)–(6.65) count is
  certified inline as ONE jointly-independent row family (the `D−1` panel rows + the `±r` row +
  the trimmed base block), not via a separate block-rank lemma. (ii) The finish (6.67) is
  **Lemma 2.1 at general grade** (`span_omitTwoExtensor_eq_top`): the `D` joins of the `d+1 = k+2`
  chain-panel normals span the screw space, forcing the discriminator's matched candidate — at the
  homogeneous-vector layer, so no new algebraic-independence obligation arises (OD-4 resolved,
  `notes/AlgebraicIndependence.md` row §Phase-23(b)). **Written** (Phase-23 close): the
  three-step narrative block preceding `lem:case-III` in `case-iii.tex` (one base / the ±r carry
  with the member moving / the (6.67) discriminator), with `lem:case-III` restated at general
  grade. Pointers: KT pp. 692–698, eqs. (6.46)–(6.67); `notes/Phase23-design.md` §(o‴)(I.8.22),
  §(4.107)–(4.109); the project-side fixed-functional detour → `DESIGN.md` *Match the source's
  argument structure …*.
  **R2 readability-rewrite note — delivered (R2 slice 3, 2026-07-05):** the seeded ask (narrate
  KT's own §6.4.1 (`d=3`, `D=6`) → §6.4.2 (general `D`) two-stage structure explicitly, flagging
  which steps lift verbatim vs. which are genuinely new at general `d`) landed in the
  `case-iii.tex` connective paragraph opening *The general-`d` chain dispatch*: Claim 6.11 and
  Lemma 2.1's span argument are named as the verbatim-lifted pieces, the `±`-carry transport across
  the chain's `d` panels as the genuinely new bridge between them. The narrative also promoted (S3,
  `notes/Phase23-cleanup.md`) into two blueprint nodes — `lem:case-III-chain-discriminator`
  (`chainData_fire_discriminator`) and `lem:case-III-chain-dispatch` (`chainData_dispatch`) — with
  `lem:case-III`'s own proof shortened to cite the dispatch node rather than re-narrate the
  mechanism inline.
- **`lem:case-III-candidate-dispatch-d3` / `case_III_candidate_dispatch` — the `d = 3` Case-III
  worked concrete case (Lemma 6.10) as an accessible entry point to the general Lemma 6.13** —
  [done (`case-iii.tex`, Phase-27 A2-x worked-case exposition)] **(b)**, a *worked-case*
  deliverable (a sibling to the reroute-triggered entries, not one of them): KT's own
  concrete-first pedagogy (§6.4.1 before §6.4.2), presented as the accessible instance of the
  general argument. **Stable insight:** the `d = 3` case is *genuinely* simpler than the general
  Lemma 6.13, not a mechanical specialization — it drops the chain discriminator (three *fixed*
  candidates via a case split over three panels, not a discriminator ranging over a length-`d`
  chain's interior), the iterated chain transport (the third candidate needs one vertex relabel
  `v ↔ a`, not a column op per interior vertex), the chain-vs-short-cycle dichotomy + cycle family
  (KT Lemmas 4.6/4.8, 5.4 — present in the general proof, vacuous at `d = 3`), and the moving-vertex
  block certificate (a direct three-panel rank count); and its span finish runs on the six joins of
  four points in `⋀²ℝ⁴` (6-dim, visualizable) rather than the `(k+2 choose 2)` joins of
  `⋀^k(ℝ^{k+2})`. **Written** (Phase 27, this commit): the `sec:…-claim612` section lead reframed as
  the `d = 3` worked case (the simplicity gains in prose), a new capstone node
  `lem:case-III-candidate-dispatch-d3` pinning `case_III_candidate_dispatch` (honestly green, a
  dep-graph leaf with no Lean callers — correct for a worked example; its eq.-(6.22) bound
  discharged by `\uses{lem:case-III-nested-rank-lower}`, hence not a laundered hypothesis), and a
  navigational `\cref` from `lem:case-III`'s proof to it — *not* a `\uses` edge, since the general
  proof does not depend on the `d = 3` dispatch. Source verified: KT §6.4.1 / Lemma 6.10 (p. 680),
  §6.4.2 / Lemma 6.13 (p. 692). Pointer: `notes/CaseIII-d3-exposition.md`; `notes/Phase27.md`.

### `bar-joint-3d.tex` — Phase 24 (generic bar-joint rigidity matroid)

**No entries — judged at phase close (2026-07-06).** The phase was
deliberately reuse-heavy (Phase-4/8/14 machinery repackaged
dimension-generally), and no node met the KT-math inclusion criterion:
the one non-plumbing argument, `lem:exists-generic-placement`, is a
rerun of the Phase-8 dimension-2 linear-interpolation induction with
the witness placements now definitional (easier, not harder, than its
model), and the rank/matroid nodes are `Matroid.ofFun` +
representation-bridge composition. Nothing here spells out a step KT
compresses — KT Cor 5.7's `r(·)` is consumed, not proved, in this
chapter. Recorded so the no-entry state reads as a judgment, not an
omission.

### `molecule-modelling.tex` — Phase 25 (projective duality + the molecule modelling equivalence)

Judged at phase close (2026-07-06). The chapter's expositions were written
node-by-node during the phase and were final when each node went green; the
phase-close re-read confirmed them, so the entries below are captured and
flipped `done` in the same pass.

- **`thm:molecular-iff-square-bar-joint` / `molecular_finrank_motions_eq_square_ker`
  (the square-graph dictionary)** — [done (the node's statement + proof prose)]
  **(a)**. **Stable insight:** the primary source for the molecule ↔
  hinge-concurrent-body-hinge equivalence, Whiteley's [35] (*The equivalence of
  molecular rigidity models*, manuscript), is **unpublished** — KT p. 650/671 and
  JJ 2008 §2.1 only sketch it — so the chapter's proof is the project's own
  reconstruction (screw-velocity fields, per-body determination on
  closed-neighbourhood cliques), verified internally, with JJ 2008 as the citable
  anchor. Formalizing it forced the placement hypothesis sharp: injectivity +
  non-collinearity is **not** enough — four coplanar points admit the out-of-plane
  flex of a flat complete quadrilateral, which is a bar-joint motion but no screw
  restriction — so the dictionary needs general position **up to order four**
  (`lem:screw-determination` states the counterexample). No source states the
  exact general-position grade. Pointer: `notes/Phase25-design.md` §2.3/F5;
  `notes/Phase25.md`.
- **rank-level chain over realizability-iff chain (the chapter preamble +
  `thm:panel-hinge-iff-molecular`)** — [done (the chapter's opening paragraphs)]
  **(b)**. **Stable insight:** KT/Whiteley state the modelling links as
  realizability equivalences, but the iff-level chain cannot reach Cor 5.7
  (`r(G²) = 3|V| − 6 − def(G̃)`) on its own — JJ 2008's derivation (their Thm 4.3
  from Conjecture 2.1) consumes their §3–4 machinery (independent 2-thin covers,
  brick partitions, ear induction), quoted from two further papers. Stating both
  links at the **motion-space-dimension / rank level** instead lets Cor 5.7 fall
  out arithmetically from Theorem 5.6, replacing that whole development. Pointer:
  `notes/Phase25-design.md` §2.1–2.2; JJ 2008 Thms 4.1/4.3.
- **`lem:theorem-56-general-position` / `exists_rankHypothesis_isGeneralPosition4`
  (the "nonparallel" strengthening)** — [done (the node's proof prose)] **(a)**.
  **Stable insight:** KT compress the entire strengthening of Theorem 5.6's output
  to the general-position form the dictionary consumes into the single word
  "nonparallel" (p. 671). Unpacked, it is a genuine avoidance-polynomial argument:
  the realized rank is re-witnessed as one nonzero rational minor polynomial in
  the normal coordinates, multiplied by the order-four general-position avoidance
  product (last-coordinate variables × leading square minors of the normal
  matrix, each nonzero at moment-curve normals by Vandermonde), evaluated at an
  algebraically-independent-over-ℚ seed; the rank is then pinched between the
  witnessed count and the genuine-hinge deterministic bound. Pointer:
  `notes/Phase25-design.md` §2.4; KT p. 671.

### `molecule-application.tex` — Phase 26 (Corollary 5.7, the rank formula)

**No entries — judged at phase close (2026-07-07).** The phase is pure
arithmetic assembly on top of the green Phase-23/24/25 machinery: no node
was rerouted or decomposed, and none spells out a step KT compresses.
Corollary 5.7 itself is a one-line `le_antisymm` of its two legs; each leg
composes the Phase-25 dictionary with a Phase-24 rank bound and closes with
`omega`. The two genuine modelling insights the formula rests on — the
rank-level (not realizability-level) chain that lets Cor 5.7 fall out
arithmetically, and the order-four general-position grade the dictionary
needs — are already ledgered under `molecule-modelling.tex` (Phase 25,
both `done`). The one project-side subtlety here (the padded shadowing
carrier `SimpleGraph.shadowGraph` supplying enough edge labels for
Theorem 5.6) is formalization setup, not KT-math, so it is excluded per
the inclusion criterion. Recorded so the no-entry state reads as a
judgment, not an omission.

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
- **Scheduled retroactive scan (set 2026-06-21; run as Phase 28 / RETROSCAN).** A
  dedicated retroactive-coverage round, run cleanup-style (candidate list producible
  on demand from `notes/PhaseN.md` + `git log`), covering two gaps.
  - **Group B — molecular phases 22b–23a, the two un-ledgered candidates: both
    judged OUT (Phase 28, 2026-07-08).** Captured incrementally at phase-close;
    the 2026-06-21 forward-scan turned up two candidates, each adjudicated here
    against the source-side inclusion criterion and verified against the *landed*
    source (KT text + landed Lean), not the provisional read. Neither meets the
    criterion. Recorded so each no-entry state reads as a judgment, not an
    omission. (22j/22l were already confirmed correctly absent — build-time
    refactors, project-side.)
    - **22i — the all-`k` genuine-hinge motive: OUT (project-side).** Candidate:
      the strengthening of the realization motive from the derived-hinge-as-meet
      `PanelHingeFramework` form (`HasFullRankRealization`) to the free-hinge
      `BodyHingeFramework` form (`HasPanelRealization` + per-link `ExtensorInPanel`
      containment). The provisional "source-side, (a)/(c)" read does not survive
      the source check, on three counts. (i) The **trigger is a project-side
      statement-selection weakness**, not a KT-math difficulty: the bare motive was
      born *vacuous* at Phase 21 (an all-zero-extensor "welded" framework satisfies
      it for every connected graph), and 22i made the project's own statement
      faithful to KT's definition of a panel-hinge realization. This is canonically
      recorded, *as project-side*, at `DESIGN.md` *Statement faithfulness to the
      source* ("a statement-selection weakness, not an empty proof") — the home the
      ledger header directs project-side items to. (ii) The **carrier split itself**
      (derived-meet → free-hinge, KT's actual model) is Lean-modelling narration —
      excluded by the header's out-of-scope carve-out, and the exact vocabulary
      (`motive`/`carrier`) is banned from chapter prose by the blueprint vocabulary
      gate. (iii) The **one genuine source-side kernel underneath — KT Lemma 5.3's
      coincident-panel full rank** (a realization with `Π(u)=Π(v)` but two *distinct*
      hinges `p(e)≠p(f)` still attaining rank `D`) — is **already exposited in full**
      at `lem:rank-parallel-full` (`rigidity-matrix.tex`, "Two hinges of parallel
      edges give the full block; KT Lemma 5.3"), spelling out the
      extensor-determined-up-to-scalar argument. KT proves Lemma 5.3 in full (p. 670)
      — it is among KT's *least* intricate arguments (a two-vertex base), below the
      "most intricate / reasonably compressed" bar — and Lemma 6.2's coincident-panel
      splice reuses it (its eq. (6.3)–(6.5) rank addition is already covered by the
      Case-I block-triangular / two-body-set entries above). Nothing un-exposited
      remains source-side. Source verified: KT pp. 669–670 (Lemmas 5.2/5.3),
      pp. 673–674 (Lemma 6.2). Pointer: `notes/Phase22i.md`;
      `notes/Phase22-realization-design.md` §1.56(a); `DESIGN.md` *Statement
      faithfulness to the source*.
    - **23a/CARRIER — `linearIndependent_normals_of_algebraicIndependent_triple`:
      OUT (routine linear algebra).** "The one genuinely-new piece" of the OD-7
      (KT Lemma 6.5) general-`k` cut-arm lift (`case_I_realization_h65_gen`).
      Verified against the landed declaration
      (`CombinatorialRigidity/Molecular/AlgebraicInduction/CaseIII/Realization.lean`):
      it is the **standard "generic ⟹ linearly independent" fact** — three (or `k+1`)
      rows of an algebraically-independent-over-`ℚ` family are `ℝ`-LI — by the
      det-polynomial argument (`det(mvPolynomialX)` is a nonzero polynomial by
      `Matrix.det_mvPolynomialX_ne_zero`, hence nonzero at an algebraically-independent
      point by `AlgebraicIndependent.aeval_ne_zero`, giving
      `Matrix.linearIndependent_rows_of_det_ne_zero`), all mathlib-standard
      commutative-algebra API. Its own docstring states it: "No `d = 3` content: the
      same Vandermonde/projection argument runs at every grade." KT never states it —
      it is the unpacking of "generic" / "algebraically independent," which KT (like
      every rigidity paper) takes as background, so there is **no compressed KT step to
      expand**. The "genuinely-new" label is *project-side Lean-decl novelty*: the
      Lemma-6.5 arm has exactly three vertices `v, a, b` (not `k+1`), so the `_general`
      companion's `(k+1)`-row shape did not fit and the fixed-three-row statement
      needed its own (identical-argument) proof — novelty to the Lean library, not a
      source-side KT-math difficulty. Excluded per the header's routine-mathlib-standard
      / linear-algebra carve-out ("mathematical difficulty, not Lean verbosity").
      Pointer: `notes/Phase23a.md` Leaf 2b.
  - **Group A — non-molecular phases 1–16 (never scanned): pending.** The Phase 5
    Laman-theorem blocker argument is the flagged likely candidate; the rest
    (Laman 1–6, matroid/pebble 7–11, body-bar/body-hinge 12–16) get a lighter
    screen (see `notes/Phase28.md` *Scan scope and method* → Group A).
