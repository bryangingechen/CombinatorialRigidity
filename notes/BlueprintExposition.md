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

**Codification status (updated 2026-06-05, after 22a).** The **capture/tracking
side is now codified**: this ledger is referenced from the standing process docs
— `notes/CLAUDE.md` (the directory file list), top-level `CLAUDE.md` *When this
commit closes a phase* (the blueprint re-read step now also writes ledgered
nodes), `blueprint/CLAUDE.md` *Proof verbosity* (the crux-node carve-out), and
`notes/MolecularConjecture.md`. The format, the sharpened inclusion criterion
(KT-math, not project-side setup), and the `(a)/(b)/(c)` flavors are stable
across 16 captured entries (17–22a). **The write-stage codification is still
deferred**, for the file's original reason: *no exposition has been written yet*
(0 of 16 entries are `done`), so "post-`sorry`-free simplification may change
what the clean account is" remains untested. Revisit the full *Proof verbosity*
write-stage rule once the first exposition lands — the natural trigger is
**22b-close**, when Case I goes fully green (Claim 6.4 discharged) and its
ledgered nodes get their first write-up.

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
- **`lem:case-II-realization` / eq. (6.12) degenerate placement** — [pending]
  **(a)**. **Stable insight:** KT's construction (Lemma 6.8, eq. 6.12) is
  *row-side with a degenerate placement* — `p1(vb) = q(ab)` places `v`'s new
  hinge *at the* `e₀=ab` *hinge of the inductive realization*, so column ops make
  `R(G,p1)` block-triangular with the `vb`-row reproducing the `e₀`-row; a slight
  rotation (Lemma 5.2 semicontinuity) lifts to nonparallel. The motion-side route
  KT gestures at ("a motion constant on `V(G)∖{v}`") is unsound — a `G`-motion
  need not be (`G−v` isn't rigid). Pointer: `notes/Phase21b.md` *Finding A*.
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
