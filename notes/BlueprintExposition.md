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

**Phase-28 close (2026-07-09).** The scheduled retroactive-coverage scan
(Group A non-molecular phases 1–16 + Group B molecular candidates 22i / 23a)
ran and closed: every candidate screened **OUT** against the source-side
inclusion criterion, no new entries — the ledger stays at **30 done**. Detail
in *Retroactive coverage* below. (The concurrent non-molecular A–F readability
sweep is not a ledger item — prose conformance, not crux-exposition coverage.)

**Phase-29 close (2026-07-09).** No-entries judgment: the phase's one new
blueprint chapter, the retrospective appendix
(`blueprint/src/chapter/retrospective.tex`), is **project-side by
construction** — it is the wrong-turns narrative this ledger's header names
as its explicit project-side mirror (`notes/FormalizationRetrospective.md`),
not KT mathematics — so it adds nothing under the source-side inclusion
criterion. The ledger stays at **30 done**.

**Phase-39 chapter pass (2026-09-25, the pre-close commit).** The
`pencil.tex` section below is written: six entries done in place (the
minimality-free reduction, the two-pencil extension biconditional, the
cut-edge repositioning, the conditioned pair's shape, the parallel-class
case, the degree-two-chain normal form) and two `[pending]` under the
green-*modulo* rule — the main-component headline, whose two hypotheses are
Phase 40's target, and the held-kernel theorem. **Result: 2 pending / 36
done** (of 38). At the close proper (L0c-ii, same day) both pending entries
were handed to Phase 40 (`notes/Phase40-design.md` §7), which writes or closes
them.

**Phase-40 close (2026-09-29).** Both entries handed over are settled: the
main-component headline's account is written, as the introduction of
`main-component.tex`, and the kernel theorem's entry closes as superseded (the
kernels retired by the PI at the close). Phase 40 added thirteen entries over its
sixteen sub-phases, all written at their sub-phase closes; the last, the good
ear's shorter count, is 40p's. **Result: 0 pending / 50 done / 1 closed as
superseded** (of 51).

**Post-Phase-40 cleanup, round 3 (`40-exposition`, closed 2026-10-04).** The round rewrote the
prose of `pencil.tex` and `main-component.tex`, and `intro.tex`'s reader path into them. No node's
statement, pins or `\uses` edges changed and no node rerouted, so no entry is added. Under the
round's default (a) (`notes/Phase40-exposition.md` *Decisions*) the blueprint no longer compares a
step with the workbook's informal argument; the reason a proof is shaped as it is stays, stated on
its own. So where a **(b)** entry below records how a step departs from the informal proof, the
entry, not the blueprint, is now the record. The close checked every pointer of the `pencil.tex`
and `main-component.tex` sections against the new text. Tasks 5, 6, 18 and 19 had updated theirs.
The close updated the rest that had gone stale: the Phase-39 main-component entry (the
introduction is now a roadmap, and the account has three homes), the remarks cut after
`lem:pencil-bridge-fibre`, `thm:pencil-x0-open-ear`, the two SHORT theorems and
`thm:pencil-x0-splitoff`, the coverage's cut comparisons, and the 40p note on the introduction.
**Result: unchanged, 0 pending / 50 done / 1 closed as superseded** (of 51).

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
  the abstract pigeonhole at `G_v^{ab}` / `G_v`. **[Updated at Phase-30 close (RELAX,
  2026-07-10): the formalization retired the footnote-6 seed-rank kernel — the
  `lem:case-III-seed-rank-bridge`/`-seed-rank-upper`/`-rank-attainment` chain named above is
  deleted, each composition now taking a device-chosen seed off a finite polynomial product's
  zero locus. `case-iii.tex` states the eq.-(6.22) bound in rank-polynomial form
  (`lem:case-III-nested-rank-lower`) with KT's original transfer summarized in a short
  remark; the Gap-2→3→1 exposition otherwise stands, and the KT-side insight above is
  unchanged — footnote 6 is KT's actual argument.]** What stays *open* (deferred successor) is
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
  triangle *directly* — third-edge/vertex-pin counting, then a cyclic-seed realization — rather
  than recurse. **Written** (22h-close): the *triangle floor* prose block in `case-iii.tex`
  (preceding `lem:triangle-third-edge`) spells out why the floor exists. Since Phase 31 (R1-3)
  the live path packages the triangle as the `m = 3` instance of `lem:cycle-realization` (KT
  state Lemma 5.4 at `3 ≤ |V| ≤ D`); the standalone three-normal assembly
  (`lem:triangle-realization` + T1–T4) is retained off-path as the accessible worked instance.
  Pointer: `notes/Phase22-realization-design.md` §1.46–§1.48 (T1–T4 signatures);
  `notes/Phase22g.md`; `notes/Phase31.md`.
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
  matrix, each nonzero at moment-curve normals by Vandermonde), evaluated at a
  common non-root of the product (originally at an algebraically-independent-over-ℚ
  seed; Phase 30 rerouted to the one-shot `exists_eval_ne_zero` non-root choice);
  the rank is then pinched between the
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

### `jacobs.tex` — Phase 32 (Jacobs' conjecture + the degree-one rank formula)

**No new entries — judged at phase close (2026-07-16).** The phase's source is
Jackson–Jordán 2008, not KT, but the criterion transfers: nothing here needed
a reroute that surfaced a compressed *source-side* step still lacking a
followable account. The two chapter-open reroutes were project-side encoding
pins (the `(3,6)`-sparsity guard admitting `|X| = 2`, fixed as the standalone
predicate — recorded reader-facing in `fmlnote:isLaman3-guard`; the
chapter-open unconditional `min(3,d)` rank form, a transcription
over-generalization refuted by `K₁,₄` and repaired to JJ's own clique
condition). The one genuine source-side compression — JJ's proof of Lemma 4.2
citing "Lemma 3.3" for a *rank* step at unbounded degree, where their stated
3.3 is independence-only at `s ≤ 3` — is already fully exposited in the
chapter itself: `sec:jacobs-zero-extension`'s preamble states exactly what
the two corollaries need (including the `K₁,₄` non-removability witness and
JJ's own "complete (and hence rigid) subgraphs" invocation), and
`cor:zero-extension-clique-rank`'s proof spells out the `K₅`-closure argument
in full. Recorded so the no-entry state reads as a judgment, not an omission.

### Phase 33 (field generality, ℝ→K structural edit — no new chapter)

**No new entries — judged at phase close (2026-07-17).** The phase restates
existing (all-green) nodes over an arbitrary infinite field; no KT-side
compressed step surfaced. Its two genuinely-new proof routes are both
*project-side* reroutes of the formalization's own earlier crutches, not
expansions of anything KT compress: the metric-free contragredient-equivariance
route replacing the project's Gram–Schmidt/O(n) proof of the meet-duality crux
(exposited in place in `meet.tex`, Slice 0), and the maximal-minor genericity
engine replacing the project's ordered-field Gram-determinant route (doc-comments
in `Mathlib/LinearAlgebra/Matrix/Rank.lean`, Slice 1). The chain-level
field-generality *claim* (appears new; Whiteley 1988 for the layer-down
precedent) lives in `algebraic-induction.tex`'s *Field generality* preamble
paragraph, which is chapter prose, not a dep-graph node. Recorded so the
no-entry state reads as a judgment, not an omission.

### `generic-lift.tex` — Phase 34 (the generic lift)

**No new entries — judged at phase close (2026-07-18).** The phase's source
is Jackson–Jordán 2010, not KT; the criterion transfers, and its two genuine
source-side compressions are both already exposited *in place* in the
chapter rather than deferred here: (i) JJ's Lemma-5.1 staged elimination on
the coordinate-segment extensor entries is replaced by the
change-of-extensor-coordinates route their own §5 Remark attributes to
Whiteley, and `lem:coordinate-extensor-basis` + `lem:endpoint-witness` spell
the whole argument out (including the entry table and why the R0-era
"standard-basis image" shortcut fails — no segment yields a pure moment
basis vector); (ii) JJ's Thm 6.4 coordinate-simplex witness and their
Lemma-7.1 perturbation are bypassed by transplanting the KT Theorem-5.6
panel witness, and the `sec:generic-lift-bodyhinge` preamble +
`lem:hinge-point-witness` state exactly what replaces them (the simultaneous
move off the hyperplane at infinity, `lem:simultaneous-affine-position`,
parallels their Lemma-7.1 coordinate choice and is credited as such). The
remaining reroutes were project-side encoding pins (transfer-form genericity
for their max-rank definition; the literal spanning-tree-family shape of the
packing corollary). Recorded so the no-entry state reads as a judgment, not
an omission.

### `pencil.tex` — Phase 39 (the hinge-pencil conjecture)

The phase's source is not KT: the conjecture is new (no literature result,
`ROADMAP.md` §39), and the chapter builds its reduction on KT Theorem 4.9's
template. The criterion transfers as in the Phase 32/34 sections — a
*source-side* step is one in the mathematical argument itself (KT's where
the chapter reuses KT, the chapter's own where it departs), a *project-side*
one is a Lean-encoding reroute. Written at the L0c chapter pass (2026-09-25).
The phase closes on a reduction (PI, 2026-09-25): `pencil_conjecture_of_X0`
carries the two main-component statements, which Phase 40 discharges, so two
entries stay `[pending]` under the green-*modulo* rule with Phase 40 as the
discharge point.

- **`thm:pencil-reduction` / `Graph.pencil_reduction`, with
  `lem:pencil-min-degree-rigid`** — [done (`pencil.tex`, the
  `sec:pencil-reduction` preamble + the two nodes)] **(b)** KT's induction
  runs over minimal graphs and reaches the others by adding
  deficiency-neutral edges in panel meets (KT Theorem 5.6, p. 670), which
  need no rank. A pencil edge added back needs its two cross-incidences, and
  imposing them can sink the smaller graph below its target: at `K₄` the
  diagonals' cross-incidences put all four points in every panel, so a
  4-cycle's hinges span ≤ 3 dimensions and its rank is ≤ 17 < 18. So the
  reduction is restated on every spanning multigraph (corrected at
  `40-exposition` task 5). **Stable insight:** once the induction runs over
  all graphs, minimality's remaining job in KT's case analysis is to supply a
  degree-two vertex when there is no proper rigid subgraph (KT Lemmas 4.5–4.6);
  a handshake count against the `(D,D)`-sparsity bound shows minimum degree
  ≥ 3 already forces a proper rigid subgraph once `D ≥ 4`, and simplicity in
  case (v) is free (`lem:pencil-simple-of-noRigid`). Pointer:
  `notes/Phase39-design.md` § *W3–W5 route recon*.
- **`lem:two-pencil-extension-iff` / `exists_extensor_two_pencils_iff`** —
  [done (the `sec:pencil-extension` preamble + proofs)] **(a)** the coplanar
  strip-and-re-add move (KT p. 670) always has a hinge in the meet of two
  panels; the pencil analogue asks for one through two prescribed points, and
  it exists iff each concurrency point lies in the other body's panel.
  **Stable insight:** the two cross-incidences are the exact obstruction, by
  Plücker injectivity of a nonzero decomposable 2-extensor; they are what the
  cut-edge case must arrange by repositioning (`lem:pencil-cut-nondegeneracy`)
  and what forces every hub's normal into a common complement at `K₄` — the
  reason simplicity alone cannot condition the generic conjunct. Pointer:
  `notes/Phase39-design.md` (the W2 leaf; opening recon R3).
- **`lem:pencil-cut-case` /
  `hasPencilRealization_of_not_twoEdgeConnected_core`, with
  `lem:pencil-cut-nondegeneracy`** — [done (node proofs)] **(a)** the
  panel-only cut-edge case places two sides independently; the pencil version
  must reposition one side by a projective automorphism (a contragredient
  acting on the normals) so the crossing edge's cross-incidences hold.
  **Stable insight:** an explicit frame automorphism over any field does it,
  and its independence choice gives the adjacent-distinct clause at the
  crossing edge for free, so the bare and adjacent-distinct forms share one
  assembly. Pointer: `notes/Phase39-design.md` § *Kernel restatement*.
- **`def:pencil-nondegenerate` + `def:pencil-conditioned-pair` +
  `def:pencil-distinct-motive`** — [done (the `sec:pencil-nondegenerate`
  prose around the three definitions; moved out of formalization notes at
  `40-exposition` task 6)] **(a)** the induction statement was
  reshaped twice: the generic conjunct conditioned on simplicity *and*
  nondegeneracy-feasibility (`K₄` refutes simplicity alone; a parallel class
  refutes feasibility alone), then an adjacent-distinct conjunct added under
  simplicity (the R2 recon's (α)). **Stable insight:** why distinctness
  cannot be a conjunct of the pencil realization itself — at a parallel class
  the deficiency-rank target is attained only with coincident points, and the
  pencil self-duality would break at the coplanar-panel base — so it is
  imposed only where parallel classes are excluded. Pointer:
  `notes/Phase39-design.md` § *W5 design pass*, § *R2 recon* (b);
  `notes/pencil/adjudications.md` (α).
- **`lem:pencil-nonsimple-case` / `hasPencilRealization_of_not_simple`, with
  `lem:extensor-pair-through-given-point`** — [done (node proof, L0b)]
  **(b)** KT Lemma 6.2's parallel-edge contraction, run without minimality
  and at the pencil condition. **Stable insight:** the contraction's
  realization *prescribes* the concurrency point the two re-realized hinges
  must pass through, so the base pair lemma is needed in prescribed-point
  form; the rank arithmetic is the block-triangular splice (KT eq. (6.3))
  plus the general upper bound, with the contraction preserving the
  deficiency. Pointer: `notes/Phase39.md` item 0 (L0b).
- **`sec:pencil-girth-chain` (`lem:pencil-degree-two-chain`,
  `lem:pencil-chain-side-distance`)** — [done (subsection preamble + nodes)]
  **(a)** the normal form of the kernel hypotheses' consumed shape was first
  stated as a chain between two hubs; the design pass found a trichotomy (the
  chain can close at a single hub — a cycle through a cut vertex) and that
  the chain's ends are non-adjacent only for `m ≤ D − 2`, the general clause
  being the distance bound `D − m`. Pointer: `notes/Phase39.md` items 1–2;
  `notes/Phase39-design.md` § *Lean-track design pass* (V3, V4).
- **`thm:pencil-conditional-realization-main-component` /
  `pencil_conjecture_of_X0`, with `def:pencil-main-component-statements`** —
  [done (`main-component.tex`, the section introduction, at Phase 40's close,
  2026-09-29; since round 3 of the post-Phase-40 cleanup, `sec:pencil-main-component-route`'s
  opening, that introduction and the subsection openings)] **(c)** the reduction itself
  is final and exposited (the three-way case split in the node's proof); what
  is not final is the account of the two main-component statements
  (`X0Dist`/`X0Gen`), hypotheses here and Phase 40's target
  (`notes/Phase40-design.md`; informal proof `notes/pencil/workbook/K-main*.md`
  (MC-89), (MC-133), (MC-157)). Under the green-*modulo* rule the fuller
  exposition — the main component as a vector bundle over planar pictures, the
  flat rank, the ear/split-off/contraction/cut steps — is written at Phase
  40's close, in Phase 40's chapter. *Rerouted at 40n's open (2026-09-28):*
  `thm:pencil-x0-generic-attains`' generic half no longer intersects fibres of
  `X₀` (refuted at two hubs with three common neighbours); it runs inside the
  pencil reduction's induction (route B, (MC-183)–(MC-189)), which this
  entry's account covers at the close; 40n landed its base, 40o its steering and both ear
  steps, and 40p the good ear and the assembly. *Written at the close* as the section
  introduction, a walk through the whole argument in order. *Since round 3 of the post-Phase-40
  cleanup* (task 25) that introduction is a roadmap with a notation list, and the account has
  three homes. `sec:pencil-main-component-route`'s opening lifts planar pictures to pencil
  realizations, describes the main component as a bundle over the admissible pictures of least
  `dim L(q)`, and shows at `K_{2,3}` the two-hubs obstruction that forces route B. The
  introduction names the one-witness and fibre-intersection lemmas (which stand in for
  irreducibility, `rem:pencil-x0-main-component`), the flat rank and Jackson–Jordán's equality,
  the steps of the induction one subsection each, the coverage, and route B for the generic
  statement. Each subsection's opening states its step's idea; `sec:main-component-cut`'s also
  states the scheme the steps share.
- **`thm:pencil-conditional-realization-pair` (kernels (K), (K-bare))** —
  [closed — superseded (Phase 40's close, 2026-09-29): the main-component route proved the
  conjecture and the PI retired the kernels] **(c)** the two kernel hypotheses were held as the
  fallback (PI, 2026-09-25) and bypassed by the main-component route; the
  theorem's lead-in carries what is stable (why both kernels take the
  induction hypothesis), and `fmlnote:pencil-conditional-realization-pair-field`
  the field hypothesis each of the project's routes would need. Nothing further is written unless a
  kernel is proved; if Phase 40 discharges the main-component statements the
  entry closes as superseded.

### Phase 40a (the Katoh–Tanigawa spine at `n = 2`, structural edit — no new chapter)

**No new entries — judged at the sub-phase close (2026-09-25).** The sub-phase restates existing
(all-green) nodes at the floor `D ≥ 3` and adds one node, `thm:theorem-55-6-rows`. No KT-side
compressed step surfaced: KT fix `d ≥ 2` throughout (p. 651), so the lowered floor recovers their
own range rather than expanding anything they compress. The two new arguments are project-side.
The triangle-base repair, a single degree-2 vertex in place of the `d = 3`-only adjacent pair
(false at `D = 3`, `K_{2,3}`), undoes a crutch of the formalization's own `D ≥ 6` pinning. The
non-spanning row-rank form serves Phase 40's consumer, not a step of KT's proof. The done
triangle-floor entry above (`lem:case-III` `|V|=3` base) stays done: `case-iii.tex`'s *The triangle
floor* now reads `d ≤ 3` for the vacuous cycle disjunct, and `lem:case-III`'s proof names the single
degree-2 vertex. The ledger stays at **2 pending / 36 done** (of 38).

### `main-component.tex` — Phase 40b (CARRIER: planar pictures, the lifting space, `X₀`)

**No new entries — judged at the sub-phase close (2026-09-26).** The chapter's source is the
project's own informal proof (`notes/pencil/workbook/K-main.md` §(K-main), Steps MC1–MC3), not KT;
the criterion transfers as in the `pencil.tex` section. Every node of `sec:main-component-carrier`
is green with a terse proof. The one restatement, `thm:pencil-x0-main-component` (the
vector-bundle / irreducible-closure form cut to its formalized content, the geometry kept in
`rem:pencil-x0-main-component`), is project-side: the formalization never forms `X₀` and replaces
its irreducibility by a fibre-intersection lemma and products of picture polynomials. The node
whose argument spans later sub-phases, `thm:pencil-x0-generic-attains` (red, in the stub
subsection `sec:main-component-statements`), gets no exposition now: its account is the Phase-39
entry `thm:pencil-conditional-realization-main-component` above, `[pending]` with Phase 40's close
as discharge point. The ledger stays at **2 pending / 36 done** (of 38).

### `main-component.tex` — Phase 40c (FLAT: the flat rank)

**No new entries — judged at the sub-phase close (2026-09-26).** The source is again the project's
own informal proof (`notes/pencil/workbook/K-main.md`, Steps MC4–MC5), and the criterion transfers
as in the `pencil.tex` section. Every node of `sec:main-component-flat`, with
`lem:deficiency-antitone` (`deficiency.tex`) and `lem:relative-deficiency-rank-bound`
(`rigidity-matrix.tex`), is green and landed as first scoped, in one build commit from the design
recon's spike: nothing rerouted or decomposed. The substantive step, identifying the planar screws
of a flat configuration with affine functions (`lem:pencil-flat-split`) and the lifting planes with
the lifting space (`lem:pencil-lifting-planes-dim`), is spelled out in full in Step MC4 and in those
nodes' proofs, with its classical instances cited (Crapo–Whiteley 1982 Example 4.4; Whiteley 1996
§8.3); nothing compressed needed expanding. The field-general coordinates on the screw space and the
bookkeeping of bodies off `V(G)` (`fmlnote:pencil-lifting-planes`) are project-side. The account of
the whole induction stays with the Phase-39 entry `thm:pencil-conditional-realization-main-component`
above, `[pending]` until Phase 40's close. The ledger stays at **2 pending / 36 done** (of 38).

### `main-component.tex` — Phase 40d (BRIDGE: Jackson–Jordán's equality)

**No new entries — judged at the sub-phase close (2026-09-26).** The source is the project's own
informal proof (`notes/pencil/workbook/K-main-MC11.md`, (MC-172)), which derives the equality
`dim L(q) = 3 + def₂` from Katoh–Tanigawa's rank formula at `d = 2` in place of Jackson–Jordán's
pin-collinear theorem; the criterion transfers as in the `pencil.tex` section. Every node of
`sec:main-component-jj` is green and landed as first scoped, in one build commit from the design
recon's spike: nothing rerouted or decomposed. The argument is short and complete in the nodes'
proofs: move a realization at the deficiency rank into the chart `(x_v, y_v, 1)` by rescaling the
normals, read its rank there by the flat rank's plane framework, and close with the partition bound.
The edge relabelling (`lem:pencil-jj-embed-edges`, `fmlnote:pencil-jj-embed-edges`) serves only the
formal label type and is project-side. The end-to-end re-read added one clause to
`thm:pencil-jj-equality`'s proof (three members in a closed neighbourhood give the chart lemma's two
bodies). The account of the whole induction stays with the Phase-39 entry
`thm:pencil-conditional-realization-main-component` above, `[pending]` until Phase 40's close. The
ledger stays at **2 pending / 36 done** (of 38).

### `main-component.tex` — Phase 40e (CUTBRIDGE: cut vertices and bridges)

**One new entry — judged at the sub-phase close (2026-09-26).** The source is the project's own
informal proof (`notes/pencil/workbook/K-main-MC14.md`, (MC-52) and (MC-53)); the criterion
transfers as in the `pencil.tex` section. The entry below is written in place. The rest landed as
scoped or is project-side. The cut-vertex deficiency and rank laws follow the informal (i) and (ii)
directly. BRIDGE counts ranks and deficiencies by one cut at the last bridge and a telescope along
the path, not by the single-bridge step applied `k + 1` times, because the intermediate graphs have
no admissible picture; the node's proof says so in one sentence. The "only if" halves are a tracked
item of the design doc, not nodes. The account of the whole induction stays with the Phase-39 entry
`thm:pencil-conditional-realization-main-component` above, `[pending]` until Phase 40's close. The
ledger is now **2 pending / 37 done** (of 39).

- **`lem:pencil-bridge-fibre` / `Graph.exists_liftingRestrict_eq_of_bridgePath`, with
  `lem:pencil-cut-fibre`** — [done (the two nodes' proofs and the remark after
  `lem:pencil-bridge-fibre`, at the 40e close; round 3 of the post-Phase-40 cleanup cut the remark,
  a comparison with the informal count, and the subsection opening now states the extension)]
  **(b)** the informal proof of (MC-53)(iii) derives
  the ontoness of both restrictions from the dimension count
  `dim L_G = dim L_{G₁} + dim L_{G₂} + k − 2`, case by case in `k = 0, 1, ≥ 2` and at admissible
  pictures (the case `k = 0` uses `q_a ≠ q_b`); (MC-52)(iii) likewise uses three non-collinear points
  at the cut vertex. **Stable insight:** the steps need each restriction onto separately, not the
  fibre-product description, and that holds at every picture by one extension. `a` is the only body
  of `G₁` with an edge leaving it, so extending `z¹` by any affine function agreeing with it on
  `N_{G₁}[a]` is affine on every closed neighbourhood of `G`, for every `k` and with no
  admissibility; at a cut vertex the same extension runs through `v`. Pointer: `notes/Phase40e.md`
  (build 2's first half).

### `main-component.tex` — Phase 40f (CONTRACT-R: contraction at a `def₂`-rigid core)

**One new entry — judged at the sub-phase close (2026-09-26).** The source is the project's own
informal proof (`notes/pencil/workbook/K-main-MC12.md` and `K-main-MC14.md`, (MC-34)–(MC-39) and
(MC-59)), after Katoh–Tanigawa's Lemma 6.3; the criterion transfers as in the `pencil.tex` section.
The entry below is written in place. The rest landed as scoped, in one build commit from the design
recon's spike: the rescaled lifting system and its two ends follow (MC-37) and (MC-59)(c1)–(c3),
and the collapsed-placement rank is Phase 22i's composition, with the projected rank polynomial now
keeping its value at the witness. The placement of the general pieces is project-side. The account
of the whole induction stays with the Phase-39 entry
`thm:pencil-conditional-realization-main-component` above, `[pending]` until Phase 40's close. The
ledger is now **2 pending / 38 done** (of 40).

- **`lem:pencil-contract-core-plane` / `Graph.exists_core_plane`, with
  `lem:pencil-contract-core-rank` and `thm:pencil-x0-contract-rigid`** — [done (the three nodes'
  proofs, at the 40f close)] **(b)** the informal step (MC-39) takes `X₀(H)` attaining as a
  hypothesis and gets the core's rigidity at `X₀(G)`'s generic point from it, through (MC-38)'s
  core-free condition (restriction onto `L_H`, then dominance of `B_G → B_H`); (MC-37)'s step 3 adds
  a translation-invariance and slice-irreducibility argument for the collapsed picture. **Stable
  insight:** at a core of planar deficiency zero neither is needed. The rows of the rescaled system
  at a core body keep the weight `(x_w, y_w, 1)` along the whole curve, so with `L_H(q) = Aff(q)`
  every solution is flat on the core, and at `t ≠ 0` its core heights are affine in `q(t)`; the
  core's rank is then its flat rank `6(|W| − 1)`, from Jackson–Jordán at `H` alone. One ambient
  picture, generic for `G/H` and `H` and main for `G`, collapses at `r`'s own picture point, so no
  translation argument arises either. Pointer: `notes/Phase40f.md`; `notes/Phase40-design.md` §3
  STEPS (the settled slice item).

### `main-component.tex` — Phase 40g (CHAIN: the ear steps and the cycle)

**One new entry — judged at the sub-phase close (2026-09-27).** The source is the project's own
informal proof (`notes/pencil/workbook/K-main-MC10.md`, `K-main-MC13.md` and `K-main-MC20.md`,
(MC-16)–(MC-21), (MC-134) and (MC-177)); the criterion transfers as in the `pencil.tex` section. The
entry below is written in place. The rest landed as scoped, in two build commits from the design
recon's spike: the 2-cut rank identity for any two graphs sharing out the edges has the landed
induced identity's proof (which is now its corollary), the path's rank and relative screws are
(MC-177)(i)(ii), and the closed ear is the cut-vertex step plus the cycle. The explicit-path format
and asking (H) at `G` only are project-side. The account of the whole induction stays with the
Phase-39 entry `thm:pencil-conditional-realization-main-component` above, `[pending]` until Phase
40's close. The ledger is now **2 pending / 39 done** (of 41).

- **`thm:pencil-x0-open-ear` / `Graph.X0Attains.of_openEar`, with `lem:pencil-ear-fibre`** —
  [done (the theorem's proof and the remark after it, at the 40g close; round 3 of the
  post-Phase-40 cleanup cut the remark, a comparison with the informal step, and the subsection
  opening now states the one-configuration idea)] **(b)** the informal step
  (MC-20) takes the span `Λ = K⁶` of an open ear with `k ≥ 5` from (MC-19)(b), which holds "for any
  flag pair with `p_a ≠ p_b`": the ends sit wherever `X₀(G′)`'s generic point puts them, and
  (MC-19)(b)'s proof exhibits one placement per projective orbit of flag pairs, over the
  irreducible placement space. **Stable insight:** no uniformity over the ends is needed. The
  independence of six fixed ear joins is one polynomial condition in the picture and the heights, so
  one point where it holds suffices, and that point may be degenerate: a picture putting `a` and `b`
  at one point (not admissible), carrying the closed hexagon of (MC-134)(a). What the point must
  satisfy is that its heights are heights of `G` at the general picture, and the free interior
  heights of an ear give that ((MC-18)(a)): the height `1` at `x₂`, `x₃` and `0` elsewhere vanishes on
  `V₁ ∪ {x₁, x_k}`, so it lies in `L_G(q)` at every admissible `q` (this needs `k ≥ 4`). The picture
  is then chosen off that polynomial's zero set, and the heights where `G[V₁]` attains and the joins
  stay independent meet in `L_G(q)` by the fibre-intersection lemma. Pointer: `notes/Phase40g.md`;
  `notes/Phase40-design.md` §3 STEPS (*CHAIN done*).

### `main-component.tex` — Phase 40h (SHORT: the open ears with two, three and four interior bodies)

**One new entry — judged at the sub-phase close (2026-09-27).** The source is the project's own
informal proof (`notes/pencil/workbook/K-main-MC13.md` and `K-main-MC14.md`, (MC-54) and
(MC-179)–(MC-182)); the criterion transfers as in the `pencil.tex` section. The entry below is
written in place. The rest landed as scoped or is project-side. The line geometry is (MC-179), its
insertion half by a shorter proof: a vector off a subspace stays off it along a line at one of any
two nonzero parameters. The two-body step is CHAIN's one-picture route with three joins of the
closed hexagon. The fixed-base-data order is (MC-180)'s Steps 1–2, and the two deficiency bounds are
direct per-partition extensions. Where the four-body step departs from (MC-180)'s Steps 3–4 (the
collision witness, two rounds of genericity) was the remark after `thm:pencil-x0-open-ear-four`, a
formalization detail, not an entry; round 3 of the post-Phase-40 cleanup cut it, and the
theorem's proof gives its reasons. The account of the whole induction stays with the Phase-39
entry `thm:pencil-conditional-realization-main-component` above, `[pending]` until Phase 40's close.
The ledger is now **2 pending / 40 done** (of 42).

- **`thm:pencil-x0-open-ear-four` / `Graph.X0Attains.of_openEar_four` and
  `thm:pencil-x0-open-ear-three` / `Graph.X0Attains.of_openEar_three`, with
  `lem:pencil-insertion`** — [done (the subsection preamble, the two theorems' proofs and the remark
  after the three-body theorem, at the 40h close; round 3 of the post-Phase-40 cleanup cut the
  remark, a comparison with the informal route, and the count against `G″` now leads the
  opening)] **(b)** the informal proof first counted the
  `k = 3, 4` open-ear steps against `G′ = G[V₁]` alone, reduced by (MC-22) to two conditions at
  `X₀(G′)`'s generic point: a lower bound on `dim ρ` from the 2-ear gadget (MC-24), a further strong
  induction, and a property of `Λ_k` over the placements, proved in each of the four orbits of the
  ends' flag pair ((MC-25) with the collision lemma (MC-136) at `k = 4`; (MC-45)'s `r`-split with
  (MC-26)'s links at `k = 3`). The SHORT recon found the shorter route, now (MC-179)–(MC-181), found
  by formalization and second-read before the open. **Stable insight:** count against `G″`, `G` with
  its second interior body suppressed, whose deficiency is no larger ((MC-182)). `G″` bounds
  `dim W = dim(ρ + Λ_{k−1})` directly, and putting `x₂` back on a line through `x₁` or `x₃` gains a
  dimension unless `W` holds both stars ((MC-179)(d)). Both stars force `W = Λ²K⁴`. At `k = 4` they
  contain the six edges of the tetrahedron `x₁, x₃, x₄, p_b` ((MC-179)(a)). At `k = 3` they span the
  5-dimensional `(x₁ ∧ x₃)^⊥` ((MC-179)(b)): either a relative screw pairing nonzero with a line
  joining the ends' planes, chosen before the ear, lies outside them, or every relative screw pairs
  to zero with those lines and `dim W ≤ 3` ((MC-179)(c)). No `δ`, no bound on `dim ρ`, no orbit:
  the four orbits collapse to whether the ends' planes coincide. Pointer: `notes/Phase40h.md`;
  `notes/Phase40-design.md` §3 STEPS (*SHORT done*).

### `main-component.tex` — Phase 40i (ORBIT: the open ears with one or two interior bodies at non-adjacent ends)

**One new entry — judged at the sub-phase close (2026-09-28).** The source is the project's own
informal proof (`notes/pencil/workbook/K-main-MC13.md`, (MC-54) at `k = 1` and (MC-173)–(MC-176)),
and the criterion transfers as in the `pencil.tex` section. The entry below is written in place.
The rest landed as scoped, in three build commits from the design recon's spike. U2 is (MC-48)(ii)'s
argument read as rank–nullity on the lifting system's kernel, the incidence is (MC-174), and the
merged-deficiency split-off bound is a direct per-partition comparison. That (MC-173) is consumed
in existence form, its chart polynomial replaced by EARGEN's span transfer, is project-side. The
account of the whole induction stays with the Phase-39 entry
`thm:pencil-conditional-realization-main-component` above, `[pending]` until Phase 40's close. The
ledger is now **2 pending / 41 done** (of 43).

- **`thm:pencil-x0-open-ear-two-orbit` / `Graph.X0Attains.of_openEar_two_of_splitOff`, with
  `lem:pencil-insertion-two` and `lem:pencil-one-ear-base`** — [done (the subsection preamble and the
  nodes' proofs, at the 40i close; round 3 of the post-Phase-40 cleanup folded the remark after the
  two-body theorem into the preamble)] **(b)** the informal proof first proved the `k = 2`, `a ≁ b`
  open-ear step against `G′ = G[V₁]` alone, through
  (MC-22)'s reduction. It described the bad subspaces `B₂(r)` of `ρ` by a dimension count over the
  ear's placements, one orbit of the ends' flag pair at a time ((MC-46), with the orbit table
  (MC-138)), and needed `dim U ≠ 1`. The ORBIT recon (2026-09-26) found the shorter route, now
  (MC-173)–(MC-176), found by formalization and second-read. **Stable insight:** count against
  `G₁`, `G` with `x₂` suppressed, a one-body ear. Its base configuration puts `x₁`'s point `y` on
  `m = π_a ∩ π_b` with the flag pair in orbit (i): `p_b ∉ π_a` and `p_a ∉ π_b`. In the frame
  `p_a, y, u₀, p_b` (`u₀` the direction of `m`) the six joins span `Λ²K⁴`, and `W = ρ + Λ₁(y)`
  already holds `p_a ∧ y` and `y ∧ p_b`. So unless `W = Λ²K⁴`, one of `y ∧ u₀`, `u₀ ∧ p_b`,
  `p_a ∧ u₀`, `p_a ∧ p_b` lies off `W`, and moving `x₁` in `π_a` or `x₂` in `π_b` along the
  matching line gains a dimension. No orbit is computed and `B₂(r)` is never described: orbit (i)
  is the only property of the ends used, and `δ₂ ≥ 2` gives it at a general point through
  Jackson–Jordán at `G′ + ab` (U2, `dim U ≥ 2`). The base is the other half: a height of a one-body
  ear graph restricts to one of `G′` whose planes at `a` and `b` agree at the ear body's picture,
  so that picture is chosen jointly with the heights ((MC-174)), with no dominance argument. The
  same base is the whole `k = 1` step. Pointer: `notes/Phase40i.md`; `notes/Phase40-design.md` §3
  STEPS (*ORBIT done*).

### `main-component.tex` — Phase 40j (SPLITOFF: splitting off a body of degree two at non-adjacent neighbours)

**One new entry — judged at the sub-phase close (2026-09-28).** The source is the project's own
informal proof (`notes/pencil/workbook/K-main-MC11.md`, Step MC11, (MC-28)–(MC-31)), after the
splitting-off case of Jackson–Jordán's proof of the pin-collinear theorem; the criterion transfers
as in the `pencil.tex` section. The entry below is written in place. The rest landed as scoped, in
two build commits from the design recon's spike. (MC-28) is the informal motion count, (MC-29) is
two landed deficiency bounds composed, and (MC-30)(i) is the informal dimension count at one
picture, on the lifting system's kernel. That the flexes of `G′` are that kernel, not `L_{G′}`
(`G′` may have bodies of degree 1), is a carrier detail recorded in the node's proof (since round
3 of the post-Phase-40 cleanup, in the lead-in to `lem:pencil-splitoff-flexes`). The account of
the whole induction stays with the Phase-39 entry `thm:pencil-conditional-realization-main-component`
above, `[pending]` until Phase 40's close. The ledger is now **2 pending / 42 done** (of 44).

- **`thm:pencil-x0-splitoff` / `Graph.X0Attains.of_splitOff`, with `lem:pencil-splitoff-curve` and
  `lem:pencil-curve-limit`** — [done (the subsection preamble, the theorem's proof and the remark
  after it, at the 40j close; round 3 of the post-Phase-40 cleanup cut the remark, a comparison
  with the informal step, and its idea is in the opening and the theorem's proof)]
  **(b)** the informal step (MC-31) reaches `X₀(G)` from the special
  configuration, which puts `x` on the line `p_a p_b` and has the rank of `G″` plus five but is not
  admissible: (MC-30)(ii) moves `x`'s picture off the line in an arbitrary direction `η`, keeps the
  curve over admissible pictures with `dim L_G` minimal by the formula (★) and (MC-4)(b), lifts it by
  a rational family `P(t)` of flexes, and (MC-31) closes by lower semicontinuity of the rank on the
  irreducible `X₀(G)` ((MC-2)). **Stable insight:** no geometry of `X₀(G)` is needed. Take `η` to end
  the curve at the general picture itself (`q(1) = q`), so main-ness along it is one polynomial in
  `t`, nonzero at `t = 1`, and solution dimensions are compared only at `q` ((MC-30)(i)). The
  incidence that makes a flex a height of `G` is the pencil `φ₀ + tψ`; once `s` makes `φ₀` nonzero
  on the flexes of `G′` (or every flex has `h_a = h_b`), the pencil has an explicit line of
  solutions through `y₀`, on which `ψ` is constant. It is `P(t)` times a scalar equal to `1` at
  `t = 0`, so the family is polynomial. Lower semicontinuity is then along the one curve of normals: the rank polynomial
  restricted to it is nonzero at `t = 0`, and one attaining configuration over a main picture
  suffices. Pointer: `notes/Phase40j.md`; `notes/Phase40-design.md` §3 STEPS (*SPLITOFF done*).

### `main-component.tex` — Phase 40k (CONTRACT-A: contraction at an additive core)

**One new entry — judged at the sub-phase close (2026-09-28).** The source is the project's own
informal proof (`notes/pencil/workbook/K-main-MC15.md` and `K-main-MC12.md`, (MC-69), (MC-71) and
(MC-34)–(MC-39)), after Katoh–Tanigawa's Lemma 6.3; the criterion transfers as in the `pencil.tex`
section. The entry below is written in place. The rest landed as scoped, in three build commits
from the design recon's spike: the curve, the rescaled lifting system and both of its ends are
CONTRACT-R's, (MC-69)(a)'s dimension formula enters as an inequality, and the `Contract.lean`
split and the placement of the general pieces are project-side. The account of the whole
induction stays with the Phase-39 entry `thm:pencil-conditional-realization-main-component` above,
`[pending]` until Phase 40's close. The ledger is now **2 pending / 43 done** (of 45).

- **`thm:pencil-x0-contract-additive` / `Graph.X0Attains.of_additiveContract`, with
  `lem:pencil-contract-kernel-bound` and `lem:pencil-contract-magnified-rank`** — [done (the
  subsection preamble and the theorem's proof, at the 40k close; round 3 of the post-Phase-40
  cleanup folded the remark after the theorem into the preamble)] **(b)** the
  informal step (MC-71) gets the core's rank at `X₀(G)`'s generic point as CONTRACT-R's informal
  step does: at a generic picture (MC-68)(d) makes the heights of `G` restrict onto `L_H`
  ((MC-38)(i), core-freeness), (MC-38) deduces from it, by the dominance of restriction to the
  core, that the core is rigid at `X₀(G)`'s generic point, (MC-69)(b) supplies the no-jump
  condition (MC-37)(ii), and (MC-39) assembles. **Stable insight:** neither the restriction at a
  generic picture nor the dominance is needed. At the one picture `q`, the kernel
  of `M(0)` is bounded below by `3 + def₂(G)` (it is no smaller than the kernels near it, and those
  contain `L_G(q(t))`) and above by `dim ρ(ker M(0)) + dim L_{G/H}(q) − 3` through the core heights
  `ρ`; with Jackson–Jordán at `H` and `G/H`, additivity makes the bounds meet, so
  `ρ(ker M(0)) = L_H(q)` ((MC-69)(b)'s by-product `S ⊆ T`) and the kernel does not jump. Attainment
  at `H` then pulls back to a nonempty open condition on `ker M(0)`, which meets the degenerate-rank
  condition, and along the polynomial section through a common point both hold off finitely many
  `t`. The rows of `M(t)` between core bodies do not depend on `t`, so the core heights stay in
  `L_H(q)`, and the configuration of `H` over `q(t)` is a collineation of `K⁴` applied to the one
  over the fixed `q`; the core's rank is read there, where `X₀(H)` attains. At `def₂(H) = 0` the
  same curve gives CONTRACT-R (the 40f entry above), with the flat core in place of attainment at
  `H`. Pointer: `notes/Phase40k.md`; `notes/Phase40-design.md` §3 STEPS (*CONTRACT-A done*).

### `main-component.tex` — Phase 40l (REDUCE: the one-step interface, the induction and the deficiency layer)

**Three new entries — judged at the sub-phase close (2026-09-28).** The source is the project's own
informal proof (`notes/pencil/workbook/K-main-MC16.md`, Step MC16, (MC-75)–(MC-89)); the criterion
transfers as in the `pencil.tex` section. The three entries are the design recon's proof-level
departures D1–D3, each written in place in its node's proof (the core bound's expanded at this
close). They share one stable insight: none of the partition estimates needs the partition of a
graph into its maximal rigid sets and its rigid-free quotient ((MC-77)), through which the informal
proofs pass. The rest landed as scoped, in three build commits from the design recon's two spikes:
the one-step predicate and the carried induction are project-side packaging, and the value
calculus (the singleton bound, adding one body, (MC-76), merging along a rigid set, the additive
core) is the informal proof's own counting. The account of the whole induction stays with the
Phase-39 entry `thm:pencil-conditional-realization-main-component` above, `[pending]` until Phase
40's close. The ledger is now **2 pending / 46 done** (of 48).

- **`lem:deficiency-core-bound` / `Graph.partitionDef_induce_id_le_of_maximal`, with
  `Graph.deficiency_three_induce_eq_zero_of_le`** — [done (the node's proof, expanded at the 40l
  close)] **(b)** the informal (MC-87)(ii) bounds the singleton values above a maximal rigid set
  through the partition of `G` into its maximal rigid sets, whose quotient has no rigid set of two
  or more members ((MC-77)), or through (MC-119)'s finest optimal partition, with the maximal rigid
  sets of `G − x` treated apart. **Stable insight:** a minimal counterexample needs neither
  partition and treats both cases alike. Part (1): if `W ⊆ Y` is rigid, `s(Y) ≤ s(W)`, and
  `s(W) ≤ s(Q)` whenever `W ⊆ Q ⊊ Y`, then `G[Y]` is rigid — coarsen any partition so that `W`
  lies in one part (the value does not drop), and the singleton bound at that part caps the planar
  value at zero, hence the spatial one. Part (2): a smallest `X ⊇ W` with `s(X) < s(W)` either
  avoids `X₀`, and is rigid by (1), or is `Y` plus the body of `X₀`, which then sends two edges
  into `Y ≠ W`, so `s(Y) = s(W)` and `Y` is rigid by (1); both contradict maximality. Pointer:
  `notes/Phase40l.md`; `notes/Phase40-design.md` §3 COVERAGE (D1).
- **`lem:deficiency-tight-rigid` / `Graph.deficiency_three_induce_eq_zero_of_tight`** — [done (the
  node's proof, at 40l's B3)] **(b)** the informal (MC-79)(iii) places a tight set inside a maximal
  rigid set through the same partition, by Lemma T ((MC-78)). **Stable insight:** a direct count.
  On a partition of a tight set `X` (`|X| ≥ 3`, `s(X) ≤ 1`, every subset of two or more bodies of
  singleton value at least one) the spatial value is `v₃ = 2v₂ − d`. A partition with a part `Z`,
  `2 ≤ |Z| < |X|`, has `v₂ ≤ s(X) − s(Z) ≤ 0`; the singletons have `e(X) ≥ 3`, so `v₃ < 0`; only
  `{X}` reaches zero. The 4-cycle of a two-body chain with adjacent ends is rigid this way.
  Pointer: `notes/Phase40l.md`; `notes/Phase40-design.md` §3 COVERAGE (D3).
- **`lem:deficiency-one-body-chain` / `Graph.deficiencyMerged_three_add_five_le`** — [done (the
  node's proof, at 40l's B3)] **(b)** the informal (MC-79)(ii) first bullet reads the merged
  deficiency at a one-body chain off (MC-79)(i)'s formula over the quotient of `G − x` by its
  maximal rigid sets. **Stable insight:** refine one part. In an optimal merged partition with part
  `Q ∋ a, b`, refining `Q` by a partition `R` changes the value by `R`'s value in `G[Q]`, so a gap
  below five bounds every such `R` by `4`, and by `0` when `R` keeps `a` and `b` together. Then
  every partition of `Q ∪ {x}` has value at most zero (alone, `x`'s two crossing edges cost
  `10 − 6`; beside others, each crossing edge at `x` costs `5`), so `x` lies in a rigid set.
  Pointer: `notes/Phase40l.md`; `notes/Phase40-design.md` §3 COVERAGE (D2).

### `main-component.tex` — Phase 40m (CHAINS + THEOREM-S: chains, cuts, Theorem S and the covering theorem)

**One new entry — judged at the sub-phase close (2026-09-28).** The source is the project's own
informal proof (`notes/pencil/workbook/K-main-MC16.md`, Step MC16, (MC-75)–(MC-89), with
(MC-21)(b) and (MC-139) for θ-graphs); the criterion transfers as in the `pencil.tex` section. The
entry below is the design recon's fourth proof-level departure, D4, written in place in the node
proofs and the remark. The rest landed as scoped, in five build commits from the design recon's
spikes: the maximal ear, which serves chain extraction, the cycle and the chain of bridges, is the
informal proof's maximal path of bodies of degree two, and the one-gate connectivity lemma and the
standing hypotheses at the smaller graphs are project-side graph bookkeeping; the chain dispatch,
the count of bodies of degree two and the planar-rigid contraction follow (MC-79)(v), (MC-76) and
(MC-75)(iii). The account of the whole induction stays with the Phase-39 entry
`thm:pencil-conditional-realization-main-component` above, `[pending]` until Phase 40's close, at
MOTIVES. The ledger is now **2 pending / 47 done** (of 49).

- **`thm:pencil-x0-theorem-s` / `Graph.IsX0Graph.exists_additiveCore`, with
  `thm:pencil-x0-coverage` and `rem:pencil-x0-theta`** — [done (the two nodes' proofs and the
  remark, at 40m's B5 and close; round 3 of the post-Phase-40 cleanup cut the comparisons with the
  informal case analysis, and the remark now ends with how the coverage reaches a θ-graph)]
  **(b)** the informal case analysis ((MC-89), step 5) sends
  θ-graphs to their own step, THETA ((MC-21)(b), covered along the longest path by (MC-139)), and
  states Theorem S ((MC-80)) on the class 𝒮, which excludes them, with the extra conclusion
  `1 ≤ def₂(G[W]) < def₂(G)`. **Stable insight:** with the core produced by maximality, the core
  bound (D1) and additivity ((MC-87)), no step of Theorem S's proof uses that `G` is not a
  θ-graph, and the contraction step needs neither inequality; so θ-graphs fall under the covering
  theorem's other cases and need no step of their own (`rem:pencil-x0-theta` keeps (MC-139)'s
  covering as a second one). Pointer: `notes/Phase40m.md`; `notes/Phase40-design.md` §3 COVERAGE
  (D4).

### `main-component.tex` — Phase 40n (MOTIVES-DIST+BASE: the distinct statement, and the generic realization without a planar-rigid set)

**One new entry — judged at the sub-phase close (2026-09-28).** The source is the project's own
informal proof (`notes/pencil/workbook/K-main.md`, (MC-12)–(MC-14), and `K-main-MC19.md`, route B,
(MC-183)–(MC-189)); the criterion transfers as in the `pencil.tex` section. The entry below is
written in place in the three node proofs. The rest landed as scoped: the distinct statement is
two lines over the covering theorem, feasibility's hub bounds and the three-body case are landed
Phase-39 facts restated, and the two-ear graph is a type change (the new body and edges in larger
types). The two-hubs obstruction and route B, which move the generic statement inside the pencil
reduction's induction, belong to the Phase-39 entry `thm:pencil-conditional-realization-main-component`
above, `[pending]` until Phase 40's close. The ledger is now **2 pending / 48 done** (of 50).

- **`thm:pencil-x0-base-generic` /
  `Graph.IsX0Graph.hasGenericPencilRealization_of_forall_deficiency_two_ne_zero`, with
  `lem:pencil-x0-planes-separate` and `lem:pencil-x0-conjunct-three`** — [done (the three nodes'
  proofs, at 40n's B1–B3 and close)] **(b)** the informal base ((MC-14), informal modulo
  Jackson–Jordán in characteristic zero) reads nondegeneracy off (MC-12)'s conditions on the hub
  pairs, and gets each from (MC-13): an isomorphism of `G_e`'s lifting space with the equal-planes
  heights at pictures with the new body off a line, and the exact value of `def₂(G_e)`. **Stable
  insight:** an injection and an inequality are enough, at every pair of distinct bodies at once.
  The equal-planes heights extend to `G_e` at any picture of the new body; at a graph with no
  planar-rigid set the partition case analysis gives `def₂(G_e) ≤ def₂(G) − 1`; Jackson–Jordán's
  equality at both graphs, over every infinite field, then separates the two planes off one
  polynomial, the new body's picture fixed at a non-root. (MC-12)'s sufficient half needs neither the standing hypotheses nor
  feasibility ((MC-189)). Pointer: `notes/Phase40n.md`; `notes/Phase40-design.md` §3 MOTIVES.

### `main-component.tex` — Phase 40o (MOTIVES-EARS: the steering and the two ear steps)

**No new entries — judged at the sub-phase close (2026-09-29).** The source is the project's own
informal proof (`notes/pencil/workbook/K-main-MC19.md`, route B, (MC-185)–(MC-188) and
(MC-190)–(MC-192), second-read after the builds); the criterion transfers as in the `pencil.tex`
section. The three new green nodes, `lem:pencil-generic-steer`, `lem:pencil-generic-one-ear` and
`lem:pencil-generic-pendant-triangle`, carry their arguments in full in their proofs. What they
change against the informal route is scope, not a compressed step: the steering holds at any
subgraph and reads its conditions off a second realization, the one-ear step needs no non-adjacent
ends (feasibility excludes the triangle), and the pendant triangle needs no deficiency hypothesis
(the deficiencies add at the cut vertex). The steering's three-closed-neighbours count is the Lean
chart's coordinates ((MC-193)), Lean-modelling the header's carve-out excludes. The account of
route B as a whole stays with the Phase-39 entry
`thm:pencil-conditional-realization-main-component` above, `[pending]` until Phase 40's close. The
ledger stays at **2 pending / 48 done** (of 50).

### `main-component.tex` — Phase 40p (MOTIVES-REDUCE+CLOSE: the good ear, the assembly and both headlines) and the Phase 40 close

**One new entry — judged at the sub-phase close, which is Phase 40's (2026-09-29).** The source is
the project's own informal proof (`notes/pencil/workbook/K-main-MC19.md`, (MC-129)); the criterion
transfers as in the `pencil.tex` section. The entry below is a proof-level departure, written in
place in the node's proof (the 40l/40m precedent: compiler-checked, recorded in the blueprint, not
second-read; the PI did not overturn it at the close). The rest landed as scoped: the generic step,
the conditioned pair at every nonempty graph and both headlines assemble landed pieces, and the
add-one-body identity is a count. With the phase closed the two entries handed over from Phase 39
are settled (the `pencil.tex` section above), and the chapter end-to-end re-read found the
section introduction a list of subsections; it became the account of the whole argument (since
round 3 of the post-Phase-40 cleanup, a roadmap with a notation list: the Phase-39 entry above
says where the account now is). The
ledger is now **0 pending / 50 done / 1 closed as superseded** (of 51).

- **`lem:pencil-rigid-good-ear` / `Graph.IsX0Graph.exists_oneEar_or_pendantTriangle`, with
  `Graph.exists_eq_triple_of_minimal` and `Graph.exists_closedEar_two_of_triangle`** — [done (the
  node's proof, at 40p's B1)] **(b)** the informal (MC-129) settles the all-hub case by `G[W₀]`
  being a cycle, walks the maximal chain of bodies of degree two through the chosen body, and gets
  the rigidity of `W₀ ∖ {y}` from its connectivity and its bridges. **Stable insight:** at a
  minimal planar-rigid set `W₀` the singleton values do all the work. Two adjacent bodies of `W₀`
  with at most one neighbour each in the rest force `W₀` to be a triangle (N1, the count at one
  edge, which also excludes the all-hub case by the hub-neighbourhood bound); a non-hub neighbour
  of the chosen body gives the pendant triangle by the same count (N2, no chain walk); and at two
  hub neighbours `W₀ ∖ {y}` is tight, hence rigid by the tight-set lemma (N3, no bridge case),
  minimality entering only through the singleton values of proper subsets (N4). Pointer:
  `notes/Phase40p.md`; `notes/Phase40-design.md` §3 MOTIVES.

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
      (Decl since deleted — Phase 30's relaxation; the surviving LI bricks are the pure
      det-polynomial `exists_tripleLI_polynomial` / `exists_tupleLI_polynomial`, the same
      det argument without the alg-indep evaluation point. The screening verdict is
      unaffected.) Pointer: `notes/Phase23a.md` Leaf 2b.
  - **Group A — non-molecular phases 1–16 (never scanned): all screened OUT,
    no new entries (Phase 28, 2026-07-08).** These predate the ledger; the scan
    re-read each phase's `notes/PhaseN.md` + blueprint chapter for a source-side
    compressed step not already exposited. None qualifies — the header's 30-done
    count is unchanged. The structural reason: Phases 1–5 ran in **backfill mode**
    (blueprint written end-to-end after the Lean, full green prose proofs from the
    start) and Phases 6–16 in forward mode *with the phase-close prose pass*, so
    unlike the molecular program's churny reroutes (which motivated capture-now/
    write-later), the Laman/matroid/body-bar chapters were self-exposited by
    construction — every node landed green with a followable prose proof (verified:
    `laman`/`frameworks`/`trivial-motions`/`rigidity-matrix`/`count-matroid`/
    `matroid-union`/`pebble-game`/`dfs`/`executable`/`body-bar`/`body-hinge`.tex
    carry only `\leanok` proofs, no red/`\notready`/TODO nodes). Recorded so the
    no-entry state reads as a deliberate judgment, not an omission.
    - **Phase 5 Laman-theorem blocker argument (the flagged likely-IN candidate)
      — OUT, source-side kernel already exposited.** Candidate: the classical
      Henneberg/Lovász–Yemini degree-3 blocker argument (KT is *not* the source
      here — this is Jordán 2016 Lemma 2.1.4(b), *every degree-3 vertex of a
      `(2,3)`-sparse graph is suitable*: if not, three maximal critical sets
      `X_uw, X_uz, X_wz` each holding exactly two neighbours have singleton
      pairwise intersections, so their union is critical and forces `d(v, ·) ≥ 3`,
      violating sparsity). This *is* a genuine source-side argument that Jordán
      states compactly (≈8 lines, p.44), and the formalization expanded it a lot —
      the degree-3 contradiction-unification refactor, the whole
      `notes/Phase5.md` *Appendix* post-mortem. But two source checks overturn the
      likely-IN flag, on the Group-B 22i pattern (verify against landed source; is
      the kernel already exposited?). (i) The **source-side kernel is already
      exposited in full**, node-by-node with accurate Jordán citations: critical-
      set (= project *tight subset*) union/intersection closure = Jordán Lemma
      2.1.2 = `thm:isTightOn-union-inter` (`sparsity.tex`, full proof); three-pair
      critical-set union = Jordán Lemma 2.1.3 = `thm:isTightOn-union-with-bonus`
      composed twice (full proof); the per-pair blocker characterization
      ("splitting not suitable ⟺ ∃ critical `X ⊇ {u,w}, ∌ {v,z}`") =
      `lem:isSparse-typeII-reverse-blocker` (`sparsity.tex` §"Per-pair tight-blocker
      witness", full proof); the overshoot observation + maximal-set assembly =
      `thm:isSparse-exists-typeI-or-typeII-reverse` (`rigidity-matroid.tex`), whose
      proof reproduces Jordán 2.1.4(b) with the chapter preamble mapping each node
      to its Jordán lemma number; and the non-adjacent-pair existence =
      `lem:isSparse-exists-nonadj-among-three-neighbors` (full proof). The argument
      is followable end-to-end across these green nodes. (ii) The **un-exposited
      residual is project-side Lean bookkeeping** — the contradiction-template
      organization (`IsSparse.contradiction_{one,two,three}_pair`,
      `False_of_pairwise_blocker_or_edge`), the LoC budget, the "1-deficient
      intermediate" primitive-shape mismatch (`notes/Phase5.md` *Appendix*) — the
      header's Lean-modelling / "mathematical difficulty, not Lean verbosity"
      carve-out excludes it. No mathematical gap or slip in Jordán was surfaced
      (flavor (a) gap/slip does not apply; the formalization's route even *avoids*
      Jordán's explicit maximality machinery via direct tight-subset chaining, a
      project-side reorganization, not an expansion of a compressed step). Source
      verified: Jordán 2016 §2.1 Lemmas 2.1.2/2.1.3/2.1.4 (pp.43–44), §2.2 Theorem
      2.2.1 (p.45). Pointer: `notes/Phase5.md` *Milestone 1* + *Appendix*.
    - **The rest of 1–16 (light screen) — OUT, reuse-heavy / matroid-standard /
      algorithmic, all already exposited.** Phases 1–4 (sparsity API, Laman graphs,
      frameworks/rigidity matrix, trivial motions): definitional API + Asimow–Roth /
      Maxwell-type counting, self-exposited backfill. Phase 6 (Laman `⇒`): Lovász–
      Yemini easy direction (Maxwell counting, cited Jordán 1.3.1) at
      `lem:isSparse-of-rowIndependent-two`. Phase 7 (Lovász–Yemini hard direction +
      `(k,ℓ)`-count matroid): the Henneberg row-LI-lift induction (Jordán 2.2.1
      sufficiency) fully exposited in `rigidity-matroid.tex`; the count matroid is
      an `IndepMatroid.ofFinite` axiom-check. Phase 8 (linear-matroid framing):
      `Matroid.ofFun` plumbing + uniform-genericity perturbation. Phases 9–11
      (pebble game, Lee–Streinu 2008): algorithm / invariants / correctness /
      executable / witness — algorithmic, mathlib-standard; Phase 11 is a
      structural-edit Lean reshape. Phases 12–14 (matroid union, Tutte–Nash-Williams
      tree-packing, Whiteley k-frame): Phase 12 is **vendored** from
      apnelson1/Matroid, 13/14 are matroid-partition specialisations
      (Edmonds/Nash-Williams/Whiteley 1988), matroid-standard (cross-checked to
      Oxley/Schrijver per top-level `CLAUDE.md`). Phases 15–16 (body-bar/body-hinge
      Tay): Phase 16 "adds no new linear algebra" (edge-multiply reduction to
      Phase 15); reuse-heavy. None spells out a source-compressed step that isn't
      already exposited followably in its (green) chapter.
