# PENCIL-NATURAL — a simpler or more natural pencil proof (planning note and recon record)

**Status:** opened as **Phase 43** on 2026-11-07, with the PI, after the recon of §4 (verdicts §3).
The plan, the PI's decisions (D1–D5 included) and the layers are `notes/Phase43-design.md`; the
active work log is `notes/Phase43b.md` (LIFT3; 43a, closed: `notes/Phase43a.md`). This note stays
the recon record, cited by section: §2–§5 are kept as they were at the open, net of the probes'
tags once D4 banks them.

## 1. The PI's words (verbatim)

From an attended session on 2026-11-07. The PI had asked how the inductions of the pencil
realization theorem in every dimension relate to KT's *Road Map of the Proof* (KT §1.1), and was
given the structure of §2. The PI then asked: "This is rather intricate -- is there some hope of
simplifying this or making the cases more intuitive?" Given §3's candidates and intuitions:

> "Let's make a note of this somewhere and schedule a recon related to further exploring this. I
> think we will want to add some of this intuition to the blueprint but we should first see if we
> can simplify the proof or make it more natural somehow first."

Asked where to queue it and whether to start the recon at once, the PI chose "Ahead of ORIGAMI" and
"Queue only".

## 2. The proof as it stands

KT run one induction, over minimal k-dof-graphs: a combinatorial theorem (KT §4, Cases I–III) and
a geometric implementation of each case (KT §6). The pencil proof has two or three inductions,
depending on the dimension, and none of them is on `d`:

- **A, the reduction** (`thm:pencil-reduction`; in dimension `d`, `sec:pencil-d-reduction`):
  KT Theorem 4.9's template on `(|V|, |E|)`, over every multigraph, without minimality. The loop,
  base and cut-edge cases are direct. At a 2-edge-connected multigraph a non-simple one contracts a
  parallel pair (KT Lemma 6.2), and a simple one is handed to B whole, without A's hypothesis.
  This gives the bare and adjacent-distinct conjuncts.
- **B, the main-component induction** (`sec:main-component`; `sec:pencil-d-induction` to
  `sec:pencil-d-coverage`): on `|V|`, over simple connected graphs of minimum degree two. Its
  claim is that the general configuration (a planar picture `q`, `d − 2` heights in `L(q)`)
  attains `D(n−1) − def_d`. The coverage is the case table: 13 rows at `d = 3`, and for `d ≥ 4`
  the first five rows, then the `P³` embedding, then a long chain or a core. KT's Case I survives
  as contraction at an additive core. Cases II and III become ear steps and one split-off row.
  KT Theorem 5.6 at `d = 2` enters at the base, through Jackson–Jordán's equality.
- **C, the generic conjunct.** At `d = 3` this is not a separate induction:
  `thm:pencil-generic-step` runs inside A, on A's hypothesis at smaller multigraphs. For `d ≥ 4` it
  is a separate induction on `|V|` over lifts of nondegenerate `P³` realizations
  (`thm:pencil-d-generic`).

The obstructions recorded as forcing this shape, each with its example in the chapters:
minimality fails (`K₄ ⊃ C₄`, `sec:pencil-reduction`); parallel edges cannot live on the main
component, so A and B are separate statements; at two hubs with three common neighbours the
general point of the main component is degenerate (`K_{2,3}`,
`lem:pencil-x0-two-hubs-obstruction`), so C is separate from B; an induction on `d` fails because
contraction moves every height along its curve (`notes/Phase42-design.md` §2.2).


## 3. Candidates and the recon's verdicts (2026-11-07)

These are the recon's verdicts, read-only (§4). The probes behind the figures were banked in Phase
43a (D4): N1's spike `notes/pencil-natural/N1Spike.lean` with its inventory scripts beside it, and
the T2 probe `notes/scripts/natural/shortrows.py` (invocations: `notes/scripts/README.md` §3).

- **N1. The `d = 3` generic conjunct by C: GO.** `liftAttains_of_simple 0`, then
  `LiftAttains.hasGradedGenericPencilRealization`, then `hasGradedGenericPencilRealization_two_iff`
  gives `HasGenericPencilRealization K 3 G` at every simple, nonempty, feasible `G`, with no cast.
  The Lean spike `lake lean`s with 0 errors and 0 `sorry`, on the standard axioms. A kernel walk of
  its closure finds no `d = 3` main-component statement, nor its generic machinery: no `x0Gen`,
  `pencilPair_of_*`, `hasGenericPencilRealization_of_IH` or reduction. A control on the landed
  `x0Gen` finds them all (`N1Spike.lean`). Three restructures, each keeping every
  main statement byte-identical, are listed after this list.
- **N2. A as a normal form: GO for the restatement; the strict normal form waits on N1.**
  `thm:pencil-reduction`'s cases (iv) and (v) are dead: all three callers pass one function to both
  (`Statements.lean`, `X0.lean`, `Grade/Reduction.lean`; checked). Restate it on five structural
  cases: loop; at most two bodies; not 2EC; non-simple; simple 2EC. Lean about −170 lines across 6
  files; blueprint about −40 lines. `lem:pencil-min-degree-rigid` leaves the route (design doc §1
  (b)). The base stays "loopless, ≤ 2 bodies", because the parallel-pair expansion fails on two
  bodies.
- **N3. The short-chain rows at `d = 3`: two of four go (GO, it changes mathematics, so a fresh
  read first).** Open-ear-two and the split-off are never needed. A restructured Theorem S′, with
  long ears, two-orbit, open-ear-one and the core, is `thm:pencil-d-chain-or-core` at `ℓ = 1`, with
  those two steps standing in for the embedding. It is built from landed lemmas plus a ~40-line
  extraction from `SparseDeficiency.lean`. It revises the 42f record (`notes/Phase42-design.md`
  §1: "in `P³` both are load-bearing"; both are used, neither is needed). Sizing: TeX net about
  −500; Lean about −1,000 (`SplitOff.lean` whole, 748) and +150–200.
- **N3, the rest: NO-GO without new mathematics.** These graphs each admit one step only:
  - W8 (`K₄` with its 4-cycle `0-2-1-3` subdivided once; open-ear-one only);
  - DK4 (`K₄` with every edge subdivided twice; two-orbit only, with no proper rigid set at all);
  - `K₄` with one edge kept and five subdivided twice (two-orbit only).

  The count's bound at `D = 6`, `ℓ = 2` is attained at DK4. Probe: the census over
  `geng -C -t -d2`, `n ≤ 13`, `m ≤ (3n−4)/2`, is exhaustive for the class rows 1–5 leave (42,501
  members). Two hub sweeps (not exhaustive) cover 4,781 and 5,964 more. 0 graphs are stepless
  once the two rows are dropped. Under the census's cap no graph has two-orbit as its only step;
  the first found is the 14-body `K₄` family (the hub sweeps).
- **N4. The gap `def₂ − def₃` as the measure: NO-GO; an exposition line only.** It is not monotone:
  open-ear-one raises it by 1, and three rows keep it. Its per-row table rests on an identity whose
  `≤` half is not landed (derived by hand, about 30 TeX lines). Every step of the `d ≥ 4` table is
  gap-non-increasing (derived, not measured). After N3, open-ear-one is `d = 3`'s only raising row.
- **N5. One gluing lemma: NO-GO.** The count is already shared. The alignments differ:
  - A moves one side by a linear map, with no nondegeneracy;
  - B has no group action: a common main picture and two open conditions;
  - C's sides overlap on the cut edge, since the hub conditions read across the cut.

  N1b or N1c retires A's `d = 3` glue (`Arms.lean`), which leaves two gluings.
- **N6. B and C on one statement: NO-GO.** C's locus is empty at infeasible graphs such as `K₄`,
  where B still owes the distinct conjunct. B is degenerate at `K_{2,3}`, and more widely: by hand,
  every planar-rigid set is flat on the main component (one panel). This "flatness reading" is an
  exposition candidate that needs a fresh read. No proof needs it as a Lean node (~100–200 lines).

The three restructures of N1 (sizes from `N1Spike.lean`'s kernel liveness walk, its R1, R1' and R2;
nodes by `notes/pencil-natural/n1_pins_r1_r2.py` and `n1_pins.py`):

- **N1a**, the minimal one. `x0Gen` comes from C, so A no longer hosts `thm:pencil-generic-step`.
  Lean about −1.9k lines (`GenericEar.lean`, `GenericTriangle.lean` whole); 6 blueprint nodes.
- **N1b.** No case of A reads its hypothesis's generic conjunct, so the `d = 3` generic glue goes
  (`Pair`, `Pair2`, `Arms`, part (b) of `lem:pencil-generic-steer`). Lean about −4.1k; 11 nodes.
- **N1c.** `pencilPair_of_nonempty` is the `m = 1` case of `Graph.graded_pencil_conditioned_pair`.
  The graded A already proves bare ∧ distinct at `d = 3` without `Pair`, `Pair2` or `X0`. Lean
  about −4.6k across 17 files; 15 nodes, including `pencil.tex`'s five A cases.

All three need the same blueprint fixes:
- remove or reverse the `\uses` edges `pencil-d.tex:6673` and `:6755`, which would close a cycle;
- the `sec:pencil-d-lift` intro's "proved inside the induction of the reduction" becomes false;
- about 17 "At `d = 3` this is …" remarks change.

A fresh read must confirm that `sec:pencil-d-generic` uses no `d = 3` generic node as a premise.

**The four obstructions of §2.** All are forced by the route; none by a main statement.
- Minimality (`K₄ ⊃ C₄`; the minimal spanning subgraphs are its three `C₄`s) forces A over every
  multigraph, but not cases (iv) and (v).
- The parallel edges and `K_{2,3}` force B's locus. C is the escape for `K_{2,3}`.
- Induction on `d` is forced only against the add-one-height step. As an outer induction it is a
  route choice that removes no step (Tier 2, `notes/Phase42-design.md` §2.2).

## 4. The recon (done 2026-11-07)

The brief (rung `recon-opus`, read-only, every count with its population and cap) ran in three
parallel tracks:
- T1: N1, with the session's one Lean build slot;
- T2: N3, N4, I1, I2 and I4;
- T3: N2, N5, N6, the obstructions and I3.

The returns are recorded in §3 and §5. The T1 spike and the T2 probe were banked in Phase 43a
(§3's first paragraph); the T2 probe needs nauty's `geng`.

## 5. After the recon: the exposition

It comes last: a road map in the manner of KT §1.1, with the A/B/C structure as it stands after the
simplifications. Where the reduction plays KT Theorem 4.9's role, cite it in a remark or glue text
(design doc §1 (a)). The counting heir of KT Lemmas 4.5–4.6 is B's chain count
(`lem:pencil-d-chain-count`).
The intuitions, as the recon corrected them:

- **I1, the gap** (N4): confirmed. The heights recover `def₂ − def_d`
  (`thm:pencil-flat-rank`, `thm:pencil-jj-equality`). Say that the gap shrinks or splits along most
  steps, not all: open-ear-one raises it.
- **I2, degree-two bodies**: half confirmed. "Three points lie in a plane" holds
  (`lem:pencil-three-points`). But the condition sits on hubs' closed neighbourhoods, so a hub's
  degree-two neighbour is constrained, and degree-two bodies carry an independence condition. The
  chain is the unit removed only at `k ≥ 5`, open-ear-one and (pre-N3) open-ear-two. At `k = 2`
  (orbit), 3 and 4, one interior body is suppressed for comparison.
- **I3, a planar-rigid set is one body**: needs correction. `dim L = 3` holds at a main picture
  only. Contraction is also at `D`-rigid additive cores that need not be planar-rigid. C's
  `lem:pencil-d-ear-free` uses `def₂(W₀ − x) = 1` (`IsPencilGoodEar.deficiency_eq`; checked): one
  height more, so that set spans `P³` and lifts as one body of `P³`.
- **I4, slack at larger `D`**: needs correction. Counting forces a core only at a chain with
  `k ≥ 2`. At all `k = 1`, the core comes from `def₃ > 0` (tight parts), and W8 has none. The `P³`
  rows drop out of the dimension-`d` table only, since they still run at `d = 3` through the
  embedding. Not extending them was a design choice (Phase42-design §2.2, §2.5).

## 6. The PI's decisions

Moved verbatim to `notes/Phase43-design.md` §1 at the open (2026-11-07), with D1–D5's answers and
the order of the layers (§2 there).
