# CLEANUP-42 round 2 — the chapter to the Lean (work log)

**Status:** in progress (opened 2026-11-05 at the PI's word, `notes/Cleanup42.md` §1). Round 2 of
CLEANUP-42 applies to `blueprint/src/chapter/pencil-d.tex` the remedy the PI gave each of the 34
`open` rows of the proof-route ledger (`notes/Cleanup42.md` §2; the remedies in §3 *Round 1's
stop* and *The B/C judgment*): 11 statements and 14 proof routes restated to their Lean (L), and a
formalization note naming the Lean's route for each of the 17 kept parts (K), with the two prose
slips round 1 moved here; then one `\uses` sweep over the chapter's missing edges (60 at the open).
Blueprint and notes only: no Lean, no pin, no `\leanok`. Eleven tasks, one commit each: the open,
eight slices by layer, the sweep and the close. 17 rows end `aligned` and 17 `kept`. **Next
concrete task:** task 2, 42b with 42g (R-35 L; R-3, R-4, R-5 K). Round manual: `CLEANUP.md`.

## Autopilot: for the PI

CLEANUP-42's row of `.claude/autopilot/queue.toml` is attended, so the coordinator runs this round.
**No planned stop:** every row's remedy is settled (`notes/Cleanup42.md` §1). An unplanned
`NEEDS_PI` entry goes here, newest first, for a remedy that does not apply as approved (an L route
the chapter cannot state without a new node, a note that needs more than its sentences, a
restatement that would claim more or less than its pin) or a statement change outside the eleven;
the PI answers in an entry that starts `**PI, <date>:**`.

- None yet.

## Current state

**Round 2 is open** (task 1, docs only). Nothing is mid-stream; task 2 is next.

**Verified at the open** (2026-11-05, at `6eb7a2e6`):
- **The ledger** (`notes/Cleanup42.md` §2): 54 rows, 34 `open` (R-3 to R-5, R-9 to R-12, R-14 to
  R-21, R-23 to R-35, R-46, R-48 to R-51, R-53), 6 `aligned`, 14 `no departure`; the next row is
  R-55. Their remedies (§3 there): every part L for 17 rows (R-9, R-14, R-19 to R-21, R-24 to R-26,
  R-30, R-32 to R-35, R-48 to R-51); a K part for the other 17 (R-3 to R-5, R-10 to R-12, R-15 to
  R-18, R-23, R-27 to R-29, R-31, R-46, R-53), of which R-15, R-28 and R-29 also restate a
  statement and R-29 its (T2).
- **The chapter:** 6 359 lines, 99 nodes, all green, 236 pins; two formalization notes (after
  `lem:pencil-d-point-configuration` and `lem:pencil-d-steer`). `python3 scripts/blueprint-deps.py
  --chapter pencil-d` (saved as `scratch/cleanup-42/round2/deps-pencil-d-6eb7a2e6.txt`): 99 nodes,
  99 pinned, 236 pins; 60 *missing* edges on 31 nodes, 653 implied, 19 unbacked transitive, 55
  with no Lean basis, 31 dead pins.
- **The graph's baseline** (G5's, below): `python3 scripts/blueprint-deps.py --dump` at the web
  build of this TeX, `scratch/cleanup-42/round2/dump-6eb7a2e6.txt`, opens `1886 edges
  f539dcce186aa853` and the `lean_decls` hash `28b0db9377d77782`; `--summary` has both consistency
  checks OK; `blueprint/print/print.log` has 0 `LaTeX Warning` lines. `verify.sh` was not run (the
  open edits no TeX): task 2 counts its `WARNING:` lines on its parent first.
- **No Lean or blueprint edit since `a3b80ac4`:** `git diff --stat a3b80ac4.. -- CombinatorialRigidity/
  blueprint/ lakefile.toml lake-manifest.json lean-toolchain` prints nothing. The Lean baseline is
  the coordinator's `lake build CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.Generic`,
  green this session; no task rebuilds it.

## Scope and standing rules

- **The hygiene rule, lifted exactly for the PI's remedies** (`CLEANUP.md` *Per-round work log*).
  The statements that change are the 11 family-A L rows', each to its pin and no further: R-15,
  R-25, R-28, R-29 (the ear's), R-30, R-33, R-35 and R-48 to R-51. Every other statement keeps its
  strength; no main result's node changes. A finding that would change another statement goes
  under *Candidates for the PI* (with a new ledger row from R-55 if it is a departure); a stale Lean
  docstring, a slip outside the task's nodes or any Lean work under *Moved to a later round*; each
  line mirrored into `notes/Cleanup42.md` §3 in the same commit. Neither is a stop.
- **Writes.** `blueprint/src/chapter/pencil-d.tex`, the task's nodes only (and
  `thm:pencil-d-generic`'s proof in task 8); `notes/Cleanup42.md` (§2's rows, the **Status** tally,
  §3's mirrored lines); this log; at the open and the close only, ROADMAP's row, §42's *Next* and
  the CLEANUP-42 bullet, `notes/MolecularConjecture.md`'s CLEANUP-42 sentence and the queue's
  comment. No other chapter; no node, `\lean{…}` pin or `\leanok` added, moved or removed; no Lean
  (`CombinatorialRigidity/`, `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`).
- **Evidence.** A claim about the Lean comes from the pinned declaration's statement and body at
  HEAD (`python3 scripts/blueprint-deps.py --label <label>` for what it reaches), never its
  docstring (root `CLAUDE.md` *Docstrings are not evidence*): the row's *Lean:* text guides, and is
  re-read against the pins before it becomes prose. A surprise gets a `lake lean` probe in
  `scratch/cleanup-42/round2/<task>/` (gitignored) before it is written.
- **Decision (the open): an L statement.** Restated to its pin: the hypothesis the pin does not
  take is dropped (or generalized as the row says), nothing beyond the pin is claimed, and the
  proof changes only where it read what was dropped (forced at R-25 and R-35). The changed-statement
  gate (`CombinatorialRigidity/CLAUDE.md` *Forward-mode slices*, read for a blueprint-side change):
  `grep` the label over `blueprint/src/` and `notes/BlueprintExposition.md`, and restate in the same
  commit a sentence that still states the old form (a caller's "as `G` is simple" may stay where it
  is true); `grep -rn '<label>' --include='*.lean' CombinatorialRigidity/` for a docstring stating
  it, which goes under *Moved*, for round 4.
- **Decision (the open): an L proof route.** Rewritten on the Lean's route as the row's *Lean:*
  and the B/C table's reason give it, in the chapter's notation and register
  (`blueprint/AUTHORING.md`), each step citing the node that pins its lemma. Its `\uses` follows the
  new text: an edge added for each node it now cites; one removed only when the new text no longer
  cites it and `--label` calls it *unbacked*, with the reason in the commit message. A closing
  comparison with `d = 3` stays, corrected where the route changed it (R-19's).
- **Decision (the open): a K note**, R-22's shape (`lem:pencil-d-steer`, the `fmlnote` after its
  proof): one `\begin{fmlnote} … \end{fmlnote}` per node, right after its `\end{proof}`, outside
  every other environment, with no `\lean`, `\uses` or `\leanok`. One sentence per kept part, as the
  PI approved it (`notes/Cleanup42.md` §3 *The B/C judgment*), naming the Lean's route in the
  chapter's notation, as R-22's "The formalization nevertheless takes six, …" does: "The
  formalization proves <the step> by <the Lean's route>[, not <the chapter's>]." Mathematical
  English: no Lean name, `\mathtt`, ledger number, round or remedy letter (`blueprint/lint.sh` check
  5); `\cref`s are fine. Two kept rows on one node (`lem:pencil-d-lift-small`: R-27, R-28;
  `lem:pencil-d-good-ear`: R-31, R-53) share one note (`blueprint/AUTHORING.md` D). The proof is not
  edited for a K part. Fifteen notes in all.
- **Decision (the open): the row's status.** Every part L: `**aligned, round 2 task <N>**`, its
  *Chapter:* renamed *Chapter (until then):* (R-1's form), its *Remedies:* ending "the prose to the
  Lean, taken (the PI, 2026-11-05)". A K part: `**kept, round 2 task <N>**`, *Remedies:* ending
  "keep both, taken: a formalization note after the proof names the Lean's route (the PI,
  2026-11-05)". **One status per row:** a row with a statement L and an argument K (R-15, R-28,
  R-29's non-(T2) part) is `kept`, as a row records a departure while any part of it stands; its
  *Remedies:* names each part's remedy (R-29: the ear's statement and (T2) to the Lean, the rest
  kept). R-46, K on its statement, is `kept`. The close replaces each `round 2 task <N>` by its sha.
  `notes/Cleanup42.md` §2's header defines `kept` (the open). Round 2 leaves 23 `aligned`, 17
  `kept`, 14 `no departure`, none `open`.
- **Decision (the open): the `\uses` sweep is task 10.** Tasks 2–9 change `\uses` only as their
  restated text needs. Task 10 takes each *missing* edge that `--chapter pencil-d` reports at its
  parent (60 at the open, fewer as tasks 5, 6 and 8 add theirs): into the statement's `\uses` for a
  *statement* edge, the proof's for a *proof* edge; an edge marked as closing a cycle is left, with
  its reason in task 10's line. *Implied* and *unbacked* edges are out of scope.
- **Decision (the open): the gates**, each in the foreground with an explicit `timeout`, and the
  commit under `if <gates>; then git commit …; fi`:
  - **Every task:** (G1) `python3 notes/check-phase-note.py` green (it gates this log by its title);
    (G2) `git diff --stat a3b80ac4.. -- CombinatorialRigidity/ lakefile.toml lake-manifest.json
    lean-toolchain` empty.
  - **Tasks 2–10, which edit TeX:** (G3) `blueprint/lint.sh` green, all nine checks (check 9's
    docstring-label ratchet holds, as no pin moves). (G4) `blueprint/verify.sh` green: `checkdecls`
    silent, no more `WARNING:` lines than the parent's run (each task records its count under
    *Current state*), and `blueprint/print/print.log` rebuilt (its date) with 0 `LaTeX Warning`
    lines. (G5) The expected-diff gate (PROSE round 5's, `notes/Prose-graph-cleanup.md` *Scope*):
    (a) the parent's `--dump` after `verify.sh` (the previous task's after-dump serves; task 2's is
    the open's); (b) before editing, the expected diff in the task's line: the `\uses` added and
    removed per node, statement or proof; (c) after, `verify.sh`, the dump again and `diff`: exactly
    those, with the drawn edges they imply, and the `lean_decls` hash still `28b0db9377d77782`; a
    task with no `\uses` change has a byte-identical dump; (d) `--summary` exits 0, both consistency
    checks OK.
  - **Tasks 2–9 also:** (G6) for each L statement, the changed-statement gate above and the honesty
    check: the restated statement claims what its pins' statements give, read from the source (the
    file or `lean_hover_info`), each dropped hypothesis absent from every pin proving that clause.
  - **Task 10 also:** (G7) `--chapter pencil-d` at its commit reports no *missing* edge but those
    its line leaves.
  - **Task 11** (no TeX): G1, G2 and the tally its line names.
- **One task, one dispatch.** Opus builders for tasks 2–10, a fresh agent each; the close may be
  Sonnet. A slice that does not fit lands whole rows only (every part of each, on all its nodes)
  and appends the rest as a new task right after it, with a one-line note; no row lands half-done.

## Lemma checklist (the round's task list)

One commit per task, in this order. Each names its rows with their remedies (*L statement*, *L
proof*, *K note*), its nodes with their lines at the open (re-`grep` before editing), the slips it
takes, the pinned files it reads (under `CombinatorialRigidity/Molecular/Molecule/Pencil/` unless
the path says otherwise) and *Expected*, the open's estimate of G5's diff, which the task makes
exact before editing. Each also sets its rows' status in `notes/Cleanup42.md` §2 and the tally in
its **Status**. **On landing, its line is cut to at most three lines:** number, sha, its rows by
new status, its `\uses` changes, and a pointer to any *Candidates* or *Moved* line.

**Count check:** tasks 2–9 take 4, 4, 4, 3, 6, 5, 4 and 4 rows: 34, each `open` row once (R-29's
statement, (T2) and other parts all in task 8).

- [x] **1. Open** (this commit; docs only): this log; `notes/Cleanup42.md`'s **Status**, §2's
  header (`kept`) and §3; ROADMAP's Status row, §42's *Next* and the CLEANUP-42 bullet;
  `notes/MolecularConjecture.md`; the queue's comment.

**42b with 42g** (`sec:pencil-d-realization`, `sec:pencil-d-long`).

- [ ] **2. The agreement at `d = 3`, the polygons and the cycle.** R-35, L statement and L proof:
  `lem:pencil-d-agrees-three` (l. 151) without "nonzero" points, its proof gaining the sentence
  that `q^⊥` is three-dimensional exactly when `q ≠ 0` (`Grade/Realization.lean`). K notes: R-3,
  `lem:pencil-d-polygon-normal` (l. 3471) part (2), the basis map extended, then a transvection;
  R-4, `lem:pencil-d-polygons` (l. 3636), the base triangle by three `2 × 2` minors; R-5,
  `thm:pencil-d-cycle` (l. 3731), one closed `N`-gon at `N = min(m, D)` (`Grade/Polygon.lean`,
  `Grade/Chain.lean`). *Expected:* no `\uses` change.

**42h** (`sec:pencil-d-short`, its first eight nodes).

- [ ] **3. The kernel curve, the ear data, two stars and four interior bodies.** R-9, L proof:
  `lem:pencil-d-kernel-curve` (l. 2550), the rank count at some `t ≠ 0` for Cramer's rule over
  `K(t)` (`Grade/Stars.lean`). K notes: R-10, `lem:pencil-d-ear-data` (l. 2832) part (3), a
  coefficient of `h(λ, s)` in `λ` (`Grade/EarData.lean`); R-11, `lem:pencil-d-two-stars` (l. 2426)
  part (1), a linear section of the quotient and rank–nullity; R-12, `thm:pencil-d-open-ear-four`
  (l. 2955), the factored order (`Grade/Short.lean`). The slip there: an ear datum `y` becomes `s`
  (l. 3041, l. 3053). *Expected:* at most an edge from the kernel curve's proof, which has none.

**42i with 42j** (`sec:pencil-d-short`, its last four nodes; `sec:pencil-d-chains`).

- [ ] **4. Three interior bodies, the planes, glued ends and the chain count.** R-14, L proof:
  `thm:pencil-d-open-ear-three` (l. 3307), its first stage: at `r ≤ 2`, `dim ρ ≤ 2` by glued-ends
  or a common member `t`, no component step or path, the factoring R-12's
  (`Grade/ShortThree.lean`). R-15, L statement and K note: `lem:pencil-d-planes-meet` (l. 3222)
  without `K` infinite; the note: no `λ` map, `R` by rank openness at a fixed inverse
  (`Grade/PlanesMeet.lean`). K notes: R-16, `lem:pencil-d-glued-ends` (l. 3111), a partition of
  `G′` pulled back, `X` split in two (`Grade/GluedEnds.lean`); R-17, `lem:pencil-d-chain-count`
  (l. 2156), classes of interior bodies and the handshake bound (`Grade/Chains.lean`).
  *Expected:* the theorem's proof may drop `lem:relative-screws-path` (*unbacked* at the open).

**42k** (`sec:pencil-d-reduction`).

- [ ] **5. Two pencils, the base case and parallel edges.** R-19, L proof:
  `lem:pencil-d-nonsimple-case` (l. 4497), the rank by the splice at every `D` (at least `D` plus
  that of `G/H`, at most the target), its closing remark's third point widened
  (`Grade/Reduction.lean`). K notes: R-18, `lem:pencil-d-base-case` (l. 4365), a hinge's `D − 1`
  rows below and the target above (`Grade/Arms.lean`); R-46, `lem:pencil-d-two-pencil-extension`
  (l. 4175), parts (1) and (2) for any vectors and subspaces, `b_u ≠ 0` only in (2)'s last claim
  (`Grade/TwoPencil.lean`). *Expected:* the parallel-edge proof gains `lem:rigidityRows-splice-rank-add`
  and `lem:relative-deficiency-rank-bound` (both *missing* at the open).

**42l** (`sec:pencil-d-nondegenerate`, `sec:pencil-d-lift`).

- [ ] **6. Nondegeneracy, its feasibility and the lifts' setting.** R-48, L statement:
  `lem:pencil-d-nondegenerate-maps` (l. 4773), parts (1) and (2) for any vectors and subspaces,
  with the slip there (`p` runs `K^(d+1) → K^(d′+1)`, but the "in particular" embeds from `d′ ≤ d`
  into `d`: one convention) (`Grade/Nondegenerate.lean`). R-20, L proof:
  `lem:pencil-d-nondegenerate-feasible` (l. 4814), `π`'s rows a form nonzero at `b_v` and one
  vanishing on each `Π_w`, chosen off at most two proper subspaces, for the quotient, the induction
  and the quadric, and the TeX comment above it to match (`Grade/Feasible.lean`). R-49, L
  statement: "simple" dropped from `lem:pencil-d-steer` (l. 4965), `-lift-one-witness` (l. 5234)
  and `-lift-transfer` (l. 5321). R-50, L statement: `lem:pencil-d-lift-realization` (l. 5141), (2)
  and (3) for any `(b⁰, Π⁰)` as in `def:pencil-d-lift`, (1) at a nondegenerate realization
  (`Grade/Lift.lean`). R-21, L proof: `-lift-one-witness`, one polynomial section through the
  given lift's parameters, no Cramer basis or `γ`. R-23, K note: `-lift-transfer`, openness by the
  rank polynomial at each `λ` (`Grade/LiftWitness.lean`). *Expected:* `-lift-one-witness`'s proof
  gains `lem:pencil-polynomial-section` (*missing* at the open).

**42m** (`sec:pencil-d-generic`), in three.

- [ ] **7. The small cases, the cut edge and no planar-rigid set.** `lem:pencil-d-lift-small`
  (l. 5424): R-51, L statement, without `K` infinite; R-28, L statement, (2) without `G` simple;
  one K note for R-27 (the triangle's rank `D(|V| − 1)` at most the target, the deficiency
  nonnegative, no partition values) and R-28 (the sides' lifts glued body by body, never a product)
  (`Grade/LiftSmall.lean`). R-30, L statement and L proof: `lem:pencil-d-lift-cut-edge` (l. 5488)
  without `|V₁|, |V₂| ≥ 2`; one frame map, one minor `E₁`, `E₁ ≠ 0` and `r₂` from one realization
  of `G`, no `𝒢`, case analysis on `|S|` or replaced normal (`Grade/LiftCutEdge.lean`). R-32, L
  proof: `lem:pencil-d-lift-no-rigid` (l. 5747), `q` off the main-picture polynomial, no `ℓ₀`;
  `dim L̃` through the lifting system's kernel plus the free coordinates; no map `g`
  (`Grade/LiftNoRigid.lean`). *Expected:* `-lift-no-rigid`'s proof may drop `thm:pencil-jj-equality`
  (*unbacked* at the open).
- [ ] **8. The pendant, the pendant triangle and the ear.** R-24, L proof, (T1) of
  `lem:pencil-d-lift-pendant` (l. 5621), `-lift-pendant-triangle` (l. 5688) and `-lift-ear`
  (l. 5936): one minor per closed hub-neighbourhood of `G`. R-25, L statement and L proof: the
  pendant without "`u` has another neighbour", (T1) split on `u` a hub of `G`. R-26, L proof, (T2)
  of the pendant and the ear: one form on `K⁴` per body (part (2) of `-lift-realization`). R-29: L
  statement, the ear's `a ≁ b` as its pin's `a ≠ b`; L proof, the triangle's (T2) by one form at
  `x₁`, `x₂`, `c`; K note, its rank and deficiency as R-27. `thm:pencil-d-generic`'s proof: its two
  derived clauses (l. 6293–6294, `u`'s other neighbour; l. 6307, "non-adjacent") cut to what the
  restated statements ask, and R-54's text on them updated in place, its status unchanged
  (`Grade/LiftCases.lean`, `Grade/Lift.lean`, `Grade/Generic.lean`). *Expected:* the three proofs
  may gain `lem:pencil-d-lift-realization`; the rest by the rule.
- [ ] **9. The good ear and the ear's condition.** One K note on `lem:pencil-d-good-ear` (l. 5844)
  for R-31 (the core split; `def₂(G[X]) = 1` by a partition case split; connectivity not through
  `s(X)`) and R-53 (`|X| ≥ 3` from the core) (`Grade/GoodEar.lean`, `MainComponent/GoodEar.lean`).
  R-33, L statement and L proof: `lem:pencil-d-ear-extend` (l. 6035) without `G` simple or the
  neighbour selector; one witness per condition, no moment curve; the `n_u` chosen greedily, no
  case analysis on `O_v`. R-34, L proof: `lem:pencil-d-ear-free` (l. 6127), the trivial lifts and
  task 7's free coordinates fill `L̃` by (c); rank at most three only in `U(G)`; (b) and the
  openness may stay (`Grade/EarFree.lean`). *Expected:* by the rule; none estimated.

**The sweep and the close.**

- [ ] **10. The `\uses` sweep.** Every *missing* edge of `--chapter pencil-d` at its parent (60 at
  the open on 31 nodes, round 1 task 2's `lem:pencil-d-point-configuration` →
  `def:pencil-nondegenerate` among them), as the standing rule says; G7. *Expected:* the parent's
  report, listed before editing.
- [ ] **11. The close** (docs only). §2's `round 2 task <N>` replaced by shas; the tally re-counted
  (54 rows: 23 `aligned`, 17 `kept`, 14 `no departure`, none `open`) and 17 formalization notes in
  the chapter; `--chapter pencil-d` (99 nodes, 236 pins, task 10's leftover *missing*); the
  `lean_decls` hash; the restated statements listed for the PI in *Hand-off*; the round closed in
  this log, `notes/Cleanup42.md`'s **Status** and §3 (next: round 4's open), ROADMAP,
  `notes/MolecularConjecture.md` and the queue's comment (the row stays `done = false`).

## Candidates for the PI

- None yet.

## Moved to a later round

- None yet. (Round 1's stale `Grade/LiftNoRigid.lean` docstring is round 4's, `notes/Cleanup42.md`
  §3; this round edits no Lean.)

## Blockers / open questions

- None.

## Hand-off / next phase

**Next concrete task:** task 2, 42b with 42g: R-35's statement and sentence (L) and the K notes of
R-3, R-4 and R-5, one Opus dispatch. Its G5 parent dump is the open's
(`scratch/cleanup-42/round2/dump-6eb7a2e6.txt`), and it first runs `blueprint/verify.sh` on its
parent to count the `WARNING:` lines G4 holds.

## Decisions made during this round

- **The log** (the open): `notes/Phase42-align.md`, a log per round as CLEANUP-40's
  (`Phase40-cleanup.md`, `-factor`, `-exposition`, `-simplify`, `-docs`).
- **The slicing** (the open): the PI's proposal as written (`notes/Cleanup42.md` §1), 11 tasks.
  42m's three slices go by node group, about two proof rewrites each: the small cases, the cut edge
  and no planar-rigid set; the template cases, whose (T1) and (T2) rows span three nodes and land
  together; the good ear and the ear's condition. 42l stays whole: six rows, but two rewrites and
  four one-clause statements.
- **The standing rules' decisions** (the open): the statuses, the K note's shape, the sweep and
  the gates, each under *Scope and standing rules*.
