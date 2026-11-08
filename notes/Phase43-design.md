# Phase 43 — PENCIL-NATURAL: design (cross-phase plan)

**Status:** in progress (opened 2026-11-07 with the PI), sub-lettered: a simpler pencil proof,
with no main result's statement to change. **43a** READS is open (`notes/Phase43a.md`): the three
fresh reads and the probes banked. The later layers (§2) open one at a time, each at the PI's word
(§1, D5). Next: 43a's reads, dispatched in parallel.

This file is the phase's entry point: the target (§0), the PI's decisions (§1, verbatim), the
layers by stable code (§2) and the open questions (§3). The recon record stays in
`notes/PencilNatural.md`, cited by section: the proof as it stands (§2), the verdicts N1–N6 with
their sizes (§3), the recon's brief (§4) and the intuitions I1–I4 (§5).

## 0. Target

Make the proof of the pencil realization theorem simpler and its cases more natural, in every
dimension, and then explain it in the blueprint: a road map in the manner of KT §1.1. The main
results (`pencil_realization_theorem`, `pencilPair_of_nonempty`,
`Graph.graded_pencil_conditioned_pair`) keep their statements. What changes is the route:
- the `d = 3` generic conjunct comes from the every-dimension lift (N1c), so every dimension has one
  shape: A the reduction, B the main-component induction, C the lift;
- the reduction is restated on five structural cases (N2);
- the `d = 3` coverage loses two short-chain rows (N3, Theorem S′).
What the recon ruled out (N3's other rows, N4, N5, N6) is `notes/PencilNatural.md` §3.

## 1. The PI's decisions (verbatim)

**PI, 2026-11-07, on N2's call (a), whether the reduction may stop mirroring KT Theorem 4.9:** "I
think we should be free to diverge from KT Theorem 4.9, but if it plays a similar role in the proof
as KT Theorem 4.9 does in the KT proof, then it's worth a reference (perhaps just in a remark or in
surrounding glue text)."

**PI, 2026-11-07, on N2's call (b), `lem:pencil-min-degree-rigid`, after asking why it would
retire:** "Let's keep it off the route for now; perhaps we could move it into a separate appendix."
The blueprint's `\appendix` holds only `retrospective.tex` today.

**PI, 2026-11-07 (a second session), D1–D5**, deferred from the first, after a synthesis of the
verdicts. Each was chosen from the options offered; the chosen label is quoted, then what it was
offered as:
- **D1:** "N1c (Recommended)": the reduction proved once, for every `d` (about −4.6k Lean lines,
  17 files, 15 nodes); `pencil.tex` stops proving `d = 3` on its own terms.
- **D1, the old route:** "Collapse to a remark (Recommended)": the explicit `d = 3` generic
  constructions leave, Lean and nodes, for one short remark naming the route and why C replaces it.
- **D2:** "Yes, before N3's build (Recommended)": the fresh read of Theorem S′.
- **D3:** "Both now": the premise check and the flatness reading, in parallel, before any N1 work.
- **D4:** "Bank them, geng allowed (Recommended)": the probes committed with README rows, nauty's
  `geng` the second exception to stdlib-only Python.
- **D5:** "Open as Phase 43 (Recommended)": in this session, sub-lettered, each sub-phase opened
  at the PI's word.

## 2. The layers, by stable code

In order. A letter is minted when a layer opens.

- **READS** (43a, open). Three read-only fresh reads, in parallel: Theorem S′ (N3, D2); the premise
  check, that `sec:pencil-d-generic` uses no `d = 3` generic node as a premise (N1, D3); and N6's
  flatness reading, every planar-rigid set flat on the main component (D3). With them, the probes
  of `notes/PencilNatural.md` §4 banked (D4). Gates LIFT3 (the premise check: no cycle, 43a) and
  SPRIME (S′).
- **LIFT3** (N1c). `HasGenericPencilRealization K 3 G` by `liftAttains_of_simple 0`, then the
  reduction proved once for every `d`, and `pencilPair_of_nonempty` as the `m = 1` case of
  `Graph.graded_pencil_conditioned_pair`. The explicit `d = 3` route collapses to a remark (D1).
  N1a, its first slice, may land alone. The blueprint fixes are `notes/PencilNatural.md` §3: the
  two `\uses` edges that would close a cycle, the `sec:pencil-d-lift` intro, about 17 "At `d = 3`
  this is …" remarks.
- **NORMAL** (N2). `thm:pencil-reduction` on five structural cases: a loop; at most two bodies; not
  2-edge-connected; non-simple; simple and 2-edge-connected. Cases (iv) and (v) merge;
  `lem:pencil-min-degree-rigid` leaves the route for an appendix (§1 (b)); KT Theorem 4.9 cited in a
  remark (§1 (a)). After LIFT3, which leaves one caller.
- **SPRIME** (N3). Theorem S′: `thm:pencil-d-chain-or-core` at `ℓ = 1`, with open-ear-one and
  two-orbit standing in for the embedding. Open-ear-two and the split-off leave the `d = 3`
  coverage (`SplitOff.lean` whole). It revises the 42f record (`notes/Phase42-design.md` §1: "in
  `P³` both are load-bearing"). Only if S′'s fresh read holds.
- **EXPO**. The road map (`notes/PencilNatural.md` §5), with the A/B/C structure as it stands after
  the layers above, I1–I4 as corrected, and the flatness reading if its read holds. Last.

## 3. Open questions

- Whether LIFT3 lands as one sub-phase or two (N1a first): the PI's, at its open. The premise
  check unblocks both; its constraints on LIFT3 are at its item in `notes/Phase43a.md`.
- SPRIME's sizing (`notes/PencilNatural.md` §3: TeX net about −500, Lean about −1,000 and +150–200)
  is the recon's estimate; S′'s read may change it.
