# Attack nondeg — state

Sessions so far: 1 · last session: 2026-10-30 · baseline HEAD: 97a631ba

## Statement <!-- budget 10 -->
The brief's §3 (cleared 2026-10-30): for each `d ≥ 3` a predicate `Nondeg_d(G, F, b, Π)` on
`HasPencilPlaneRealization` data meeting (a) agreement at `d = 3` through the polarity with
`IsNondegPencilRealization` (template: `hasGradedDistinctPencilRealization_two_iff`), (b) N1 on `b`
(`HasGradedDistinctPencilRealization`'s link independence), (c) openness; per candidate the verdict on
`G.Simple → Feasible_d(G) → Generic_d(G)`, the `Pᵈ` form of `PencilPair`'s first conjunct, `d = 3, 4, 5`.
Consumer diff (S1): the brief's §1 matches the Lean at `97a631ba`. Unused: `X0Gen`'s `htec`, `hV`, `hIH`
bear on the route (O6), not the definition; `n` is read at `k + 1`; `[Infinite K]` enters only through
general choices (S9, S13, S14), and every figure is exact over `ℚ`.

## Current route and proof sketch <!-- budget 30 -->
Leader **C2-same**: N1, N3 on `b`, and `dim ⋂_{w∈S} Π_w ≤ 4 − |S|` for `S ⊆ H[v]`, `|S| ≥ 2` (workbook
preamble). Settled this session, each by an S-number:
- Q0 (S2): only the conjunct's own induction and the headline statements consume it.
- Q1 (S7): C2-same and C2-vac meet (a), (b), (c) and survive the embedding; C1 fails (a) at `K₄` (S4);
  C2-gp and the direct transcription retired (`log.md`). §4's readings confirmed, refined (S3–S6).
- Q2: under C2-same `Feasible_d = PencilNondegFeasible` in every `d` (S9, by projection); C2-vac's is
  "loopless" from `d = 4` (S12). D's witness is feasible (S11).
- Q3: C2-same's conjunct holds at every feasible graph of the brief's population and `GRAPHS4` at
  `d = 3, 4, 5` (S11, S16: 27 graphs, exact certificates, no miss); C1/C2-vac's at all 12 drawn (S10);
  Tier 0 transfers from `P³` (S8).
- Q4: C2-same's conjunct follows from the coverage at graphs without a planar-rigid set (S14), and in
  general from attaining over the picture of a nondegenerate `P³` realization (R-L, S13).
Open obligations (O1–O5 closed this session: S2, S7, S9–S12, S16):
- O6a (Q4, the new mathematics): R-L's hypothesis at a feasible graph with a planar-rigid set: at a
  general nondegenerate `(q₀, z¹)`, `{q₀} × L(q₀)^{d−2}` attains in dimension `d`. Consumer: case (ii)
  of `hasGenericPencilRealization_of_IH` (the `hrig` branch), which route B handles at `d = 3`.
- O6b (Q4): the reduction's arms in `Pᵈ` under C2-same (few bodies, no-crossing cut, cut edge, pendant body) for the
  generic conjunct. Consumer: `PencilPair`'s first conjunct at the non-main-component graphs
  (`Pencil/Pair.lean`, `Pencil/Pair2.lean`). Two arms lift (S15 (α), (β)); the cut edge and the pendant
  arm need an irreducible carrier, the crux O6a shares.

## Where it breaks <!-- budget 10 -->
No irreducible carrier of the C2-same realizations in `Pᵈ`. Route B's `P³` steps combine two open
conditions on one irreducible family (the steer, `lem:pencil-generic-steer` (b)); the steer's free hub
planes reach no point at `d ≥ 5` (S6). This blocks O6a (a feasible graph with a planar-rigid set: its
nondegenerate realizations lie over special pictures, `dim L(q₀)` one above the general value, S10–S11,
so the coverage at general pictures misses them) and O6b's pendant and cut-edge arms (S15). The
candidate carrier is S13's: a general point of the `P³` steer family, lifted over its picture `q₀`; it
needs the motive strengthened to R-L(G), "that family attains in dimension `d`", and R-L proved by an
induction mirroring route B. Measured to hold at all 84 cells drawn (S11, S16).

## Tried on this route, and what each rules out <!-- budget 10 -->
- C2-gp, the direct transcription, C1 as the definition: retired (`log.md`, S7, S4).
- R-C (the general configuration is nondegenerate) at graphs with two hubs sharing three neighbours:
  fails in every `d` (S5), as at `d = 3`; R-L (S13) is the candidate there.

## Next steps <!-- budget 5 -->
1. The PI's choice of definition (the report's question). 2. If C2-same: state R-L(G) as the motive and
try the one-ear step over `q₀` in `Pᵈ` (`b_x ∈ Π_a ∩ Π_b` is built into `L(q₀)`), then the pendant arm.
3. A second reader for S9's `|S| = 3` step, S13, S14 (review 1 is due after session 3).

## Worries <!-- budget 5 -->
- S9's `|S| = 3` step (transversals sweep dimension ≤ 2) and S13–S14 have one reader (this session).
- Intermediate `f_d` (between `4 − |S|` and 3 at some `S`) were not examined; S4 shows they can make a
  conjunct false (`K₄`).
- The brief counts four `[READING]` items in §4; there are five (S2 settles the fifth).

## Signals <!-- budget 2 -->
- Sessions since "Where it breaks" last changed: 0
- Open obligations: 2 (O6a, O6b; from 6 at the session's start)
