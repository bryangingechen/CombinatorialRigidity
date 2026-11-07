# PENCIL-NATURAL — a simpler or more natural pencil proof (planning note)

**Status:** queued by the PI on 2026-11-07, ahead of ORIGAMI; unopened, attended (it opens with the
PI). **Next concrete task:** the recon of §4, read-only, then the PI's decisions on its verdicts.
The blueprint exposition the PI wants (§5) waits for those decisions. Same editing discipline as
phase notes (≤ 8-line entries, lift cross-cutting lessons).

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

## 3. Candidates (2026-11-07, unverified unless marked)

- **N1. The `d = 3` generic step through C.** `liftAttains_of_simple` (`Pencil/Grade/Generic.lean`)
  takes `r : ℕ`, with `d = r + 3`. Outside docstrings, nothing in `Pencil/Grade/` names
  `pencilPair_of_nonempty` or `hasGenericPencilRealization_of_IH` (grep, this session). If
  `liftAttains_of_simple 0` with `lem:pencil-d-nondegenerate-three` gives the `d = 3` generic
  conjunct, then A need not host it, and every `d ≥ 3` has the shape A, B, C with no interleaving.
  C uses `lem:pencil-generic-steer` (the `P³` parametrization), so the steer stays. Not built.
- **N2. A as a normal-form lemma.** Every multigraph is built from `K₁` and simple 2-edge-connected
  graphs by adding a loop, joining along a cut edge and expanding a body into a parallel pair. Each
  operation keeps a realization at the deficiency rank. Is this cleaner than a five-case induction?
- **N3. The `d = 3` rows at short chains.** The four rows at chains with one or two interior bodies
  (`thm:pencil-x0-open-ear-one`, `-open-ear-two`, `-open-ear-two-orbit`, `-splitoff`) are the ones
  that the count of `lem:pencil-d-chain-count` removes for `d ≥ 4`. At `D = 6` that count gives
  only `ℓ = 1`. Its exception, every chain with one interior body and `def₃ = 0`, cannot be handed
  down: no lower dimension shares the target. Can a finer count, or another decomposition, remove
  these rows at `d = 3`? This is the main lever, since `d ≥ 4` leans on `d = 3` through the
  embedding. A numerics probe could list the graphs (under a stated cap) where only these rows
  apply, and test whether another step applies there.
- **N4. The gap as the organizing measure.** The flat rank and Jackson–Jordán's equality give a
  flat configuration rank of `D(n−1) − def₂`. The target is `D(n−1) − def_d`, so the heights
  recover `def₂ − def_d`. Does ordering B's cases by what each step does to this gap give a more
  natural table, or a shorter proof of the coverage (Theorem S)?
- **N5. One gluing lemma.** Cuts are glued three times: A's cut edge by a projective repositioning,
  B's cut vertex and chain of bridges, and C's cut edge and pendant body. Is a shared lemma
  possible, or does each statement force its own?
- **N6. Anything else**, including whether B and C could share one statement on some other
  sublocus that avoids the `K_{2,3}` obstruction.

## 4. The recon (brief)

- **Rung and mode:** `recon-opus`, read-only (`.claude/agents-core/recon.md`): the verdict is the
  return, recorded here by the session that dispatches it.
- **Question:** can the proof of §2 be made simpler, or its case structure more natural, without
  weakening any main result's statement? Settle N1–N6, and re-check each obstruction of §2 for
  whether it forces the shape for this route or only for the current statements.
- **Deliverable:** one verdict per candidate (GO, NO-GO or OPEN), each with its source or witness,
  the Lean and blueprint it touches sized in files and approximate lines, and a recommended order.
  N1 needs a `lake lean` witness that `liftAttains_of_simple 0` gives the `d = 3` generic motive.
  Every count or "no other step applies" names its population and cap (`HARNESS.md` *Evidence*). A
  figure from an uncommitted probe is tagged "measured, script not retained".
- **Out of scope:** Lean or blueprint edits, the exposition of §5, and new mathematics past a
  sizing. A GO that changes mathematics gets a second, fresh read before it is built.
- **Inputs:** `blueprint/src/chapter/pencil.tex`, `main-component.tex`, `pencil-d.tex`;
  `notes/Phase42-design.md` §2 (the step table, the route verdict, the obligations);
  `notes/Cleanup42.md` (the proof-route ledger); `notes/Phase40-simplify-verdicts.md` (the last
  simplification recon, so as not to repeat it).

## 5. After the recon

The PI decides at a stop. Then any simplification the PI takes lands first. The blueprint
exposition comes last: a road map in the manner of KT §1.1, with the A/B/C structure and the
intuitions below as they stand after the simplifications. These are the readings offered on
2026-11-07; the recon checks them before any goes into the blueprint.

- **I1, the gap** (N4): the heights only have to recover `def₂ − def_d`. At a gap of zero there is
  nothing to do (the equal-deficiencies row).
- **I2, bodies of degree two are free** (`sec:pencil-cycle`). Three points always lie in a plane,
  so the pencil condition constrains only hubs. In a chain only `x₁` and `x_k` are tied to the
  hubs' planes. So the chain, not KT's single vertex, is the unit removed: a long chain has free
  heights enough to make its hinges independent, and the short chains are the tight cases.
- **I3, a planar-rigid set is one body.** `def₂ = 0` gives `dim L = 3`: affine heights, one
  3-space. This is why such a set is contracted, and what C's `lem:pencil-d-ear-free` uses.
- **I4, a larger `D` gives slack.** When every chain is short, counting forces a rigid core
  (`thm:pencil-d-chain-or-core`). So for `d ≥ 4` the rows that put a point in `Π_a ∩ Π_b` drop out:
  two planes always share a line only in `P³`.
