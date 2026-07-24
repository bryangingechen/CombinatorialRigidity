# ORIGAMI — planar-blocks block-and-hole rigidity (planning note)

**Status:** queued (user-queued 2026-07-23); unopened — number minted
on open. Same editing discipline as phase notes (≤8-line entries,
lift cross-cutting lessons).

## The question

The "molecular origami" conjecture gestured at in Chen–Cruickshank–
Kitson, *Block-and-hole graphs: constructibility and (3,0)-sparsity*
(arXiv:2309.06804, §4.3): a polyhedral surface with flat rigid faces
(rigid origami) is modelled by a block-and-hole graph realized with
each block's boundary **coplanar**; the conjecture is that rigidity
at coplanarity-generic placements equals generic rigidity, so the
known combinatorial characterizations govern generic rigid origami.

Precise shape, as a KT-template subvariety statement: let `X` be the
variety of placements with each B-face boundary coplanar, with each
block rigidified by a gadget that stays infinitesimally rigid at flat
boundaries (the triangulated-prism/discus construction of CCK §4.3 —
a *generic* isostatic gadget can go flexible when its boundary
flattens). Claim: generic-in-`X` rank = ambient generic rank. The
claim is generic-in-stratum only — deeper strata genuinely differ
(fully flat states and symmetric Miura-type configurations have extra
mechanisms), so KT-style relative-genericity bookkeeping is
essential, not a luxury.

Scope limit: only attackable where the *ambient* generic
characterization exists — one block or one hole
(Cruickshank–Kitson–Power, JCTB **122** (2017), 550–577; CCK
Thm 2.15; single-block rank formula: Jordán, Discrete Math.
**346**(3) (2023), 113268). Happily, pure single-sheet origami is
the one-hole case (CCK §4.3).

## Candidate routes (2026-07-23 discussion)

1. **Vertex splitting inside `X`** (primary). CCK Thm 2.15
   (constructibility from `K₃` by vertex splitting, via the
   discus-and-hole reformulation) supplies the combinatorial
   induction — the analog of KT Thm 4.9. The missing engine, the
   Thm 5.5 analog: *vertex splitting preserves infinitesimal rigidity
   at `X`-generic realizations, with the split performable inside
   `X`*. Whiteley's coincident-point proof of vertex splitting
   (Structural Topology **16** (1990), 23–30) is subvariety-friendly
   in spirit; the modern tool is Cruickshank–Jackson–Tanigawa's
   coincident-realisations machinery (DCG **69** (2023), 192–208).
   Delicate case: splitting a vertex lying on one or more block
   planes (perturbation confined to their intersection; note the
   block's own boundary edges lie in its plane, which is the
   direction Whiteley's argument wants).
2. **FRW swapping at fixed placement.** Finbow–Ross–Whiteley,
   *The rigidity of spherical frameworks: swapping blocks and holes*
   (SIAM J. Discrete Math. **26** (2012), no. 1, 280–304) relates
   stresses of `(P, p)` to first-order motions of the swapped
   structure at the *same* `p`. Applied on `X`, flat *blocks* become
   flat *holes* — a fabric-only non-genericity with no gadget
   interaction, plausibly easier to verify directly. Check which
   auxiliary genericity their projective-statics argument consumes at
   non-generic `p`. Their machinery is projective statics — the
   Phase 17 extensor infrastructure is the natural carrier.
3. **Mine the polytope literature.** Himmelmann–Schulze–Winter,
   *Rigidity of polytopes with edge length and coplanarity
   constraints* (arXiv:2505.00874) prove `d = 3` convex polytopes
   generically rigid with face-coplanarity constraints — a different
   regime (faces flex in-plane; no rigid blocks) but the same
   "flat faces don't create generic flexes" phenomenon, and their
   genericity notion for the coplanarity variety is reusable.

## Prerequisite background (why this is a program, not one phase)

Beyond in-tree material, a formalization needs, roughly in dependency
order:

- **3D bar-joint vertex splitting** (Whiteley 1990) — the one
  algebraic engine; also unlocks triangulated-sphere rigidity and
  CCK's ℓ³ₚ Conjecture 4.2 direction independently of ORIGAMI.
- **Block-and-hole / discus-and-hole combinatorics** (CKP 2017, CCK
  2023): face graphs, the constructibility theorem (Henneberg-style
  discrete math, comparable to Phase 3), and the (3,0)-tight
  looped-face-graph characterization — the latter is
  pebble-game-adjacent to Phases 9–11 and is a self-contained
  formalization target of independent value.
- **The `X`-generic vertex-splitting lemma** (route 1) — the new
  mathematics.

In-tree assets: Phase 24's dimension-general generic bar-joint
rigidity matroid (read at `d = 3`), Phase 17 extensors (route 2),
Phase 25's general-position/genericity infrastructure.

Suggested opening move when the phase opens: a recon that pins the
formal statement of `X` and the gadget convention, then a
prerequisite-ladder plan (the combinatorial layer first — it is
useful even if the subvariety conjecture stalls).
