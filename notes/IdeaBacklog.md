# IdeaBacklog.md — unqueued phase ideas (survey record)

**Status:** live backlog; surveyed 2026-07-23 in the discussion that
queued PENCIL + ORIGAMI. Entries here are **not queued** — the queue
itself lives in ROADMAP *Queued post-program phases*. Promotion path:
when an entry is queued, it gets a ROADMAP queue bullet + (if it has
planning substance) its own codename planning note, and its entry here
compresses to a pointer. Same editing discipline as phase notes
(≤8-line entries).

Ordering within tiers is a rough preference, not a commitment. As of
2026-07-23 the recommendation on record: none of these jump the
queued PENCIL → ORIGAMI → PIN order; IDENT-PANEL is the strongest
challenger (see its entry).

## Tier A — KT-template subvariety questions (likely new mathematics)

- **IDENT-PANEL** — Tanigawa's Problem 1 (*Generic rigidity matroids
  with Dilworth truncations*, SIAM J. Discrete Math., 2012;
  arXiv:1010.5699, §5): if a bipartite body/hinge incidence graph
  satisfies the identified-body-hinge count (Cor. 5.1 there, Tay 1989),
  is there a rigid **panel**-hinge realization — i.e. KT's theorem with
  the two-bodies-per-hinge restriction dropped? Explicitly open in the
  literature, citing KT as the solved 2-body case; unsolved even at
  `d = 2` (Whiteley's hypergraph-matroid paper, SIAM JDM **4** (1989),
  75–95, has a partial 2-d result per Tanigawa §5). Closest of all
  entries to the formalized surface (Phase 35's coplanar panel model +
  a bipartite carrier), but "open since Tay 1989 even at d = 2"
  signals real hardness — hence behind PENCIL, whose recon is cheaper.
- **Symmetric molecular conjecture** — does symmetry-generic
  panel-hinge achieve symmetry-forced body-hinge rank? Posed by
  Schulze–Guest–Fowler (*When is a symmetric body-hinge structure
  isostatic?*, Int. J. Solids Struct., 2014); ambient symmetric
  body-bar/hinge characterizations (Abelian point groups) by
  Schulze–Tanigawa (*Linking rigid bodies symmetrically*,
  arXiv:1402.0039). Heavy new prerequisites: symmetry-adapted rigidity
  matrices, group actions on the screw space.
- **Higher-`d` pencil hierarchy** — PENCIL's sequel: in dimension `d`
  the per-body strata between panel (done) and molecular (done) form
  an unmapped lattice (hinges containing a common `(d−3)`-space, lying
  in a hyperplane pencil, …). Our KT formalization is
  dimension-general, so unusually accessible. Fold into PENCIL's
  phase-open recon if that phase goes well rather than queueing
  separately.
- **Developable origami** — ORIGAMI's sequel (CCK arXiv:2309.06804
  §4.3, second remark): add the angle-sum-2π (developability)
  constraints, a deeper stratum below ORIGAMI's. Only meaningful after
  ORIGAMI.

## Tier B — formalization targets (known mathematics, extends in-tree layers)

- **Body-rod-bar + Dilworth truncation** — Tanigawa 2012
  (arXiv:1010.5699): the generic body-rod-bar matroid = union of `D`
  graphic matroids with one Dilworth truncation per rod; alternative
  proofs of Tay's rod-bar and identified-body-hinge theorems
  (Tay, *Linking (n−2)-dimensional panels in n-space II*, Graphs
  Combin. **5** (1989), 245–273). Would extend `Matroid/` with
  Dilworth truncation (independent mathlib value) and is the ambient
  theory IDENT-PANEL sits over — a natural prerequisite phase for it.
- **Body-bar-and-hinge** — Jackson–Jordán, Eur. J. Combin. **31**
  (2009), 574–588: mixed bars + hinges; the natural completion of the
  Phases 13–16 layer.
- **Frameworks with boundaries** — Katoh–Tanigawa, *Rooted-tree
  decompositions with matroid constraints and infinitesimal rigidity
  of frameworks with boundaries* (arXiv:1109.0787): pinned/grounded
  bodies; extends the tree-packing layer.
- **Direction-rigidity** — Whiteley's characterization
  (*Some matroids from discrete applied geometry*, Contemp. Math.
  **197** (1996), 171–312, Thm 8.2.2), short Dilworth-truncation proof
  in Tanigawa 2012 §6. Small, count-matroid-adjacent.
- **Molecular matroid rank function** — KT 2011 §7's own open end:
  Cor. 5.7 computes whole-graph rank of `G²` only. Status check
  against the Cruickshank–Jackson–Jordán–Tanigawa survey
  (arXiv:2508.11636) before treating as open; close to the formalized
  deficiency-matroid surface either way.
- **Tanigawa's Problem 2** — tree-decomposition form of the
  identified-body-hinge count (possibly false; hypergraph
  spanning-connected packing is NP-hard). Combinatorial;
  pebble-game-side interest.

## Tier C — recorded, not recommended

- **ℓ³ₚ minimal rigidity of block-and-hole graphs** — CCK
  arXiv:2309.06804, Conjecture 4.2. Rides on ORIGAMI's
  vertex-splitting engine (noted in `notes/Origami.md`); revisit only
  after that engine lands, and it also needs the normed-space rigidity
  base layer (Dewar–Kitson–Nixon).
- **Global rigidity of discus-and-hole graphs** — CCK Conjecture 4.3.
  Opens the entire global-rigidity front (stress matrices, Connelly
  sufficiency, Hendrickson necessity): a program of its own with
  little overlap with in-tree material.
