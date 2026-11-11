# Recon (i): Part C lifts as motions — verdict

Read-only recon, 2026-11-11, for `notes/PencilScenes.md` §7 *The simplification recon*, question
(i). Banked as delivered by the agent (Claude Mythos 5.2), with one change: the cycle table's
"script not retained" is now a pointer to the script, which the agent kept and the coordinator
committed. The coordinator's checks are in `notes/PencilScenes.md` §7a.

**Verdict: no.** A Part C lift of a realization in 3-space is not a motion of that panel structure, and "every lift of r⁰|_Y is trivial" neither follows from nor implies that r⁰|_Y has only trivial motions in 3-space. The correspondence that does hold is the one the chapter and the Lean already use: the lifts of r⁰ are the scenes over its plane projection q, which are the motions of the plane framework P_q, and the rank statement that gives triviality is `thm:pencil-jj-equality` at Y with def₂(Y) = 1, which the proof of `lem:pencil-d-ear-free` already cites. Nothing is saved, and no Lean change joins the phase from this question.

My environment block names Mythos 5.2, matching the dispatch. Nothing committed; `git status` is clean. No `lake build` was run and no compiler witness was needed: every Lean claim below is read from a definition body or theorem statement.

## Step 1. Does the correspondence hold at Part C's base?

### What the Lean definitions say (bodies read)

- **`liftSpace G b0 P0`** (`Grade/Lift.lean:285`): pairs (ζ, φ) with ζ : α → K and φ_v a linear form on the 3-dimensional `P0 v`, such that ζ_w = φ_v(b⁰_w) for every v ∈ V(G) and w in its closed neighbourhood.
- **`IsTrivialLift`** (`Grade/Lift.lean:301`): one form ψ on K⁴ with ζ_v = ψ(b⁰_v) and φ_v = ψ|Π⁰_v at every body.
- **`mem_liftMaps_iff`** (`Grade/Lift.lean:408`): ζ is the map of a lift iff at every body some form on K⁴ agrees with ζ on the closed neighbourhood.

So a lift carries 3 unknowns per body (a form on a 3-dimensional subspace) and 2 conditions per edge (φ_u = φ_v on span(b⁰_u, b⁰_v)), with 4 dimensions of trivial lifts. That is the plane count 3|V| − 2|E|. The motions of the structure in 3-space carry 6 unknowns per body and 5 conditions per edge, with 6 trivial dimensions. The two spaces follow different counts.

### Refuted: lifts as motions of the structure in 3-space

**Whiteley 1984 says so for hyperplane faces.** §7.3, p. 293 (page image read): the reduced matrix "has K + 1 columns for each body", it is a generalized bar-and-body framework in n-space iff K + 1 = n(n+1)/2, and "Thus the reduction map is undefined for K = 3, K = 4, K = 6, etc." Prop. 4.1 (pp. 282–283, read) is the case K = 2, where 3 = 3. The lead's "W84 Prop. 4.1 a dimension up" is the case W84 excludes.

**Part C's faces are 2-planes, not hyperplanes, so they have 3 columns per body.** That matches n = 2, a plane framework, not a framework in 3-space. This is my inference from the definition body; W84 does not treat it.

**No map from motions to lifts exists at a non-flat base (my derivation).** The only natural candidate is the normal velocity: body v's velocity field on Π⁰_v, paired with the normal of Π⁰_v, is a form on Π⁰_v. Two adjacent bodies have equal velocities on their hinge, but the normal components are taken against different normals, so the forms agree on the hinge only when Π⁰_u = Π⁰_v. This is why `lem:pencil-flat-split` (`main-component.tex` ~l. 922, read) is stated at the flat configuration (q, 0), where all hinges lie in one plane.

**Embedding in 4-space does not help (my derivation).** Splitting ⋀²K⁵ = ⋀²K⁴ ⊕ K⁴∧e, the motions of the embedded structure are the motions of r⁰ in 3-space plus a constant c ∈ K⁴. The lift such a motion induces is ζ_v = c·b⁰_v, a trivial lift. Non-trivial lifts are deformations of the structure that keep its section, not motions.

**Counterexamples in both directions (measured, exact rationals; `PYTHONHASHSEED=0 python3 notes/scripts/scenes/lift_cycles.py`, seed 7).** General points b_v ∈ ℚ⁴ on a cycle, Π_v the span of the closed neighbourhood. No body is a hub (`Graph.PencilHub` is degree ≥ 3, `Pencil/Motive.lean:74`), so these meet the conditions of `mem_steerSet_iff`.

| Graph | dim lift space | trivial lifts | dim motions in 3-space | trivial motions |
|---|---|---|---|---|
| C₄ | 4 | 4 | 6 | 6 |
| C₅ | 5 | 4 | 6 | 6 |
| C₆ | 6 | 4 | 6 | 6 |
| C₇ | 7 | 4 | 7 | 6 |
| K₂ (Π₁ ≠ Π₂) | 4 | 4 | 7 | 6 |

- C₅ and C₆ are infinitesimally rigid in 3-space and have non-trivial lifts, so rigidity does not give triviality.
- K₂ has only trivial lifts and a flex, so triviality does not give rigidity.
- The excess of lifts is def₂ − 1 on each row (C_n: n − 4), the plane count.

### Confirmed: the correspondence that holds, already in the Lean

Projecting from the third coordinate axis, a realization in 3-space with no vertical plane is a configuration (q′, z′) over an admissible plane picture, and its lift maps are L(q′).

- `exists_pencilConfigPoint_of_dotProduct` (`Grade/LiftNoRigid.lean:394`, statement read): a realization with nonzero last coordinates of points and nonzero third coordinates of normals is, rescaled, a configuration with z′ ∈ L(q′) and the same dim L̃.
- `mem_liftMaps_pencilConfigPoint_iff` (`LiftNoRigid.lean:267`): at a configuration, L(b⁰) = L(q).
- `finrank_liftSpaceTilde_pencilConfigPoint` (`LiftNoRigid.lean:256`): dim L̃ = dim L(q) + the free coordinates.
- `lem:pencil-lifting-planes-dim` and `lem:pencil-lifting-planes-motions` (`main-component.tex`, read): L(q) ≅ F(q) ≅ the motions of P_q.

So the precise statement is:

- **The map:** lift (ζ, φ) ↦ ζ ↦ the family of affine functions on the picture ↦ a motion of the plane framework P_{q′}, q′ the projection of r⁰.
- **Injective and surjective** when each Π⁰_v is spanned by the points of its closed neighbourhood (condition (a) of the ear-free proof).
- **Trivial lifts** go to Aff(q′) ⊕ K·z′, of dimension 4, not to the trivial motions of P_{q′}, of dimension 3. The base's own height z′ is a non-trivial motion of P_{q′} and a trivial lift.
- **"Every lift trivial"** therefore means dim L(q′) = 4: P_{q′} has exactly one non-trivial motion.

This is W84 Prop. 4.1 at K = 2, composed with a projection. It needs no new proof.

## Step 2. Is there a rigidity statement that gives triviality?

**The one that works is already used.** Part (iii) of `lem:pencil-d-good-ear` (statement read, l. 6036) gives def₂(G[X]) = 1 and def₂(G[Z]) ≠ 0 for every Z ⊆ X with |Z| ≥ 2. The proof of `lem:pencil-d-ear-free` (ll. 6413–6431, read) takes a picture q of Y off the zero set of `thm:pencil-jj-equality`'s polynomial, so dim L_Y(q) = 3 + def₂(Y) = 4, and reads dim L̃_Y = |X| + 4 through `finrank_liftSpaceTilde_pencilConfigPoint` (`exists_earFree_config`, `Grade/EarFree.lean:745`). In Step 1's terms that is "P_q has one non-trivial motion".

**A rigidity statement about r⁰|_Y in 3-space would not help**, whether or not it is available: by the table it is neither sufficient nor necessary. The circularity question does not arise.

**Hypothesis diff against the consumer.** `lem:pencil-d-lift-ear` (l. 6149; Lean `liftAttains_of_ear` with `EarLiftCondition`) asks that, at a general nondegenerate realization r⁰ of **G**, every lift of r⁰|_{G−x} has φ_a(b⁰_x) = φ_b(b⁰_x). `holdsGenerally_earFree` (`EarFree.lean:1062`) delivers exactly that, as `HoldsGenerally G …` on G's chart. The base is the restriction to Y of a general realization of G, not a general realization of Y. Any route therefore has to show that some realization of G restricts to a Y-configuration over a picture where dim L_Y = 4. That is what the steering argument does (`lem:pencil-d-ear-extend`, `exists_earFree_gammaL`, the "Into G" paragraph), and no correspondence removes it.

## Step 3. What would be saved?

Nothing.

- **`\uses` of the proof:** none becomes unused. `thm:pencil-jj-equality` is the rank statement; `lem:pencil-d-ear-extend`, `lem:pencil-d-steer` and `lem:pencil-x0-fibre-intersection` are the transfer to G; `lem:pencil-d-lift-no-rigid` and `lem:pencil-d-lift-one-witness` supply the correspondence and L̃; the rest serve conditions (a) and (b) at the witness.
- **Lean:** `Grade/EarFree.lean` (1156 lines; ear-extend ll. 159–468, ear-free ll. 469–1156) is unchanged. No declaration becomes unused, and no new Lean is needed.
- **Scope:** not a "small Lean change that could join this phase". Question (i) contributes exposition only.

**What the exposition can say (for the `pencil-d.tex` slice, the PI's call):** at `def:pencil-d-lift`, a lift is W84 Def. 7.2's scene with faces restricted to the planes Π⁰_v; W84 §7.3 (p. 293) notes that for hyperplane faces over a picture in 3-space the reduction to a framework is undefined; with plane faces the lifts are the scenes over a plane projection, hence motions of P_q by W84 Prop. 4.1. At `lem:pencil-d-ear-free`: "every lift is trivial" says P_q has exactly one non-trivial motion, the base's own height.

## Sources: read versus taken from the note

- **Read on page images:** W84 pp. 281–284 (Prop. 4.1, Cor. 4.2) and pp. 290–294 (§7, Def. 7.2, §7.3).
- **Read in the repo:** the Lean bodies and statements named above; `pencil-d.tex` ll. 5160–5230, 5310–5345, 5905–6075, 6140–6200, 6330–6590; `main-component.tex` ll. 900–1010.
- **From the note's summary, not re-read:** CW82 Prop. 4.1 (p. 70) and Example 4.4; W89; Crapo 1984; Crapo–Ryan 1986. None is load-bearing for the verdict.
- **My derivations, unchecked by a second reader:** the normal-velocity obstruction; the 4-space splitting; the reading of trivial lifts as Aff(q′) ⊕ K·z′.

## Open, and who decides

- **PI:** whether the two exposition sentences above go into the `pencil-d.tex` slice. They would replace §7's hope of a route change, and they sharpen §3's row for `def:pencil-d-lift`: Def. 7.2 with plane faces, plus the §7.3 remark.
- **PI:** §7 says "A yes to (i) is a small Lean change that could join this phase". With a no, the phase's Lean scope is the rename alone, pending question (ii).

## Other leads seen while reading (unverified, one line each)

- `exists_pencilConfigPoint_of_dotProduct` and `mem_liftMaps_pencilConfigPoint_iff` are, together, "every general realization in 3-space is a scene over its projection, and its lifts are L(q′)": this is the natural shared statement for question (ii), more than the flat split.
- The ear-free proof uses only dim L_Y(q) ≤ 4 at one picture; the lower bound is `lem:pencil-lifting-space-deficiency`, so W89 Thm 3.1 with the merging lemma (the second derivation) could stand in for the equality here in exposition, though not shorten the Lean.
- Conditions (a)–(c) of the ear-free proof are W84's "flat scene" (Def. 7.2, p. 292) for Y with plane faces: the lemma could be titled "the scenes over r⁰|_Y are flat".
- Whiteley 1991's section diagrams (note §5c) describe the lift in the normal reading (a 4-space panel structure with a prescribed section); whether Corollary 5.7's count gives dim of the lift space at a general section was not checked, and r⁰|_Y is a restriction, not a generic section.
- W84 §7.3's "n-frames" (White–Whiteley, p. 293) are the frame-like structures the reduced matrix defines for every K; whether the Part C lift system is a 2-frame in their sense, giving a cited count for "generically completely shaky", was not checked.
