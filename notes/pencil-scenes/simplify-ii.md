# Recon (ii): do the flat split and Part C's lift space share one statement?

Read-only recon, 2026-11-11, for `notes/PencilScenes.md` §7 *The simplification recon*, question
(ii). Banked as delivered by the agent (Claude Mythos 5.2), assembled from its return and four
follow-up messages; its closing list of files read and its answer about scripts are folded into
*Sources and measurements*. The coordinator's checks are in `notes/PencilScenes.md` §7a.

## Verdict

**Partly: one definition, not one theorem.** Both spaces are scene spaces of S_G in Whiteley's sense, over a plane picture and over a realization in 3-space. The lead's statement, "scenes over a realization in dimension k are the normal motions of its flat structure in dimension k+1", holds only at k = 2. It is false at k = 3 for the project's dimension-4 framework, and Whiteley 1984 p. 293 says the reduction "is undefined for K = 3". No declaration in `Grade/Lift.lean` or `Grade/Flat.lean` would become an application of it.

I ran as Claude Mythos 5.2, matching the dispatch. Nothing committed, no `lake build`, `git status` clean, no scratch files left in the repo.

## Step 1. The candidate statement, and where each side diverges

### What the Lean bodies say (verified in the definition bodies)

| Object | Declaration | Body |
|---|---|---|
| Screw space | `ScrewSpace K k` (`RigidityMatrix/Basic.lean:87`) | `⋀^k K^(k+2)`: grade k is dimension k+1, screws have C(k+2, 2) coordinates |
| L(q) | `Graph.liftingSpace` (`MainComponent/Carrier.lean:187`) | heights z, zero off V(G), with some `h : Fin 3 → K` per body v such that `z w = h ⬝ᵥ (x_w, y_w, 1)` on N[v] |
| F(q) | `Graph.liftingPlanes` (`MainComponent/Flat.lean:140`) | families `h : α → Fin 3 → K`, with `h u − h v` orthogonal to both picture points at each link; free off V(G) |
| Flat split | `Graph.finrank_infinitesimalMotions_pointJoinFramework_flat` (`Flat.lean:549`) | motions of `pointJoinFramework G ends (pencilConfigPoint q 0)` in `ScrewSpace K 2` ≅ `G.linkConstants × G.liftingPlanes q` |
| Lift space | `liftSpace G b0 P0` (`Grade/Lift.lean:285`) | pairs (ζ, φ), φ_v a form on the subspace `P0 v ⊆ K⁴`, with `ζ w = φ_v ⟨b0 w, _⟩` for v ∈ V(G), w ∈ N[v]; ζ free off V(G) |
| L̃(b⁰) | `liftSpaceTilde G b0` (`Grade/LiftWitness.lean:121`) | pairs (ζ, ψ), ψ_v a form on all of K⁴, same incidences |
| Trivial lift | `IsTrivialLift` (`Lift.lean:301`) | one form ψ on K⁴ |

### The common shape that does exist

For points `b : α → Kⁿ` and faces N[v], the scene space is the set of (ζ, ψ) with `ζ_w = ψ_v(b_w)` for w ∈ N[v].

- **n = 4:** this is `liftSpaceTilde` literally, and it is Whiteley 1984 Def. 7.2 (p. 292, read in the text layer) at K = 3 in homogeneous coordinates.
- **n = 3, b = `pencilPicturePoint q`:** its heights are `Graph.liftingSpace` and its forms are `Graph.liftingPlanes`, compared by `Graph.finrank_liftingPlanes` under admissibility.

So the two developments are the same definition along the axis n. They differ in three ways:

1. **Off-V(G) convention.** `liftingSpace` forces heights to zero off V(G); `liftSpace` and `liftSpaceTilde` leave them free. Bookkeeping only.
2. **Face forms.** The plane side keeps forms on all of K³, since admissibility makes each face span K³. Part C's `liftSpace` keeps forms on `P0 v` only, because the points of N[v] in a pencil realization are coplanar. A hyperplane of 4-space through them has one free parameter per face; `liftSpaceTilde` carries that slack.
3. **Elimination.** F(q) is stated by link conditions, the lift space by incidences with ζ kept.

The Lean already proves the bridge. `mem_liftMaps_pencilConfigPoint_iff` (`Grade/LiftNoRigid.lean:267`) says that at a configuration base (q, z⁰) with z⁰ ∈ L(q), ζ ∈ L(b⁰) exactly when ζ is affine in the picture on every closed neighbourhood. So lifting by a scene does not change the scene space. `liftNormal_pencilConfigPoint` (`LiftNoRigid.lean:460`) says a lift of a configuration is a configuration.

### The divergence that refutes the lead

**Source.** Whiteley 1984 §7.3 (p. 293): the reduced matrix "has K + 1 columns for each body", and it corresponds to a bar and body framework in n-space "iff K + 1 = n(n + 1)/2 for some integer n. Thus the reduction map is undefined for K = 3, K = 4, K = 6, etc." And: "Even for values of K when the correspondence exists we do not know of an interesting alternative geometric interpretation parallel to that in Section 5." Section 5 (pp. 287–289) is the normal-velocity reading that the flat split formalizes.

**The same count in the Lean.** A face form over Kⁿ has n coordinates; a screw at the next grade has C(n+1, 2). These agree only at n = 3, which is why `flatPi` can read `⋀²K³` as affine functions. Trivial lifts over a spanning base in K⁴ have dimension 4; trivial motions have dimension 6.

**What the flat structure in dimension 4 actually has.** `finrank_infinitesimalMotions_map_injective` (`Grade/Embedding.lean:210`) gives motions(φ∘F) = motions(F) + (D − D′)(|V(G)ᶜ| + 1) for any framework on a connected graph. So the motions of the lift by λ = 0 are those of the base r⁰ plus constants. The lift space does not appear.

- Verified: the statement of that lemma, and its use for configurations in `Graph.finrank_span_rigidityRows_ofNormals_pencilConfigPointGrade_padHeights` (`Grade/ZeroHeights.lean:97`).
- Inferred, not compiled: that the lift by 0 of a general (b⁰, Π⁰) is `F.map screwEmbed`. It rests on `liftVec` inserting zeros as `gradeEmbed` does, and on `screwEmbed_panelSupportExtensor`.

**Numerical witness.** `python3 notes/scripts/scenes/example.py cycle7`, rerun in this session: def₂, def₃, def₄ = 4, 1, 0; dim L(q) = 7; at d = 3, flat 32 and one height 35; at d = 4, flat 56, "W of dim 1" 59, "W of dim 2" 60.

- Base: the general configuration (q, z⁰) of C₇ at d = 3. Rank 35, so 7 motions, 1 non-trivial.
- Its lifts: L(b⁰) = L(q) has dimension 7, trivial lifts 4, so 3 non-trivial.
- Its flat lift at d = 4: rank 59 = 35 + 4·6, so 11 motions, 1 non-trivial.
- 3 ≠ 1, so the scenes over this base are not the non-trivial motions of its flat lift, nor of the base.
- Inferred: that this configuration is a legitimate Part C base, and that it spans K⁴ (its rank exceeds the flat rank).

At the flat base (q, 0) of C₇ both counts are 4: this is the flat split. At θ(2,2,3) they coincide at 0 and at 1 (the note's ranks, not rerun), so that example does not detect the failure.

**What would make the lead true** (my derivation, in no source I read): 2-plates in a hyperplane of 4-space whose velocities agree pointwise on shared lines. Their motions split as motions of r⁰ plus the hyperplane scenes over r⁰. But a line is not a hinge in 4-space (it leaves three relative freedoms), and `BodyHingeFramework` has one support extensor per link. No Lean object carries this structure and no consumer needs it. The note's quote of Tay–Whiteley 1984 p. 34 ("Only in 3-space does projective duality convert a hinge structure to a new hinge structure") says the same; I took it from `notes/PencilScenes.md` §5b and did not reread the scan.

**What holds in every dimension** (verified): `gradePi_comp_mem_liftingPlanes` (`Grade/GluedEnds.lean:76`) maps the motions of every configuration over q, at every number of heights, into F(q). The flat split is the case where this map is onto with kernel the constants.

## Step 2. What each file would reuse

No declaration becomes an application of the motion statement. Against a shared definition of the scene space over `α → Fin n → K`:

| File | Would become instances | Would not |
|---|---|---|
| `MainComponent/Flat.lean` (967) | `Graph.finrank_liftingPlanes` (lines 184–253, 70), as the n = 3 case of a general comparison of heights and forms | flat split and coordinates (386–625, ~240); plane framework P_q (255–384, ~130); corollaries (627–713, ~87); joins (715–967, ~250) |
| `Grade/Flat.lean` (173) | none | all of it: padding by zero heights plus arithmetic on dim L(q); it never uses the flat split |
| `Grade/Lift.lean` (563) | `liftSpace`, `IsTrivialLift`, `liftMaps` (285–308, ~25); `mem_liftMaps_iff` (408–423, 16); possibly `liftSmul_mem_liftSpace_iff` and `liftTransport_mem_liftSpace_iff` (~70) | steering chart (43–237, ~195); coordinates (238–278); `IsNondegPencilPlaneRealization.lift` (354–402); rank invariance (453–536); `LiftAttains` |

Also touched: `Grade/LiftWitness.lean` 172–195 (the passage between `liftSpace` and `liftSpaceTilde`, ~24 lines) and the bridge in `Grade/LiftNoRigid.lean` 44–296.

**Size (estimate, not measured).** The common layer is about 250–350 lines: definition, membership, heights, trivial scenes, the comparison of the two eliminations, invariance under lifting, scaling and automorphisms. Adapters to the existing carriers are about 150 more (zero off V(G), `pencilPicturePoint`, forms on the subtype `P0 v`). It removes about 150–200. Net growth is roughly 200–300 lines, and no long proof gets shorter.

**Consumers do not overlap.**
- The flat motion count has none outside its file: `grep` finds no use of `finrank_infinitesimalMotions_pointJoinFramework_flat`, `linkConstants` or `mem_span_extensor_flat_iff` outside `Flat.lean`. The flat rank is used once outside the two flat files (`MainComponent/Bridge.lean:391`), as a witness for `X0Attains`.
- `liftingPlanes` is used by `Grade/GluedEnds.lean`, `PlanesMeet.lean` and `ShortThree.lean`, always over a plane picture.
- `liftSpace` is used in `EarFree`, `LiftWitness`, `LiftNoRigid`, `LiftCases`, `LiftCutEdge` and `LiftSmall` (127 occurrences) as a parameter space of realizations in dimension r + 3 and for triviality of lifts. None of them reads it as a motion space.

## Step 3. Verdict for two audiences

**(a) Exposition.** The chapters should say the two are one definition, and should not say they are one statement. A draft that is true as written:

> The lift space of Part C and the lifting space L(q) are one construction at two dimensions: the scenes of the incidence structure S_G over a realization in 3-space and over a picture in the plane (Whiteley 1984, Definition 7.2, at K = 3 and K = 2). Over a pencil realization the points of a closed neighbourhood are coplanar, so a face hyperplane of Definition 7.2 has one free parameter, and the lift keeps only its restriction to Π⁰_v. The flat split does not extend with it. That scenes are the motions of a framework (Whiteley 1984, Proposition 4.1), and the normal velocities of the flat structure (§§5.1–5.3), is special to plane pictures: a face plane over K-space has K + 1 coordinates and a screw of n-space n(n + 1)/2, and Whiteley notes that the reduction is undefined at K = 3 (§7.3, p. 293). In every dimension one direction remains: the motions of every configuration over q project to F(q).

I read pp. 280–293 of Whiteley 1984 in the text layer, not the page images. The note's §3 table also cites Defs 2.1–2.4, which I did not read; the slice that lands the sentence should reread them. This makes `def:pencil-d-lift` "no longer presented as new" in the right sense: the definition is classical, the correspondence is not available.

**(b) ORIGAMI's opening recon.** There are two independent axes of generality.
- **Faces:** an arbitrary family in place of the closed neighbourhoods. This is the axis ORIGAMI needs, at n = 3 only (a placement with coplanar blocks is a plane picture with a scene).
- **Ambient dimension n:** only Part C needs it. The Lean already has it at n = 4 as `liftSpaceTilde`, and the bridge lemmas above tie it back to n = 3.

A definition with both existing developments as instances is `liftSpaceTilde` with `Fin 4` replaced by `Fin n` and N[v] by a face family. Its cost is the estimate of Step 2, plus the choice of what the forms are defined on (all of Kⁿ, or the face's span). The findings imply that such a layer should not be justified by a motion correspondence in dimension above 2: there is none to prove.

## Open, for the PI

- Whether the exposition says "one definition" with the draft above, and where (the introduction of `sec:pencil-d-lift`, or the road map).
- Whether ORIGAMI's first layer generalizes faces only, or n as well.
- Unchecked by a compiler: the lift by 0 of a general base as `F.map screwEmbed`. Unchecked by a second reader: my reading of p. 293.

## Other duplicated developments (unverified leads, one line each)

- `flatPiForm`, `flatPi`, `planarProj` (`MainComponent/Flat.lean`) against `gradePiForm`, `gradePi`, `gradePlanarProj` (`Grade/GluedEnds.lean`): the same map, the first at one height.
- `Graph.finrank_span_rigidityRows_ofNormals_flat` is the m = 1 case of `…_flat_grade`, which is proved by padding without the flat split; the flat motion count (~120 lines) could retire if the import order allows (`Grade/Flat.lean` imports `MainComponent/Bridge.lean`).
- `MainComponent/Flat.lean` 627–713 against `Grade/Flat.lean` 84–171: the same four corollaries, def₃ against def_(m+2), joinable through `Graph.x0AttainsGrade_one_iff`.
- `Graph.liftingMatrix` (`Carrier.lean:520`), `liftMatrixPoly` (`LiftWitness.lean`) and `Graph.liftingPlanesZeroMatrix` (`GluedEnds.lean:139`): three polynomial matrices of scene systems, each with its kernel lemma and its "least dimension is open" lemma.
- `Graph.x0Attains_of_exists`, `Graph.x0AttainsGrade_of_exists` and the one-witness lemma for `LiftAttains`: one argument three times.
- `pointJoinFramework` (grade 2) against `joinMotions` (every grade): two carriers for the point reading of a configuration's motions.
- `liftSmul` and `liftTransport` against the scale-and-shift and collineation lemmas for configurations.

## Sources and measurements

- **Read:** the Lean files `MainComponent/Flat.lean`, `MainComponent/Carrier.lean`, `Grade/Flat.lean`, `Grade/Lift.lean`, `Grade/LiftWitness.lean`, `Grade/LiftNoRigid.lean`, `Grade/Embedding.lean`, `Grade/ZeroHeights.lean`, `Grade/GluedEnds.lean` (all under `CombinatorialRigidity/Molecular/Molecule/Pencil/`); Whiteley 1984 pp. 280–293, in a `pdftotext -layout` extract, not the page images.
- **The one numerical measurement** (the C₇ ranks) came from the committed script, run as `PYTHONHASHSEED=0 python3 notes/scripts/scenes/example.py cycle7`. I wrote no script of my own. Its output matched the figures in `notes/PencilScenes.md` §4 (def 4, 1, 0; dim L(q) = 7; d = 3: 32, 35; d = 4: 56, 59, 60).
- **The θ(2,2,3) figures** I quoted are the note's, not rerun.
- **Line counts and consumer counts** came from one-off `grep`, `sed` and `wc` shell commands, not saved anywhere. The "127 occurrences" of the lift-space names is the sum of per-file `grep` line counts for `liftSpace|IsTrivialLift|liftMaps` outside `Grade/Lift.lean` (40 + 9 + 5 + 27 + 2 + 44); it also matches `liftSpaceTilde`, so it overcounts uses of `liftSpace` proper.
