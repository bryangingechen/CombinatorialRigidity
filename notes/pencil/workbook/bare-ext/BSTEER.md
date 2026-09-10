## §(K-bare-ext) — continuation (direction BSTEER): **(BE-162)(iii) IS ANSWERED, NO** — side 2's single screw cannot be steered into `Π_x`, and the obstruction is neither genericity nor a missing degree of freedom but a **DEGREE COUNT AT `x`**: `Π_x` is totally singular, so the containment needs `ρ̄₂` to be a *pure rotation*, the only landed mechanism that makes it one is the forced hinge at a **series end**, and `rnode_shaped` rejects a side-2 series end at `x` as an **S-node** — so **(BE-E4′) survives its own tight boundary and gains the two-sided family's FIRST POSITIVE structural fact** (*Steps BE171–BE177*)

**It opens at exactly the tail BFOUR and BSERIES both declared** (*"The next
tail is (BE-172) / Step BE171"*), and **not** at (BE-173).

**The question was one targeted draw, and the draw was not the hard part —
knowing what to draw was.** (BE-161)(iii) measured (BE-E4′) **tight** at
`δ₂ = 1`: `e₁ + e₂ = 4` exactly, so `e₂ = 0` refutes it, and `e₂ = 0` at
`ρ₂ = 1` is exactly `ρ̄₂ ⊆ Π_x`. **The first result is a reduction nobody had
made**: `Π_x = Σ_{p_x} ∩ Λ²π_x` is **totally singular** ((BE-149)(v)(b),
recorded by BARCH and never used), so `ρ̄₂ = ⟨w⟩ ⊆ Π_x` demands **three**
independent things — `Q(w) = 0` (the screw is a **line**, zero pitch),
`w ∧ p_x = 0` (that line passes through `p_x`) and `w ∈ Λ²π_x` (it lies in
`π_x`) — the first of them a condition on the **Klein quadric**, invisible to
every incidence argument on this thread ((BE-172)). **The coordinator's
prediction was NO and its stated reason was that `Π_x` is pinned while `ρ̄₂` is
determined, so there is no shared freedom. That reason is REFUTED**: at a
**fixed** bad plane, with side 1 asserted byte-untouched, the reflag moves
`ρ̄₂` to **144 distinct lines in 144 rows** ((BE-173)). The freedom is total;
the **target** is empty. **And the empty target is empty for the first
condition, not the incidence ones**: at all **56** `δ₂ = 1` R-node rows over
three skeletons `Q(ρ̄₂) ≠ 0` — side 2's single screw has **nonzero pitch** — and
all three conditions fail independently, `0/56` each ((BE-174)). **Then the
proof.** The one landed mechanism that makes `ρ̄₂` singular is the series-end
hinge: at `deg₂(x) = 1`, (BE-45)(i) forces `ℓ = p_x ∧ p_c ∈ ρ̄₂` and (CH-1)'s
chart condition puts `p_c ∈ π_x`, so `ℓ ∈ Π_x` and at `ρ₂ = 1` the containment
is **free**. But `rnode_shaped` puts the virtual edge `xy` back and demands
degree `≥ 3` at the kept terminals, so it forces `deg₂(x) ≥ 2` and rejects
`deg₂(x) = 1` as an **S-node** (asserted at 12/12 constructed shapes); and
(BE-105)'s bad plane needs `deg₁(x) = 1`. The two demands force
`deg(x) = 2`, where **neither** side is R-node-shaped (asserted at 6/6 peels)
**and** the flag at `x` is *determined* by its own 3-point star, so the bad
plane is not constructible by rotation either — **jointly unsatisfiable**
((BE-175)). **The mechanism is real and measured just outside the habitat**:
at a constructed S-node peel, `c₂(Π_x) = 1` at **9/9** rows with the forced
hinge asserted in both `ρ̄₂` and `Π_x`, against `c₂(Π_x) = 0` at **all 56**
R-node rows — so the boundary is a **topological test**, not a genericity
threshold ((BE-176)). **The last gap closes by a second count**: a series end
whose `x`-neighbour the reflag can actually place has a pendant of length
`≥ 2`, contributing two hinges, so `δ₂ ≥ 2` at **72/72** constructed peels
(minimum 2) — `ρ₂ = 1` at a series end needs an **immovable hub** neighbour,
which is `deg(x) = 2` again ((BE-177)). **Nothing landed is refuted**: (E4)
stays refuted, `Γ`-properness stays where BFOUR left it, and (BE-E4′) is
**still UNPROVED** — what it gains is that its tight boundary **cannot be
attacked from this direction**.

### Standing notation (on top of *Steps BE155–BE161*)

BFOUR's, verbatim — `(BE-E4′)`, the `pr` axis, the `δ₂` ladder — and BARCH's
`Π_x`, `e_i`, `Γ`, `Γ_Π`. Three additions:

> **`Q`** is the Klein quadratic form on `Λ²K⁴` and **`B`** its polarization
> (`pitch.Q`, `pitch.klein`). A subspace is **totally singular** when `Q` and
> `B` both vanish on it — equivalently, every element is a **line** and any two
> of them **meet**. `Q(w) ≠ 0` says `w` is a **screw with nonzero pitch**, not a
> rotation about any axis.
>
> **A *series end at `x` on side `i`*** is `deg_i(x) = 1`, the hypothesis
> (BE-45)(i)'s leaf collapse runs under. It is a statement about **one side**,
> and the two sides' values at `x` sum to `deg(x)`; that sum is the whole of
> (BE-175).
>
> **A *movable* `x`-neighbour** is one of degree 2 in `H` — a branch interior,
> which `bsatur.reflag`/`bdecor.draw_branch` can re-place. A neighbour of degree
> `≥ 3` is a **hub** and the reflag cannot move it, which is why (BE-177) is a
> separate count from (BE-175).

**Carrier check, done off the landed bodies rather than the prose.** No new Lean
object is read and **no `.lean` was opened** (the standing 2026-08-05 hold).
Three landed facts are consumed here and each was re-read at its **proof site**,
not its summary: (BE-45)(i)'s leaf collapse (`ρ̄_{u,w₁}(A ∪ e_u) = K·ℓ_u`
because `w₁` is a leaf — exact at every configuration, and its proof says
nothing about the far terminal); (BE-149)(v)(a)/(b)'s two Klein-geometry facts,
which `barch.run_geom` asserts off the graphs entirely; and `rnode_shaped`'s own
body, whose docstring states the S-node rejection and whose code implements it
as a `min degree ≥ 3` test **after** suppression with `keep={u,v}` — the
docstring and the body agree here, and both were read.

### Step BE171 — (BE-172): the REDUCTION — `Π_x` is TOTALLY SINGULAR, so the target is a PITCH condition

> **(BE-172)(i)** *(**PROVED**, and asserted on the ladder rather than cited)*
> `Π_x = Σ_{p_x} ∩ Λ²π_x` ((BE-149)(v)(a)) and `Π_x` is **totally singular**:
> `Q ≡ 0` and `B ≡ 0` on it ((BE-149)(v)(b)) — any two lines through `p_x`
> inside `π_x` meet, at `p_x`. Both asserted at **10/10** `δ₂ = 1` rows over
> three skeletons, as identities of subspaces and of forms. `bsteer.py --crit`.

> **(BE-172)(ii)** *(**PROVED**; the three-way split, and it is pointwise
> exact)* At `ρ₂ = 1`, writing `ρ̄₂ = ⟨w⟩`:
>
> > **`ρ̄₂ ⊆ Π_x` ⟺ `Q(w) = 0` and `w ∧ p_x = 0` and `w ∈ Λ²π_x`.**
>
> *Proof.* (⟹) `Π_x` totally singular gives `Q(w) = 0`; `Π_x ⊆ Σ_{p_x}` gives
> `w ∧ p_x = 0`; `Π_x ⊆ Λ²π_x` gives the third. (⟸) `w ∧ p_x = 0` with
> `Q(w) = 0` makes `w` a line through `p_x`, and `w ∈ Λ²π_x` puts it in `π_x`,
> so `w ∈ p_x ∧ π_x = Π_x`. ∎ Asserted **pointwise** at every row of (BE-174)
> as an `iff`, so the split cannot drift from the containment it decomposes.
>
> **Why this is the step the question was missing.** Stated as *"can a line be
> steered onto a 2-plane"* the target reads like a 3-condition incidence problem
> against however many parameters the reflag has — a *counting* question. The
> reduction says the first condition is not incidence at all: **the screw has to
> be a pure rotation.** That is a condition on the Klein quadric, it is
> **independent of the flag**, and no amount of steering inside `π_x` touches
> it. (BE-174) then measures that it is the one that bites.

### Step BE172 — (BE-173): the FREEDOM EXISTS — the prediction's stated REASON is refuted

> **(BE-173)(i)** *(**MEASURED**; a claim about the sampler's support, tested as
> one)* The dispatch predicted NO because *"`Π_x` is pinned by (BE-105)'s bad
> plane while `ρ̄₂`'s line is determined by side 2's own core, so the two have no
> shared freedom to exploit."* Held to its own terms — bad plane **fixed** per
> configuration, side 1 asserted **byte-untouched** at every row — the reflag
> re-places side 2's branch interiors at `x` inside `π_x`, and
>
> > **`ρ̄₂` takes 144 DISTINCT lines in 144 rows** (48 at each of `K4`, `prism`,
> > `K33`) — a different line at *every* resweep.
>
> Asserted (`len(distinct) > 1`). `bsteer.py --free`.

> **(BE-173)(ii)** *(the reading, and why it is worth a label)* The verdict the
> reason supported is **right**; the reason is **wrong**, and the difference is
> not cosmetic. *"No freedom"* would mean the question is ill-posed — nothing to
> steer. What is true is that the freedom is **total** and the **target set is
> empty**: `ρ̄₂` sweeps a positive-dimensional family of lines and not one of
> them is even a *line in the right pencil*, because (BE-174) shows none of them
> is a line at all in the `Q = 0` sense. **Recorded because it is the difference
> between *"we could not reach it"* and *"there is nothing there to reach"***,
> and only the second is an obstruction. It is also why (BE-175) had to be
> found: with freedom this large, a census alone would leave the clause one
> lucky draw from death.

### Step BE173 — (BE-174): the OBSTRUCTION is TOTAL SINGULARITY, and all three conditions fail independently

> **(BE-174)(i)** *(**MEASURED**; the three conditions, separately)* Over
> **56** `δ₂ = 1` R-node rows — `K4` 24, `prism` 16, `K33` 16 — with side 1
> asserted **BAD** (`c₁(Π_x) = 2` and `Π_x ⊆ ρ̄₁`) at every one:
>
> | condition | holds at |
> |---|---|
> | `Q(ρ̄₂) = 0` — a **line**, zero pitch | **0 of 56** |
> | that line through `p_x` | **0 of 56** |
> | that line inside `π_x` | **0 of 56** |
> | **`ρ̄₂ ⊆ Π_x`** | **0 of 56** |
>
> Asserted, together with (BE-172)(ii)'s `iff` at every row. `bsteer.py
> --pitch`.

> **(BE-174)(ii)** *(the reading, with the cap disclosed)* **Side 2's single
> screw has nonzero pitch at every row**, so it is not a line and cannot lie in
> a totally singular plane *at all* — the failure is not a near-miss incidence
> that a better draw might fix. Stated as `RESEARCH-ARC.md` §5 requires: **not
> found under this cap** — 56 rows, `δ₁ = 5`, three skeletons, one profile
> family — never *"cannot happen"*. **The cap is why (BE-175) is the load-bearing
> step**: the census says the target is empty where we looked, and the proof says
> *why* it is empty everywhere in the habitat.

### Step BE174 — (BE-175): the PROOF — a DEGREE COUNT AT `x`, and the two demands are jointly unsatisfiable

> **(BE-175)(i)** *(**PROVED**; the mechanism, and it makes the containment
> FREE)* Let side `i` have a **series end at `x`**, `deg_i(x) = 1`, with
> neighbour `c`. Then (BE-45)(i)'s leaf collapse forces
> **`ℓ = p_x ∧ p_c ∈ ρ̄_i`** (`c` is a leaf of `side_i ∪ {xc}`; exact at every
> configuration). And (CH-1)'s chart condition makes the **closed star of `x`
> coplanar**, so `p_c ∈ π_x` and therefore
>
> > **`ℓ ∈ p_x ∧ π_x = Π_x`.**
>
> Hence `dim(ρ̄_i ∩ Π_x) ≥ 1` **always** at a series end at `x`, and at
> `ρ_i = 1` — where `ρ̄_i = ⟨ℓ⟩` — the containment **`ρ̄_i ⊆ Π_x` holds with no
> steering at all**. ∎ So the containment is not hard; it is **free**, in a
> habitat this question is not asked in.

> **(BE-175)(ii)** *(**PROVED**; and `rnode_shaped` rejects exactly that shape)*
> `rnode_shaped(E_side, u, v)` puts the virtual edge `uv` back, suppresses
> degree-2 vertices **keeping `{u, v}`**, and requires the result simple,
> 3-connected and of **min degree `≥ 3`** — its own docstring saying *"a
> degree-2 marked vertex after suppression is an S-node and is rejected"*. With
> `deg₂(x) = 1` the kept terminal `x` carries one side-2 edge plus the virtual
> edge, so its degree is **2** and the test **fails**. ∎ Asserted at **12/12**
> constructed pendant side-2 shapes (pendant length `1…4` × three arc pairs),
> every one returning `rnode_shaped = False`. So **the R-node habitat forces
> `deg₂(x) ≥ 2`**, and (i)'s mechanism is unavailable at `x` on side 2.

> **(BE-175)(iii)** *(**PROVED**; the count, and it is the whole obstruction)*
> (BE-105)'s bad plane is a **series-end device**: `bad_plane` asserts (M1),
> `ℓ₁ ∈ ρ̄₁`, and is documented *"at a terminal of side-degree 1"* — so making
> side 1 bad by that mechanism needs **`deg₁(x) = 1`**. (i) needs
> **`deg₂(x) = 1`**. Since `deg(x) = deg₁(x) + deg₂(x)`, together they force
> **`deg(x) = 2`** — and there:
>
> - **neither side is R-node-shaped**, asserted at **6/6** full peels: side 1 is
>   a path, so side 1 plus the virtual edge is a **cycle** (a P/S-node), and
>   side 2 is (ii)'s S-node. So a `deg(x) = 2` peel is **not an internal R-node
>   peel on either side**, which is the habitat (E4) and (BE-E4′) are stated in;
> - and **the flag at `x` is DETERMINED** — a second, independent exclusion. The
>   closed star of `x` is **three** points, so `π_x` is pinned by the
>   configuration and (BE-105)'s rotation cannot move the flag onto a bad plane
>   without moving a neighbour the star already fixes. This is (BE-136)'s *"at
>   `k ≥ 2` the flag is determined"* phenomenon arriving at `x` **from the other
>   side of the peel**, and it is why the exclusion does not evaporate if a
>   future `rnode_shaped` variant were to admit an S-node.
>
> **The two demands are jointly unsatisfiable.** ∎ That is why (BE-174)'s census
> is empty, and it is a **proof rather than a cap** — the residual cap is only
> the claim that no *other* mechanism makes `ρ̄₂` singular.

### Step BE175 — (BE-176): the mechanism is REAL, measured just OUTSIDE the habitat

> **(BE-176)(i)** *(**CONSTRUCTED and MEASURED**; (BE-175)(i) exhibited)*
> (BE-175)(i) is an argument, so it is measured at the nearest legal peel it
> applies to — **an S-node peel, disclosed as constructed and as outside (E4)'s
> habitat**: side 1 the 5-path `x…y`, side 2 a **pendant 2-path** from `x` to a
> hub `h` plus two 2-arcs `h…y`. `|V| = 10`, `|E| = 11`, girth 4, `hcard` true,
> `deg(x) = 2`, `deg₂(x) = 1`, `rnode_shaped(side₂) = False` — asserted. Over
> 9 reflagged rows, census `(ρ₁, ρ₂, c₁, c₂) = (5, 2, 2, 1)` at **9/9**, with
>
> > **the forced hinge `ℓ = p_x ∧ p_c` asserted in BOTH `ρ̄₂` and `Π_x`, and
> > `c₂(Π_x) ≥ 1`, at 9/9.**
>
> `bsteer.py --snode`.

> **(BE-176)(ii)** *(the contrast, and it is the finding)* `c₂(Π_x) = 0` at
> **every** one of (BE-174)'s 56 R-node rows and `≥ 1` at **every** row here.
> **So the boundary is `rnode_shaped` — a topological test on the side's
> skeleton — and not genericity of the draw.** That is a sharper statement than
> the census alone supports, and it is what makes (BE-175)(ii)/(iii)
> load-bearing rather than idle. **DISCLOSED, twice over:** this peel is outside
> (E4)'s stated habitat, so it is **not** a refutation of (BE-E4′); and it has
> `ρ₂ = 2`, so it reaches `c₂(Π_x) = 1` and **not** `ρ̄₂ ⊆ Π_x` — why `ρ₂ = 1`
> cannot be had here is (BE-177).

### Step BE176 — (BE-177): the second count, and the board

> **(BE-177)(i)** *(**MEASURED**; the last gap, closed by a count on the
> pendant)* For the containment at a series end one needs `ρ₂ = 1`, i.e.
> `δ₂ = 1`. Is that reachable with a series end whose `x`-neighbour the reflag
> can actually **place**? Enumerated over `arc(x → v, L)` glued to a subdivided
> skeleton at two non-adjacent hubs, at the **rigid** `pr = [2]*n` profile where
> `δ₂` is smallest — `L ∈ {2, 3}`, three skeletons, every non-adjacent hub
> pair: **72** constructed peels with a movable series end, `δ₂` census
> `{2: 36, 3: 36}`, **minimum 2** — asserted.
>
> **The reason, and it is arithmetic.** A pendant whose first vertex is
> *movable* is a branch interior, so the pendant has length `≥ 2` and
> contributes **two** hinges. Hence `δ₂ ≥ 2`, and a series end at `x` with
> `ρ₂ = 1` needs its `x`-neighbour to be an **immovable hub** — which is
> `deg(x) = 2` again, (BE-175)(iii)'s exclusion, reached a second time by a
> different route. **Cap, disclosed:** three skeletons at `pr = [2]*n` and
> `L ∈ {2, 3}`, **not** all side-2 shapes.

> **(BE-177)(ii)** *(**the verdict**)* **(BE-162)(iii) is ANSWERED: NO.** Side
> 2's single screw cannot be steered into `Π_x` at any internal R-node peel
> where side 1 is bad. **(BE-E4′) SURVIVES its own tight boundary**, and this is
> the **first positive structural fact the two-sided clause family owns**: every
> earlier step in the family — (BE-152)'s floors, (BE-153)'s patch, (BE-156)'s
> containment, (BE-160)'s witness — is a negative. (BE-E4′) remains **UNPROVED**;
> what changes is that `δ₂ = 1`, the one place it had zero margin, is now
> **closed to attack** by (BE-175)/(BE-177) rather than merely unrefuted.

> **(BE-177)(iii)** *(the cross-half consequence, stated because no single
> direction has had to before)* BSERIES's habitat-(I) reduction of **(b2) to
> (b1)** is **conditional on (PENCIL-SATURATES) at side-degree `≥ 2`**
> ((BE-168)(ii)/(BE-170)) — half (B)'s open item 0(a), whose surviving repair is
> (BE-E4′). So **both halves of S-mark hang on this one clause**, and this
> landing is the first news that is *good* for it: had the draw come back YES,
> (BE-E4′) would have died and **BSERIES's conditional would have lost its
> antecedent's cheapest replacement in the same stroke** — the (β) side's
> one-end reduction and half (B)'s 14 → 12 falling together. It came back NO, so
> the conditional stands exactly as BSERIES left it, and the shared exposure is
> unchanged rather than worsened.

> **(BE-177)(iv)** *(**the board**)* **What moved.** (BE-162)(iii) **ANSWERED,
> NO** ((BE-177)(ii)); the obstruction is a **degree count**, not genericity
> ((BE-175)); the prediction's **reason** refuted while its verdict stands
> ((BE-173)); and **`Π_x`'s total singularity becomes a working tool** —
> (BE-149)(v)(b) recorded it and nothing had used it until (BE-172). **What did
> NOT move.** `PencilPair K 3 G`, `hbareSplit`, `hK`, `hcontract`, (GR-15),
> (BE-14) and **S-mark**, class uniformity, the 12 unwitnessed-not-excluded
> blocks ((BE-97)(iv), `⟨M⟩` empty at 93 rows), cross-pair welding, item 0(b)
> **[MARGIN]** (still unexhibited), (BE-101)(iii). **(E4) stays REFUTED** and
> **`Γ`-properness stays exactly where BFOUR left it**. No `.lean` opened; the
> 2026-08-05 hold untouched. **Not a PENCIL event**; **`hK` is not closer**.
> **The E-rider.** No termination-ledger entry fires: **E1** no g-flank and no
> rank computed here; **E2** untouched; **E3 ARMED, does not fire** — this is a
> per-habitat obstruction, not a class-uniform positive.

### Verification

New driver `notes/scripts/w4/bsteer.py`, **seven modes**, exact ℚ, every
headline an `assert`, seed printed by every mode; each run in the **foreground**
with an explicit 600 s timeout:

```
PYTHONHASHSEED=0 python3 notes/scripts/w4/bsteer.py --crit      #   6 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/bsteer.py --free      #  84 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/bsteer.py --pitch     #  31 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/bsteer.py --habitat   #   0 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/bsteer.py --snode     #   1 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/bsteer.py --bound     #   0 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/bsteer.py --support   #   0 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/bsteer.py --validate  # 120 s, rc 0
```

**`--validate` FITS** — 120 s against the 600 s foreground ceiling — so this
landing adds **no** over-ceiling case to `notes/scripts/README.md` §0.

**Figure-invariance gate, discharged with its one exception NAMED.** This
landing **adds** a harness driver and modifies **no** harness driver:
`git diff --name-only -- 'notes/scripts/*.py' 'notes/scripts/*.m2'` is
**empty**, and `git status --porcelain notes/scripts/` shows only the
**addition** of `w4/bsteer.py` — so *No tracked driver modified* discharges the
gate and §3 is not baselined. **The unscoped form of that command is NOT
empty**, and the difference is disclosed rather than glossed: it reports
`notes/check-gapmap-cells.py`, whose `SPECIAL_CAPS` entry and dated docstring
reason this landing adds under the coordinator's explicit authorization. That
file is a **gate, not a figure source** — it lives outside `notes/scripts/`,
appears in no §3 reproduce row, and produces no recorded figure — exactly the
class §3's own table marks for `gapdiff.py`. So nothing a re-run could detect
has changed. **`bfour.py` is IMPORTED, not edited**, which is the whole reason
the discharge survives: the coordinator's own correction to BFOUR's hand-off,
which had said *"one `bfour.py` leg"*. Reproducibility spot-check:
`--crit --pitch --habitat --snode --bound` run twice at `PYTHONHASHSEED=0` is
**byte-identical** modulo each mode's own timing line.

**Harness hazards navigated** (`notes/scripts/README.md` *Harness debt*).
`bimage.pt_in` is **not called at all**, so no `Λ²`-side draw goes near its
`K⁴` truncation. **No width-12 object goes through `span`/`dim`/`isect`**: every
subspace built here is width 6 (`Λ²K⁴`) or width 4 through
`nullspace`/`plane_at`, and no `Γ`-level object is round-tripped. `bwin` is
**not imported**, so `dehom`'s list-vs-tuple guard defeat is unreachable; the
one place an interior vertex is written it goes through
`bsatur.reflag`/`bdecor.draw_branch`, never a hand-rolled dehomogenization.
