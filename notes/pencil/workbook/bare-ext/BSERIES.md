## §(K-bare-ext) — continuation (direction BSERIES): the *sharpened-at-one-end* route **SPLITS INTO TWO HABITATS** — at a piece clean at **exactly one** end BWIN's machine **DOES transport**, at ONE peel, with the end sweep **confined to two self-conjugate 3-spaces** whose intersection is `Π_v` and a kill budget of **TWO**, reducing **(b2) to (b1)** and making the *sharpening* unnecessary — but the reduction is **CONDITIONAL on (PENCIL-SATURATES) at side-degree `≥ 2`**, half (B)'s OPEN item 0(a); and at a piece clean at **both** ends there is **no bridge, hence no peel and no end sweep at all**, so no machine in this sub-arc has an object — which is (BE-45)(iv)'s item, and (BE-58)(iv)'s four-item ledger therefore reads **TWO items plus a corner**

Direction **BSERIES** (`notes/pencil/fanout.md` §"BSERIES", ordinal 83), one
of a **concurrent round of three** (siblings BFOUR, same section; BINSERT,
§(K-ins)), at **(BE-58)(iv)'s largest item**: can the (BE-46)/(BE-52)
per-shape witnesses behind the *sharpened-at-one-end* route be retired
**class-level** by running BWIN's machine at **one peel** instead of two?
Read against *Steps BE53–BE57* (BWIN), *Steps BE141–BE147* (BSCOND), *Steps
BE43–BE47* (BSHARP), *Steps BE48–BE52* (BRULE) and *Steps BE103–BE110*
(BSATUR/BSIGMA), whose figures are **cited, never re-run**. Driver
`notes/scripts/w4/bseries.py` (`peel|conf|sweep|tools|budget|b1|board|
validate`), importing `bscond` / `bwin` / `bsharp` / `bimage` / `bsigma` /
`binduc` / `bearcase` / `bearfull` **read-only**; all exact ℚ, every rng
seeded from a printed literal (`20260908`), every drawn configuration
through `assert_generic_star` **and** `kbare_common.verify_pencil_witness`.

**WHICH DELIVERABLE THIS IS — said at the top.** The spec named a class
statement as the target and a re-scoping of the ledger as an acceptable
alternative. **This landing delivers BOTH, because the question SPLITS**:
one habitat gets a class statement (**conditional**, see below), the other
is shown to have **no object** for the machine, and the ledger is corrected
from four items to **two plus a corner**. **The kill condition — *that
per-shape half discharged class-level* — FIRES ON ONE HABITAT ONLY, and
what it delivers there is CONDITIONAL, not closed.**

**Status, stated before the mathematics.**

- **THE ONE-END PEEL, and what survives it.** At a piece that is a series
  end at `u` and **not** at `v`, (BE-45)(i) at `u` alone gives
  `ρ̄₁ = ⟨ℓ_u⟩ + W′` with `W′ := ρ̄_{w₁,v}(H − u)` — exact at every
  configuration, because the leaf collapse needs **only** that `e_u` is a
  bridge. `Z = μ^{⊥K} ∩ λ^{⊥K}` and the modular law transport verbatim, so
  `ρ̄₁ ∩ Z = ⟨ℓ_u⟩ + (W′ ∩ Z)`. **But the Grassmann count that funds
  (BE-56)(i)/(iii) goes VACUOUS**: at two peels the peeled-off space `Λ_{uv}`
  **is also** the sweep's survivor space, and that coincidence — never
  remarked on in *Steps BE53–BE56*, because with both ends peeled there is
  nothing to distinguish — is what the two-end excess law rests on. At one
  peel the two spaces differ. **(BE-164)**.
- **THE TWO CONFINEMENTS, and both are self-conjugate.** `v` sits inside
  the `W′`-side, so `p_v`, `π_v` are fixed by it and, for **every**
  admissible end choice, `λ ∈ Λ²π_v` and `μ ∈ Σ_{p_v}` — two
  **codimension-3** restrictions of what BWIN sweeps freely. Both confining
  spaces are self-conjugate (the β-plane and the α-plane of the Klein
  quadric through the flag), so the survivors of the **whole** sweep are
  `W′ ∩ Λ²π_v ∩ Σ_{p_v} = W′ ∩ Π_v`, because `Λ²π_v ∩ Σ_{p_v} = Π_v`
  exactly. **`Π_v` is the one-end analogue of `Λ_{uv}` — and it is produced
  by the clean end's own flag, not by the peel. (BE-165)**.
- **THE RESWEEP EXISTS: `W′` DOES NOT MOVE.** `ρ̄` is a function of the
  points alone and the pencil condition at `w₁` is the only constraint the
  `A`-side sees, so over a fixed configuration of `H − u` the end family
  leaves `W′`, `p_v`, `π_v`, `Π_v` **constant** — asserted as an identity of
  spaces at 256 resweep draws — and the drawn `λ`s span `Λ²π_v` **exactly**,
  the drawn `μ`s `Σ_{p_v}` **exactly**, at 32 of 32 pieces. **The
  confinement is tight in both directions: the sweep cannot leave those
  3-spaces and it fills them. (BE-166)**.
- **BSCOND's TWO TOOLS, TESTED — and the pairing is REVERSED from the
  spec's.** (BE-144) has **no object** (no second leading line, so
  `σ := ℓ_u ∨ ℓ_v` is undefined; 32/32). (BE-147)'s **cap has no instance**
  (it needs `Λ_{uv} ⊆ Σ_p`, and `ℓ_u ∉ Σ_{p_v}` is asserted 32/32) — but its
  **mechanism transports verbatim** with `Λ²π_v` for `Σ_p`. The tool that
  actually **breaks** is one the spec did not name: **(BE-146)(i)**, whose
  proof is *"the Klein quadric SPANS `Λ²K⁴`"* while the admissible `λ`s span
  exactly `Λ²π_v` (dim 3, 30/30). **Its breaking is what creates the case
  split**, and it is (BE-146)(ii)'s failure shape one codimension worse and
  **permanent** rather than a stratum. **(BE-167)**.
- **THE ONE-END EXCESS LAW — the budget is TWO, not one.**
  `min dim(W′ ∩ Z) = max(dim(W′ ∩ Π_v), t′ − 2)` when `W′ ⊄ Λ²π_v` (case
  b′), `= max(dim(W′ ∩ Π_v), t′ − 1)` when `W′ ⊆ Λ²π_v` (case a′, which
  caps `t′ ≤ 3`). The lower bound is genericity-free; the upper bound is two
  independent kills, one from each confinement. Hence **(b2) ⟺
  `dim(W′ ∩ Π_v) ≤ 1` and `t′ ≤ 3`**, i.e. `δ₁ ≤ 4` in case (b′) and
  `δ₁ ≤ 3` in case (a′) — the spec's own budget, with `δ₁ = 4` the
  **boundary between the two cases** rather than a wall. Verified at **180
  of 180 abstract rows** with `W` an **arbitrary** subspace, which is what
  makes the statement a class statement, and asserted at 32 of 32 real
  pieces. **(BE-168)**.
- **WHAT THE REDUCTION LEAVES, and it is NOT closed.** `W′ ⊆ ρ̄₁`, so **(b1)
  at the clean end ⟹ the reduction's hypothesis**; and (b3) is already free
  by (BE-50)(iii) since (M1) fires at `u`. So habitat (I) has all three
  clauses **from (b1) alone** — and (b1) at a clean end **IS
  (PENCIL-SATURATES)** below the `δ₁ = 6` vacuous corner, at side-degree
  `≥ 2` because a clean end has `deg_1(v) ≥ 2`: **half (B)'s item 0(a),
  a theorem at side-degree `1` ((BE-127)) and OPEN above it**. The
  reduction is therefore **CONDITIONAL ON AN OPEN CLAUSE**. **(BE-169)**.
- **HABITAT (II) HAS NO OBJECT.** Clean at both ends ⟹ no edge at either
  terminal is a bridge (asserted, 7/7 rows including all three of
  (BE-45)(iv)'s measured-only rows) ⟹ no peel, and by (BE-105)(iv) **both**
  terminal flags are forced by the piece ⟹ **no end sweep whatever**. The
  only quantifier left is the configuration, which is exactly what
  (BE-46)(i)/(ii) formalizes per shape. **(BE-169)(iii)**.
- **THE RE-SCOPING: (BE-58)(iv)'s FOUR ITEMS ARE NOT INDEPENDENT.** Item 3
  **splits**; its habitat-(II) half **IS item 1**; item 2 is what habitat
  (I)'s closure is **conditional on**; item 4 is untouched. **The ledger
  reads TWO items plus a corner**, and half (β) outside the window is
  **not independent of half (B)**. **(BE-170)**.
- **Verdict: a SPLIT, one half CONDITIONALLY class-level and one
  RE-SCOPED.** **Nothing landed is refuted** — not (BE-46)/(BE-52) as
  statements (one of their two consumers stops needing them, which is not a
  refutation), not (BE-45)(iv)'s converse. `PencilPair K 3 G`,
  `hbareSplit`, `hK`, (GR-15), the 2-cut step, S-mark, half (B), (BE-32)(+)
  and class uniformity are untouched; **not a PENCIL event**; the
  phase-boundary consequence is **reported, not acted on**.
- **Reservation FULLY CONSUMED.** Labels **(BE-164)–(BE-171)** and *Steps
  BE163–BE170*; nothing returned. Next tail **(BE-172) / *Step BE171***.

### Standing notation

Inherited from *Steps BE9–BE58* verbatim (`ρ̄_{uv}`, `δ₁`,
`Π_v := p_v ∧ π_v`, `E := Π_u + Π_v`, `Z`, `M := p_u ∨ p_v`,
`L := π_u ∩ π_v`, `λ`/`μ` their Plücker points, `⟨·,·⟩_K`,
`Σ_p := p ∧ K⁴`, `Λ²π`, (M1)/(M2) of (BE-45), `d_min`, `dist_{G₁}`, series
end, `ℓ_u`, `(b1)`/`(b2)`/`(b3)` of (BE-37)(ii), the window of (BE-47)(ii),
`Λ_{uv}`, `W`, `t`, `V`, `excess` of *Steps BE53–BE56*). Added here:

- a **one-end piece** is a series end at `u` ((BE-45)(i): `e_u = u w₁` is a
  bridge) and **not** at `v`; `v` is the **clean end**, and it has `≥ 2`
  usable first edges, hence `deg_1(v) ≥ 2`;
- **`W′ := ρ̄_{w₁,v}(H − u)`**, **`t′ := dim W′`**. This is **not** BWIN's
  middle: `v` is inside it;
- **case (a′)** `W′ ⊆ Λ²π_v`; **case (b′)** `W′ ⊄ Λ²π_v`;
- `c_u := dim(ρ̄₁ ∩ Π_u)`, `c_v := dim(ρ̄₁ ∩ Π_v)`, `c_Z := dim(ρ̄₁ ∩ Z)`;
- **habitat (I)** = clean at exactly one end; **habitat (II)** = clean at
  both.

**Carrier check, done off the landed bodies rather than the prose.** No new
Lean object is read and **no `.lean` was opened** (the standing 2026-08-05
hold). The three landed facts consumed here were re-read at their proof
sites, not their summaries: (BE-45)(i)'s leaf collapse
(`ρ̄_{u,w₁}(A ∪ e_u) = K·ℓ_u` because `w₁` is a leaf of `A ∪ e_u` — exact at
every configuration, and its proof says **nothing** about the far
terminal); (BE-31)(i)'s series glue; and (BE-110)(i)'s corank identity,
whose own text states *"and it holds at any side"*. The screw-space
convention is `kbare_common.build_rigidity`'s own.

### Step BE163 — (BE-164): the ONE-END PEEL, and why the two-end excess law has no analogue

> **(BE-164)(i)** *(proven; **THE ONE-END PEEL**, exact at every
> configuration)* At a one-end piece, (BE-45)(i) at `u` alone gives, by
> (BE-31)(i),
>
> **`ρ̄₁ = K·ℓ_u + ρ̄_{w₁,v}(H − u) = ⟨ℓ_u⟩ + W′`.**
>
> No genericity: the collapse is a leaf collapse, and (BE-45)(i)'s proof
> uses only that `e_u` is a bridge. ∎ Asserted as an identity of spaces
> (`W′` recomputed **directly** on `H − u`, never read off `ρ̄₁`) at every
> one of the driver's **256** guarded configurations.

> **(BE-164)(ii)** *(proven; **THE PERP FORM AND THE MODULAR LAW TRANSPORT
> VERBATIM**)* `Z = μ^{⊥K} ∩ λ^{⊥K}` ((BE-54)(ii)) is a statement about the
> two terminal flags only, so it is untouched by how many ends were peeled;
> and `ℓ_u ∈ Π_u ⊆ Z`, so the modular law gives at every configuration
>
> **`ρ̄₁ ∩ Z = ⟨ℓ_u⟩ + (W′ ∩ Z)`, hence (b2) at `δ₁ ≤ 4` ⟺
> `dim(W′ ∩ Z) ≤ 1`.** ∎
>
> Both asserted as identities of spaces at all 256 draws.

> **(BE-164)(iii)** *(proven; **THE GRASSMANN COUNT GOES VACUOUS** — the
> structural reason the two-end excess law does not transport)* The peel
> gives `dim(W′ ∩ ⟨ℓ_u⟩) = t′ + 1 − δ₁ ∈ {0, 1}`, asserted at every draw.
> In BWIN's machine the corresponding count `dim(W ∩ Λ_{uv}) = t + 2 − δ₁`
> ((BE-56)(i)) **funds** the excess law, and it funds it because the
> peeled-off space `Λ_{uv}` **is also the survivor space of the end sweep**
> ((BE-55)(ii)). At one peel those are different spaces — `⟨ℓ_u⟩` and
> `W′ ∩ Π_v` ((BE-165)(iii)) — so the count says nothing about the quantity
> the budget must control, and **(BE-56)(i)/(iii) have no one-end
> analogue**. ∎ *The coincidence of the two roles at two peels is not
> remarked on anywhere in *Steps BE53–BE56*, because with both ends peeled
> there is nothing to distinguish; it is visible only from here.*

### Step BE164 — (BE-165): the TWO CONFINEMENTS, both self-conjugate, meeting exactly in `Π_v`

> **(BE-165)(i)** *(proven; **THE CONFINEMENTS**)* At a one-end piece the
> clean end sits inside the `W′`-side, so `p_v` and `π_v` are part of that
> side's configuration and are fixed by it. Hence for **every** admissible
> end choice **`λ ∈ Λ²π_v`** (because `L = π_u ∩ π_v ⊆ π_v`) and
> **`μ ∈ Σ_{p_v}`** (because `M = p_u ∨ p_v ∋ p_v`) — each a
> **codimension-3** restriction of the space BWIN sweeps freely. ∎ Asserted
> at every draw and every resweep.

> **(BE-165)(ii)** *(proven; **BOTH CONFINING SPACES ARE SELF-CONJUGATE**)*
> `Λ²π` is the β-plane and `Σ_p` the α-plane of the Klein quadric through
> the flag; each is a 3-dimensional totally singular subspace, so
> `(Λ²π)^{⊥K} = Λ²π` (which is (BE-55)(iii)'s own identity) and
> `(Σ_p)^{⊥K} = Σ_p` (which is (BE-146)(ii)'s). ∎ Asserted at every draw and
> at **39 of 40** synthetic exact-ℚ flags (one draw rejected, not failed).

> **(BE-165)(iii)** *(proven; **THE SURVIVOR SPACE IS `W′ ∩ Π_v`** — the
> one-end analogue of `Λ_{uv}`)* By self-conjugacy
> `⋂_{λ ∈ Λ²π_v} λ^{⊥K} = Λ²π_v` and `⋂_{μ ∈ Σ_{p_v}} μ^{⊥K} = Σ_{p_v}`, so
> the elements of `W′` surviving the **whole** end sweep are
>
> **`W′ ∩ Λ²π_v ∩ Σ_{p_v} = W′ ∩ Π_v`,**
>
> because `Λ²π_v ∩ Σ_{p_v} = p_v ∧ π_v = Π_v` — the lines of `π_v` through
> `p_v`. ∎ Asserted as a chain of space identities at all 256 draws and at
> 39/40 synthetic flags. **This is the exact analogue of BWIN's
> `(span(ℓ_u ∧ ℓ_v))^{⊥K} = Λ_{uv}`, with the one difference that decides
> everything: `Λ_{uv}` is what the peel produced; `Π_v` is what the clean
> end's own flag produces.**

> **(BE-165)(iv)** *(proven; **THE LOWER BOUND, with no genericity**)* A
> line of `Π_v` meets `λ` (two lines of the plane `π_v`) and meets `μ` (two
> lines through `p_v`), so `Π_v ⊆ Z`; and `dim Z = 4` off cross-incidence.
> Hence
>
> **`dim(W′ ∩ Z) ≥ max(dim(W′ ∩ Π_v), t′ − 2)`** —
>
> asserted at **every** admissible `(λ, μ)` pair of **every** abstract row,
> not merely at the minimizing one. ∎

### Step BE165 — (BE-166): the ONE-END RESWEEP — `W′` is INVARIANT, and the sweep fills its confinement

> **(BE-166)(i)** *(proven; **`W′` DOES NOT MOVE**)* `ρ̄` is a function of
> the **points** alone (`kbare_common.build_rigidity`), and the pencil
> condition at `w₁` is the **only** constraint the `A`-side sees: moving
> `p_u` changes the closed star of `w₁` and of no other vertex of `H − u`.
> So over a fixed configuration of `H − u` the end family `{(p_u, π_u)}`
> leaves `W′`, `p_v`, `π_v` and `Π_v` **constant** — the one-end analogue of
> BWIN's fixed middle, and the reason the machine has anything to sweep. ∎
> Asserted as `same_space(W′(resweep), W′(base))` at every one of **256**
> resweep draws over 32 pieces.

> **(BE-166)(ii)** *(measured; **THE SWEEP FILLS ITS CONFINEMENT**)* Over
> the resweep family the drawn `λ`s span `Λ²π_v` **exactly** (dimension 3)
> and the drawn `μ`s span `Σ_{p_v}` **exactly** (dimension 3), at **32 of
> 32** pieces, with every drawn `λ` asserted inside `Λ²π_v` and every `μ`
> inside `Σ_{p_v}`. So (BE-165)(i)'s confinement is **tight in both
> directions**.

> **(BE-166)(iii)** *(measured; **THE FULL TWO-DIMENSIONAL KILL IS
> REALIZED**)* At **32 of 32** pieces some single resweep draw attains
> (BE-165)(iv)'s lower bound. 256 resweep draws, every one re-gated through
> `assert_generic_star` **and** `verify_pencil_witness` after the end is
> replaced.

### Step BE166 — (BE-167): BSCOND's two tools have no object and no instance; the tool that BREAKS is a third one

> **(BE-167)(i)** *(proven; **(BE-144) HAS NO OBJECT**)* (BE-144) annotates
> (BE-55)(iii) as plane-agnostic at `σ := ℓ_u ∨ ℓ_v`. At a one-end piece
> `e_v` is **not** a bridge — `v` has `≥ 2` usable first edges, asserted at
> **32 of 32** battery rows — so there is no second leading line and `σ` is
> **undefined**. The tool is not weakened here; it has no instance. ∎

> **(BE-167)(ii)** *(proven; **(BE-147)'s CAP HAS NO INSTANCE, its
> MECHANISM TRANSPORTS VERBATIM**)* (BE-147)(i) caps `dim ρ̄₁ ≤ 3` from
> `ρ̄₁ = Λ_{uv} + W ⊆ Σ_p`, which needs `Λ_{uv} ⊆ Σ_p` — **both** leading
> lines through one point. At one peel the peeled-off space is `⟨ℓ_u⟩` and
> `ℓ_u ∉ Σ_{p_v}` (asserted 32/32: `ℓ_u = p_u ∨ p_{w₁}` and
> cross-incidence-freeness puts `p_u ∉ π_v`), so `ρ̄₁ ⊄ Σ_{p_v}` (asserted)
> and the cap cannot fire. What **does** transport is the *mechanism* — a
> self-conjugate 3-space, a case split on whether `W` lies inside it, and a
> dimension cap in the inside case — and substituting `Λ²π_v` for `Σ_p`
> reproduces (BE-147)(i)/(ii) line for line, which is (BE-168). ∎ **So the
> coordinator's tool-availability argument was right about the mechanism and
> wrong about the object.**

> **(BE-167)(iii)** *(proven; **THE TOOL THAT BREAKS IS (BE-146)(i)**)*
> (BE-146)(i) proves *"a middle cannot pin `λ` at a free `L`"* from one
> hypothesis: **the Klein quadric SPANS `Λ²K⁴`**, so `𝒬 ⊆ P(W^{⊥K})` is
> impossible. At one peel the admissible `λ`s are the lines of `π_v`; they
> all lie on `𝒬` and span **exactly `Λ²π_v`** (dimension 3, asserted at
> **30 of 30** synthetic flags), never `Λ²K⁴`. So `W′^{⊥K} ⊇ Λ²π_v` is
> possible and `λ` **can** be pinned, for every admissible `L` at once. ∎
>
> **This is (BE-146)(ii)'s failure shape, one codimension worse and
> permanent.** There the coincidence stratum restricted `L` to the lines
> through a point — codimension 2, the reason (BE-56)(ii)'s slice was
> defeated. Here the restriction is codimension 3 and it is not a stratum
> but the geometry: the one-end case lives **inside** a worse version of the
> locus where the two-end slice fails, which is why the pinned case is a
> **case** and not a corner.

### Step BE167 — (BE-168): THE ONE-END EXCESS LAW, and the `δ₁ ≤ 3` / `δ₁ = 4` case boundary

> **(BE-168)(i)** *(proven; **THE LAW**, over an arbitrary subspace)* Let
> `W` be **any** subspace of `Λ²K⁴`, `t = dim W`, and `(p, π)` a flag; write
> `Π = p ∧ π`, `Λ = Λ²π`, `Σ = Σ_p`. Over the admissible pairs — `λ` a line
> of `π` with `p ∉ λ`, `μ` a line through `p` with `μ ⊄ π`, which is exactly
> cross-incidence-freeness —
>
> **`min dim(W ∩ Z) = max(dim(W ∩ Π), t − 2)` if `W ⊄ Λ` (case b′),
> `= max(dim(W ∩ Π), t − 1)` if `W ⊆ Λ` (case a′).**
>
> *Proof.* `≥` is (BE-165)(iv). For `≤`: in case (b′), `Λ` being
> self-conjugate gives `Λ ⊄ W^{⊥K}`, so `Λ ∩ W^{⊥K}` and `Π` are proper
> subspaces of the 3-dimensional `Λ` and over an infinite field their union
> is not all of `Λ`; pick an admissible `λ ∉ W^{⊥K}`, so
> `V := W ∩ λ^{⊥K}` has `dim V = t − 1`. In case (a′) every admissible `λ`
> pins and `V = W`. Then `λ^{⊥K} ∩ Σ = Λ ∩ Σ = Π` — a line through `p` meets
> a line `λ ⊆ π` with `p ∉ λ` iff it lies in `p ∨ λ = π` — so
> `V ∩ Σ = W ∩ Π`; and if `V ⊄ Σ` the same argument inside the
> self-conjugate `Σ` supplies an admissible `μ` with
> `dim(V ∩ μ^{⊥K}) = dim V − 1`. If instead `V ⊆ Σ` then
> `V ⊆ λ^{⊥K} ∩ Σ = Π`, so `V = W ∩ Π` and `dim(W ∩ Z) = dim V` **equals the
> claimed maximum anyway** — so the `μ`-non-pinning condition is **not** a
> side condition. ∎
>
> **Two independent kills, not one.** The `λ` sweep pays one dimension and
> the `μ` sweep a second; BWIN's rank-one budget ((BE-55)(iv)) is the `μ`
> half alone, its `λ` being fixed generic rather than swept inside a
> confinement.
>
> Verified at **180 of 180 abstract rows** — `W` an arbitrary subspace of
> every dimension `0…6`, in case (b′), case (a′) (`t ≤ 3`) and a planted
> case (c′) with `Π ⊆ W` and `W ⊄ Λ` where `min ≥ 2` is **asserted** — with
> the lower bound asserted at every admissible pair of every row. **The
> abstract tier is what makes this a class statement**: `W` enters as an
> opaque subspace, exactly as BWIN's middle does, so no shape is enumerated.

> **(BE-168)(ii)** *(proven; **(b2) REDUCES TO (b1)**, and the sharpening
> becomes unnecessary)* At a one-end piece with `ℓ_u ∉ W′` (so
> `t′ = δ₁ − 1`), (BE-164)(ii) and (i) give
> `dim(ρ̄₁ ∩ Z) = 1 + max(dim(W′ ∩ Π_v), t′ − 2)` at a suitable end choice,
> so
>
> **(b2) ⟺ `dim(W′ ∩ Π_v) ≤ 1` and `t′ ≤ 3`, i.e. `δ₁ ≤ 4` in case (b′) and
> `δ₁ ≤ 3` in case (a′);**
>
> and since `W′ ⊆ ρ̄₁`, **(b1) at the clean end ⟹ `dim(W′ ∩ Π_v) ≤ 1`**. The
> exact breaker is `Π_v ⊆ W′` — the **(P) trap at `v`**. ∎
>
> **The sharpened-at-one-end route needs `c_v = 0` and gets it per shape
> from (BE-46); this reduction needs only `dim(W′ ∩ Π_v) ≤ 1`, which (b1)
> supplies — and (b1) is a clause the (β) side needs anyway, at both ends,
> for every piece.** With (b3) free by (BE-50)(iii) ((M1) fires at `u`) and
> `c_u = 1` from `ρ̄₁ ∩ Π_u ⊇ ⟨ℓ_u⟩`, **habitat (I) has all three clauses of
> (BE-37)(ii) from (b1) alone** — so the (BE-46)/(BE-52) witnesses are not
> needed there. **What this is NOT: unconditional.** (b1) at a clean end is
> open as a class ((BE-169)(ii)).

> **(BE-168)(iii)** *(measured; the battery tier)* The law is **asserted**,
> not reported, at **32 of 32** one-end pieces: the minimum over resweeps
> equals the case's own closed form at every one. Census
> `(δ₁, t′, dim(W′ ∩ Π_v), min dim(W′ ∩ Z))` came out `(1,0,0,0)`,
> `(2,1,0,0)`, `(3,2,0,0)`, `(4,3,0,1)`, `(4,3,1,1)`, `(5,4,0,2)`,
> `(5,4,1,2)`, `(6,5,1,3)`, `(6,6,2,4)` and nothing else — the law tight at
> every row. **(b2) holds at 32 of 32**, with `c_Z = max(1, δ₁ − 2)` — the
> forced minimum of (BE-36) plus the one dimension `ℓ_u` contributes.

> **(BE-168)(iv)** *(the `δ₁ = 4` boundary, said plainly)* At `δ₁ ≤ 3` the
> reduction has **one dimension of slack** (`c_Z = 1 < 2`); at `δ₁ = 4` it
> has **none**, and (b2) there is exactly *"`ρ̄₁` in general position against
> `Z`"*. Case (a′) caps `t′ ≤ 3` hence `δ₁ ≤ 4`, and at `δ₁ = 4` case (a′)
> has `dim V = 3` and **fails** — requiring `W′ = Λ²π_v`, i.e. `H − u`
> entirely coplanar in `π_v`. So `δ₁ = 4` is the value at which the two
> cases separate: the precise analogue of (BE-147)(iii)'s corollary, where
> case (a) makes `δ₁ = 4` **impossible** and here it makes it the
> **boundary**. **Cap, disclosed:** case (a′) at `t′ ≥ 1` is inhabited in
> the abstract tier (36 rows) and **not witnessed by any real piece** —
> every battery row in case (a′) has `t′ = 0` — so the `δ₁ ≤ 3` budget is a
> **lemma with no graph instance here**, the same shape as (BE-147)(iv)'s
> own disclosure.

### Step BE168 — (BE-169): what the reduction LEAVES, and the habitat with no peel

> **(BE-169)(i)** *(proven; **THE ONE CLASS-LEVEL TOOL THAT DOES HOLD AT A
> CLEAN END**)* (BE-110)(i)'s corank identity is stated *"and it holds at
> any side"*, and it does: **`dim(ρ̄ ∩ Σ_{p_v}) = dim ρ̄ − dim(ρ̄ ∧ p_v)`**,
> asserted at every one of the 256 guarded configurations. Since
> `Π_v ⊆ Σ_{p_v}`, (b1) at the clean end is a statement about **what the
> piece looks like projected from `p_v`** — the only reformulation of the
> residue found here that is not per-shape. Census
> `(δ₁, dim(ρ̄₁ ∩ Σ_{p_v}))`: `(1,0)`, `(2,0)`, `(3,0)`, `(4,1)`, `(5,2)`,
> `(6,3)` — i.e. **`max(0, δ₁ − 3)`** at every row, the modular-law floor,
> attained.
>
> **The `0` is the whole difference from a series end.** (BE-105)(ii)'s
> identity at a **degree-1** terminal is `max(1, ρ_i − 3)`, the `1` being
> (M1)'s forced `ℓ_e ∈ ρ̄_i` — which is exactly why the sharpening **cannot**
> hold at a series end ((BE-45)(i)). At a **clean** end no hinge line is
> forced into `ρ̄₁`, the floor drops to `max(0, δ₁ − 3)`, and the sharpening
> becomes possible — generically true at `δ₁ ≤ 3` for a **proved** reason
> (the floor is `0`) and, at `δ₁ = 4`, a genuine general-position condition.
> **So (BE-105)'s trichotomy and (BE-45)'s dichotomy are one statement in
> two habitats, separated by that constant.**

> **(BE-169)(ii)** *(proven; **AT A CLEAN END THERE IS NO FLAG FREEDOM** —
> and the identification, with its one qualification)* A clean end has
> `deg_1(v) ≥ 2`, so by **(BE-105)(iv)** two side-1 edges at `v` give
> distinct hinge lines and `Π_v = ⟨ℓ_e, ℓ_{e′}⟩` — asserted as an identity of
> spaces at every battery row. `Π_v` is therefore **determined by side 1's
> own configuration**, the bad-plane mechanism of (BE-105)(i) cannot run,
> and `c₁(Π_v) = 2` is a closed condition on the configuration alone:
> **generic-or-never** by (BE-46)(i)/(ii). ∎
>
> **The identification, stated with its qualification because the
> qualification is load-bearing.** (PENCIL-SATURATES) is
> `Π_x ⊆ ρ̄_i ⟹ ρ_i = 6`; (b1) at `v` is `Π_v ⊄ ρ̄₁`. **Below the `δ₁ = 6`
> vacuous corner** — where (b1) legitimately fails and (BE-47)(i) does not
> consult it — **the two are the same statement**, and at a clean end
> `deg_1(v) ≥ 2`, so the instance needed is **(PENCIL-SATURATES) at
> side-degree `≥ 2`**: half (B)'s live item 0(a), a **theorem** at
> side-degree `1` ((BE-113)/(BE-127)) and **OPEN** above it, whose current
> successor is the two-sided **(E4)** ((BE-153)/(BE-155)). The row's own
> `deg_i(x) ≥ 2` status is *asserted and holds at 19/19* ((BE-105)(iv)) — a
> measurement, not a class theorem — which is exactly the status (β)'s item
> 2 has carried independently. **Habitat (I)'s class statement is therefore
> CONDITIONAL on an OPEN clause, and no status surface may drop that.**

> **(BE-169)(iii)** *(proven; **HABITAT (II) HAS NO OBJECT**)* At a piece
> clean at **both** ends, `usable_first_edges` has `≥ 2` members at each
> terminal — asserted at **7 of 7** rows, including all three of
> (BE-45)(iv)'s measured-only rows (`K₄ ×3 @ 0,1`, `K_{3,3} ×3 @ 0,1`,
> prism `×3 @ 0,5`) — so **no edge at either terminal is a bridge**,
> (BE-45)(i)'s leaf collapse has nothing to peel, and by (BE-169)(ii)
> **both** terminal flags are forced by the piece. There is therefore **no
> end sweep whatever**: the only quantifier left is the configuration, which
> is precisely what (BE-46)(i)/(ii) formalizes per shape. ∎ **So
> (BE-46)/(BE-52) are not the wrong tool in habitat (II); they are the only
> tool, and (BE-46)(iv)'s own disclosure names what is missing —
> *"nothing here bounds the shapes needing one"*.**

> **(BE-169)(iv)** *(measured; two hunts, both with their caps)* **(a)** The
> reduction's **breaker** — a habitat-(I) row with `δ₁ ≤ 4` and
> `dim(W′ ∩ Π_v) = 2`, the (P) trap at `v` — **not found at 32 pieces**; it
> **is** inhabited as pure linear algebra (case (c′)'s 60 abstract rows,
> where `min ≥ 2` is asserted), so whether a **graph** inhabits it is exactly
> (PENCIL-SATURATES) at side-degree `≥ 2`. **(b)** A **strict-strength** row
> — habitat (I), `δ₁ ≤ 4`, `dist ≥ 5`, (M2) quiet, `c_v ≥ 1`, where the
> per-shape route fails and the one-peel machine still delivers — **not
> found at 32 pieces**, so **the machine is NOT measured strictly stronger
> than the per-shape route**; what it gives is a class-level proof of what
> the route gave per shape. Never *"does not exist"*. Two rows do have
> `c_v = 1` at `δ₁ = 4` (`K33×3 @ v=3, pendant 1` and
> `prism×3 @ v=1, pendant 1`), and at both **(M2) fires** (`δ₁ = d_min = 4`)
> with `dist = 4` — so **(BE-45)(iv)'s converse is intact** and no landed
> measurement is disturbed.

### Step BE169 — (BE-170): the verdict, the RE-SCOPING, and the prediction classified

> **(BE-170)(i)** *(the verdict; **A SPLIT, one half CONDITIONALLY
> class-level and one RE-SCOPED**)* The spec's kill condition — *"that
> per-shape half discharged class-level"* — **fires on habitat (I) and does
> not fire on habitat (II)**, and the split is the deliverable. Habitat (I):
> the per-shape witnesses are not needed, replaced by (BE-168)(ii)'s
> reduction of (b2) to (b1) — **conditional on (PENCIL-SATURATES) at
> side-degree `≥ 2`, OPEN**. Habitat (II): no peel, no sweep, no transport,
> at any number of peels.

> **(BE-170)(ii)** *(**THE RE-SCOPING** — (BE-58)(iv)'s four items are not
> independent)*
>
> - **item 3** (the (BE-46)/(BE-52) witnesses) **SPLITS**: habitat (I)
>   becomes a class statement conditional on (b1); habitat (II) **is item
>   1**;
> - **item 1** ((BE-45)(iv)'s three no-mechanism rows) is **the real
>   obstruction** — it is item 3's surviving half, it admits **no peel**,
>   and it needs the **sharpening** `c = 0`, strictly stronger than
>   (PENCIL-SATURATES)'s `c ≤ 1`;
> - **item 2** ((b1) at `δ₁ = 5`) is what habitat (I)'s closure is
>   **conditional** on, and by (BE-169)(ii) it **IS** (PENCIL-SATURATES) at
>   the ear terminal — so **half (β) outside the window is NOT independent
>   of half (B)**, and one open clause serves both;
> - **item 4** (the `π_u = π_v` corner, (BE-32)(+)'s forced branch) is
>   **untouched**.
>
> **The ledger reads TWO items plus a corner, not four**, and its largest
> item has moved from *"per-shape witnesses over an unbounded shape set"* to
> *"the sharpening at a piece clean at both ends"*. ∎ *This is the most
> transferable thing the direction produced — more than either half of the
> split — and it is stated here so the next pass inherits the corrected
> ledger rather than the four-item one.*

> **(BE-170)(iii)** *(the coordinator's prediction, classified)*
> **CONFIRMED in its framing; the mechanism is a case split it did not
> name; the tool pairing is REVERSED.** Confirmed: *"budget `δ₁ ≤ 3`"*
> (case a′), *"the `δ₁ = 4` boundary is the risk"* (the case boundary), and
> *"the excess law closes a slice argument by capping a dimension"*
> (transports as a mechanism). Corrected: the excess law's **hypotheses do
> not** survive — `Λ_{uv} ⊆ Σ_p` has no instance — and (BE-144) has no
> object; the operative tool is **(BE-146)(i) failing**. Reframed: *"the
> one-end obstruction is a per-shape slice argument"* is right for habitat
> (II) and **wrong for habitat (I)**, where it is a two-kill budget.
> `RESEARCH-ARC.md` §7's **sixth kind** — *the framing was right and
> load-bearing, and the stated test carried a dropped proviso* — the
> dropped proviso being **which pieces have a series end at all**. *(The
> tally is the coordinator's to reconcile and is not touched here.)*

> **(BE-170)(iv)** *(the price, stated as a price)* **(1)** Every battery
> row has `deg(u) = 1`, so the `A`-side of the peel is a single vertex; a
> general `A`-side is covered by **(BE-57)(ii)'s projective move**, prose
> and not battery — `bwin.py`'s own cap, inherited, and the argument is
> unchanged because (BE-164)(i) makes the target depend on the `A`-side
> through `ℓ_u` alone. **(2)** Case (a′) at `t′ ≥ 1` is **not witnessed by
> any real piece** ((BE-168)(iv)), so the `δ₁ ≤ 3` budget is a lemma with no
> graph instance here. **(3)** The reduction is **conditional on (b1)**,
> open at side-degree `≥ 2`; nothing here proves it, and (BE-169)(iv)'s two
> hunts are capped at 32 pieces. **(4)** The machine is **not measured
> strictly stronger** than the per-shape route.

> **(BE-170)(v)** *(classification, mandatory and explicit)* **Nothing the
> arc carries is refuted.** Not `PencilPair K 3 G`; not `hbareSplit`; not
> `hcontract`; not `hK`; not (GR-15); not (BE-14)-for-all-`G`; not the 2-cut
> composition lemma; not S-mark; not half (B); not (BE-32)(+); not the
> short-cycle law; not class uniformity; not cross-pair welding; not
> (BE-57) or (BE-58)(i)–(iii); not (BE-46)/(BE-52) **as statements** — one
> of their two consumers stops needing them, which is not a refutation; not
> (BE-45)(iv)'s converse, whose two `c_v = 1` rows both have (M2) firing.
> **One route is closed** (habitat (I)'s per-shape wall, conditionally);
> **one is re-scoped** (item 3 → item 1); **none is opened. NOT a PENCIL
> event** — no gap-map status word for `hK`, (GR-15), (OC-8) or class
> uniformity moves, and `hbareSplit` stays OPEN. The phase-boundary
> consequence of a reduced (β) ledger is the **user's call**
> (`notes/Phase39.md` *Status*), reported and not acted on.
>
> **ONE COORDINATOR-SPEC CLAIM CORRECTED.** The spec called item 3 *"(β)'s
> largest remaining per-shape component"* and treated it as one object. It
> is two, in two habitats with different geometry, and the arc's own
> (BE-47)(iv) bucket list already contained the distinction — *sharpened at
> one end* is a bucket, but *at which end, and is the other one series* is
> not a question that list asks. **(BE-47)(iv)'s six-bucket classification
> is nevertheless EXHAUSTIVE on this direction's 32-piece battery too: 0
> uncovered rows. No gap in it is claimed.**

> **(BE-170)(vi)** *(E-rider, reported not fired)* **(E1)** a g-flank:
> **DOES NOT FIRE** — this landing is on the `(K-bare)` line and exhibits no
> colouring object; (GR-15) untouched. **(E2)** the target refuted or
> unprovable-as-posed **and** no named dispatchable attack left: **DOES NOT
> FIRE on both conjuncts** — nothing is refuted, and (BE-171) names three
> dispatchable successors. **(E3)** the target proven with every entry
> adjudication-gated: **DOES NOT FIRE** — nothing that was open is proven;
> (BE-14), `hbareSplit` and `hK` are untouched.

### Step BE170 — (BE-171): successors, priced

> **(BE-171)(i)** *(the cheapest, and it is a lemma rather than a search)*
> **Prove that the (P) trap at a clean end forces case (a′)** — i.e.
> `Π_v ⊆ W′` with `δ₁ ≤ 4` ⟹ `W′ ⊆ Λ²π_v` — which would make
> (BE-168)(ii)'s reduction **unconditional in case (b′) at `δ₁ ≤ 4`**.
> (BE-110)(ii)'s coplanarity argument does this for a **path** side; the gap
> is that `W′ ⊆ ⟨P⟩` gives no bound on `dim(⟨P⟩ ∧ p_v)` from a bound on
> `dim(W′ ∧ p_v)`. **Priced: one direction.** *Kill:* that implication
> proved, or a subspace realizing its failure exhibited by a graph.
> *Decided by:* the `(K-bare)` row.

> **(BE-171)(ii)** *(the one that matters, and it is half (B)'s)*
> **(PENCIL-SATURATES) at side-degree `≥ 2`** now carries **both** halves of
> S-mark's residue: half (B)'s item 0(a) and, by (BE-169)(ii), half (β)'s
> item 2 together with habitat (I)'s condition. Its live successor is the
> two-sided **(E4)** ((BE-153)), and (BE-154)(iv)'s `barch.py` chart mode is
> the next concrete task on it. **This direction's contribution to that
> ranking is that (E4) is load-bearing on one more surface than the board
> records.**

> **(BE-171)(iii)** *(habitat (II), priced NOT cheap)* A class statement
> there needs the **sharpening** at a piece with **both** flags forced and
> **no** free end parameter. The only lever the arc owns is (BE-169)(i)'s
> corank identity plus openness/irreducibility, i.e. (BE-46) — so a class
> statement requires either **bounding the shapes needing a witness**
> ((BE-46)(iv)'s own words) or a genuinely new mechanism. Flagged rather
> than forced.

> **(BE-171)(iv)** *(what NOT to re-run)* Do not re-hunt the reduction's
> breaker on this battery (32 pieces, capped, reported); do not look for a
> *second functional* at the clean end — (BE-165)(iii) shows the two
> confinements already exhaust the end freedom and their intersection is
> `Π_v`; do not attempt (BE-144) or (BE-147)'s cap at one peel
> ((BE-167)(i)/(ii): no object, no instance).

### Verification

Every claim above is reproduced by
`python3 notes/scripts/w4/bseries.py {peel|conf|sweep|tools|budget|b1|board|validate}`,
run from the repo root; **`validate` runs every mode at a reduced tier in
~310 s and gates 256 guarded configurations**. Full-tier figures: `peel` 64
(82 s), `conf` 32 + 39/40 synthetic (42 s), `sweep` 32 bases + **256**
resweeps (355 s), `tools` 32 + 32 + 30 (22 s), `budget` **180** abstract
rows + 32 pieces (277 s), `b1` 32 + 7 (75 s). The load-bearing asserts (a
failure **stops** the run; it is not reported):

1. **Every configuration is a pencil configuration** —
   `assert_generic_star` **and** `kbare_common.verify_pencil_witness` on
   every draw and on **every resweep** (re-gated after the end is
   replaced).
2. **Every space claim is an identity of SPACES** (`same_space`/`contains`,
   never dimensions): the one-end peel (with `W′` recomputed directly on
   `H − u`), `Z = μ^{⊥K} ∩ λ^{⊥K}`, the modular-law factorization,
   `λ ∈ Λ²π_v`, `μ ∈ Σ_{p_v}`, `(Λ²π_v)^{⊥K} = Λ²π_v`,
   `(Σ_{p_v})^{⊥K} = Σ_{p_v}`, `Λ²π_v ∩ Σ_{p_v} = Π_v`, the survivor space
   `W′ ∩ Λ²π_v ∩ Σ_{p_v} = W′ ∩ Π_v`, `Π_v = ⟨ℓ_e, ℓ_{e′}⟩`, and `W′`'s
   invariance across every resweep.
3. **The one-end excess law is asserted, not reported** — the lower bound
   at **every** admissible pair of every abstract row, and the closed form
   at the minimizing pair of every battery row.
4. **The corank identity** and the peel count
   `dim(W′ ∩ ⟨ℓ_u⟩) = t′ + 1 − δ₁` at every draw.
5. **The negative results are asserts too** — `ℓ_u ∉ Σ_{p_v}`,
   `ρ̄₁ ⊄ Σ_{p_v}`, `≥ 2` usable first edges at `v` and at both terminals of
   every habitat-(II) row, and the admissible `λ`s spanning exactly
   `Λ²π_v`.

**The generator's parameters, and which the evidence varied** (the RPOOL
sharpening, `RESEARCH-ARC.md` §4). `one_end(core, cu, cv, k)` has four:
**(1)** pendant length `k` — varied `1, 2, 3, 4`; **(2)** far-end topology
— `θ(a,b,c)`, `C_n`, `θ⁴(a,b,c,d)` and the three **R-node** subdivisions
`K₄`, `K_{3,3}`, prism; **(3)** side-degree at the clean end — `2` (cycle),
`3` (θ, R-nodes), `4` (θ⁴); **(4)** attachment site relative to `v` — the
opposite hub, a branch interior, an adjacent core vertex, a far one. **32
pieces.** *The first version of this battery held `k ≥ 2`, which made `W′`
the pendant tail and hid the far end's own screw space at every `δ₁ ≤ 4`
row; the `k = 1` rows were added for exactly that reason and they are where
`dim(W′ ∩ Π_v) = 1` at `δ₁ ≤ 4` first appears. Disclosed as a self-caught
support defect of this direction's own generator.*

**Sampler support, named** (§4's BSATUR sharpening). The resweep varies
`p_u` (3 parameters) and `π_u` through `ℓ_u` (1), holding the configuration
of `H − u` — hence `p_v`, `π_v`, `Π_v`, `W′` — **fixed**. So it varies the
**end flag** and not the **`W′`-side configuration**: every claim
quantified over `W′` is tested in the **abstract tier** (`W` an arbitrary
subspace), not by the resweep, and every claim quantified over `(λ, μ)` is
tested by the resweep. The clause `dim(W′ ∩ Π_v) ≤ 1` is quantified over
the `W′`-side and is therefore **measured, not asserted class-level** —
which is why it is reported as the reduction's **condition** and not as a
theorem.

**Harness hazards navigated** (`notes/scripts/README.md` *Harness debt*).
`bwin.dehom` returns a **list**; every point this module writes into a
configuration goes through **`bscond.aff`**, so `assert_generic_star`'s
edge check compares tuples with tuples (the recorded silent guard defeat,
avoided rather than re-discovered). No `Λ²`-side draw goes through
`bimage.pt_in`. Every `K⁴` subspace goes through
`bwin.k4_span`/`k4_isect`; `bimage.span`/`isect`/`dim` are used on width-6
rows only, so `bimage.span`'s width-6 special case is never reached with a
`K⁴` input.

**Figure-invariance gate.** This landing only **adds** a driver:
`git diff --name-only -- '*.py' '*.m2'` is empty and
`git status --porcelain notes/scripts/` shows only the **addition** of
`w4/bseries.py`, so *No tracked driver modified* discharges the gate and §3
is not baselined.
