## §(K-bare-ext), continued — direction BSCOND: **BOTH WINDOW CONDITIONS ARE DECIDED — (S1) IS REMOVABLE, (S2)'s FIRST HALF IS A THEOREM WITH AN EXHAUSTIVE MECHANISM LIST, AND ITS SECOND HALF IS REFUTED AS STATED AND THEN CLOSED** (*Steps BE141–BE147*)

Direction **BSCOND** (`notes/pencil/fanout.md` §"BSCOND", ordinal 76), the
arc's eighty-fourth, at **(BE-57)(iv)**'s two side conditions — half (β)'s
only residue, open since **BWIN** (ordinal 51) and attacked by none of the
eleven (BE-14)-thread landings BONEONE (56) through BDEGTWO (74). Read
against *Steps BE53–BE57* (BWIN), *Steps BE43–BE47* (BSHARP), *Steps
BE48–BE52* (BRULE) and *Steps BE34–BE37* (BEARCASE), whose figures are
**cited, never re-run**. Driver `notes/scripts/w4/bscond.py`
(`support|incid|cover|crit|pin|law|ident|board|validate`), importing `bwin` /
`bsharp` / `bimage` / `binduc` read-only and through them `brule` /
`bearfull` / `bearcase` / `btwocut` / `bzavoid` / `kbare_common`; all exact
ℚ, every rng seeded from the printed literal `20260829` (`bwin.SEED`).

**Status, stated before the mathematics.**

- **THE TWO CONDITIONS WERE NEVER INDEPENDENT — ONE INCIDENCE LEMMA COLLAPSES
  THEM.** The pencil condition at `u` puts `p_{w₁}` in `π_u` and at `v` puts
  `p_{w₂}` in `π_v`, at **every** configuration (`w₁ ∼ u`, `w₂ ∼ v` are the
  two bridges). Hence `p_{w₁} = p_{w₂}` forces that point onto
  `L = π_u ∩ π_v`, and `ℓ_u = p_u ∨ p_{w₁}`, `ℓ_v = p_v ∨ p_{w₂}` **meet**
  there. **So (S1) failing IS (S2)'s meeting-lines regime**, and (S2)'s
  feared *"other algebraic relation between its boundary flags"* is not
  hypothetical — it is (S1)'s own failure. **(BE-143)**.
- **(BE-55)(iii)'s PROOF IS PLANE-AGNOSTIC, WHICH IS STRICTLY MORE THAN IT
  CLAIMS.** It is stated for `π₁ = π₂ = π` and instantiated at `σ = π`,
  `q = L ∩ π`; every step of it needs only **a plane containing both leading
  lines with `L` outside it**, and `σ := ℓ_u ∨ ℓ_v` is always one. From
  cross-incidence-freeness and `π_u ≠ π_v` alone: `L ⊄ σ`, `q := L ∩ σ` is a
  single point, `q` **is** `ℓ_u ∩ ℓ_v` (each leading line meets `L` by
  (BE-56)(ii), inside `σ`, and `L ∩ σ` is that one point), and
  `λ^{⊥K} ∩ Λ²σ = q ∧ σ = Λ_{uv}` exactly — so the rank-one kill step is
  **unchanged at every non-skew configuration, whatever forces it**.
  **(BE-144)**.
- **THE SKEWNESS CRITERION IS EXACT AND ITS FORCING LIST IS EXHAUSTIVE.**
  `ℓ_u`, `ℓ_v` are non-skew ⟺ `L ∩ π₁ = L ∩ π₂` ⟺ **`L` meets the line
  `π₁ ∩ π₂`** — a Schubert hyperplane section, codimension `1` in the
  4-dimensional Grassmannian. A dense open is not contained in a proper
  closed set, so the middle forces the regime for *every* admissible `L`
  **iff `π₁ = π₂` or `p_{w₁} = p_{w₂}`**: the `2 × 2` table over those two
  bits is enumerated and exactly three of its four cells force. **(S2)'s
  first half is PROVED**, and (BE-55)(iii)'s coverage, read through
  (BE-144), is **complete**. **(BE-145)**.
- **(S2)'s SECOND HALF IS REFUTED AS STATED.** *"No such mechanism is
  known"* — and the mechanism exists. At a **free** `L` no middle can pin
  `λ`: the admissible lines are a dense open of the Klein quadric `𝒬`, and
  `𝒬 ∩ P(W^{⊥K})` is proper closed for `t ≥ 1` because **`𝒬` spans
  `Λ²K⁴`**. But `p_{w₁} = p_{w₂} = p` forces `L` **through `p`**, the lines
  through `p` span the **self-conjugate** `Σ_p := p ∧ K⁴`, and therefore
  `λ ∈ W^{⊥K}` for every admissible `L` **⟺ `W ⊆ Σ_p`** — an equivalence,
  with **both** branches inhabited by real window middles (R-node middles
  among them). (BE-56)(ii)'s generic slice really is defeated there.
  **(BE-146)**.
- **AND IT CLOSES, BY A DIMENSION CAP RATHER THAN A REPAIRED GENERICITY —
  THE COINCIDENCE EXCESS LAW.** `Λ_{uv} ⊆ Σ_p` always at a coincident
  middle (both leading lines pass through `p`), so: **(a)** `W ⊆ Σ_p` ⟹ `λ`
  is pinned and `V = W`, but `W + Λ_{uv} ⊆ Σ_p` **caps `dim ρ̄₁ ≤ 3`**, and
  then `excess = t − (t + 2 − dim ρ̄₁) = dim ρ̄₁ − 2 ≤ 1`; **(b)** `W ⊄ Σ_p`
  ⟹ some line through `p` pairs nonzero with `W` (`Σ_p` is self-conjugate),
  so generic `L ∋ p` restores `dim V = t − 1` and (BE-56)(iii) runs
  **verbatim**. Either way **`excess ≤ 1` in the window**. Corollary worth
  its own line: `δ₁ = 4` **excludes case (a) outright**, so the window's
  hardest arithmetic row can only meet the coincidence regime through case
  (b), where nothing new is needed. **(BE-147)**.
- **HENCE (S1) IS REMOVABLE, NOT MERELY TRUE.** (BE-57)(i) used `p₁ ≠ p₂`
  **only** to make `ℓ_u`, `ℓ_v` skew; (BE-144) covers the non-skew case and
  (BE-147) covers the pinning, so the hypothesis is **deleted** and the
  window's class theorem is **unconditional on the window's own regime**
  (cross-incidence-free flags with `dim Z = 4`). Verified end to end at
  **100** coincident configurations over **20** shape-seeds — configurations
  the theorem's own hypothesis excluded — `dim Z = 4` at all of them, the
  identity at **all 80** with `dim ρ̄₁ ≤ 4` and at **none** of the 20 with
  `dim ρ̄₁ = 5`, which (BE-56)(iv) **requires** to fail. **(BE-148)**.
- **THE EVIDENCE SENTENCE FOR (S1) WAS CIRCULAR, and the guard it names does
  not do what it is named for.** (BE-57)(iv) offered *"both samplers reject
  coincidence, and every drawn middle satisfies it"*. Read at source:
  `bearcase.sample_piece_config` and `bsharp.sample_piece_config_adj` each
  carry `if len(set(pt.values())) != len(V): continue`, a **global**
  pairwise-distinctness filter — so the third clause is a property of the
  **filter**; `binduc.assert_generic_star` rejects coincidence only on
  **edges** (plus collinearity at distance `2`), and `dist_C(w₁,w₂) ≥ 3` in
  the window, so the named guard never reached (S1) at all;
  `kbare_common.verify_pencil_witness` — the pencil **predicate** — rejects
  only *adjacent* coincidence, so the **mathematics admits** the
  coincidence; and `bwin.resweep` rejects `rank(L + [p₁,p₂]) ≠ 4`, which
  `p₁ = p₂` makes unsatisfiable (**0 of 60** end draws over a constructed
  coincident middle survived). The case was invisible **three layers deep**.
  **(BE-142)**, and it is `RESEARCH-ARC.md` §4's BSATUR sharpening firing
  exactly as written.
- **Verdict: HIT shape 1 on both conditions, with a refutation attached.**
  One landed clause is **REFUTED** ((BE-57)(iv)'s *"no such mechanism is
  known"*), one landed hypothesis is **DELETED** ((BE-57)(i)'s (S1)), three
  landed surfaces are **annotated at source** (per F12) with every landed
  measurement intact. `PencilPair K 3 G`, `hbareSplit`, (BE-14)-for-all-`G`,
  the 2-cut step, S-mark, (BE-32)(+) and **half (B) at side-degree `≥ 2`**
  are untouched; **not a PENCIL event**. **(BE-148)**, classification below.
- **Reservation NOT fully consumed.** Labels **(BE-142)–(BE-148)** and
  *Steps BE141–BE147*; **(BE-149)** and *Step BE148* are **returned
  unused**.

### Standing notation (on top of *Steps BE53–BE57*)

Inherited verbatim: the middle `C`, `W := ρ̄_{w₁,w₂}(C)`, `t := dim W`,
`Λ_{uv} := ⟨ℓ_u, ℓ_v⟩`, `λ`/`μ` the Plücker points of `L := π_u ∩ π_v` and
`M := p_u ∨ p_v`, `V := W ∩ λ^{⊥K}`,
`excess := dim V − dim(V ∩ Λ_{uv})`, the boundary pencils
`T₁ := p_{w₁} ∧ π_{w₁}`, `T₂ := p_{w₂} ∧ π_{w₂}`, and `π₁ := π_{w₁}`,
`π₂ := π_{w₂}`. Added here:

- **`Σ_p := p ∧ K⁴`**, the 3-dimensional space of lines through a point `p`.
  It is **self-conjugate** — `Σ_p^{⊥K} = Σ_p`, since two lines through one
  point always meet and `dim = 6 − 3` — and it is the same object
  (BE-114)/(BE-116) write `Σ_x` on the half-(B) side, at a different vertex;
- **`σ := ℓ_u ∨ ℓ_v`** and **`q := L ∩ σ`**, when `ℓ_u`, `ℓ_v` are non-skew;
- the **coincidence regime**: the stratum `p_{w₁} = p_{w₂}` of the middle's
  pencil chart, on which (BE-55)(i)'s parametrization is **empty** and the
  honest end family is instead *a line `L` through `p`, two distinct planes
  `π_u`, `π_v` of the pencil through `L`, and `p_u ∈ π_u ∩ π₁`,
  `p_v ∈ π_v ∩ π₂`* — an iterated fibration with irreducible fibres over the
  irreducible `P²` of lines through `p`, hence **irreducible**, so
  (BE-25)(i)'s simultaneity argument applies to it unchanged.

**Carrier check, done off the landed bodies rather than the prose.** No new
Lean object is read. The three identities this direction consumes were
re-checked at their proof sites: (BE-54)(i)'s double peel (exact at *every*
configuration, which is what lets it be evaluated on a stratum no sampler
draws), (BE-55)(ii)'s Klein-perp computation (used only in its **skew**
branch, and replaced rather than extended in the non-skew one) and
(BE-56)(i)'s Grassmann count (pure linear algebra, hypothesis-free once
`dim Λ_{uv} = 2`). The screw-space convention is
`kbare_common.build_rigidity`'s own (`m_u − m_w ∈ K·ℓ_{uw}`), and `ρ̄` is
`binduc.rel_screw_space`'s image of `ker` under `m ↦ m(v) − m(u)`, read off
the driver chain. **No `.lean` was opened; the standing 2026-08-05 Lean hold
binds.**

### Step BE141 — (BE-142): the evidence sentence for (S1), and why it is circular

> **(BE-142)(i)** *(read at source; **THE FILTER IS THE FINDING**)*
> (BE-57)(iv) argues for (S1) that *"no arc mechanism forces two distinct
> vertices onto one point, **both samplers reject coincidence**, and every
> drawn middle satisfies it"*. The second clause and the third are the same
> fact: `bearcase.sample_piece_config` and `bsharp.sample_piece_config_adj`
> — the arc's only two middle samplers — each carry
>
> **`if len(set(pt.values())) != len(V): continue`**
>
> a **global** pairwise-distinctness filter over *all* vertices, adjacent or
> not. So *"every drawn middle satisfies (S1)"* is guaranteed by the
> sampler's support and carries no evidential weight whatever, and *"both
> samplers reject coincidence"* is the **reason**, not corroboration. ∎ This
> is `RESEARCH-ARC.md` §4's BSATUR sharpening — *name the sampler's support
> and ask which of the claim's own variables it varies* — firing on the
> claim's own variable, `p_{w₁} − p_{w₂}`.

> **(BE-142)(ii)** *(read at source; **the named guard does not reach the
> claim**)* `binduc.assert_generic_star` — the composite genericity guard,
> and the one (BE-57)(iv)'s phrase most naturally points at — asserts
> `pt[u] != pt[v]` **only for `(u,v) ∈ edges`**, plus non-collinearity on
> every path of length `2`. In the window `dist ≥ 5` forces
> `dist_C(w₁,w₂) ≥ 3` ((BE-47)(ii) and the *Standing notation* of *Step
> BE53*), so `w₁`, `w₂` are neither adjacent nor at distance `2`: **the
> guard does not reject (S1)'s coincidence.** ∎ Witness, exhibited: a legal
> pencil configuration of a 3-edge path with its two **ends** at the same
> point passes the guard.

> **(BE-142)(iii)** *(read at source; **the mathematics admits it**)*
> `kbare_common.verify_pencil_witness` — the pencil **predicate** itself,
> the independent check every draw in the arc goes through — returns a
> violation only for `pt[u] == pt[w]` with `(u,w) ∈ edges`, after requiring a
> nonzero common normal at each closed star. So the pencil condition
> **permits** `p_{w₁} = p_{w₂}` at `dist ≥ 3`; it is not excluded by any
> mechanism, and the witness of (ii) is accepted by it too. ∎ *There was
> never a mechanism to find: what (BE-57)(iv) called an absence of forcing
> is an absence of prohibition, which is the opposite claim.*

> **(BE-142)(iv)** *(measured; **the case is invisible three layers deep**)*
> `bwin.resweep` — the end sampler the whole (BE-57) construction runs
> through — returns `None` on `rank(L + [p₁, p₂]) != 4`, i.e. it demands
> that `L` be non-coplanar with `{p₁, p₂}`, which `p₁ = p₂` makes
> **unsatisfiable** (a line and a point are always coplanar). Over a
> constructed coincident middle of `barbell(1, θ(3,3,3), 1)`, **0 of 60**
> end draws survived. And (BE-55)(i)'s own *honest domain* says
> `p₁, p₂ ∉ L`, which by (BE-143)(i) is exactly `p₁ ≠ p₂` — so the
> parametrization the theorem is built on **excludes the stratum by
> hypothesis**. ∎ Middle sampler, star guard, end sampler: three
> independent layers, none of which could have produced a counterexample,
> and the fourth layer — the statement's own domain — quietly agrees.
> **The sentence is struck as evidence at source.**

### Step BE142 — (BE-143): the incidence lemma, and (S1)-failure IS (S2)'s regime

> **(BE-143)(i)** *(proven; **THE INCIDENCE LEMMA**, and it is two lines)*
> At **every** pencil configuration of a both-ends-series piece, the pencil
> condition at `u` makes `u`'s closed star `{p_u, p_{w₁}} ∪ A`-neighbours
> coplanar in `π_u`, so **`p_{w₁} ∈ π_u`**; symmetrically **`p_{w₂} ∈
> π_v`**. Hence
>
> **`p_{w₁} = p_{w₂} ⟹ p_{w₁} ∈ π_u ∩ π_v`,**
>
> which at `π_u ≠ π_v` reads `p_{w₁} ∈ L`. Contrapositive, in the form the
> parametrization uses: **`p_{w₁} ∉ π_v` (or `p_{w₂} ∉ π_u`) ⟹ `p_{w₁} ≠
> p_{w₂}`**, so (BE-55)(i)'s domain condition `p₁, p₂ ∉ L` **is** (S1) at
> the configuration level, not an extra requirement beside it. ∎ Asserted
> per draw at all **80** constructed coincidence configurations
> (`p_{w₁} ∈ π_u`, `p_{w₂} ∈ π_v`, `p ∈ L`, `L = π_u ∩ π_v`, each an
> identity or an incidence of spaces).

> **(BE-143)(ii)** *(proven; **COINCIDENCE FORCES THE MEETING-LINES
> REGIME**)* `ℓ_u = p_u ∨ p_{w₁}` and `ℓ_v = p_v ∨ p_{w₂}` are the two
> leading lines ((BE-45)(i)'s leaf collapse names them). At
> `p_{w₁} = p_{w₂} = p` they **both pass through `p`**, hence **meet**, and
> they are distinct (`ℓ_u = ℓ_v` would put `p_v ∈ ℓ_u ⊆ π_u`, a terminal
> cross-incidence). So `dim Λ_{uv} = 2` still, `Λ_{uv}` is the pencil of
> lines through `p` inside `σ = p ∨ M`, and the regime (BE-55)(iii) treats
> is **entered for every admissible `L`**. ∎ Asserted at all 80: `ℓ_u`,
> `ℓ_v` non-skew (`rank = 3`), `ℓ_u ∩ ℓ_v = p` as a space, and
> **`π₁ ≠ π₂` throughout** — so these are *not* (BE-55)(iii)'s own case.

> **(BE-143)(iii)** *(the consequence for the two conditions, said plainly)*
> **(S1) and (S2) are ONE gap.** (S1) failing at a middle *is* a middle
> forcing the meeting-lines regime by a relation other than `π₁ = π₂` —
> precisely the object (BE-57)(iv)'s (S2) says *"would need its own
> argument"* and *"no such mechanism is known"*. Recording them as two
> independent side conditions, one *"checkable per middle"* and one an
> asserted absence, hid the implication. ∎ *The arc's own labelling was the
> obstacle: (S1) was filed as a hypothesis about the middle's points and
> (S2) as a hypothesis about its flags, and they are the same hypothesis.*

> **(BE-143)(iv)** *(constructed; **the stratum is INHABITED at real window
> middles**, and it is not a path-piece artefact)* Coincident middles are
> built by (BE-48)'s parametrization run **planes-first**: pick the shared
> point `p`, then choose the plane at every branch vertex, forcing it
> through `p` at exactly those branch vertices whose closed star must
> contain `p` (`w₁`, `w₂` when they are branch, and every branch neighbour
> of either); the points then drop out, and legality is the pencil condition
> itself, checked by **both** gates. **20 shape-seeds** over **10** distinct
> shapes: BWIN's five landed window barbells, its **four-branch theta**, its
> **two R-node middles** (a subdivided `K₄` between two branch vertices,
> wrapped) and two **theta chains with a 3-edge bridge**. `dim Z = 4` and
> terminal cross-incidence-freeness hold at every one. ∎ Two of BWIN's
> twelve `wide` rows fall outside this sampler's shape guard — disclosed in
> *Caps*, and the longer-bridge chains are the repair.

### Step BE143 — (BE-144): the coplanar-boundary lemma — (BE-55)(iii) is plane-agnostic

> **(BE-144)(i)** *(proven; **THE COPLANAR-BOUNDARY LEMMA**)* Let a
> configuration be cross-incidence-free at the terminals with `π_u ≠ π_v`,
> and suppose `ℓ_u ≠ ℓ_v` are **non-skew**. Put `σ := ℓ_u ∨ ℓ_v` (a plane)
> and `q := L ∩ σ`. Then
>
> - **`L ⊄ σ`**: `ℓ_u ≠ L` (else `p_u ∈ L ⊆ π_v`, a cross-incidence) and
>   `L, ℓ_u ⊆ π_u`, so `L ∨ ℓ_u = π_u`; if `L ⊆ σ` then `σ ⊇ π_u` and
>   likewise `σ ⊇ π_v`, forcing `π_u = π_v`. So `q` is a **single point**;
> - **`q = ℓ_u ∩ ℓ_v`**: by (BE-56)(ii) each leading line meets `L` (it is
>   coplanar with `L` inside `π_u`, resp. `π_v`), and the meeting point lies
>   in `L ∩ σ = {q}`, so `q ∈ ℓ_u` and `q ∈ ℓ_v`;
> - **`span(ℓ_u ∧ ℓ_v) = Λ²σ`** (3-dimensional: with `ℓ_u = ⟨e₀,e₁⟩`,
>   `ℓ_v = ⟨e₀,e₂⟩` the wedges span `Λ²⟨e₀,e₁,e₂⟩`), and
>   **`(Λ²σ)^{⊥K} = Λ²σ`** (isotropic, `dim 3 = 6 − 3`);
> - **`λ^{⊥K} ∩ Λ²σ = q ∧ σ = Λ_{uv}`**: the lines of `σ` conjugate to `λ`
>   are exactly those meeting `L`, i.e. those through `q`; and `ℓ_u ≠ ℓ_v`
>   are two of them, so they span that 2-dimensional pencil.
>
> Hence `V ∩ (span(ℓ_u ∧ ℓ_v))^{⊥K} ⊆ Λ_{uv}`, and the kill step is
> unchanged: any `x ∈ V ∖ Λ_{uv}` lies outside `Λ²σ` and is therefore
> killable by one `μ`. ∎ **This is (BE-55)(iii)'s argument verbatim with `π`
> replaced by `σ`** — every step of it used `π` only as *a plane containing
> both leading lines with `L` outside it*.

> **(BE-144)(ii)** *(the annotation this earns, per F12)* **(BE-55)(iii)'s
> scope statement is UNDERSTATED, not wrong.** Its hypothesis — *"if the
> middle forces its boundary planes equal"* — and its parenthetical
> *"conceivable at `dist_C ≥ 3` only through a forced-same-plane chain …
> both proved mechanisms need `dist ≤ 2` and are excluded here"* read as if
> the regime were both **unreachable** in the window and **covered only
> under `π₁ = π₂`**. The first half is what (BE-143)(iv) refutes; the second
> half is what this step corrects, and the correction costs nothing because
> the proof already had the generality. Its **cap 3** disclosure — *"no
> drawn middle forces the regime, so it is covered by lemma, not by
> battery"* — is likewise superseded: a drawn middle now does. ∎ *No landed
> measurement moves; the twelve synthetic trials stay exactly as strong as
> they were, and are re-run here in the lemma's general form.*

> **(BE-144)(iii)** *(measured; **three independent populations, and the
> middle one is the load-bearing one**)* The lemma is asserted as identities
> of **spaces** at: **60** synthetic `π₁ = π₂` flag data (BE-55)(iii)'s own
> case; **60** synthetic data with an **arbitrary** non-skew pair, `σ`
> forced by nothing and equal to no boundary plane — this is the population
> that establishes *plane-agnostic*, since the landed trials could only ever
> instantiate `σ = π`; and **60** configurations over the 20 real coincident
> shape-seeds, at which `σ = p ∨ M` is asserted **distinct from both**
> boundary planes and `q` asserted **equal to the shared point**. ∎ In the
> synthetic populations `L` is **not** drawn freely: (BE-56)(ii) makes both
> leading lines meet it, so `L ⊄ σ` forces `L` through `q`, and drawing it
> as `q ∨ r` with `r ∉ σ` is the honest domain rather than a convenience.

### Step BE144 — (BE-145): the skewness criterion, and the forcing list is exhaustive

> **(BE-145)(i)** *(proven; **THE EXACT CRITERION**)* On (BE-55)(i)'s
> domain, `ℓ_u = π_u ∩ π₁` and `ℓ_v = π_v ∩ π₂`, with `L ⊆ π_u ∩ π_v`. Two
> distinct lines meet iff coplanar, and any common point of `ℓ_u`, `ℓ_v`
> lies in `π_u ∩ π_v = L`; since `ℓ_u`, `L` are two distinct lines of the
> plane `π_u` they meet, at `ℓ_u ∩ L = π₁ ∩ L`. Hence
>
> **`ℓ_u`, `ℓ_v` non-skew ⟺ `L ∩ π₁ = L ∩ π₂` ⟺ `L` meets the line
> `π₁ ∩ π₂`.**
>
> ∎ Both readings asserted **equal to the skewness fact itself** at
> **200 of 200** draws with `π₁ ≠ π₂`, and non-skew at **0** of them — which
> is what a random draw must give against a codimension-`1` locus.

> **(BE-145)(ii)** *(proven; **THE FORCING LIST IS EXHAUSTIVE AT TWO**)*
> `{L : L` meets `π₁ ∩ π₂}` is a **Schubert hyperplane section** of the
> Klein quadric — closed of codimension `1` in the 4-dimensional
> Grassmannian — whenever `π₁ ≠ π₂`; and when `p₁ ≠ p₂` the admissible `L`
> are a **dense open** of that irreducible 4-fold (removing `{L ∋ p_i}`,
> codimension `2` each, and `{L` meets `p₁ ∨ p₂}`, codimension `1`). A dense
> open is **not contained** in a proper closed set. Therefore a middle
> forces the regime at every admissible `L` **iff** `π₁ = π₂` (the locus is
> a plane, met by every line) **or** `p₁ = p₂` (the shared point lies on
> `π₁ ∩ π₂` **and**, by (BE-143)(i), on every admissible `L`). ∎ The `2 × 2`
> table over `(π₁ = π₂?, p₁ = p₂?)` is **enumerated**, not sampled: cell
> `(≠, ≠)` **cannot** force (the argument above, with 0/200 as
> corroboration); `(=, ≠)` forces, at 80/80 lines; `(≠, =)` forces, at 25
> configurations over 5 shapes; `(=, =)` forces **a fortiori** by the first
> mechanism, so no independent witness is claimed for it. Exactly **three of
> four** cells force, and the two mechanisms are all there are.

> **(BE-145)(iii)** *(the consequence for (S2)'s first half)* **PROVED.**
> (BE-57)(iv)'s hedge — *"handled by (BE-55)(iii) only when the forced
> equality is of the boundary planes"* — is answered in both directions:
> the regime has exactly two forcing mechanisms ((ii)), and (BE-144) covers
> **both** with (BE-55)(iii)'s own argument. Nothing about the second
> mechanism needed a separate treatment of the *kill step*; what it needed,
> and did not have, was a treatment of the **excess bound**, which is
> (BE-146)/(BE-147). ∎ *That split is the whole reason this half was
> tractable and the other half was not.*

### Step BE145 — (BE-146): `λ` cannot be pinned at a free `L`, and IS pinned at a coincident middle

> **(BE-146)(i)** *(proven; **IMPOSSIBLE AT A FREE `L`**)* `λ` is the
> Plücker point of `L`, and `L` is **end** data: (BE-55)(i) makes it a free
> line subject only to `p₁, p₂ ∉ L` and non-coplanarity with `{p₁, p₂}`.
> `W^{⊥K}` is a fixed linear subspace of dimension `6 − t` determined by the
> middle alone. Since the Klein quadric `𝒬` **spans** `Λ²K⁴` (asserted: 6
> Plücker points of drawn lines reach rank 6), `𝒬 ⊆ P(W^{⊥K})` is
> impossible for `t ≥ 1`, so `𝒬 ∩ P(W^{⊥K})` is **proper closed** in the
> irreducible 4-fold `𝒬` and the dense-open admissible set meets its
> complement. At `t = 0`, `V = 0` and `excess = 0` outright — (BE-56)(iii)'s
> own `max` covers it. ∎ Census over **120** admissible draws at each
> `t = 0…5`: pinned at `120, 0, 0, 0, 0, 0`. **A middle cannot reach a
> proper linear condition on `λ` through two points** — the boundary flags
> constrain `π_u`, `π_v` *given* `L` and place no condition on `L` beyond
> those two.

> **(BE-146)(ii)** *(proven; **REAL AT A COINCIDENT MIDDLE**, and it is an
> equivalence)* At `p₁ = p₂ = p` the honest end family has `L ∋ p`
> ((BE-143)(i)) — a **codimension-2** restriction the free regime never
> sees. The lines through `p` span `Σ_p`, and `Σ_p` is **self-conjugate**,
> so `⋂_{L ∋ p} λ^{⊥K} = (Σ_p)^{⊥K} = Σ_p` and
>
> **`λ ∈ W^{⊥K}` for every admissible `L` ⟺ `Σ_p ⊆ W^{⊥K}` ⟺ `W ⊆ Σ_p`.**
>
> ∎ Asserted as an equivalence at all **60** coincidence configurations of
> the `pin` population, and **both branches are inhabited by real window
> middles**: `W ⊆ Σ_p` at **16** shape-seeds (the five barbells, the
> four-branch theta and **both R-node middles**), `W ⊄ Σ_p` at **4** (the
> two longer-bridge theta chains). No middle is mixed — the branch is a
> property of the middle, not of the end draw.

> **(BE-146)(iii)** *(classification of the landed clause; **REFUTED AS
> STATED**)* (BE-57)(iv)'s (S2) says a middle *"forcing some other algebraic
> relation between its boundary flags that pins `λ` onto `W^{⊥K}`
> (defeating (BE-56)(ii)'s generic slice) would need its own argument — no
> such mechanism is known"*. **The mechanism is `p_{w₁} = p_{w₂}`**, it
> defeats the generic slice exactly as feared (`dim V = t`, not `t − 1`),
> and it is realized at real window middles including R-node ones. So the
> asserted absence is **false**, and the clause's own conditional obligation
> — *"would need its own argument"* — is **triggered**. (BE-147) is that
> argument. ∎ *This is the sixth clause of this shape to fall in this
> section, after (BE-41)(ii), (BE-66)(iv), (BE-109)(iv), (BE-110)(iv) and
> (BE-134)(i); every one was an asserted absence backed by a population that
> could not contain the witness.*

> **(BE-146)(iv)** *(why the landed measurement could not have seen it, and
> the figure)* `bwin.full_measure` — the landed measurement of *Steps
> BE53–BE56* — carries `assert dim(V) <= max(0, t - 1)` labelled
> `(BE-56)(ii)`. On the coincidence stratum that assert **fires**, at
> **30 of 100** rows of the `ident` population (exactly the case-(a) rows
> with `t ≥ 1`). ∎ So the defect was not that a driver ran wrong: the driver
> asserted the right thing and **could not be run** where the claim needed
> testing. That is the quantitative form of (BE-142), and it is why this
> direction writes its own `coin_measure` rather than reusing
> `full_measure`.

### Step BE146 — (BE-147): the coincidence excess law — the budget survives, by a dimension cap

> **(BE-147)(i)** *(proven; **CASE (a): `W ⊆ Σ_p` CAPS `dim ρ̄₁ ≤ 3`**)*
> Both leading lines pass through `p`, so **`Λ_{uv} ⊆ Σ_p`** always at a
> coincident middle. If also `W ⊆ Σ_p` then, by (BE-54)(i)'s peel,
>
> **`ρ̄₁ = Λ_{uv} + W ⊆ Σ_p`, so `dim ρ̄₁ ≤ dim Σ_p = 3`,**
>
> and `V = W ∩ λ^{⊥K} = W` (the pinning, (BE-146)(ii)), so with
> (BE-56)(i)'s count `dim(W ∩ Λ_{uv}) = t + 2 − dim ρ̄₁`,
>
> **`excess = t − (t + 2 − dim ρ̄₁) = dim ρ̄₁ − 2 ≤ 1`.** ∎
>
> The generic slice is **not repaired here — it is replaced**, by a
> dimension cap that is a *consequence of the same coincidence* that broke
> it. Asserted at every case-(a) row: `Λ_{uv} ⊆ Σ_p`, `V = W`,
> `dim ρ̄₁ ≤ 3` and `excess = dim ρ̄₁ − 2` **exactly** — census
> `(dim ρ̄₁, t, excess) ∈ {(2,0,0), (3,1,1), (3,2,1)}` at 40/16/8 of the
> `law` population's 80 rows.

> **(BE-147)(ii)** *(proven; **CASE (b): the generic slice is RESTORED**)*
> If `W ⊄ Σ_p` then, `Σ_p` being self-conjugate, `Σ_p ⊄ W^{⊥K}`, so **some
> line through `p` pairs nonzero with `W`**; the pinned locus is a proper
> closed subset of the irreducible 2-dimensional family `{L ∋ p}`, and
> generic `L ∋ p` gives `dim V = t − 1`. Also `Λ_{uv} ⊆ λ^{⊥K}` still (both
> leading lines contain `p ∈ L`, hence meet `L`), so `W ∩ Λ_{uv} ⊆ V` and
> (BE-56)(iii) runs **verbatim**: `excess ≤ max(0, dim ρ̄₁ − 3)`. ∎ Measured
> at the 16 case-(b) rows: `dim V = t − 1 = 2` and
> `(dim ρ̄₁, t, excess) = (5, 3, 2)` at every one — the excess law tight,
> and `dim ρ̄₁ = 5` puts them **outside** the window, where (BE-56)(iv)
> requires failure.

> **(BE-147)(iii)** `[PROVED]` *(the law, and its corollary)* **At a coincident middle
> `excess ≤ 1` whenever `dim ρ̄₁ ≤ 4`** — by (i) when `W ⊆ Σ_p` and by (ii)
> otherwise — so the rank-one budget of (BE-55)(iv) is met and the window
> identity follows by (BE-144)'s kill step. **Corollary:** case (a) forces
> `dim ρ̄₁ ≤ 3`, so **`δ₁ = 4` excludes case (a) outright** and the
> window's hardest arithmetic row can only meet the coincidence regime
> through case (b), where nothing beyond (BE-56)(iii) is used. ∎ Verified
> both branches in pure linear algebra as well: **80** abstract `W ⊆ Σ_p`
> and **80** abstract `W ⊄ Σ_p`, with the pinning asserted at *every* line
> through `p` in the first and at *not every* one in the second.

> **(BE-147)(iv)** *(what this does NOT establish, stated before the
> verdict)* It does **not** show that the coincidence locus can be
> `δ₁`-**attaining** — no coincident middle here is claimed to attain, and
> the question is left **open**. After (BE-148) it is also **immaterial**:
> with (S1) deleted the theorem quantifies over the attaining middle
> whatever its boundary points do, so attainment on the coincidence stratum
> stops being a hypothesis anything rests on. It does **not** touch
> (BE-56)(ii) off the coincidence stratum, where (BE-146)(i) stands. And it
> does **not** reach a case-(b) coincident middle with `δ₁ = 4`: all four
> measure `5`. ∎ *Disclosed in* Caps *rather than smoothed.*

### Step BE147 — (BE-148): (S1) is REMOVABLE, and the board

> **(BE-148)(i)** *(proven; **THE HYPOTHESIS IS DELETED**)* (BE-57)(i)'s
> proof invokes `p₁ ≠ p₂` at exactly one place — *"the boundary lines are
> skew when `p₁ ≠ p₂` and the boundary planes differ"*. Replace that
> sentence by the dichotomy of (BE-145)(i): at generic `L` the lines are
> skew unless the middle forces otherwise, and if they are non-skew
> (BE-144) supplies the same survivor slice `λ^{⊥K} ∩ span(ℓ_u ∧ ℓ_v) =
> Λ_{uv}`; the excess bound is (BE-56)(iii) when `λ` is generic and
> (BE-147) when it is pinned. Every other ingredient — the peel (BE-54)(i),
> the perp form (BE-54)(ii), the modular law (BE-54)(iii), the Grassmann
> count (BE-56)(i), the rank-one kill — is hypothesis-free in `p₁` versus
> `p₂`. Hence
>
> **(BE-57)(i) holds with (S1) DELETED**, for every both-ends-series piece
> with `δ₁ ≤ 4`, on a dense open subset of the honest end family over a
> `δ₁`-attaining middle — (BE-55)(i)'s family when `p₁ ≠ p₂`, the
> coincidence family (irreducible, *Standing notation*) when `p₁ = p₂`. ∎

> **(BE-148)(ii)** *(measured; **the conclusion at the excluded stratum**)*
> **100** coincidence configurations over 20 shape-seeds, every one through
> `assert_generic_star` **and** `verify_pencil_witness`, with `coin_measure`
> asserting each of (BE-54)(i)/(ii)/(iii), (BE-55)(i)'s two vanishings,
> (BE-144)'s five space identities, (BE-56)(i)'s count, both branches of
> (BE-147) and `W ∩ Z = ker(φ|_V)` at each: `dim Z = 4` at **100/100**; the
> identity `ρ̄₁ ∩ Z = Λ_{uv}` **and** (b1) `ρ̄₁ ∩ Π_u = ⟨ℓ_u⟩` at **all 80**
> rows with `dim ρ̄₁ ≤ 4`; and the identity **failing at all 20** rows with
> `dim ρ̄₁ = 5`, which (BE-56)(iv) requires. Census
> `(dim ρ̄₁, t, excess)`: `(2,0,0)` 50, `(3,1,1)` 20, `(3,2,1)` 10,
> `(5,3,2)` 20. ∎ **Non-vacuous in both directions** — the driver would have
> caught a false positive at the `δ₁ = 5` rows and a false negative in the
> window, and it reports both.

> **(BE-148)(iii)** *(the annotations this landing owes, per F12 — three
> landed surfaces, none refuted in its measurement)*
>
> 1. **(BE-57)(i)** — hypothesis **(S1) deleted**; the conclusion's *"end
>    resweep family"* is generalized to *the honest end family*, which is
>    (BE-55)(i)'s on the complement of the coincidence stratum.
> 2. **(BE-55)(iii)** — scope **understated**: the argument is
>    plane-agnostic ((BE-144)(ii)), and its **cap 3** *"no drawn middle
>    forces the regime"* is superseded by (BE-143)(iv).
> 3. **(BE-56)(ii)** — its generic slice **is** defeated on the coincidence
>    stratum ((BE-146)(ii)); the step stands verbatim off that stratum, and
>    (BE-147) is what covers it on it.
>
> **(BE-57)(iv) as a whole is SUPERSEDED**: it is no longer a pair of side
> conditions but a decided pair — one removable, one a theorem plus a
> refuted-and-then-closed clause. Its *"vacuous at every drawn piece"* is
> exactly the sentence (BE-142) strikes. ∎

> **(BE-148)(iv)** *(classification, mandatory and explicit)* **Nothing the
> arc carries is refuted.** Not `PencilPair K 3 G`; not `hbareSplit`; not
> (BE-14)-for-all-`G`; not the 2-cut step; not **S-mark**; not (BE-32)(+);
> not the short-cycle law; not BSHARP's dichotomy; not BRULE's separation
> theorem; not (BE-58)(i)–(iv); and **not half (B) at side-degree `≥ 2`**,
> whose obstruction remains the **METHOD** ((BE-139)) — closing (S1)/(S2)
> does **not** close S-mark, and (BE-14) needs both halves. What **is**
> refuted is one clause of one landed statement, (BE-57)(iv)'s *"no such
> mechanism is known"* ((BE-146)(iii)); what is **deleted** is one
> hypothesis, (S1); what is **struck as evidence** is one sentence,
> (BE-57)(iv)'s sampler argument for (S1). **Every landed measurement is
> intact** — BWIN's 358 guarded draws, the 160-of-160 `cls` census, the
> 84/84 per-`L` criterion, the 42-draw excess census and (BE-58)(ii)'s five
> modes are cited and unmoved. **No route is closed; no route is opened.**
> **Not a PENCIL event.**

### Verdict, classification, and the price

| claim | verdict |
|---|---|
| (BE-142)(i)–(iv) the support audit: the (S1) evidence sentence is circular; the named guard, the pencil predicate and the end sampler each miss or admit the coincidence | **PROVED at source** (three landed guards read, one witness constructed, 0/60 end draws) |
| (BE-143)(i) the incidence lemma `p_{w₁} ∈ π_u`, `p_{w₂} ∈ π_v` ⟹ coincidence lands on `L` | **PROVED**; asserted per draw at 80 configurations |
| (BE-143)(ii)/(iii) coincidence forces the meeting-lines regime, so (S1) and (S2) are ONE gap | **PROVED**; `π₁ ≠ π₂` asserted at every one, so it is not (BE-55)(iii)'s case |
| (BE-143)(iv) the stratum is inhabited at real window middles | **CONSTRUCTED**, 20 shape-seeds / 10 shapes, R-node middles among them |
| (BE-144)(i) the coplanar-boundary lemma | **PROVED**; five identities of spaces at 60 + 60 + 60 draws |
| (BE-144)(ii) (BE-55)(iii)'s scope is understated, its cap 3 superseded | **PROVED** (annotation; no measurement moves) |
| (BE-145)(i) the exact skewness criterion, both readings | **PROVED**; asserted equal to the fact at 200/200 |
| (BE-145)(ii) the forcing list is EXHAUSTIVE at two mechanisms | **PROVED** by a `2 × 2` enumeration + a dense-open-vs-proper-closed argument (a sample cannot establish "the only") |
| (BE-145)(iii) **(S2)'s first half** | **PROVED** |
| (BE-146)(i) `λ` cannot be pinned at a free `L` | **PROVED** (`𝒬` spans `Λ²K⁴`); census 0 at every `t ≥ 1` over 120 draws each |
| (BE-146)(ii) at a coincident middle, pinned ⟺ `W ⊆ Σ_p` | **PROVED**; asserted as an equivalence at 60, both branches inhabited (16 / 4 shape-seeds) |
| (BE-146)(iii) **(S2)'s second half as stated** | **REFUTED** — the mechanism exists and is (S1) failing |
| (BE-146)(iv) the landed measurement's own `(BE-56)(ii)` assert fires on the stratum | **MEASURED**, 30 of 100 rows |
| (BE-147)(i)/(ii)/(iii) the coincidence excess law, both branches, and `δ₁ = 4` excluding case (a) | **PROVED**; `excess = dim ρ̄₁ − 2` asserted at every case-(a) row, `dim V = t − 1` at every case-(b) row |
| (BE-147)(iv) whether the coincidence locus ATTAINS | **OPEN, and IMMATERIAL after (BE-148)(i)** |
| (BE-148)(i) **(S1) is REMOVABLE** — (BE-57)(i) holds with it deleted | **PROVED** |
| (BE-148)(ii) the identity + (b1) at the excluded stratum | **MEASURED** 80/80 in-window, 0/20 at `dim ρ̄₁ = 5` (required to fail) |
| (BE-148)(iii)/(iv) the three annotations and the classification | **PROVED**; nothing the arc carries is refuted |

**The price.** (β) at the window no longer carries a side condition: the
class theorem is **unconditional on the window's own regime**. What that
does *not* buy is named in (BE-148)(iv) — S-mark's other half, half (B) at
side-degree `≥ 2`, is untouched and its obstruction is still the **METHOD**
((BE-139)). The cost paid: one landed clause refuted, one hypothesis
deleted, one sampler argument struck, three surfaces annotated, and **no
landed measurement moved**.

### Verification

Driver `notes/scripts/w4/bscond.py`, eight modes, `validate` **229 s** (fits
the 600 s foreground budget); every rng seeded from the printed literal
`20260829` (`bwin.SEED`), all exact ℚ, every subspace claim an identity of
spaces.

| mode | what it asserts | figure |
|---|---|---|
| `support` | (BE-142): three landed guards read at source; the coincident-middle witness accepted by guard and predicate; `bwin.resweep` on a coincident middle | 0/60 end draws survive; 0 s |
| `incid` | (BE-143): the incidence lemma, `p ∈ L`, `ℓ_u ∩ ℓ_v = p`, `π₁ ≠ π₂`, per draw | 20 shape-seeds, **80** configurations; 0 s |
| `cover` | (BE-144): five space identities in three populations | 60 + 60 + 60; 1 s |
| `crit` | (BE-145): both readings of the criterion vs the fact; the `2 × 2` table | 200/200, 0 non-skew; 80/80 + 25 (5 shapes); 0 s |
| `pin` | (BE-146): `𝒬` spans; the free-`L` census; the coincidence equivalence | 6 → rank 6; 120 × 6 draws; **60**, 16 / 4 shape-seeds; 17 s |
| `law` | (BE-147): both branches abstractly and at real middles | 80 + 80 abstract; **80** configurations; 57 s |
| `ident` | (BE-148): the identity, (b1), `dim Z = 4`, and `full_measure`'s own assert | **100** configurations, 80 in-window all holding, 20 at `δ₁ = 5` all failing, 30 firing; 143 s |
| `board` | the support audit and the caps (`RESEARCH-ARC.md` §4 + §5) | 7 populations named; 0 s |

**405 guarded coincidence configurations** in total across the six drawing
modes, each through `binduc.assert_generic_star` **and**
`kbare_common.verify_pencil_witness`, with the coincidence itself the only
repeated point.

### Caps, disclosed rather than smoothed — with the denominator named

1. **Every battery piece has `deg(u) = deg(v) = 1`** — bwin's own disclosed
   cap, inherited through `series_data`. The general `A`-side is
   (BE-57)(ii)'s `PGL(4)` move: prose then, prose now, and untouched here.
2. **The coincidence sampler's shape guard.** It supports middles whose
   branch set is **independent** with every free vertex carrying at most one
   branch neighbour — `bearcase.sample_piece_config`'s guard, **not** a
   claim about the window's extent ((BE-58)(i) owns that). **Two of BWIN's
   twelve `wide` rows fall outside it** (the two short-bridge theta chains,
   which have adjacent branch vertices or a free vertex with two branch
   neighbours); the two 3-edge-bridge chains added here are the repair, and
   **both R-node middles and the four-branch theta are inside it**.
3. **No coincident row reaches `δ₁ = 4`.** In case (a) that is a
   **theorem**, not a gap — `Σ_p` caps `dim ρ̄₁ ≤ 3` ((BE-147)(i)). In case
   (b) a `δ₁ = 4` coincident middle is **not found under this cap** (all
   four case-(b) rows measure `5`), and it is covered by (BE-56)(iii)
   verbatim rather than by a row.
4. **No coincident middle is claimed `δ₁`-attaining** ((BE-147)(iv)).
5. **The free-`L` census is corroboration, not proof.** (BE-146)(i)'s
   0-at-every-`t ≥ 1` is a *not-found-under-cap* reading of 120 draws each;
   the proof is the proper-closed argument, and by (BE-37)(i)(2) the sample
   errs in the safe direction.
6. **Every figure is a count over CONSTRUCTED populations.** None is a
   class-level rate; no shape count is a statement about how many window
   pieces reach the coincidence stratum.

### Harness note — `w4/bscond.py`, and the two silent hazards navigated

`bscond.py` imports `bwin`, `bsharp`, `bimage`, `binduc`, `bearcase`,
`kbare_common` and `exactcore` read-only, so the recorded **unpaid**
`kbare/` sibling-import debt (`notes/scripts/README.md` *Harness debt*)
gains its next `w4/` consumer and the chain is one deeper —
`bscond → bwin → bsharp → bearfull → bearcase → bimage → btwocut → binduc →
bzavoid → kbare_common`. **NO MOVE MADE**, per the same rule.

**Both recorded silent hazards were navigated rather than tripped, and
neither needed a new guard.** `bimage.pt_in`'s `K⁴` truncation: no `Λ²`-side
draw goes through it (this module never calls it). `bimage.span`/`isect`'s
width-6-only special case: every `K⁴` subspace here goes through
`bwin.k4_span` / `bwin.k4_isect`, which are the pre-existing guarded
versions in the layer this module succeeds — so **no new wrapper is minted**
and `bdegtwo.k4span`/`k4meet` are left alone.

**One genuine friction, recorded because it is a trap for the next
direction:** `bwin.dehom` returns a **list**, while every sampler in the
tree stores points as **tuples**. A list is unhashable, so a
`len(set(pt.values()))` check raises, and — worse — it compares **unequal**
to a tuple, so `assert_generic_star`'s `pt[u] != pt[v]` edge check silently
passes for any edge with one endpoint written by `dehom` and the other by a
sampler. `bscond.aff` is the local one-line fix (`tuple(dehom(x))`) and
carries the warning at its definition. **No landed figure is affected** —
`bwin` writes only the two terminals through `dehom`, and their adjacency
distinctness is separately implied by the cross-incidence checks — but a
future module that writes an interior vertex that way would lose the guard.

### Confidence verdicts, per claim

- **PROVEN INFORMALLY, no gap:** (BE-143)(i)/(ii)/(iii), (BE-144)(i)/(ii),
  (BE-145)(i)/(ii)/(iii), (BE-146)(i)/(ii)/(iii), (BE-147)(i)/(ii)/(iii),
  (BE-148)(i)/(iii)/(iv). Each is elementary projective geometry or linear
  algebra over the landed peel; each is asserted per draw as identities of
  spaces.
- **CONSTRUCTED / MEASURED:** (BE-142)(iv) (0/60), (BE-143)(iv) (20
  shape-seeds), (BE-146)(iv) (30/100), (BE-148)(ii) (100 configurations).
- **OPEN, and immaterial after (BE-148)(i):** whether the coincidence
  stratum can be `δ₁`-attaining ((BE-147)(iv)).
- **NOT-FOUND-UNDER-CAP:** a case-(b) coincident middle with `δ₁ = 4` (cap
  3); the free-`L` pinning census (cap 5).

### What would change this

- **A both-ends-series middle in the window with `δ₁ = 4` and `W ⊄ Σ_p` at a
  coincident configuration whose `excess` exceeds `1`** would refute
  (BE-147)(ii) — it cannot, since that branch is (BE-56)(iii) verbatim, but
  it is the row the battery does not reach and therefore the row to build if
  the law is doubted.
- **A middle whose boundary flags satisfy an algebraic relation OTHER than
  `π₁ = π₂` and `p₁ = p₂` that forces the meeting-lines regime** would
  refute (BE-145)(ii). The `2 × 2` table's completeness rests on
  (BE-55)(i)'s honest domain reading **exactly** those two data off the
  middle; a parametrization that reads a third would reopen it.
- **A cross-incidence-free configuration with `π_u ≠ π_v` at which
  `L ⊆ σ`** would break (BE-144)(i)'s first bullet and with it the whole
  lemma; the bullet derives `L ⊄ σ` from `π_u ≠ π_v` alone, so such a
  configuration would contradict elementary incidence.
- **A demonstration that half (B) at side-degree `≥ 2` is closed** would
  make this landing S-mark's last step rather than one of two; nothing here
  bears on it.

## TERMINATION check (E1/E2/E3) — read at source, decided explicitly

Read at `notes/pencil/fanout-archive.md` (the ledger's own statement, not by
analogy), each decided:

- **(E1)** — *a g-flank: a `D = 0` shape whose every admissible colouring is
  binding, refuting per-shape (GR-15)*. **DOES NOT FIRE.** This direction is
  on the `(K-bare)` line and exhibits no colouring object at all; (GR-15) is
  untouched.
- **(E2)** — *the target is refuted or unprovable-as-posed **and** no ledger
  entry is left open-with-a-named-dispatchable-attack*. **DOES NOT FIRE**,
  on **both** conjuncts: what is refuted is one *clause* of one landed
  statement, and the target ((BE-14), and S-mark under it) is **advanced**
  rather than refuted — half (β)'s window residue is discharged. The
  remaining ledger entry, half (B) at side-degree `≥ 2`, is open with a
  named dispatchable attack ((BE-139)(iv), (BE-140)).
- **(E3)** — *the target is **proven** and every remaining ledger entry is
  adjudication-gated rather than dispatchable*. **DOES NOT FIRE**: (BE-14),
  `hbareSplit` and `hK` are untouched, S-mark's other half is open, and
  dispatchable entries remain. **A window condition closing is not a target
  closing** — the phase-boundary consequence is **reported, not acted on**.

**Per the "otherwise" clause the natural next step is a further direction**;
this landing does not prep one. See `notes/Phase39.md` *Hand-off*.
