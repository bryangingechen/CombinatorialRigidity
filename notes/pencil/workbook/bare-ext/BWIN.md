## §(K-bare-ext) — continuation (direction BWIN): **THE WINDOW IS CLOSED, BY A CLASS THEOREM** — at every piece that is a series end at **both** ends with `δ₁ ≤ 4`, a constructed configuration has **`ρ̄₁ ∩ Z = ⟨ℓ_u, ℓ_v⟩` exactly**, because the ends see the middle's screw space through **ONE hyperplane and ONE linear functional**, and `δ₁ ≤ 4` is precisely the hypothesis that leaves an excess **one rank-1 functional can kill**; the middle enters as an **arbitrary subspace** — no induction on it, no enumeration of window shapes — so the ear case's **(β) side has all three clauses at every window piece**, and job 3 shows the window is **NOT the barbells**: theta chains and **R-node middles** live in it

Direction **BWIN** (`notes/Pencil-fanout.md` §"BWIN", ordinal 51), the arc's
fifty-ninth, at the **last open item of the ear case's (β) side**: BSHARP's
window identity as a **CLASS statement**. Read against *Steps BE43–BE47*
(BSHARP), *Steps BE48–BE52* (BRULE), *Steps BE38–BE42* (BEARFULL), *Steps
BE34–BE37* (BEARCASE) and *Steps BE29–BE33* (BIMAGE), whose figures are
**cited, never re-run**. Driver `notes/scripts/w4/bwin.py`
(`dec|sweep|exc|cls|wide|validate`), importing `bsharp` / `bimage`, and through
them `bearfull` / `bearcase` / `btwocut` / `binduc` / `bzavoid` /
`kbare_common`, **read-only**; all exact ℚ, every rng seeded from a printed
literal (`20260829`), every drawn configuration through `assert_generic_star`
**and** `kbare_common.verify_pencil_witness`.

**WHICH DELIVERABLE THIS IS — said at the top, as the spec demands.** The spec
named three acceptable shapes (uniform argument / reduction to a named
checkable condition / characterization of the window) and barred a sixth
witness. **This landing is the first shape: the class statement is PROVED, by
a uniform argument** (*Steps BE53–BE56*, assembled as the theorem (BE-57)),
with two named side conditions, both checkable per middle and both vacuous on
every drawn piece ((BE-57)(iv)) — **both DECIDED 2026-09-03 by *Steps
BE141–BE147*, direction BSCOND: (S1) is REMOVABLE and (S2) is a theorem plus
a refuted-then-closed clause, so the class statement is UNCONDITIONAL on the
window's own regime**. Job 3's characterization finding ((BE-58)) is
a by-product, not the deliverable. **No step below exhibits a witness as
evidence for the class**: the 358 guarded draws verify the *lemmas* of the
proof at exact-ℚ instances and run the *construction* end-to-end, which is
verification of an argument, not accumulation of exhibitions — the F11
exhaustiveness rider is met by the theorem's quantifier (an arbitrary subspace
`W`), not by an enumeration.

**Status, stated before the mathematics.**

- **THE REFORMULATION (job 2, and the answer is exact).** In the window the
  double series peel ((BE-31)(i) twice, with (BE-45)(i)'s leaf collapse at
  both bridges) gives `ρ̄₁ = ⟨ℓ_u⟩ + W + ⟨ℓ_v⟩` with `W := ρ̄_{w₁,w₂}(middle)`,
  at **every** configuration. Since `⟨ℓ_u, ℓ_v⟩ ⊆ Z`, the **modular law**
  turns the target into
  **`ρ̄₁ ∩ Z = ⟨ℓ_u, ℓ_v⟩ + (W ∩ Z)`, so the identity ⟺ `W ∩ Z ⊆ ⟨ℓ_u, ℓ_v⟩`.**
  And `Z` has a **perp form**: `Z = μ^{⊥K} ∩ λ^{⊥K}`, where `λ`, `μ` are the
  Plücker points of `L = π_u ∩ π_v` and `M = p_u ∨ p_v`. **The coordinator's
  job-2 observation is CONFIRMED in its suspicion and in its hedge at once**:
  the condition does **not** factor through the middle alone (`Z`, `ℓ_u`,
  `ℓ_v` are end objects), but the whole coupling is **one hyperplane
  (`λ^{⊥K}`) and one linear functional (`⟨·, μ⟩_K`)** — and **no induction on
  the middle appears anywhere**: the middle enters the proof as one opaque
  subspace. **(BE-54)**.
- **THE END-CHOICE LEMMA, and the rank-one budget.** The functional
  `⟨·, μ⟩_K` vanishes **identically** on `⟨ℓ_u, ℓ_v⟩` (both `p_u ∈ ℓ_u` and
  `p_v ∈ ℓ_v`), and a fixed `x` survives **every** admissible `μ` iff
  `x ∈ (span(ℓ_u ∧ ℓ_v))^{⊥K}` — which for **skew** leading lines is
  `⟨ℓ_u, ℓ_v⟩` **itself** (the (BE-49)(i) computation read backwards), and in
  the meeting-lines regime is `Λ²σ`, whose relevant slice is again
  `⟨ℓ_u, ℓ_v⟩`. So over a fixed `L` the end freedom kills **exactly one
  dimension** of `V := W ∩ λ^{⊥K}`, no more: with
  `excess := dim V − dim(V ∩ ⟨ℓ_u, ℓ_v⟩)`, generic ends give the identity
  **iff `excess ≤ 1`**, and **`excess ≥ 2` fails at EVERY end choice over that
  `L`** — an exact per-`L` criterion, not a genericity statement. **(BE-55)**.
- **THE EXCESS LAW — `δ₁ ≤ 4` is exactly the budget one functional can pay.**
  `dim(W ∩ ⟨ℓ_u, ℓ_v⟩) = t + 2 − δ₁` (Grassmann, from the peel) and
  `dim V ≤ t − 1` at generic `L`, so **`excess ≤ max(0, δ₁ − 3)`**: the window
  hypothesis gives `excess ≤ 1`, and `δ₁ = 5, 6` give the forced failures
  (BE-36) already recorded, now with the mechanism named. Measured census over
  42 draws: `(δ₁, t, excess)` came out `(2,0,0)`, `(3,1,0)`, `(4,2,1)`,
  `(5,3,2)`, `(6,4,3)` and nothing else — the law is tight row by row.
  **(BE-56)**.
- **THE THEOREM.** *Every piece that is a series end at both ends with
  `δ₁ ≤ 4`, whose middle admits a `δ₁`-attaining pencil configuration with
  `p_{w₁} ≠ p_{w₂}`, has exact-ℚ configurations — a dense open subset of the
  end-resweep family over such a middle — at which `dim ρ̄₁ = δ₁`,
  `dim Z = 4`, the flags are cross-incidence-free, and*
  **`ρ̄₁ ∩ Z = ⟨ℓ_u, ℓ_v⟩` exactly.** The identity gives **(b1)** there
  (`ρ̄₁ ∩ Π_u = ⟨ℓ_u⟩`), **(b2)** by (BE-47)(iii)'s equivalence, and **(b3)**
  holds by (BE-50)(iii) since (M1) fires — so **(BE-37)(ii) has all three
  clauses at every window piece and the (β) side is proved there on the
  reduction's 87-of-91 domain**, by (BE-37)(i)(3)'s existential collapse.
  This strictly contains the window ((M2) and `dist` are not consulted).
  Verified end-to-end at **160 of 160** guarded end draws over 10 window
  pieces. **(BE-57)**.
- **JOB 3: the window is NOT the barbells — "barbell" was a sampler artifact.**
  Five constructed non-barbell pieces sit **inside** the window: two
  **theta chains** (two parallel blocks in series), a **four-branch theta**,
  and two pieces with a subdivided-`K₄` middle — an **R-node middle**, which
  no discharge outside the window reaches uniformly either. Every one is
  covered by (BE-57) anyway, which is the point: the theorem quantifies over
  the middle's screw space, so the window's true extent never needed to be
  known. At every drawn window piece the trichotomy data came out in the
  lowest regime: `t = δ₁ − 2 ≤ 2`, neither boundary pencil inside `W`,
  `W ∩ ⟨ℓ_u, ℓ_v⟩ = 0`. **(BE-58)**.
- **Verdict: HIT shape 1.** The class statement is **PROVED**; **nothing
  landed is refuted** — two landed prose surfaces are **annotated** (BSHARP's
  successor sentence *"the middle's own `ρ̄` misses `Z`"* is the `t ≤ 2` face
  of the theorem, not its general form; (BE-47)(iii) and BRULE's successor
  bullet are marked landed), with **every landed measurement intact**.
  `PencilPair K 3 G`, `hbareSplit`, (BE-14)-for-all-`G`, the 2-cut step,
  S-mark and (BE-32)(+) are untouched; **not a PENCIL event**; the
  phase-boundary consequence is **reported, not acted on** ((BE-58)(iv)).
- **Reservation FULLY CONSUMED.** Labels **(BE-54)–(BE-58)** and *Steps
  BE53–BE57*; nothing returned.

### Standing notation

Inherited from *Steps BE9–BE52* verbatim (`f := def₃`, `δ_{uv}`, `ρ̄_{uv}`,
hub, `Π_v := p_v ∧ π_v`, `E := Π_u + Π_v`, `M := p_u ∨ p_v`,
`L := π_u ∩ π_v`, `Z`, `c₂`, `loss`, `slack`, `dist_{G₁}`, (M1)/(M2) of
(BE-45), `⟨P⟩`, `d_min`, series end, `ℓ_u`/`ℓ_v`, the Klein form `⟨·,·⟩_K`,
`(b1)`/`(b2)`/`(b3)` of (BE-37)(ii), and the window of (BE-47)(ii)). Added
here:

- the **middle**: at a piece that is a series end at both ends, `e_u = u w₁`
  and `e_v = w₂ v` are the two bridges ((BE-45)(i)); `A` and `A_v` are the
  components of `H − e_u`, `H − e_v` containing `u`, `v`; the middle `C` is
  what remains — the component of `H − u − A − v − A_v` containing `w₁` and
  `w₂`. In the window `dist ≥ 5` forces `dist_C(w₁, w₂) ≥ 3`, so `w₁ ≠ w₂`;
- **`W := ρ̄_{w₁,w₂}(C)`** and **`t := dim W`**; **`Λ_{uv} := ⟨ℓ_u, ℓ_v⟩`**;
- **`λ`, `μ`**: the Plücker points (bivectors) of the lines `L` and `M`; for
  a 2-dim `X ⊆ K⁴` with basis `x, x'`, its Plücker point is `x ∧ x'`;
- **`V := W ∩ λ^{⊥K}`** and **`excess := dim V − dim(V ∩ Λ_{uv})`**;
- **`T₁ := p_{w₁} ∧ π_{w₁}`**, **`T₂ := p_{w₂} ∧ π_{w₂}`**, the boundary
  pencils of the middle — where `ℓ_u`, `ℓ_v` live, since `ℓ_u` is a line
  through `p_{w₁}` inside `π_{w₁}` whenever `w₁`'s star spans a plane.

**Carrier check, done off the landed bodies rather than the prose.** No new
Lean object is read. The three landed identities this direction consumes were
re-checked at their proof sites, not their summaries: (BE-31)(i)'s SERIES glue
(constant translation at the one shared vertex), (BE-45)(i)'s leaf collapse
(`ρ̄_{u,w₁}(A ∪ e_u) = K·ℓ_u` because `w₁` is a leaf of `A ∪ e_u` — exact at
**every** configuration, which is what makes the peel configuration-free), and
(BE-30)(iv)'s telescoping. The screw-space convention is
`kbare_common.build_rigidity`'s own (`m_u − m_w ∈ K·ℓ_{uw}`), read off the
driver chain as in *Steps BE29–BE52*. **No `.lean` was opened; the standing
2026-08-05 Lean hold binds.**

### Step BE53 — the reformulation: the double peel, the perp form of `Z`, and the modular law

> **(BE-54)(i)** *(proven; **THE DOUBLE PEEL**, exact at every configuration)*
> At a both-ends-series piece, (BE-45)(i) applied at `u` and then at `v`
> (inside `B`, where `e_v` is again a bridge, every `w₁–v` path of `B` being a
> `u–v` path of `H` with `e_u` removed) gives, by (BE-31)(i),
>
> **`ρ̄₁ = K·ℓ_u + ρ̄_{w₁,w₂}(C) + K·ℓ_v = ⟨ℓ_u⟩ + W + ⟨ℓ_v⟩`.**
>
> No genericity: both summand collapses are leaf collapses, exact at every
> configuration. In particular `dim ρ̄₁` and the whole target depend on the
> `A`-sides **only through `ℓ_u`, `ℓ_v`** — which is what lets the theorem
> treat them by a projective move ((BE-57)(ii)). ∎ Asserted as an identity of
> spaces (`W` recomputed **directly** on `C`, not read off `ρ̄₁`) at every one
> of the driver's 358 guarded draws.

> **(BE-54)(ii)** *(proven; **THE PERP FORM OF `Z`**)* For skew lines `M`,
> `L`: `M ∧ K⁴ = μ^{⊥K}` (both are the 5-dim kernel of `x ↦ x ∧ μ`), so
>
> **`Z = M ∧ L = μ^{⊥K} ∩ λ^{⊥K}`** —
>
> both sides 4-dimensional, `M ∧ L ⊆` each factor. ∎ So membership of `Z` is
> **two Klein pairings**, one against `λ` and one against `μ`; this is the
> whole interface the ends present to the middle. Asserted as an identity of
> spaces at every draw.

> **(BE-54)(iii)** *(proven; **THE MODULAR-LAW FACTORIZATION** — job 2's
> answer)* `Λ_{uv} ⊆ Z` (`ℓ_u ∈ Π_u ⊆ Z`, `ℓ_v ∈ Π_v ⊆ Z`), so the modular
> law with (i) gives, at every configuration,
>
> **`ρ̄₁ ∩ Z = (Λ_{uv} + W) ∩ Z = Λ_{uv} + (W ∩ Z)`, hence
> the window identity ⟺ `W ∩ Z ⊆ Λ_{uv}`.** ∎
>
> **VERDICT ON THE COORDINATOR OBSERVATION (job 2, `RESEARCH-ARC.md` §7):
> CONFIRMED in the suspicion, CONFIRMED in the hedge, and the phrase itself is
> REFINED.** (1) The suspicion — *"this looks like a statement about the
> middle and may not be one"* — is right: `Z` and `Λ_{uv}` are end objects,
> and the condition is a genuine cross-condition; a code or an induction
> premised on "the middle alone" would have been wrong, and **none is used**
> — the middle enters the whole proof as one opaque subspace `W`. (2) The
> hedge — *"the middle may see `Z` only through a 2-dimensional interface"* —
> is right in refined form: the interface is the two pairings `⟨·, λ⟩_K`,
> `⟨·, μ⟩_K` of (ii), plus the two boundary pencils `T₁`, `T₂` that confine
> `ℓ_u`, `ℓ_v`. (3) The landed phrase *"the middle contributes nothing to
> `Z`"* survives only in the form *"nothing beyond what it already shares
> with `Λ_{uv}`"*: at `t ≥ 3` the middle is **forced** to meet `Z`
> (`dim(W ∩ Z) ≥ t − 2 ≥ 1` at every configuration), and `δ₁ ≤ 4` is exactly
> what forces that contribution inside `Λ_{uv}` ((BE-56)). The prep's pricing
> note — five of the last six coordinator predictions refuted, split or
> reframed — lands on **reframed**.

### Step BE54 — the end-choice lemma: the ends act on `V` through one functional, and it kills exactly one dimension

> **(BE-55)(i)** *(proven; the admissible-end parametrization, and what is a
> function of what)* Fix the middle's configuration and let `p₁ := p_{w₁}`,
> `p₂ := p_{w₂}`, `π₁`, `π₂` be its boundary data (`π_i` forced when the
> boundary star spans a plane, else free through the boundary line). The
> pencil condition couples the ends to the middle by exactly four incidences —
> `p_u ∈ π₁`, `p₁ ∈ π_u`, `p_v ∈ π₂`, `p₂ ∈ π_v` — so on the honest domain
> the admissible ends are exactly:
>
> - a line `L` with `p₁, p₂ ∉ L`, not coplanar with `{p₁, p₂}`; then
>   `π_u = L ∨ p₁` and `π_v = L ∨ p₂` are **determined**;
> - `p_u` on the line `t₁ := (L ∨ p₁) ∩ π₁`, and `p_v` on
>   `t₂ := (L ∨ p₂) ∩ π₂`.
>
> Then **`ℓ_u = t₁` and `ℓ_v = t₂` as lines — functions of `L` alone** (`p_u`
> slides along `ℓ_u` without changing it), members of the boundary pencils
> `T₁`, `T₂` when the boundary planes are forced; and `μ = p_u ∧ p_v` carries
> the residual 2-parameter freedom. ∎

> **(BE-55)(ii)** *(proven; **THE END-CHOICE LEMMA**)* `⟨x, μ⟩_K = 0` for
> **every** admissible `μ` over a fixed `L` ⟺ the 4-form `x ∧ p ∧ q`
> vanishes for all `p ∈ ℓ_u`, `q ∈ ℓ_v` ⟺ `x ∈ (span(ℓ_u ∧ ℓ_v))^{⊥K}`. For
> **skew** `ℓ_u`, `ℓ_v` that span is the 4-dim `ℓ_u ∧ ℓ_v`, whose Klein-perp
> is — by (BE-54)(ii) applied to the pair `(ℓ_u, ℓ_v)` in place of `(M, L)`,
> read backwards —
>
> **`(ℓ_u ∧ ℓ_v)^{⊥K} = ⟨ℓ_u, ℓ_v⟩ = Λ_{uv}`.**
>
> And `⟨·, μ⟩_K` **vanishes on `Λ_{uv}` identically** (`p_u ∈ ℓ_u` makes
> `ℓ_u ∧ p_u = 0`). So over a fixed `L` the ends present `V` with a **single
> linear functional that is zero on `Λ_{uv}` and can be made nonzero on any
> chosen `x ∉ Λ_{uv}`** — a rank-one budget. ∎ Asserted (`(ℓ_u ∧ ℓ_v)`
> 4-dimensional, its Klein-perp `same_space` to `Λ_{uv}`) at all **84** skew
> resweep draws.

> **(BE-55)(iii)** *(proven; the MEETING-LINES regime — the budget survives
> the one degeneration the middle can force)* **SCOPE ANNOTATED 2026-09-03 by
> (BE-144), direction BSCOND: this argument is PLANE-AGNOSTIC and covers
> EVERY non-skew configuration at `σ := ℓ_u ∨ ℓ_v`, not only `π₁ = π₂`; and
> its cap-3 disclosure below — *"no drawn middle forces the regime"* — is
> SUPERSEDED, since `p_{w₁} = p_{w₂}` forces it and is realized at real
> window middles ((BE-143)(iv)). The parenthetical "conceivable at
> `dist_C ≥ 3` only through a forced-same-plane chain" is the clause that was
> wrong: coincidence is a second route in, and neither of the two proved
> same-plane mechanisms is involved. No measurement below moves.** If the middle forces its
> boundary planes equal (`π₁ = π₂ = π`; conceivable at `dist_C ≥ 3` only
> through a forced-same-plane chain, (BE-32)(+)'s closure — both proved
> mechanisms need `dist ≤ 2` and are excluded here), then `ℓ_u, ℓ_v ⊆ π` meet
> at `q := L ∩ π`, and the survivor space degrades to
> `(span(ℓ_u ∧ ℓ_v))^{⊥K} = (Λ²π)^{⊥K} = Λ²π`. But the survivors inside `V`
> still land in `Λ_{uv}`:
>
> **`V ∩ Λ²π ⊆ λ^{⊥K} ∩ Λ²π = q ∧ π = ⟨ℓ_u, ℓ_v⟩`** —
>
> the lines of `π` conjugate to `λ` are exactly those through `q`, and
> `ℓ_u ≠ ℓ_v` are two of them, spanning the pencil. The kill step is
> unchanged: any `x ∈ V ∖ Λ_{uv}` is then outside `Λ²π`, hence killable by
> one `μ`. ∎ The three space identities (`span = Λ²σ`, `(Λ²σ)^{⊥K} = Λ²σ`,
> `⟨τ₁, τ₂⟩ = q ∧ σ`) asserted at **12** synthetic exact-ℚ trials; no drawn
> middle forces the regime, so it is covered by lemma, not by battery
> (disclosed in *Caps*).

> **(BE-55)(iv)** *(proven; **THE PER-`L` CRITERION**, exact in both
> directions)* Over a fixed generic `L`: `W ∩ Z = ker(⟨·, μ⟩_K |_V)`, the
> functional vanishes on `V ∩ Λ_{uv}` always, and one functional's kernel has
> codimension `≤ 1` in `V`. Hence for `μ` generic in its 2-parameter family:
>
> **`W ∩ Z = V ∩ Λ_{uv}` and the identity holds ⟺ `excess ≤ 1`; and
> `excess ≥ 2` fails the identity at EVERY `(p_u, p_v)` over that `L`.** ∎
>
> Asserted per resweep draw at all 14 battery shapes: the identity verdict
> **equalled** `excess ≤ 1` at every one of 84 draws, the three MUST-FAIL
> control rows (`δ₁ = 5, 5, 6`, an R-node middle among them) failing at
> **0 of 6** end draws each.

### Step BE55 — the excess law: `δ₁ ≤ 4` is exactly the budget one functional can pay

> **(BE-56)(i)** *(proven; a Grassmann count, labelled a **count** ((BE-27)))*
> From the peel, `δ₁ = dim(W + Λ_{uv})` at generic ends (`ℓ_u ≠ ℓ_v`, so
> `dim Λ_{uv} = 2`), hence at any configuration attaining it,
>
> **`dim(W ∩ Λ_{uv}) = t + 2 − δ₁`.** ∎
>
> The two degenerate readings are both benign: `δ₁ = t + 2` means the sum is
> direct (the measured case at every real window piece, (BE-58)(iii)), and
> `δ₁ < t + 2` means the middle already **contains** combinations of the two
> leading lines — the contribution the modular law shows is invisible to the
> target.

> **(BE-56)(ii)** *(proven; the generic slice)* **SCOPE ANNOTATED 2026-09-03
> by (BE-146)(ii), direction BSCOND: the slice below is genuinely DEFEATED on
> the coincidence stratum `p_{w₁} = p_{w₂}` — there `L` is forced through the
> shared point, the lines through it span the self-conjugate `Σ_p`, and
> `λ ∈ W^{⊥K}` for every admissible `L` exactly when `W ⊆ Σ_p`, which happens
> at real window middles. The step stands VERBATIM off that stratum
> ((BE-146)(i): no middle can pin `λ` at a free `L`), and (BE-147) is what
> covers it on it.** `Λ_{uv} ⊆ λ^{⊥K}` always
> (each `ℓ` is coplanar with `L` inside `L ∨ p_i`, so they meet), hence
> `W ∩ Λ_{uv} ⊆ V`; and for `λ` off the proper closed set `W^{⊥K} ∩ {Klein
> quadric}` (nonempty complement: the quadric spans `Λ²K⁴`, `W^{⊥K}` is
> proper for `t ≥ 1`),
>
> **`dim V = t − 1`, and `V ∩ Λ_{uv} ⊇ W ∩ Λ_{uv}`.** ∎

> **(BE-56)(iii)** *(proven; **THE EXCESS LAW**)* Combining (i) and (ii), at
> generic `L`:
>
> **`excess ≤ (t − 1) − (t + 2 − δ₁) = δ₁ − 3`, i.e. `excess ≤ max(0, δ₁ − 3)`**
>
> (the `max` covering `t = 0`, where `V = 0`, and `δ₁ = 2`, where `W ⊆
> Λ_{uv}` outright). **So `δ₁ ≤ 4 ⟹ excess ≤ 1` — exactly the rank-one
> budget of (BE-55)(iv).** ∎ Asserted per draw across the whole battery (42
> draws, both samplers); the census `(δ₁, t, excess) ∈ {(2,0,0), (3,1,0),
> (4,2,1), (5,3,2), (6,4,3)}` shows the law **tight at every measured row**.

> **(BE-56)(iv)** *(the converse, for free — the forced failures named)* At
> `δ₁ = 5, 6` the same accounting gives `excess = δ₁ − 3 ≥ 2` at every
> measured row, so by (BE-55)(iv) the identity fails at **every** end choice
> — the mechanism behind (BE-36)'s forced minimum `dim(ρ̄₁ ∩ Z) ≥ δ₁ + dim Z
> − 6`, now with the failure located **in the middle's excess** rather than
> in a dimension count on `ρ̄₁`. The MUST-FAIL control rows (path₅,
> barbell 3+θ+3, and a `K_{3,3}`-subdivision middle at `δ₁ = 5`) all failed
> at 0-of-6 end draws, as the criterion requires.

### Step BE56 — the theorem: the class statement, proved

> **(BE-57)(i)** *(proven; **THE THEOREM**)* **HYPOTHESIS (S1) DELETED
> 2026-09-03 by (BE-148)(i), direction BSCOND — the statement below is the
> corrected one, and every landed measurement of it is intact.** Let `H` be a
> piece with
> terminals `u`, `v` that is a **series end at both ends**, let
> `δ₁ := max` over pencil configurations of `dim ρ̄₁` (the attaining value —
> the number every landed row reports), and suppose **`δ₁ ≤ 4`**. Then a
> **dense open subset of the honest end family over a `δ₁`-attaining middle**
> — the resweep family of (BE-55)(i) off the coincidence stratum, the
> (irreducible) coincidence family of §(K-bare-ext)'s *Step BE141* standing
> notation on it — consists
> of configurations at which `dim ρ̄₁ = δ₁`, `dim Z = 4`, the flags are
> cross-incidence-free, and
>
> **`ρ̄₁ ∩ Z = ⟨ℓ_u, ℓ_v⟩` exactly.**
>
> *Proof.* Choose a middle configuration `c₀` maximizing the generic-ends
> value of `dim ρ̄₁` (it exists: the middle's stratum is nonempty by (BE-11),
> the end space `{(L, p_u, p_v)}` is irreducible, and by (BE-54)(i) every
> configuration of `H` restricts to a member of the resweep family, so the
> maximum over `H`'s configurations **is** attained this way — the (BE-37)(i)
> caveat about semicontinuity off the attaining locus is dodged by
> construction, not assumed away). Fix `W = W(c₀)`, `t = dim W`. For generic
> `L`: the boundary lines `ℓ_u = t₁(L)`, `ℓ_v = t₂(L)` are skew when
> `p₁ ≠ p₂` and the boundary planes differ (choose planes `σ_i ⊇ t_i` and
> `L = σ₁ ∩ σ₂` to hit any prescribed skew pair — a nonempty open condition),
> and meet in the forced regimes, **whose list is exactly `π₁ = π₂` and
> `p₁ = p₂` ((BE-145)(ii)) and both of which (BE-144) covers with
> (BE-55)(iii)'s own argument at `σ := ℓ_u ∨ ℓ_v`**; `dim V = t − 1`
> and the excess law (BE-56)(iii) give `excess ≤ δ₁ − 3 ≤ 1` — **except on
> the coincidence stratum, where (BE-56)(ii)'s slice is genuinely defeated
> ((BE-146)(ii)) and (BE-147) supplies `excess ≤ 1` by a dimension cap
> instead**. If
> `excess = 0`, every `μ` gives `W ∩ Z ⊆ V ⊆ Λ_{uv}`. If `excess = 1`, pick
> `x₀ ∈ V ∖ Λ_{uv}`; by (BE-55)(ii)/(iii) a generic `μ` has
> `⟨x₀, μ⟩_K ≠ 0`, so `ker(⟨·,μ⟩_K|_V) = V ∩ Λ_{uv} ⊆ Λ_{uv}`. Either way
> (BE-54)(iii) gives the identity. Genericity of the ends also gives
> `dim ρ̄₁ = δ₁` (lower semicontinuity on the irreducible end space, and `c₀`
> was chosen to attain), `dim Z = 4` and cross-incidence-freeness (each a
> nonempty open condition, exhibited constructively per draw); finitely many
> dense opens meet ((BE-25)(i)). ∎

> **(BE-57)(ii)** *(proven; the `A`-sides, by one projective move)* The
> construction fixes flags at `u`, `v` before placing `A`, `A_v`. Take any
> pencil configuration of `A` (nonempty, (BE-11)); the pencil condition —
> every closed star coplanar — is `PGL(4)`-invariant, and `PGL(4)` is
> transitive on (point, plane) flags, so a projective move places `A` with
> `u`'s flag at the chosen `(p_u, π_u)`. The glued configuration is legal
> (every star of `A` unchanged up to projectivity; `u`'s star is
> `{p_u, p₁} ∪ A`-neighbours `⊆ π_u`; `w₁`'s star gains `p_u ∈ t₁ ⊆ π₁`),
> and by (BE-54)(i) it changes **nothing** the target sees. ∎ (The driver's
> battery has pendant terminals, so this step is exercised by the prose, not
> the battery — disclosed in *Caps*.)

> **(BE-57)(iii)** *(proven; **THE CONSEQUENCE FOR (β)** — all three clauses,
> at every window piece)* At the theorem's configurations: **(b2)** holds by
> (BE-47)(iii)'s equivalence (its hypothesis `dim Z = 4`, `δ₁ ≤ 4` is met);
> **(b1)** holds because `Π_u ⊆ Z` gives `ρ̄₁ ∩ Π_u = Λ_{uv} ∩ Π_u = ⟨ℓ_u⟩`
> (a combination `aℓ_u + bℓ_v ∈ Π_u` with `b ≠ 0` would put `ℓ_v` in
> `Π_u ∩ Π_v = 0`); **(b3)** holds by (BE-50)(iii), (M1) firing at both ends.
> By (BE-37)(i)(3) one such configuration per piece is a proof for that
> piece, so by (BE-37)(ii) **the composition criterion holds at every window
> piece, for every ear length, in the 87-of-91 arithmetic cases** — the ear
> case's (β) side is proved **at the window**, which was its last item with
> no class-level route at all. What this does **not** upgrade: the
> per-shape components of the discharge **outside** the window ((BE-45)(iv)'s
> three measured-only rows, (b1)-at-`δ₁ = 5` measured, (BE-46)/(BE-52)'s
> per-shape witnesses) and the `π_u = π_v` corner carried by (BE-32)(+)'s
> forced branch — named in (BE-58)(iv). ∎

> **(BE-57)(iv)** *(the side conditions, said plainly)* **SUPERSEDED
> 2026-09-03 by *Steps BE141–BE147*, direction BSCOND — BOTH CONDITIONS ARE
> DECIDED, and this clause's own evidence for (S1) is STRUCK as circular
> while its (S2) absence-claim is REFUTED.** The statement as landed, kept
> for the record: **(S1)**
> `p_{w₁} ≠ p_{w₂}` at some attaining middle configuration: no arc mechanism
> forces two distinct vertices onto one point, both samplers reject
> coincidence, and every drawn middle satisfies it — but it is a hypothesis,
> checkable per middle, not a theorem. **(S2)** the meeting-lines regime is
> handled by (BE-55)(iii) only when the forced equality is of the boundary
> **planes**; a middle forcing some *other* algebraic relation between its
> boundary flags that pins `λ` onto `W^{⊥K}` (defeating (BE-56)(ii)'s generic
> slice) would need its own argument — no such mechanism is known, and
> (BE-49)(iv)'s cross-incidence accident is configuration-level, dodged by
> the existential quantifier. Both conditions are **vacuous at every drawn
> piece**; neither is smoothed into the statement.
>
> **What is now known, in the same three sentences.** **(S1) is REMOVABLE**,
> not merely true — (BE-57)(i) holds with it deleted ((BE-148)(i)); its
> *"both samplers reject coincidence, and every drawn middle satisfies it"*
> is the **sampler's global distinctness filter**, so the second clause is
> the reason the third carries no weight ((BE-142)), and the guard the
> sentence names rejects coincidence only on **edges** while
> `dist_C(w₁,w₂) ≥ 3` here. **(S2)'s first half is PROVED** with the forcing
> list exhaustive at two mechanisms ((BE-145)), both covered by (BE-144).
> **(S2)'s second half is REFUTED AS STATED** — the mechanism exists, it is
> `p_{w₁} = p_{w₂}` itself, and it is realized at real window middles
> including R-node ones ((BE-146)) — **and then CLOSED** by the coincidence
> excess law ((BE-147)). So *"vacuous at every drawn piece"* was true and
> uninformative: the stratum is one no sampler in the chain could draw.

### Step BE57 — job 3: the window is not the barbells, and the measurements

> **(BE-58)(i)** *(constructed; **THE WINDOW IS STRICTLY BIGGER THAN THE
> BARBELLS**)* Five pieces that are **not** barbells sit inside the window
> (series both ends, `δ₁ ≤ 4 < d_min`, `dim Z = 4`, `dist ≥ 5`, each
> verified at a guarded draw): two **theta chains**
> (`u–θ(3,3,3)–bridge–θ(3,3,3)–v`, `δ₁ = 3`, `dist = 9`; and a 2-edge-bridge
> variant, `δ₁ = 4`, `dist = 10`), a **four-branch theta** (`θ(3,3,3,3)`
> wrapped, `δ₁ = 2`, `dist = 5`), and two **R-node middles** — subdivided
> `K₄` between two branch vertices, wrapped (`δ₁ = 2` and `3`). So
> *"barbell"* was the **sampler's** reach, not the window's extent — the
> honest answer to the spec's job-3 question — and a `K_{3,3}`-subdivision
> middle wrapped the same way peels to `δ₁ = 5`, landing **outside** and
> failing exactly as (BE-56)(iv) requires: the window/non-window boundary
> cuts **through** the R-node-middle class. Every window member is covered
> by (BE-57) regardless, which is why the window's extent never needed to be
> enumerated.

> **(BE-58)(ii)** *(measured; the verification census)* **358 guarded
> configurations** across the five modes (every one through
> `assert_generic_star` **and** `verify_pencil_witness`, resweeps re-gated
> after the ends are replaced): `dec` 28 draws (the three space identities of
> (BE-54) asserted at each); `sweep` 14 middles + 84 resweeps (the
> end-choice lemma asserted at all 84; per-`L` criterion equality at 84/84;
> 12 synthetic meeting-lines trials); `exc` 42 draws (the excess law and its
> census); `cls` 20 middles + 160 resweeps (**identity + (b1) + `dim Z = 4`
> asserted at 160 of 160 window end draws**); `wide` 10 window rows.

> **(BE-58)(iii)** *(measured; the trichotomy data at real pieces)* The
> excess-law accounting admits three window regimes (`t = δ₁ − 2` with the
> sum direct; `t = δ₁ − 1` with one boundary pencil inside `W` or `W` between
> the pencils; `t = δ₁` with both). **Every drawn window piece sits in the
> first**: `t = δ₁ − 2`, neither `T₁ ⊆ W` nor `T₂ ⊆ W`, `W ∩ Λ_{uv} = 0` —
> so at real pieces the middle's `ρ̄` does miss `Z` outright, which is why
> BSHARP's successor phrase was measured true 5/5 while being the special
> case, not the theorem ((BE-58)(iv)). Whether the higher regimes are
> realized by any graph middle is **open and immaterial**: (BE-57) covers
> them.

> **(BE-58)(iv)** *(classification, mandatory and explicit)* **Nothing the
> arc carries is refuted.** Not `PencilPair K 3 G`; not `hbareSplit`; not
> (BE-14)-for-all-`G`; not the 2-cut step; not S-mark; not (BE-32)(+); not
> the short-cycle law; not BSHARP's dichotomy; not BRULE's separation
> theorem. Two landed prose surfaces are **annotated at source** (per F12):
> BSHARP's successor sentence — *"the statement is 'the middle's own `ρ̄`
> misses `Z`'"* — named the `t = δ₁ − 2` face as if it were the general
> form; the class statement actually provable (and now proved) is
> `W ∩ Z ⊆ ⟨ℓ_u, ℓ_v⟩`, of which *"misses `Z`"* is the special case
> `W ∩ Λ_{uv} = 0` — measured true at every real piece, so **no measurement
> changes**; and (BE-47)(iii) / BRULE's successor bullet are marked LANDED.
> The (β) side's ledger after this landing: **the window is CLOSED as a
> class**; still per-shape or measured outside it are (BE-45)(iv)'s three
> no-mechanism rows, (b1)-at-`δ₁ = 5` (measured at every such row), the
> (BE-46)/(BE-52) witnesses behind the *sharpened-at-one-end* route, and the
> `π_u = π_v` corner ((BE-32)(+), forced branch). **One route is closed**
> (the window as an open question); **none is opened. Not a PENCIL event**
> — `hK`, (GR-15) and class uniformity are untouched, and the phase-boundary
> consequence of a proved (β)-at-the-window is the **user's call**
> (`notes/Phase39.md` *Status*), reported and not acted on.

### Verdict, classification, and the price

- **HIT shape 1: the CLASS STATEMENT IS PROVED** — the deliverable the spec
  said the arc's own machinery could not produce, produced by a different
  machine: not openness + irreducibility + a witness per shape, but a
  **modular-law reduction to one subspace inequality** plus a **rank-one
  budget** that `δ₁ ≤ 4` exactly funds. The theorem strictly contains the
  window (neither (M2) nor `dist` is consulted) and quantifies over the
  middle's screw space as an arbitrary subspace, so **no window shape ever
  needs enumerating**.
- **The ear case.** (β) now has all three clauses at **every** window piece
  on the 87-of-91 domain; with the landed routes outside the window, the (β)
  side's remaining non-class content is exactly the four items named in
  (BE-58)(iv) — none of them a window item. (α) was already proved for
  `m ≥ 3` (BEARCASE). The 2-cut lemma's remaining structure (S-mark's
  cross-pair welding, the internal R-node, (BE-32)(+)'s spread step) is
  untouched.
- **The price, stated as a price.** (S1) and (S2) are hypotheses on the
  middle, vacuous at every drawn piece but not theorems; the `A`-side step
  is exercised by prose, not battery (pendant-terminal cap); the meeting-
  lines regime is covered by lemma, with no real middle drawn in it; and the
  theorem says nothing about pieces series at only ONE end, where the
  per-shape wall still stands.
- **Untouched.** `PencilPair K 3 G`, `hbareSplit`, (BE-14)-for-all-`G`, the
  2-cut composition lemma, S-mark, (BE-32)(+), the short-cycle law, the
  refuted ear-decomposition route ((BE-43), still refuted). **Not a PENCIL
  event.**

### Verification

Every claim above is reproduced by
`python3 notes/scripts/w4/bwin.py {dec|sweep|exc|cls|wide|validate}`, run from
the repo root; `validate` runs all five modes at a reduced tier in ~112 s.
The verification bar is off the **shipped** driver, and the following are the
load-bearing asserts (a failure stops the run, it is not reported):

1. **Every configuration is a pencil configuration** — `assert_generic_star`
   **and** `kbare_common.verify_pencil_witness` on every draw of every mode,
   **including every resweep** (the glued configuration is re-gated after the
   ends are replaced): 358 guarded configurations.
2. **Every space claim is an identity of SPACES** (`same_space`/`contains`,
   never dimensions): the double peel (with `W` recomputed directly on the
   middle), `Z = μ^{⊥K} ∩ λ^{⊥K}`, the modular-law factorization,
   `Λ_{uv} ⊆ Z`, `(ℓ_u ∧ ℓ_v)^{⊥K} = Λ_{uv}` at every skew resweep,
   `W ∩ Z = ker(⟨·,μ⟩_K|_V)`, and the three meeting-lines identities.
3. **The excess law is asserted, not reported** — `dim(W ∩ Λ_{uv}) =
   t + 2 − δ₁`, `dim V ≤ t − 1`, `excess ≤ max(0, δ₁ − 3)` — at every draw,
   and **identity ⟺ `excess ≤ 1`** at every draw of every mode.
4. **The theorem's construction is the code path**: `cls` fixes a guarded
   middle, redraws `(L, p_u, p_v)` fresh with every genericity condition an
   explicit exact-ℚ rank check, and asserts the identity, (b1) and
   `dim Z = 4` at every one of 160 window end draws; the three MUST-FAIL
   controls (`δ₁ ≥ 5`) are asserted to fail at **every** end draw (the
   per-`L` criterion, non-vacuously).
5. **Exhaustiveness is carried by the argument, not the battery** (F11): the
   battery verifies lemmas at instances; the `∀`-window quantifier is
   (BE-57)'s, whose only graph inputs are the series peel and the four
   interface incidences.
6. **Exact ℚ throughout**, every rng seeded from the printed literal
   `20260829`, zero floating point.

### Caps, disclosed rather than smoothed

1. **(S1)/(S2) are hypotheses.** ~~Named in (BE-57)(iv), checkable per
   middle, vacuous at every drawn piece; a middle forcing `p_{w₁} = p_{w₂}`
   or pinning `λ` into `W^{⊥K}` would escape the theorem and is not known to
   exist.~~ **CAP LIFTED 2026-09-03 ((BE-142)–(BE-148), direction BSCOND).**
   Both are decided: (S1) is **deleted** from the statement, and the middle
   this cap said "is not known to exist" **does** exist — `p_{w₁} = p_{w₂}`
   pins `λ` into `W^{⊥K}` at real window middles — but it does **not** escape
   the theorem, by the coincidence excess law ((BE-147)). The clause was
   right that the two objects it named were the risk and wrong that they were
   two.
2. **The battery has pendant terminals** (`deg u = deg v = 1`), so the
   `A`-side step (BE-57)(ii) is proved in prose and never exercised
   numerically; the peel itself is asserted at every draw.
3. **No drawn middle forces the meeting-lines regime** — (BE-55)(iii) is
   verified on synthetic exact-ℚ flag data (12 trials), not on a graph
   middle; the two proved same-plane forcing mechanisms need `dist ≤ 2` and
   cannot fire at `dist_C ≥ 3`, but (BE-32)(+)'s closure chains are not
   excluded, which is why the regime is covered by lemma rather than
   declared empty. **CAP SUPERSEDED 2026-09-03 ((BE-143)(iv)): a graph
   middle DOES force the regime — by `p_{w₁} = p_{w₂}`, a third route in
   that this cap did not consider, realized at 20 shape-seeds including two
   R-node middles. "Covered by lemma rather than declared empty" was the
   right call for the right reason.**
4. **The battery is 14 hand-chosen shapes** (10 window + 3 must-fail + the
   path₄ theorem-not-window row), both samplers inherited; no claim above is
   a battery statement — see *Verification* item 5.
5. **`δ₁` at a drawn piece is the drawn value**, a lower bound on the
   attaining value; for the window-membership calls of (BE-58)(i) that is
   the conservative direction (a piece could only move OUT of the window at
   a higher `δ₁`, and the must-fail rows show what then happens), and for
   the theorem `δ₁` is defined as the attaining value outright.
6. **Path enumeration is capped at 4000** per piece (inherited); not hit.
7. **The trichotomy census (BE-58)(iii) is a measurement**, not a claim that
   the higher regimes are empty; the theorem does not care.

### Harness note — the `kbare/` sibling-import set gains its TENTH `w4/` consumer

`bwin.py` imports `bsharp` and `bimage` read-only, and through them
`bearfull`, `bearcase`, `btwocut`, `binduc`, `bzavoid` and `kbare_common`, so
the recorded **unpaid** sibling-import debt (`notes/scripts/README.md`
*Harness debt*, 2026-08-20) gains its **tenth** `w4/` consumer and the chain
is now **ten** deep: `battain → bzavoid → binduc → btwocut → bimage →
bearcase → bearfull → bsharp → brule → bwin`. **NO MOVE MADE** — a dispatch
may not edit a landed driver another direction may be importing in flight —
and the consumer list is extended in the README, exactly as the previous nine
did. `bsharp.sample_piece_config_adj`, `guarded_draw`, `simple_paths`,
`usable_first_edges` and the battery builders are **consumed unchanged**; the
new primitives (`resweep`, `boundary_plane`, the exact-ℚ end parametrization)
are local to this driver.

### Confidence verdicts, per claim

| claim | status |
|---|---|
| (BE-54)(i) the double peel `ρ̄₁ = ⟨ℓ_u⟩ + W + ⟨ℓ_v⟩` | **PROVED** ((BE-31)(i) + (BE-45)(i) twice, exact at every configuration); asserted at 358 draws |
| (BE-54)(ii) `Z = μ^{⊥K} ∩ λ^{⊥K}` | **PROVED**; asserted as an identity of spaces per draw |
| (BE-54)(iii) `ρ̄₁ ∩ Z = Λ_{uv} + (W ∩ Z)`; target ⟺ `W ∩ Z ⊆ Λ_{uv}` | **PROVED** (modular law); asserted per draw |
| (BE-55)(i) the admissible-end parametrization; `ℓ_u`, `ℓ_v` functions of `L` | **PROVED**; the construction is the `cls` code path |
| (BE-55)(ii) the end-choice lemma `(ℓ_u ∧ ℓ_v)^{⊥K} = Λ_{uv}` (skew) | **PROVED**; asserted at 84 skew resweeps |
| (BE-55)(iii) the meeting-lines regime lands in `q ∧ π = Λ_{uv}` | **PROVED**; 12 synthetic trials — **and the argument is PLANE-AGNOSTIC, covering every non-skew pair at `σ = ℓ_u ∨ ℓ_v` ((BE-144)); cap 3 SUPERSEDED, a graph middle reaches the regime via `p_{w₁} = p_{w₂}` ((BE-143)(iv))** |
| (BE-55)(iv) the per-`L` criterion: identity ⟺ `excess ≤ 1`; `≥ 2` fails every end choice | **PROVED**; asserted at 84/84 resweeps, non-vacuously at the 3 must-fail rows |
| (BE-56)(i)–(iii) the excess law `excess ≤ max(0, δ₁ − 3)` | **PROVED** (Grassmann counts, labelled counts); tight at every measured census row — **(ii)'s generic slice DEFEATED on the coincidence stratum ((BE-146)(ii)), where (BE-147) gives `excess = dim ρ̄₁ − 2 ≤ 1` by a dimension cap** |
| (BE-56)(iv) `δ₁ ≥ 5` fails at every end choice | **PROVED** from the law + criterion; 0-of-18 control draws |
| (BE-57)(i) **the theorem** (the class statement) | **PROVED, and UNCONDITIONAL since 2026-09-03**: (S1) DELETED ((BE-148)(i)), (S2) decided ((BE-145)–(BE-147)); construction verified 160/160, plus 100 configurations on the stratum (S1) excluded |
| (BE-57)(ii) the `A`-side projective move | **PROVED** (prose; not exercised by the pendant-terminal battery — cap 2) |
| (BE-57)(iii) (b1)+(b2)+(b3) at every window piece; (β) proved there on 87-of-91 | **PROVED**, consuming (BE-47)(iii), (BE-50)(iii), (BE-37)(i)(3)/(ii) |
| (BE-57)(iv) the side conditions | **SUPERSEDED** ((BE-142)–(BE-148)): (S1) REMOVABLE, (S2) first half PROVED, second half REFUTED as stated then CLOSED; *"vacuous at every drawn piece"* was the **sampler's filter** |
| (BE-58)(i) the window is not the barbells (R-node middles inside) | **CONSTRUCTED**, 5 non-barbell window rows + 1 R-node-middle non-window control |
| (BE-58)(ii) the census | **MEASURED**, 358 guarded configurations |
| (BE-58)(iii) real pieces all sit in the lowest trichotomy regime | **MEASURED** (10 rows); the higher regimes covered by the theorem regardless |
| (BE-58)(iv) classification | **PROVED** — nothing refuted, two prose surfaces annotated, no measurement touched |

### What would change this

- **A middle violating (S1) or (S2)** — forcing `p_{w₁} = p_{w₂}`, or pinning
  `λ` into `W^{⊥K}` across the whole admissible family — would carve a
  sub-window the theorem does not cover; none is known, and either would be
  a new forcing mechanism of independent interest (the (BE-32)(+) family is
  the place to look).
- **The one-end-series case.** The same machine plausibly applies with one
  peel instead of two (`ρ̄₁ = ⟨ℓ_u⟩ + ρ̄(rest)`, budget `excess ≤ 1` needing
  `δ₁ ≤ 3` by the same accounting — or a second functional from the clean
  end); a successor could retire the per-shape witnesses behind the
  *sharpened-at-one-end* route, which after this landing is the (β) side's
  largest remaining per-shape component.
- **A window piece failing the identity at every configuration** would
  contradict (BE-57) and hence refute one of its inputs — the first places
  to re-check would be the (BE-31)(i) glue and — since (S1)/(S2) are decided
  ((BE-142)–(BE-148)) — the coincidence excess law's case (b) at `δ₁ = 4`,
  the one row no battery reaches.
  By F27's asymmetry a single failing draw is an artifact; the claim is
  existential.
- **The spread step and the internal R-node** ((BE-58)(iv)'s ledger) are
  now the (β)-adjacent items with no class route — the successors this
  direction ranks, in that order.

### TERMINATION riders

**E1: NO** — this direction is two Grassmann counts, one modular-law
identity and one rank-one-functional argument; no `g`-flank is involved and
none is produced. **E2: NO** — nothing landed is refuted: the direction's
target is **proved**, and the two annotated prose surfaces keep every landed
measurement intact. **E3: ARMED by GBAL, not fired** — this direction is on
the §(K-bare-ext) path, not (a′); reported, not acted on.

