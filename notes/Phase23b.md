# Phase 23b — general-`d` Case-III chain dispatch + `⋀^{d−1}` duality [CHAIN] (work log)

**Status:** open. CHAIN-3's first three sub-leaves landed: the membership brick
`extensor_mem_range_map_subtype_of_mem_grade`, the **proportionality engine**
`exists_smul_eq_of_mem_range_map_subtype_grade`, and now (2026-06-17) the
**`toDual=Gram` bridge** `exteriorPower_basis_toDual_eq_pairingDual_comp_map_grade`
(all `Meet.lean`) — the grade-/ambient-generic restatements of the `Fin 4`/`⋀²`-
pinned `d=3` lemmas, each derived as the `(d:=3)` instance. The proportionality
engine carries the leaf's genuine new count via two further grade-generic bricks
(`finrank_exteriorPower_self_eq_one`, `exteriorPower_map_subtype_injective_grade`).
**One CHAIN-3 brick remains** — the heavy assembly `complementIso_smul_eq_extensor_join`
(its `Φ̃`-count dependency chain is genuinely new at general `d`, NOT a verbatim
lift). The integer Phase 23 stays **in progress** — ENTRY / ASSEMBLY remain
(coordinator owns the sub-phase boundary; codes-until-open).

**Orientation.** This is the **23b (CHAIN layer)** sub-phase work log — the
*rolling* state + hand-off for the active layer only. The cross-phase
**plan/guidance** (sub-phase division, sequence, open decisions, sources) is the
canonical job of `notes/Phase23-design.md`; the **detailed leaf-level recon of
CHAIN** is its §"CHAIN — detailed leaf-level recon" ((a) per-file reach-ins, (c)
buildable-leaf sequence, (d) green-modulo boundary, (e) OD resolutions). The
program map is `notes/MolecularConjecture.md`. **Sub-phase naming convention:**
the layers are tracked by stable **codes** — `CARRIER`(=23a, closed), `CHAIN`(=
this 23b), `ENTRY`, `ASSEMBLY`; a letter + work log is minted when a layer
opens, so a later split costs no renumber-churn. `23b` is the minted letter for
CHAIN; ENTRY/ASSEMBLY stay code-only until their turn.

## Current state

**CHAIN-3's `wedgeFixedLeft` building block has landed (2026-06-17): `wedgeFixedLeft`
(the `def`) + its three immediate facts `coe_wedgeFixedLeft` / `ker_wedgeFixedLeft` /
`finrank_range_wedgeFixedLeft` are lifted from `Fin 4` to ambient `{d} (Fin (d+1))`,
grade fixed at `2`. The range count generalizes `3 → d` (`= (d+1) − 1`). All four
were ambient-generic verbatim (`extensor` API is already `{d}`-generic); the `def`
+ facts carry implicit `{d}`, so the still-`Fin 4` consumers
(`inf_range_wedgeFixedLeft`, `finrank_sup_range_wedgeFixedLeft`, the assembly) unify
`d = 3` by defeq — no separate `d=3` instance decls needed (lighter than the prior
bricks' `_grade`/instance split, because there are no external consumers). This is
the *first sub-step* of CHAIN-3's last brick `complementIso_smul_eq_extensor_join`.**
**Next, still inside that last brick (the heavy one, NOT a verbatim lift):** lift
`inf_range_wedgeFixedLeft` (the decomposable intersection `a∧ℝ^{d+1} ⊓ b∧ℝ^{d+1} =
span{a∧b}`, ambient-generic) and then `finrank_sup_range_wedgeFixedLeft` — its `dim Φ̃`
count goes from the 2-summand `3+3−1=5` to a `(d−1)`-summand inclusion–exclusion (a
panel `Π(u)` has `d−1` normals): **the recon's "real new lemma here"** — then
`extensor_toDual_extensor_eq_zero_of_perp` and the assembly itself.
The recon
(`notes/Phase23-design.md` §"CHAIN") source-verified — against KT §6.4.2 (eqs.
6.46–6.67, read end-to-end) and the landed tree — that **the arm-realization
engine is already general-`k`** (the M₁/M₂/M₃ closers `case_III_arm_realization`
/ `_M2` / `_M3` in `CaseIII/{Arms,Relabel}.lean` were authored `(k:ℕ)`); the
genuinely-`d=3` surface is **only the dispatch** (`case_III_candidate_dispatch`,
`Realization.lean:201`) — its fixed-3-candidate count + the `⋀²ℝ⁴` discriminator
(`exists_homogeneousIncidence_of_normals` / `…complementIso…` in `Claim612.lean`,
the `Meet.lean` duality lemmas). CHAIN's job: replace that dispatch with the
`d`-candidate chain dispatch + the `⋀^{d−1}(ℝ^{d+1})` duality finish.

**The load-bearing flag (recon (b)) — SETTLED 2026-06-17.** The 23a-carried
`hdispatch` (`Theorem55.lean:2225`) takes a **fixed `v,a,b,c` 4-tuple**, faithful
at `d=3` (the chain `v₀v₁v₂v₃` *is* `b—v—a—c`) but **too short at `d≥4`** — KT's
general-`d` Lemma 6.13 needs the whole length-`d` chain. The CHAIN↔ENTRY
chain-data contract is now **frozen** (`notes/Phase23-design.md` §"CHAIN↔ENTRY
contract"): a `G.ChainData n` `structure` (length-`d` chain `vtx`/`edge`/`e₀` +
degree-2 closures) is the shared shape; the reshape is **three decls in
lockstep** — the ENTRY extractor (`exists_chain_data_of_noRigid` → a `ChainData`
producer), the producer `case_III_hsplit_producer_all_k.hcand` (which calls the
extractor inline, C.0), and the CHAIN-5 dispatch `hdispatch`. **No motive/IH
change forced** (clause (ii), C.6): the chain data is combinatorial, the base
`(G₁,q₁)` stays the existing general-`k` realization premise from the same 0-dof
IH conjunct, the `d` candidate splits are smaller 0-dof graphs. CHAIN-5's
signature is now authorable; the `d=3` line is a zero-regression wrapper (C.4).

## CHAIN leaf checklist

The buildable-leaf sequence (exact signatures + dependency order in
`notes/Phase23-design.md` §"CHAIN"(c)). Five leaves, **one** sub-phase (OD-6).
CHAIN-1/3 are buildable now (no ENTRY-contract dependency); CHAIN-5 is gated by
the (b) flag (its signature is the CHAIN↔ENTRY contract).

- [◐] **CHAIN-3 — the `⋀^{d−1}(ℝ^{d+1})` duality bricks** (`Meet.lean`).
      Re-state at `⋀[ℝ]^{d−1}(Fin (d+1)→ℝ)` with the general
      `finrank(⋀^{d−1}W)=(finrank W).choose (d−1)`. Build LAZILY at concrete grade
      — NO general Hodge-star. Unblocks CHAIN-4 + the four-producer lift (OD-7).
      - [x] `extensor_mem_range_map_subtype_of_mem_grade` — the membership brick
        (grade-generic verbatim; `d=3` `extensor_mem_range_map_subtype_of_mem`
        re-derived as the `(d:=3)` instance). Landed 2026-06-17.
      - [x] `exists_smul_eq_of_mem_range_map_subtype_grade` — the proportionality
        engine at general grade, the genuine `finrank` count via two further
        grade-generic bricks `finrank_exteriorPower_self_eq_one` (top-grade `⋀^n W`
        is a line for `dim W = n`, `exteriorPower.finrank_eq`+`Nat.choose_self`)
        and `exteriorPower_map_subtype_injective_grade`. The three `d=3` names
        (`exists_smul_…`, `finrank_exteriorPower_two_eq_one`,
        `exteriorPower_map_subtype_injective`) survive as `(d:=3)` instances
        (blueprint pins on the latter two untouched). Landed 2026-06-17.
      - [x] `exteriorPower_basis_toDual_eq_pairingDual_comp_map` — the `toDual=Gram`
        bridge, lifted to `…_grade {d}` over `Fin (d+1)` (the proof is ambient-/
        grade-generic verbatim; the `d=3` name survives as the `(d:=3)` instance,
        line-1003 internal consumer untouched, no blueprint pin on this decl).
        Landed 2026-06-17.
      - [◐] `complementIso_smul_eq_extensor_join` at general grade. **The heavier
        generalization** — `complementIso`/`toDual` built over `k+2` / `Fin 4`, not
        a verbatim grade-lift. Its dependency chain must lift first:
        - [x] `wedgeFixedLeft` (the `def`) + `coe_wedgeFixedLeft` / `ker_wedgeFixedLeft`
          / `finrank_range_wedgeFixedLeft` lifted `Fin 4` → ambient `{d} (Fin (d+1))`,
          grade `2`, range count `3 → d`. Ambient-generic verbatim; implicit `{d}` so
          the `Fin 4` consumers unify `d=3` by defeq (no instance decls). Landed
          2026-06-17. (One friction: `finrank_sup_range`'s `omega` mis-atomized the
          `(d:=3)`-vs-`Fin 4` elaborations → `simpa using hsum`; QUIRKS § 58.)
        - [ ] `inf_range_wedgeFixedLeft` (`Fin 4`, `Fin 3`-arity `decide`/`fin_cases`)
          → ambient `{d}` (the decomposable intersection, verbatim-liftable).
        - [ ] `finrank_sup_range_wedgeFixedLeft` (the `dim Φ̃ = 5` count → a `(d−1)`-summand
          inclusion–exclusion, the recon's "real new lemma"; consumes the now-general
          `finrank_range_wedgeFixedLeft = d`).
        - [ ] `extensor_toDual_extensor_eq_zero_of_perp`, and the `dim Ω = D − (D−1) = 1`
          count, then the assembly. The `toDual=Gram` brick (above) is in hand.
- [ ] **CHAIN-1 — the `d`-fold candidate augment** (`RigidityMatrix/Basic.lean`).
      Generalize `linearIndependent_sum_augment_candidateRow` (one `Unit`) to a
      `Fin d`-indexed augment. Graph-free over `ScrewSpace k`; no `d=3` content.
- [ ] **CHAIN-4 — the `Fin (d+1)` incidence + Claim-6.12 discriminator**
      (`Claim612.lean`). Re-state `exists_homogeneousIncidence_of_normals` (the
      `d+1`-point incidence pattern, eq. 6.67), the dispatch-internal bricks,
      `case_III_claim612` (reusing the general `span_omitTwoExtensor_eq_top`
      (23a Leaf 2) + Lemma 2.1), and `exists_complementIso_ne_zero_…` at
      `ScrewSpace (d−1)` / `Fin d` candidates. Consumes CHAIN-3. **OD-4 sub-leaf
      (the eq. 6.67 `d+1`-points step) lands here — flagged open.**
- [ ] **CHAIN-2 — the chain matrix bookkeeping (eqs. 6.59–6.64)** (`CaseIII/`).
      The per-candidate-`i` reduction of `R(G,pᵢ)` to `Mᵢ ⊕ R(G₁∖(v₀v₂)_{i*},q₁)`
      + the ±r chain (6.66). Reuses Claim 6.11 `exists_redundant_panelRow_…`
      (general & GREEN). Heaviest mechanical leaf ("exactly the same as `d=3`").
- [ ] **CHAIN-5 — the `d`-chain dispatch assembly** (`CaseIII/Realization.lean`).
      Replace `case_III_candidate_dispatch`; feed the (general-`k`) arm closers.
      **Signature now FROZEN** by the CHAIN↔ENTRY contract (`notes/Phase23-design.md`
      §"CHAIN↔ENTRY contract" C.3): `hdispatch` consumes a `G.ChainData n` record
      (the length-`d` chain) + the `splitOff (vtx 1)(vtx 0)(vtx 2) e₀` deficiency-0
      fact + the IH-generic base realization on that split. Keep the `d=3` dispatch
      as a `k=2`/length-3 wrapper (no `d=3` regression — C.4 zero-regression map).
- [ ] **CHAIN tail — lift the four 23a-carried producers** (OD-7 fold). After
      CHAIN-3: `hforget_k` (M4 forget, `exists_extensor_eq_panelSupportExtensor`
      routes through CHAIN-3's duality), then through it `hbase_k`/`hcut_k`/
      `hcontract_k`. Direct corollary of CHAIN-3 + numeral pass — caveat (e)
      OD-7: confirm the *only* genuinely-`d=3` reach-in is the duality at build.

## Blockers / open questions

The OD resolutions (full text in `notes/Phase23-design.md` §"CHAIN"(e)):

- **OD-6 — DECIDED: five leaves within ONE sub-phase 23b** (no separate duality
  letter). The arm-realization engine they feed is already general-`k`, so
  neither hard core stands alone as a deliverable. Split at contact only if
  CHAIN-2's index bookkeeping proves larger than estimated.
- **OD-7 — DECIDED: the four 23a-carried producers fold into CHAIN's tail**
  (after CHAIN-3), not a dedicated successor — the M4-forget reach-in *is*
  CHAIN-3's duality, and the conditioned-pair producers route through M4.
  Caveat: confirm at build that the duality is their *only* `d=3` reach-in.
- **OD-4 — FLAGGED (genuinely open; do NOT pre-commit a route).** KT eq. (6.67)
  states the `d+1`-points step **via algebraic independence** (p. 698 verbatim);
  the `d=3` N3a was AVOIDED via an explicit construction (`AlgebraicIndependence.md`
  row #106) that does **not** obviously generalize. Whether general `d` takes
  the existence route or forces the alg-independence hammer is unresolved — the
  CHAIN-4 detailed-build recon decides. Cross-checked `AlgebraicIndependence.md`
  row #107(b) (already scopes this as "uncertain whether a NEW site", defers to
  CHAIN open); this recon confirms the question is real and routes it to build.
- **(b) producer-shape mismatch — SETTLED 2026-06-17** (the docs-only
  contract-settle pass). The CHAIN↔ENTRY interface is frozen in
  `notes/Phase23-design.md` §"CHAIN↔ENTRY contract": a `G.ChainData n` `structure`
  (length-`d` chain `vtx : Fin (d+1) → α`, `edge : Fin d → β`, `e₀`, the deg-2
  closures) is the shared shape. **No motive/IH change forced** (C.6): the chain
  data is purely combinatorial, the base `(G₁,q₁)` is the existing general-`k`
  `HasGenericFullRankRealization` premise pulled from the same 0-dof IH conjunct,
  the `d` candidate splits are smaller 0-dof graphs (no higher-dof `G_v` GAP-6).
  The reshape is **three decls in lockstep** (extractor / producer-`hcand` /
  dispatch-`hdispatch`); the `d=3` line is a zero-regression wrapper (C.4 map:
  chain `v₀v₁v₂v₃ = b—v—a—c`). CHAIN-5's signature is now authorable.
- **OD-1 (re-confirmed for CHAIN/ENTRY).** KT Lemma 5.4 short-cycle base is a
  real branch of the general-`d` chain entry (unlike `d=3`'s inline triangle
  floor); whether CHAIN's dispatch assumes the chain branch (ENTRY discharging
  the cycle branch) is an ENTRY-contract question.

## Hand-off / next phase

**Next buildable sub-step = `inf_range_wedgeFixedLeft` → `finrank_sup_range_wedgeFixedLeft`
at general ambient** (`Meet.lean`, still inside CHAIN-3's last brick
`complementIso_smul_eq_extensor_join`; the `wedgeFixedLeft` building block + its
three facts landed 2026-06-17 lifted `Fin 4` → `{d} (Fin (d+1))`, joining the
`toDual=Gram` bridge / membership brick / proportionality engine from prior
sittings; still no ENTRY-contract dependency). The smallest next commit:
- `inf_range_wedgeFixedLeft` (`Meet.lean:~1068`, the decomposable intersection
  `a∧ℝ^{d+1} ⊓ b∧ℝ^{d+1} = span{a∧b}`) — `Fin 4` → ambient `{d}`. The `d=3` proof
  uses `Fin 3`-arity `decide`/`fin_cases`/`linearIndependent_finSnoc` on `![b,a,v]`,
  all ambient-generic (grade-3 extensor over `Fin (d+1)`); likely a verbatim lift.
Then, the genuinely-new count (a second commit, the "real new lemma"):
- `finrank_sup_range_wedgeFixedLeft` (`Meet.lean:~1128`, the `dim Φ̃ = 3+3−1 = 5`
  count) → a `(d−1)`-summand inclusion–exclusion at general `d` (the panel `Π(u)` has
  `d−1` normals, not 2). The `wedgeFixedLeft` range count `= d` it consumes is now
  general; the new content is the multi-summand inclusion–exclusion shape.
Then `extensor_toDual_extensor_eq_zero_of_perp` (`Meet.lean:~1023`, `Fin 2`/`Fin 4`)
and the assembly `complementIso_smul_eq_extensor_join` (`Meet.lean:~1170`): the
`dim Ω = D − dim Φ̃ = D − (D−1) = 1` count + `complementIso (k:=d−1)(j:=d−1)`. The
`toDual=Gram` brick is in hand to feed the Gram-determinant orthogonality (fact 2)
at general grade. Completing all of this closes CHAIN-3 and feeds CHAIN-4's discriminator.

**The CHAIN↔ENTRY contract is now settled** (`notes/Phase23-design.md`
§"CHAIN↔ENTRY contract", 2026-06-17) — the (b) build-recon gate is discharged:
CHAIN-5's `hdispatch`/`hcand` signature is frozen against the `G.ChainData n`
record (C.1/C.3), so it is now authorable. The next buildable leaf is still in
**CHAIN-3** (its `complementIso`/`toDual` tail — no chain-data dependency;
finishing CHAIN-3 unblocks CHAIN-4 + the four-producer lift). CHAIN-1/3/4 remain
buildable independently of the contract; CHAIN-5 is unblocked once CHAIN-1/2/4
land **and** ENTRY's extractor is reshaped.

**ENTRY obligation — PINNED (signature frozen; minted/built when its turn
comes).** ENTRY reshapes `Graph.exists_chain_data_of_noRigid` (`Reduction.lean:383`)
from the fixed `v,a,b,c` 4-tuple to the `G.ChainData n` producer
`exists_chainData_of_noRigid` (contract C.2 — KT Lemma 4.6 chain + Lemma 4.8
split-off minimality at general `d`, the "new combinatorial leaf" of the
OD-2/OD-3 verdict), and lifts the `6 ≤ bodyBarDim n` floor to the general
chain-length floor. The chain/cycle dichotomy (OD-1, KT Lemma 4.6 / Lemma 5.4)
is **ENTRY's to resolve at build** (contract C.5): the dispatch always consumes
a `ChainData` and never sees the cycle branch, so ENTRY's choice between
"chain-only extractor + cycle folded into base" (default) vs. "disjunction +
Lemma 5.4 short-cycle realization brick" is invariant for CHAIN-5's signature.
**The producer `case_III_hsplit_producer_all_k` (`Arms.lean:777`) is the chain
extractor's only consumer** (it calls the extractor inline at the `|V|≥4` arm,
Arms.lean:828–857) — its `hcand` slot is the third lockstep decl (C.0).

**Green-modulo boundary CHAIN hands downstream** (`notes/Phase23-design.md`
§"CHAIN"(d)): CHAIN discharges the general-`k` `hdispatch` (now against the frozen
`ChainData` contract) and lifts the four producers (OD-7). **ASSEMBLY** composes
the honest general-`d` Theorem 5.5, re-greens `prop:rigidity-matrix-prop11` +
`hub`, derives Thm 5.6, states Conjecture 1.2.

## Decisions made during this phase

(Phase-local choices land here as CHAIN leaves build. The opening recon's
decisions — OD-6/OD-7 resolved, OD-4 + (b) flagged — live in
`notes/Phase23-design.md` §"CHAIN"(e); the chain-data contract lives in its
§"CHAIN↔ENTRY contract".)

### Phase-local choices and proof techniques

- **CHAIN-3 `wedgeFixedLeft` building block: lift the `def` + facts in place to
  implicit `{d}`, no `d=3` instance decls (no external consumers).** `wedgeFixedLeft`
  (`def`) + `coe_`/`ker_`/`finrank_range_` were `Fin 4`-pinned; lifted to ambient
  `{d} (Fin (d+1))`, grade `2`, range count `3 → d` (`= (d+1)−1`). Unlike the prior
  three CHAIN-3 bricks (which kept a `(d:=3)` instance under the old name), these have
  **no consumers outside `Meet.lean`** (grep-confirmed), and the in-file consumers
  (`inf_range`/`finrank_sup_range`/the assembly) still pass `Fin 4` values that unify
  `d=3` by defeq — so generalizing the `def` + facts directly is the lighter touch
  (no instance boilerplate). All four proofs are ambient-generic verbatim (the
  `extensor` API is already `{d}`-generic). The numeral consumer
  `finrank_sup_range_wedgeFixedLeft` (`d=3`, out of scope) needed `(d:=3)` on its
  `finrank_range_` rewrites + `omega → simpa using hsum` (QUIRKS § 58). No blueprint
  pin on any of the four.
- **CHAIN-3 `toDual=Gram` bridge: verbatim grade-/ambient-lift, `d=3` name kept as
  the instance.** `exteriorPower_basis_toDual_eq_pairingDual_comp_map_grade {d}`
  re-states the `Meet.lean` coordinate-`toDual` = `pairingDual ∘ map` bridge over
  `Fin (d+1)` at any grade `n`; its proof is the `Fin 4` body verbatim
  (`Module.Basis.ext` ×2 → Kronecker-delta collapse → determinant diagonal/off-
  diagonal split, only `Set.powersetCard.card_eq` + `Fintype.card_fin`, no
  `Fin 4`-arity). The `d=3` `exteriorPower_basis_toDual_eq_pairingDual_comp_map`
  survives as `:= …_grade (d := 3) n` (`3+1` reduces defeq to `4`), so its internal
  consumer (`extensor_toDual_extensor_eq_zero_of_perp`, line 1003) is untouched and
  no blueprint pointer moves (no pin on this decl). Confirms recon (a): the
  `toDual`/Gram half of the duality is ambient-generic, only the
  `complementIso`-`Φ̃`-count half (the next brick) is genuinely new at general `d`.
  *Authoring trap hit twice:* `-/` inside the docstring words `grade-/ambient` /
  `the grade-/` closed the doc comment early → TACTICS-QUIRKS § 57.
- **CHAIN-3 proportionality engine: same lift pattern, two new grade-generic
  bricks for the count.** `exists_smul_eq_of_mem_range_map_subtype_grade {d}`
  re-states the `Meet.lean` line-identity at grade `d−1` / ambient `Fin (d+1)`
  with hypothesis `finrank W = d − 1`; the `d=3` `exists_smul_eq_of_mem_range_map_subtype`
  survives as `:= …_grade (d := 3) …` (defeq `3−1=2`/`3+1=4`, no `decide`). The
  count it rests on splits into two new grade-generic lemmas, each with the `d=3`
  name kept as a `(d:=3)`/`n:=2` instance: `finrank_exteriorPower_self_eq_one`
  (`exteriorPower.finrank_eq`+`Nat.choose_self`, generalizing
  `finrank_exteriorPower_two_eq_one`) and `exteriorPower_map_subtype_injective_grade`
  (`exteriorPower.map_injective_field`, generalizing the grade-2 pin). All proofs
  verbatim-lift (the route is general mathlib); blueprint pins on the two `d=3`
  names untouched, so no `checkdecls` / blueprint edit. The `complementIso`/`toDual`
  tail bricks are NOT verbatim-liftable (built over `k+2`/`Fin 4`) — flagged in
  the checklist for the next sitting.
- **CHAIN-3 membership brick: lift, don't re-author — keep the `d=3` name as the
  instance.** `extensor_mem_range_map_subtype_of_mem_grade {d}` re-states the
  `Meet.lean` membership at grade `d−1` / ambient `Fin (d+1)`; its proof is the
  `d=3` body verbatim (grade enters nothing). The old `Fin 4`/`⋀²`-pinned
  `extensor_mem_range_map_subtype_of_mem` survives as a one-line corollary
  `:= …_grade (d := 3) W v hv` (`3−1`/`3+1` reduce defeq to `2`/`4`, so no
  coercion/`decide`) — zero regression to its downstream consumers, no blueprint
  pointer touched. Confirms recon (D)'s "template, not verbatim reuse" call: the
  *route* is grade-generic, only the lemma statements need re-pinning.
- **Opened on a detailed leaf-level recon, not a build** (the design-pass-first
  discipline, `DESIGN.md` *Scale-up: design the LAYER*; the Case-I node-by-node
  precedent). The recon source-verified the central scoping fact — the
  arm-realization engine is already general-`k`, only the dispatch is `d=3` —
  and surfaced the producer-shape flag (b) before any leaf builds.
- **CHAIN↔ENTRY chain-data contract settled (docs-only design-settle pass,
  2026-06-17)** → `notes/Phase23-design.md` §"CHAIN↔ENTRY contract". Froze the
  shared interface flag (b) left open: a `G.ChainData n` `structure` (length-`d`
  chain `vtx : Fin (d+1) → α` / `edge : Fin d → β` / `e₀` + the degree-2 closures,
  grounded in KT eqs. 6.46–6.59 + the landed `splitOff` API), the reshaped
  producer-side extractor (C.2, an ENTRY obligation), the CHAIN-5 consumer
  `hdispatch` (C.3, now frozen), the zero-regression `d=3` wrapper map (C.4,
  chain `v₀v₁v₂v₃ = b—v—a—c`), and the OD-1 chain/cycle division (C.5: the
  dispatch always consumes a `ChainData`, never the cycle branch). Clause-(ii)
  verdict (C.6): **no motive/IH change forced** — chain data is combinatorial,
  base `(G₁,q₁)` is the existing general-`k` premise, candidate splits are
  smaller 0-dof graphs; the only routed unknowns are OD-1 (ENTRY's dichotomy
  shape) and OD-4 (CHAIN-4's alg-independence route), both build-time.

### Promoted to TACTICS-GOLF / TACTICS-QUIRKS / FRICTION / DESIGN

- *A `-/` inside a docstring word (`grade-/ambient`) closes the doc comment early
  → "unexpected identifier; expected 'lemma'" inside the prose* → TACTICS-QUIRKS § 57.
- *After lifting an in-place numeral-pinned `def` to implicit `{d}`, a numeral
  consumer's `omega` mis-atomizes the `(d:=3)`-vs-numeral elaborations of one term
  (free-variable counterexample, never reads the bridging hyp) — use `linarith` /
  `simpa using h`* → TACTICS-QUIRKS § 58 / FRICTION [idiom] *Generalizing an in-place
  numeral-pinned `def`…*.
