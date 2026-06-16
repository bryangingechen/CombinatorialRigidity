# ScrewSpace carrier opacity — design / prep doc for a future refactor

**Status: PREP / DEFERRED — design-recon complete (2026-06-16).** This is the single
canonical home for the post-22k investigation into the `maxHeartbeats` cost of the
`ScrewSpace` carrier (and its `abbrev` siblings) and the *carrier-opacity* refactor
option. The opacity **spike** (§3) and the **design-recon** (§5) are both done: the recon
killed the surgical "localized wrapper" option, leaving a full-carrier migration (Shape 2,
~3–5 sessions) as the only coherent path. A follow-up **micro-spike** (§5 OQ3) then confirmed
the `screwBasis` transport is *defeq-free* — downgrading the recon's hardest category to
mechanical and leaving the unconfirmable end-to-end cap drop (§5 OQ1) as the dominant residual
risk. **No migration is scheduled** — the now-vs-later call (now three-way; §6) is open.
`notes/PERFORMANCE.md` and `notes/FRICTION.md` point here; the opacity-spike dispatch records
live in `notes/model-experiment.md` (rows 167–170).

**TL;DR.** `ScrewSpace k` (`Molecular/RigidityMatrix.lean:88`) is a reducible
`abbrev = ↥(⋀^k (Fin (k+2) → ℝ))`. Reducibility means every defeq / `simp` / `rw`
motive over it (and over `α → ScrewSpace k`, `Module.Dual ℝ (α → ScrewSpace k)`)
re-unfolds the heavy exterior-power expression — the *diffuse typeclass* cost behind
the three surviving elevated `maxHeartbeats` overrides. A spike confirmed that making
the carrier **opaque** cuts that cost ~5–60× on the relevant patterns, but the full
refactor's blast radius is prohibitive as a big-bang. **The design-recon converted the open
"is it worth it?" into a concrete go/no-go: Shape 2 (full carrier) is the only coherent path,
GO-able but a 3–5 session commitment; design-risk is ~0 *for the current d=3 usage* but
unknown for the unbuilt general-`d` work (§6). Recommendation: bank the 7→3 win, lean toward
deferring the full migration to the Phase-23 design boundary or post-program (§6). The
`screwBasis`-transport micro-spike (§5 OQ3) is done — it confirmed the transport is defeq-free
(the hardest category → mechanical), leaving the unconfirmable end-to-end cap drop (§5 OQ1) as
the dominant residual risk.**

## 1. The problem — three surviving `maxHeartbeats` overrides

The post-22k audit (commit `83d5c5c`) minimized the molecular `maxHeartbeats`
overrides 7→4; the fused `finrank_sup_of_inf_eq_bot` mirror (`ae77b36`) took it to
7→3 by removing the cut brick's. The three survivors, all diagnosed **inherent**:

| Decl | File | Cap | Driver |
|---|---|---|---|
| `case_cut_edge_realization` | `Theorem55.lean` | 400000 | diffuse `ScrewSpace 2` TC re-elaboration (~16 s summed algebraic-TC, no family > 0.8 s) across a duplicated `\|C\|=0/1` two-arm body, paid ~2×. Lever: factor the shared branch (~P3, low confidence it alone reaches default). |
| `case_cut_edge_realization_gp` | `Theorem55.lean` | 600000 | same diffuse cost + the GP-seed / per-side rank-polynomial / `ofNormals` motion-space layers. The §38 *final-`∃`-witness* fix is **N/A** (witness already consumer-routed, not hand-assembled). |
| `case_II_realization_all_k` | `CaseII.lean` | 600000 | residual `CoeT` rank-cast load (≈ 3.9 s × 21, already minimized 16×→3× in 22j) + diffuse Step-12–15 geometric `isDefEq`. |

All three: diffuse §38-class typeclass cost over the carrier, **no single extractable
hotspot** (so the cheap "mark one heavy def irreducible" lever does not apply — see §4).
The fourth original survivor, `le_finrank_span_rigidityRows_of_cut`, was **resolved**
by the fused `finrank_sup_of_inf_eq_bot` mirror (now builds at default 200000; see
`notes/FRICTION.md` *Mirrored*).

## 2. The mechanism — reducible `abbrev` ⟹ repeated unfolding

`abbrev` is `@[reducible] def`. Reducible definitions are unfolded during instance-search
head-keying **and** during defeq/whnf. So over `ScrewSpace k` the elaborator repeatedly
materialises the heavy `↥(⋀^k …)` expression at every motive. Two distinct costs ride on
this, and only one is ScrewSpace's:

- **Instance-search cost** (deep hierarchies, noncomputable detours). *Not* the issue here:
  `Module ℝ (α → ScrewSpace k)` is `Pi.module → Submodule.module`, two single-step, cached
  hops — shallow. This is why **shortcut instances, instance priorities, and
  named-instances-on-the-`abbrev` do not help** — they target search depth, which is already
  cheap, and (being keyed on the reduced `↥(⋀…)` head) cannot create the distinct fast head
  that opacity gives. Priorities are additionally global/fragile (diamond risk, non-local
  regressions).
- **Type-expression whnf/defeq cost** — the heavy `↥(⋀^k …)` re-unfolding during unification
  at every `LinearMap.ext` / `≃ₗ` / `Module.Dual` motive over the carrier. **This is the
  dominant cost**, and only making the carrier opaque (a distinct non-reducing head) stops it.

## 3. The spike (2026-06-16, opus, throwaway seeded worktree; `notes/model-experiment.md` row 170)

Verdict **MIXED — positive mechanism, prohibitive blast radius.**

- **Mechanism confirmed.** Controlled synthetic benches (identical proofs, `abbrev` vs opaque
  `def`), by `maxHeartbeats` cap-descent (the `#count_heartbeats in` *command* is unreliable in
  this toolchain — use cap-descent): pure-`finrank` chains that never crack the carrier open are
  flat; **`Module.Dual` / `LinearMap.ext` / `≃ₗ`-automorphism over the carrier drop ~5–60×**
  (`dual_ext` 8–16k→1.5–2k; `columnOp` 8–16k→200–500). The win is instance synthesis matching a
  *named* `Module`/`AddCommGroup`/`FiniteDimensional` instance on the distinct opaque head rather
  than re-deriving through `↥(⋀…)`. Three `inferInstanceAs` instances sufficed (no `fast_instance%`
  needed) + a `ScrewSpace_def : ScrewSpace k = ↥(⋀…) := rfl` bridge.
- **Blast radius prohibitive.** Opacity breaks the pervasive `⟨val, proof⟩ : ScrewSpace`
  anonymous-constructor idiom and the surrounding `rw [Submodule.mem_span_singleton]` /
  `Subtype.val` / `screwBasis`-coordinate chains, which need the carrier to be a *transparent*
  Subtype. The home file `RigidityMatrix.lean` breaks at ~3 mechanical sites, but the **5 geometry
  files** that *construct* screw-space elements (PanelLayer, Pinning, GenericityDevice, CaseIII,
  RigidityMatrix) break at hundreds of sites, ~15–25 % needing genuine thought. Adversarial
  topology: the cost win lives in the *assembly* files (CaseI/II/Theorem55 — ~0 break-prone
  constructs, migrate near-free *and* hold the survivor caps), but they sit strictly *behind* the
  geometry rework. The spike could not reach a survivor to confirm an end-to-end cap drop.

**The spike's breakage catalog is the first draft of the opaque API's requirements** (§5).

## 4. mathlib precedents — and where ScrewSpace sits

Two mathlib patterns for "unfolding is the cost":

- **Pattern A — opaque type carrier** (wrap so the *type* never unfolds): `Polynomial`
  (`structure` over `AddMonoidAlgebra R ℕ`, "irreducible from the point of view of the kernel …
  Lean cannot compute anyway with `AddMonoidAlgebra`"), `Real` (`structure` over the Cauchy
  completion). Expensive — Polynomial's own docs note they "have to copy across all the arithmetic
  operators manually," and there is active work to make it defeq to `AddMonoidAlgebra` again.
- **Pattern B — irreducible heavy *construction*** (`@[irreducible]` / `irreducible_def` on a
  single heavy def to "contain abuse of defeq" / "avoid deep unfolds"): `CategoryTheory/Shift`,
  `CategoryTheory/ObjectProperty/Shift`, `AlgebraicTopology/SimplicialSet/CompStruct`,
  `RingTheory/FractionalIdeal`, the `NormNum/Pow` opaque `Nat.pow` wrapper. Cheap — no type-API
  re-plumbing.

**ScrewSpace is Pattern A, and the *hard variant* of it.** Its cost is the *type* unfolding inside
generic mathlib machinery (no single project def to mark → Pattern B does not apply, consistent with
"diffuse, no single hotspot"). And unlike Polynomial/Real — which were **born opaque with APIs that
hide the carrier** — ScrewSpace is a reducible `abbrev` whose geometry code *reaches into the carrier
everywhere*, so a retrofit pays the full migration. Flavor note: Polynomial/Real lean "kernel can't
compute with the rep"; ScrewSpace's is the *elaborator-defeq* flavor, closest to the Pattern-B
"abuse of defeq" cases. `fast_instance%` is the standard instance companion when re-declaring opaque-
carrier instances (the spike found plain `inferInstanceAs` enough here).

## 5. The design-recon result (2026-06-16) — Shape 1 dead, Shape 2 the only path

A read-only design-recon (opus) mined every `ScrewSpace`-typed reach-in across the 11 referencing files
into a concrete API spec and a per-file migration estimate. **The key enabler held:** the accumulated
call-site usage across Phases 17–22 *is* the API spec, so the boundary surface is observed, not guessed.

### Verdict: Shape 1 (localized wrapper) is NOT viable

The hoped-for surgical path — a separate opaque `def ScrewSpaceModule` used *only* in the capped
assembly files (CaseI/II/Theorem55) with a `≃ₗ` to `ScrewSpace` at the boundary, putting the opaque head
exactly where the caps live without touching the geometry files — **does not exist.** The opaque head
cannot be localized:

- The realization predicates the capped decls return *and* consume structurally embed `ScrewSpace k`:
  `HasPanelRealization` / `HasGenericFullRankRealization` (`PanelHinge.lean:1035/1090`) quantify
  `BodyHingeFramework k`, whose `.supportExtensor : β → ScrewSpace k` and
  `.rigidityRows : Set (Module.Dual ℝ (α → ScrewSpace k))`. A boundary `≃ₗ` would have to thread inside an
  existential witness shared by the whole import chain.
- The capped bodies are saturated with carrier reach-ins (`case_II_realization_all_k`
  (`CaseII.lean:298`) alone: ~40 `panelSupportExtensor` values + `annihRow` duals +
  `LinearMap.single`/`Function.update` over `α → ScrewSpace 2`, spread across its ~16 geometric Steps).
  Re-wrapping each *is* the full migration, not a localization. The caps are light *relative to geometry*
  but not isolable.

### The path: Shape 2 (full opaque carrier, bottom-up)

`abbrev ScrewSpace` → `def` + 3 `inferInstanceAs` instances + the `_def` bridge; replace `⟨val,proof⟩`
with a `ScrewSpace.mk`/`.val` (or `≃ₗ`) API; migrate one file green at a time along the import spine. The
recon corrected the doc's earlier file map:

- **`Meet.lean` is PASS-THROUGH, not geometry** — it operates on the bare `⋀[ℝ]^j V` Subtype directly and
  never returns a `ScrewSpace k`-typed value, so opacity leaves it untouched.
- **`PanelHinge.lean` IS a geometry file** (defines `supportExtensor`) — the doc's earlier order omitted it.
- Corrected spine: **RigidityMatrix → PanelLayer → Pinning → PanelHinge → GenericityDevice → Coupling →
  CaseI → CaseII → CaseIII → Theorem55** (Meet/Extensor feed RigidityMatrix; Meet untouched).

**Estimate:** ~150–200 genuine `ScrewSpace`-typed reach-in sites across 7 files; ~110–150 mechanical,
**~30–45 needing real thought**; roughly **3–5 sessions**. The needs-thought work concentrates in
RigidityMatrix's API + `Module.Dual`-ext lemmas, PanelLayer's `screwBasis`/`annihRow`, and
GenericityDevice's 5× `change`-on-basis blocks (the hard parts below). Reach-in categories: (a)
`mk`-from-membership `⟨val,proof⟩`, (b) `val`/coercion to `⋀^k`, (c) span-membership (**mostly survive
unchanged** — span is module-level, opacity-neutral), (d) `screwBasis` coordinate access, (e)
`Module.Dual` / zero / `LinearMap.single` reach-ins (the §38 cost site).

### The drafted API surface

```lean
def ScrewSpace (k : ℕ) : Type := ↥(⋀[ℝ]^k (Fin (k + 2) → ℝ))
theorem ScrewSpace_def (k : ℕ) : ScrewSpace k = ↥(⋀[ℝ]^k (Fin (k + 2) → ℝ)) := rfl  -- the defeq bridge; used sparingly
-- named instances on the opaque head (spike: plain inferInstanceAs sufficed, no fast_instance%):
noncomputable instance (k) : AddCommGroup (ScrewSpace k)        := inferInstanceAs (AddCommGroup ↥(⋀[ℝ]^k _))
noncomputable instance (k) : Module ℝ (ScrewSpace k)            := inferInstanceAs (Module ℝ ↥(⋀[ℝ]^k _))
noncomputable instance (k) : FiniteDimensional ℝ (ScrewSpace k) := inferInstanceAs (FiniteDimensional ℝ ↥(⋀[ℝ]^k _))
-- the mk/val API replacing ⟨val,proof⟩ and (C : ExteriorAlgebra …):
def ScrewSpace.mk  {k} (v : ExteriorAlgebra ℝ (Fin (k+2) → ℝ)) (h : v ∈ ⋀[ℝ]^k _) : ScrewSpace k := ScrewSpace_def k ▸ ⟨v, h⟩
def ScrewSpace.val {k} (C : ScrewSpace k) : ExteriorAlgebra ℝ (Fin (k+2) → ℝ) := (ScrewSpace_def k ▸ C : ↥_)
@[simp] theorem ScrewSpace.val_mk …  ;  @[simp] theorem ScrewSpace.mk_val …  ;  theorem ScrewSpace.val_injective …
-- a linear-equiv form, cleaner for the basis/dual work:
noncomputable def ScrewSpace.equivExteriorPower (k) : ScrewSpace k ≃ₗ[ℝ] ↥(⋀[ℝ]^k _) := … -- via ScrewSpace_def
-- screwBasis transported across the equiv (replaces the .exteriorPower-direct definition):
noncomputable def screwBasis (k) : Module.Basis _ ℝ (ScrewSpace k) :=
  ((Pi.basisFun ℝ (Fin (k+2))).exteriorPower k).map (ScrewSpace.equivExteriorPower k).symm
@[simp] theorem screwBasis_repr_apply …  ;  @[simp] theorem screwBasis_coord_apply …  -- behaviour through the iso
```

Every reach-in category maps onto this; the two categories where the mapping is *not* clean are the hard
parts below.

### The hard parts — two mechanisms

Both reduce to the same root: **opacity removes a defeq that existing proofs silently rely on.**

- **(d) The `screwBasis`/`annihRow` foundation — small but load-bearing.** `screwBasis k` is *defined* as
  `(Pi.basisFun ℝ (Fin (k+2))).exteriorPower k` (`PanelLayer.lean:1247`) — a `Module.Basis _ ℝ (↥(⋀^k V))`
  accepted as a basis *of `ScrewSpace k`* only via reducible defeq. Opaque, it must become
  `(…).exteriorPower k |>.map (equivExteriorPower k).symm`, and `screwBasis.repr`/`.coord` must be
  re-proven *through* the iso. `annihRow` (`PanelLayer.lean:1256`) and its `@[simp]` family (`annihRow_apply`,
  `_apply_self`, `_add`, …) are built on `.repr`/`.coord` and must survive the transport;
  `GenericityDevice.lean:220`'s `change … (Pi.single a (screwBasis k t)) = …` lands *only* because the
  basis vector is defeq-transparent, so opaque it becomes a `rw`/`simp` (×5 near-identical blocks).
  Concentrated — 2 defs + their simp lemmas + 5 blocks — but the coordinate foundation everything else sits
  on. **De-risked by the micro-spike (OQ3 below): the transport turns out defeq-free, so this is essentially
  mechanical, not the hardest category the recon feared.**
- **(e) The `Module.Dual` proofs — win and risk are the *same* sites.** This is the §38 cost site. Opacity
  changes defeq in *both* directions: it *stops the bad descent* (TACTICS-QUIRKS §32's `ext x` mis-binding
  to `Fin k → Fin (k+2) → ℝ`, whose explicit-`LinearMap.ext` workaround then becomes *unnecessary*) but
  *also stops the good reductions* some proofs exploit (anything closing by unfolding
  `.repr`/`.coord`/`annihRow` *through* the carrier). You cannot tell mechanically which proof is in which
  bucket until you flip the carrier and rebuild — that is the irreducible needs-thought core, spread across
  all 7 files. NB the molecular subsystem has *already* accreted ~10 distinct carrier-whnf workarounds
  (TACTICS-QUIRKS §38: `set`/`clear_value`, abstract-basis helpers, consumer-routing the final `∃`-witness,
  the `T`-bundle for `span_induction`); opacity would render many *unnecessary* — but removing them is
  unbudgeted (open question 2).

### Open questions (not resolvable from the current tree)

1. **No cap confirmation until the whole spine is green.** The spike got 5–60× on *synthetic* benches but
   could not reach a survivor; the three caps sit at the *top* of the spine (Theorem55, CaseII), so Shape 2
   commits 3–5 sessions validated only on proxies until the very end.
2. **Remove the §38 workarounds, or leave them?** The "mechanical" estimate assumes leaving them (harmless
   over an opaque carrier — just no longer load-bearing). Removing them is where much of the *clarity*
   payoff lives — but it is additional, genuinely needs-thought, unbudgeted work. A scope fork *inside*
   Shape 2.
3. **`screwBasis`-transport cleanliness** (hard-part (d)) — **ANSWERED by the micro-spike (2026-06-16,
   throwaway scratch file): the transport is *defeq-free*.** Because the opaque carrier is a plain
   (semireducible) `def`, it stays defeq to `↥(⋀^k…)` at *default* transparency, so the boundary `≃ₗ` is
   `LinearEquiv.refl` and `Basis.map` by it is a definitional no-op — `(screwBasis').repr v t = (direct
   exterior basis).repr v t` and `screwBasis' t = (direct basis vector)` both hold **by `rfl`**, and a
   `change`/`rfl` onto the direct basis vector still lands (the GenericityDevice site). So every existing
   coordinate lemma (`exteriorPower.basis_repr_apply`, `normalsJoin_repr`, `panelSupportPoly_eval`) ports
   verbatim, and `annihRow_apply` is opacity-neutral (abstract `Basis.coord_apply`). **Hard-part (d)
   downgrades from "single hardest, verbosity-propagating" to essentially mechanical.** Caveat: this is
   *default*-transparency defeq; the perf win lives at *reducible/instance* transparency (where the `def`
   does not unfold), so the two don't conflict — but the spike confirms only that the transport is *clean*,
   not the end-to-end cap drop (that is OQ1, now the dominant residual risk).
4. **`inferInstanceAs` at general `k`** — **the instance-resolution half is now confirmed:** the micro-spike
   declared all three `inferInstanceAs` instances (`AddCommGroup`/`Module`/`FiniteDimensional`) at general
   `k` and they compiled, so `FiniteDimensional ℝ ↥(⋀^k _)` etc. resolve symbolically. What remains is not
   the instances but the general-`d` *usage* surface (the new reach-in patterns Phase 23 introduces) — that
   feeds the unbuilt-work question (§6).

**Sibling `abbrev` carriers** (same diagnostic if the pattern is adopted): `Framework`/`Motion` (function
types over `EuclideanSpace`), `KFrameField` (`FractionRing (MvPolynomial …)`). (`screwDim` is a ℕ value,
`screwBasis` a term — not carriers.)

## 6. Now vs later — a three-way call, sharpened by unbuilt work

The recon's "design-risk ~0" is true **only for the current d=3 usage.** Every existing `ScrewSpace`
reach-in is at `k = 2` / `d = 3`; **Phases 23–26 are entirely unbuilt** ("◷ Planning — none yet"). An
opaque API frozen now is frozen against usage that does not yet include the general-`d` case — and
**Phase 23 = general-`d` Case III** is precisely the phase that stresses the hardest category:

- At `k=2`, `screwDim k = 6` is concrete and `Set.powersetCard (Fin 4) 2` has 6 elements; many current
  proofs lean on `fin_cases`/`decide`/concrete arithmetic.
- At general `k`, `screwDim k = C(k+2,k)` is symbolic; the `screwBasis`/`annihRow` coordinate machinery —
  hard-part (d) — gets exercised symbolically for the first time. General-`d` will both *add* reach-in
  sites and *stress-test the transport* in a way today's tree never does. (The recon could not see this:
  it only mined the existing, all-d=3 call sites.)

So the binary is really three-way:

- **Now** — clean foundation before general-`d`; but API frozen against d=3, real risk Phase 23 forces a
  reshape (re-introducing the design-risk that waiting was meant to remove), and the cap drop stays
  unconfirmed for 3–5 sessions.
- **At the Phase-23 design boundary** — once general-`d` Case III is *designed* (general-`k` reach-in
  surface known) but *before* it is built (don't pay the transparent-carrier cost building it). The
  "wait for crystallisation" benefit without the worst of the "build 23–26 transparent" cost. Requires
  Phase 23's design to be far enough along to know the surface.
- **Post-program** — usage fully crystallised, design-risk genuinely zero; but all of 23–26 built on the
  transparent carrier, accreting *more* §38 workarounds and paying the perf cost throughout.

**Recommendation.** Bank the 7→3 win and keep the three caps documented-inherent. The unbuilt-work
dependency materially strengthens *waiting* over *now* — lean toward the **Phase-23 design boundary** (or
post-program). The **`screwBasis`-transport micro-spike is done** (§5 OQ3): it confirmed the transport is
defeq-free, so the recon's hardest category (d) is mechanical and design-risk for the *known* surface is
genuinely low — the residual risks are the unconfirmable end-to-end cap drop (OQ1) and the unbuilt
general-`d` surface (above). **Decide the full-migration timing at the Phase-23 design boundary.**
