# ScrewSpace carrier opacity — design / prep doc for a future refactor

**Status: PREP / DEFERRED (opened 2026-06-16).** This is the single canonical home
for the post-22k investigation into the `maxHeartbeats` cost of the `ScrewSpace`
carrier (and its `abbrev` siblings) and the *carrier-opacity* refactor option. **No
refactor is scheduled** — the now-vs-later call is open (§6) and the refactor itself
should be done in a fresh session / its own phase. `notes/PERFORMANCE.md` and
`notes/FRICTION.md` point here; the dispatch records live in `notes/model-experiment.md`
(rows 167–170).

**TL;DR.** `ScrewSpace k` (`Molecular/RigidityMatrix.lean:88`) is a reducible
`abbrev = ↥(⋀^k (Fin (k+2) → ℝ))`. Reducibility means every defeq / `simp` / `rw`
motive over it (and over `α → ScrewSpace k`, `Module.Dual ℝ (α → ScrewSpace k)`)
re-unfolds the heavy exterior-power expression — the *diffuse typeclass* cost behind
the three surviving elevated `maxHeartbeats` overrides. A spike confirmed that making
the carrier **opaque** cuts that cost ~5–60× on the relevant patterns, but the full
refactor's blast radius is prohibitive as a big-bang. **Recommendation: defer; if/when
revisited, the accumulated call-site usage is now the API spec — start with a
design-recon, not a migration.**

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

## 5. The refactor plan (if/when pursued) — design-recon FIRST

**The key enabler: the accumulated call-site usage is now the API spec.** At Phase 17 an opaque API
would have been a speculative guess at the boundary surface; now every reach-in across Phases 17–22 is
an observed requirement. The spike's breakage catalog already names the surface: **`mk`-from-membership,
a `val`/coercion (or `≃ₗ`), span-membership lemmas, and `screwBasis` coordinate access.** So design-risk
is ~zero; the remaining cost is migration (mechanical-but-large), which a good API can *reduce* (clean
mapping onto existing patterns) but not eliminate.

Two shapes, smallest first:

1. **Localized opaque wrapper** (the plausible surgical path): a separate opaque `def ScrewSpaceModule`
   used *only* in the assembly files (CaseI/II/Theorem55) with a `≃ₗ` to `ScrewSpace` at the boundary —
   puts the opaque head exactly where the caps live without touching the 5 geometry files. Confirm by
   re-measuring one survivor's cap before committing.
2. **Full opaque carrier** (only if the localized variant is insufficient): `abbrev ScrewSpace` → `def`
   + 3 `inferInstanceAs` instances + the `_def` bridge; replace `⟨val,proof⟩` with a `ScrewSpace.mk`/
   `.val` coercion API; migrate bottom-up (RigidityMatrix → PanelLayer → Pinning/GenericityDevice →
   CaseIII → CaseI → CaseII → Theorem55), one file green at a time.

**Sibling `abbrev` carriers** (same diagnostic if the pattern is adopted): `Framework`/`Motion`
(function types over `EuclideanSpace`), `KFrameField` (`FractionRing (MvPolynomial …)`). (`screwDim`
is a ℕ value, `screwBasis` a term — not carriers.)

**Sequencing:** a *design-recon* first — mine the call sites into a concrete API spec (seed = the §3
breakage catalog), draft the `mk`/`val`/boundary-lemma surface, and produce a **bounded, per-file
migration estimate** — *without committing to the migration*. That converts the open "is it worth it?"
into a concrete go/no-go. Do **not** migration-first.

## 6. Now vs later

- **For now:** it is the cheapest it will ever be — Phases 23–26 (general-`d` Case III, the 3-D matroid,
  projective invariance, the molecule application) pile *more* construction onto the carrier, so the
  migration and the perf pain both grow; a clean API would pay off across all remaining phases in perf
  *and* clarity.
- **Against now:** it is a multi-session detour from the actual deliverable (the molecular conjecture),
  and general-`d` may reveal *new* boundary requirements — re-introducing a little of the design-risk
  that waiting was meant to remove.

**Recommendation.** Design-recon-first *if* the foundation is judged worth investing in before the
remaining math; otherwise bank the 7→3 win, keep the three caps documented-inherent, finish Phases
23–26, and do the clean-carrier refactor as a **post-program cleanup** (by which point usage is fully
crystallised and design-risk is zero). Both are defensible. **Decide in a fresh session.**
