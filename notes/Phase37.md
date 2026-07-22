# Phase 37 — `Molecular/` fragility-zone tactic sweep (AUTOMATE-Z, post-program) (work log)

**Status:** Complete (opened and closed 2026-07-22). Internals-only,
structural-edit style — no new blueprint chapter, no new mathematics; every
headline statement and its axiom profile unchanged (all 17 re-verified at the
three standard axioms `propext`/`Classical.choice`/`Quot.sound` at close). The
deferred slice 6 of Phase 36 (AUTOMATE), spun off as its own phase per the user
decision 2026-07-22. **PIN is the next queued phase to open** (ROADMAP *Queued
post-program phases*).

## Result

**GO — the going-in "Default NO-GO" prior overturned.** The six-slice,
file-cluster sweep of the defeq-fragile zone (`Molecular/`'s
`AlgebraicInduction/` incl. `CaseIII/` + `Theorem55.lean`, `RigidityMatrix/`,
and the ScrewSpace-carrier-touching files — ~381 four-plus-arg `rw` chains +
~114 `change`/`show` sites across 28 files) landed **103 build-neutral
`rw→simp only` collapses, 17 reverted** (per-slice landed/reverted:
Z1 6/4, Z2 37/7, Z3 12/0, Z4 12/2, Z4b 4/0, Z5 26/3, Z6 6/1). Each landed
collapse passed a per-file 4-run-median build-neutral gate
(`notes/PERFORMANCE.md` protocol) with a warning-clean `lake build` + `lake
lint`. Annotation set stayed **∅** (no `@[grind]` / attribute additions), so
the gate was genuinely per-file. Every slice dispatched at opus-minimum
(fragility floor). Friction review: nil across all slices (pure tactic swaps +
reverts; no new lemmas / API).

**Measured zone model (promoted to `TACTICS-GOLF.md` §7):** the defeq wall is
**site-level, not file-level** — confined to chains touching a *raw*
carrier-coercion site (raw `supportExtensor`/`ScrewSpace.val` unfolds, BIDIR
`dualMap`/`toDual` bridge pairs). Carrier-cluster *files* and even
carrier-*adjacent* chains routed through **packaged** API collapse freely
(`simp only` matches the packaged lemma before it must whnf through the
carrier). The 0-revert slices came from filtering the fragile shapes pre-build,
not from their absence.

The six collapse predictors / fragility shapes this phase produced are folded
into `TACTICS-GOLF.md` §7: trailing-`rfl`/`@[refl]`-residual; conditional-rewrite
no-progress; the `have`-block-closing discriminator refinement;
positional-sequential no-progress; leading-args-fire/trailing-arg-stranded; and
the site-level verdict above.

## Hand-off / next phase

Phase closed. **PIN** — the 2-d molecular conjecture via Jackson–Jordán 2008's
pin-collinear body-and-pin route (ROADMAP *Queued post-program phases*) — is the
next queued phase to open; unplanned, so opening it starts with its own
survey/planning note. The reusable sweep method (scan `rw4+`; exclude
BIDIR(`←`) / positional(`at h`) / goal-shaping-feeder / raw-carrier
`supportExtensor`/`ScrewSpace.val` unfolds / permutation-swap loopers on sight;
batch-convert surviving *closing* chains to `simp only` — dropping exact
duplicates up front = the dedup collapse — build once, read diagnostics, then
per-file 4-run median) is settled and lives in `TACTICS-GOLF.md` §7.

## Decisions made during this phase

One-line verdict per slice (blow-by-blow in git; predictors in
`TACTICS-GOLF.md` §7):

- **Z1 — ScrewSpace-carrier leaf files (`Molecule/`):** 6 collapses, 4 reverted
  (all trailing-`rfl` shape 1). Leaf files admit build-neutral collapses;
  carrier/definitional chains do not.
- **Z2 — RigidityMatrix carrier cluster + `Meet` (the pivot):** 37 collapses
  (16 dedup), 7 reverted. Overturned the "carrier pivot ≈ 0" prior — the wall
  is raw-carrier-coercion chains, not the files; packaged carrier-adjacent API
  collapses. Surfaced the conditional-rewrite no-progress shape.
- **Z3 — AlgInd Cases I/II + Coupling:** 12 collapses, 0 reverted. Highest
  testable fraction; even flagged-risky `dualMap`/cast chains landed. Surfaced
  the `have`-block-closing discriminator refinement.
- **Z4 — AlgInd panel/pinning/genericity:** 12 collapses, 2 not-landed
  (Theorem55 split to Z4b). Surfaced the positional-sequential no-progress shape
  (PanelLayer L1720).
- **Z4b — Theorem55:** 4 collapses, 0 reverted. Packaged-API carrier-adjacent
  chains collapse even in the most carrier-adjacent AlgInd file.
- **Z5 — CaseIII core (Candidate/Realization/Arms):** 26 collapses (~11 dedup),
  3 reverted. The "extensor-join ⇒ low testable fraction" framing overturned
  (30 of 63 testable). Surfaced the leading-args-fire/trailing-arg-stranded shape.
- **Z6 — CaseIII Relabel:** 6 collapses (2 dedup), 1 reverted. Generalized the
  trailing-`rfl` predictor beyond `Eq` to any `@[refl]` relation (a `≤` goal
  whose sides reduce to the identical term, no `le_refl` in the list).

### Promoted to TACTICS-GOLF

- *The `rw→simp only` collapse discriminator + fragility catalog (site-level
  verdict; six predictors/shapes)* → `TACTICS-GOLF.md` §7.
