# Phase 12 cleanup round — work log

**Status:** in progress (A–D surveys run; **A3 fix landed** — stale
forward-mode chapter-intro paragraph removed from `matroid-union.tex`;
remaining buckets surveyed-but-unfixed, expected mostly no-op under the
vendored-port bias).

This is the inter-phase cleanup round covering **Phase 12** (matroid
foundations: submodular functions + matroid union). See `../CLEANUP.md`
for the round-level operating manual: when to run a round, the four
audit categories (A blueprint-divergence, B code-smell, C long-proof,
D project-organization), and the per-round workflow. The task list
below is the round's "lemma checklist" equivalent — populated up front
per CLEANUP.md's *Sweep first, fix later* + *Task list discipline* so a
session that runs out of time can hand off cleanly.

## Current state

The §A blueprint↔Lean divergence walk over `matroid-union.tex`'s nine
`\lean{...}` entries, the §B code-smell greps over the two Matroid
files, the §C long-proof ranking, and the §D org-compression check
have all been **run** (results recorded under *Task checklist* below).
**A3 landed** (the only A-bucket fix the survey surfaced): the stale
forward-mode "currently red / to-do list" chapter-intro paragraph in
`matroid-union.tex` was removed; `verify.sh` green. The remaining
buckets (A1/A2 statement/proof walks, B1–B6, C2, D1–D5) are surveyed
but unfixed — expected mostly no-op under the vendored-port bias.
Build of both Lean files is cached green and warning-clean.

**Scope (coordinator-decided): Phase-12 surface** —
`CombinatorialRigidity/Matroid/Constructions/Submodular.lean` (1151 L),
`CombinatorialRigidity/Matroid/Constructions/Union.lean` (516 L), and
`blueprint/src/chapter/matroid-union.tex` (182 L). Audit categories
A–D as applicable, matching the prior post-Phase-N cadence (post-8,
post-9, post-10+11 each scoped to the phase's surface, not
project-wide; project-wide drift was discharged by Phase 7-cleanup and
reconfirmed since).

**Vendored-port caveat (sets the §B/§C disposition bias).** Both Lean
files are **ports** of Peter Nelson's `apnelson1/Matroid` WIP
(Apache-2.0; per-file headers carry the attribution + modifications
list — verified present and complete at round open). Per `../CLAUDE.md`
*Vendored provenance* and `../DESIGN.md` *Local mirror of the
matroid-union subsystem*, the discipline here is: warning-clean and
style-clean per the project lint policy (`../CombinatorialRigidity/
CLAUDE.md` *build and lint gates* — "a style sweep there is low-risk"),
but **do not reshape the vendored proof content** without a strong
reason, since that diverges from upstream and complicates offering the
port back. The §B `classical` / `Fintype.ofFinite`-bridge sites are the
project's standard `[Finite]`→`[Fintype]` convention (ROADMAP
*Engineering conventions*; these files take `[Finite]` in signatures
and bridge inline), already justified by the Phase 12 port decisions.

### Pre-sweep smell counts (Phase 12 surface)

| Smell | Submodular | Union |
|---|---|---|
| `classical` (standalone tactic) | 7 | 5 |
| `Classical.*` (term-mode) | 3 | 1 |
| `haveI/letI … Fintype.ofFinite` bridge | 3 | 7 |
| `noncomputable def` | 1 | 0 |
| `change` / `show` (tactic) | 1 | 0 |
| multi-step `rw` (4+ top-level args, depth-aware) | 5 | 0 |
| `@[nolint …]` / `set_option linter` | 0 | 0 |
| `show … from rfl` | 0 | 0 |
| `set_option backward.privateInPublic` | 0 | 0 |

Notes on the counts:
- `classical` sites pair with the `Fintype.ofFinite` bridges — both are
  the standard `[Finite V]`-signature + inline-`Fintype`/`DecidableEq`
  idiom (ROADMAP *Engineering conventions*), not a code smell to fix
  but a convention to confirm.
- `Classical.*` term-mode hits are `Classical.choice` (Submodular 1020-21,
  injective-of-subsingleton), `Classical.arbitrary` (Submodular 1059
  default index; Union 358 default element in a dependent-if). These are
  genuine choice uses inside the vendored proofs, not papering-over.
- multi-step `rw` recount is **depth-aware** (the comma-only regex
  over-counts inner `⟨_, _⟩` tuples, per Phase 11-cleanup B3): the 5
  Submodular sites (L179/L297/L375/L381/L403) are all genuine 4–5
  top-level-arg chains.

## Architectural choices made up front

These extend `../DESIGN.md` *Choices to revisit*; if any turns out
wrong, revisit there.

- **Round scoped to the Phase 12 surface**, same restrict-to-surface
  pattern as Phase 8/9/10+11-cleanup. Project-wide drift was discharged
  by Phase 7-cleanup and reconfirmed by later rounds; this round audits
  only the two new Matroid files + the new blueprint chapter.
- **Vendored-port bias on §B/§C** (see *Vendored-port caveat* above):
  fix warnings/style at source; do **not** reshape vendored proof
  content (extraction / unification / tactic substitution that rewrites
  Nelson's argument) absent a strong reason. This narrows §C's
  four-question walk to "is there a *project-side* simplification" and
  biases it toward no-op, consistent with the §C *Calibration*
  paragraph in `../CLEANUP.md`.
- **No perf pass bundled.** Per `../CLEANUP.md` *What a cleanup round is
  not*, build-time work routes through a separate `Phase12-perf.md` if
  the user opens one. (None queued; the Matroid files are not
  `module`-converted — the `apnelson1/Matroid` dep blocks it, per
  `../CombinatorialRigidity/CLAUDE.md` *Module-system conversion* — so
  the per-decl `@[expose]` lever does not apply here.)
- **No new phase queued at round close** by default. Phase 13
  (Tutte–Nash-Williams) is scoped but not opened; the user opens it at
  round close if ready.

## Task checklist

The A–D surveys were **run at round open** (per *Task list
discipline*); the closures below record the survey result, not a fix.
Items marked `[ ]` are not yet dispatched; items marked with a survey
note but `[ ]` have their survey done and their fix (if any) pending.

### Bucket A — Blueprint ↔ Lean divergence audit (`matroid-union.tex`)

Nine `\lean{...}` entries, all currently `\leanok`/green (Phase 12
closed with every node green; `checkdecls` passes on the per-commit
gate, so no separate resolve-check task here):
`def:submodular`, `def:polymatroidFn`, `def:ofSubmodular` (+
`circuit_ofSubmodular_iff`, `indep_ofSubmodular_iff`),
`def:ofPolymatroidFn` (+ `indep_ofPolymatroidFn_iff`),
`lem:polymatroid-rank`, `def:matroid-union` (`Union`, `union`),
`lem:union-indep-iff` (`union_indep_iff`, `union_indep_iff'`),
`lem:rado`, `thm:matroid-partition-rank` (`matroid_partition'`,
`matroid_partition_eRk'`).

- [ ] **A1:** Statement-form walk — for each of the 9 entries, compare
  the blueprint statement against the Lean declaration signature
  (hypotheses, conclusion form, binders). Survey-relevant unknowns to
  resolve in the walk: `def:ofSubmodular`'s blueprint groups three Lean
  names; `lem:rado`'s prose pins `Matroid.rado` with a `Finset`-valued
  family `A : ι → Finset α` — confirm the binder shape matches; the
  blueprint `\lean{}` names omit the `Matroid.` namespace prefix in two
  spots — confirm `checkdecls` resolution covers the actual qualified
  names. Expected: mostly aligned (Phase 12 ran forward-mode, so the
  blueprint tracked the Lean per node), but the walk is the gate.
- [ ] **A2:** Prose-proof "the Lean does X via Y where Y is harder"
  scan over the four `\begin{proof}` blocks carrying prose
  (`lem:polymatroid-rank`, `lem:union-indep-iff`, `lem:rado`,
  `thm:matroid-partition-rank`). For each, check the prose isn't
  carrying a smoothness gloss the Lean can't sustain. **Vendored-port
  bias:** the "fix Lean first" response is constrained — a Lean
  simplification that rewrites Nelson's proof is out of scope; record
  the residual as an aside only if no *project-side* fix exists.
- [x] **A3:** Formalization-aside scan — **done, one fix landed.** The
  stale chapter-intro paragraph (former lines 4–9: "Its nodes are
  currently \emph{red} … the phase's to-do list … turns green as the
  matching Lean lands") was forward-mode scaffolding, stale now that
  Phase 12 closed all-green; removed, letting the mathematical-content
  paragraph lead (per `../blueprint/CLAUDE.md` *Keep the reshape history
  out of the prose* — a completed chapter reads as if its current shape
  were always the shape; matches the cleaned pebble-game/count-matroid
  chapter intros). The `\paragraph{Provenance.}` block ("Phase~12
  vendors the proofs into …") is sticky factual provenance with no
  Lean-side shortening — kept. The four proof prose blocks
  (`lem:polymatroid-rank`, `lem:union-indep-iff`, `lem:rado`,
  `thm:matroid-partition-rank`) carry no stale asides. `verify.sh`
  green (bp + web + checkdecls).

### Bucket B — Code-smell sweep (Phase 12 surface)

Pre-grep counts in *Current state* above. Each smell its own commit (or
small cluster) if it converts to a fix; the vendored-port bias means
most are expected to close as no-op confirmations of the convention.

- [ ] **B1:** `classical` audit (7 Submodular + 5 Union). Question per
  `../CLEANUP.md` §B: is `[DecidableEq α]` a cleaner boundary, or is the
  decidability genuinely unavailable? Expected no-op: these pair with
  the `Fintype.ofFinite` bridges as the standard `[Finite]`-signature
  idiom; the `classical` opens the `DecidableEq` the `Finset` ops need.
  Confirm each site sits under a `[Finite]` (not `[Fintype]`) signature
  so the `classical` is load-bearing.
- [ ] **B2:** `haveI/letI … Fintype.ofFinite` bridge audit (3 + 7).
  Question: should the caller take `[Fintype]`, or is `[Finite]`+bridge
  right? Is the *same* `haveI` repeated across many sites suggesting a
  single helper? Note the Union file repeats `haveI : Fintype α :=
  Fintype.ofFinite α` at 6 sites (L248/397/464/478/506 + 249-β) — assess
  whether that's the per-lemma convention (each lemma re-bridges, which
  is the mathlib idiom) or a genuine extract candidate. The Submodular
  `termination_by haveI := Fintype.ofFinite ι; …` (L632) is the
  TACTICS-QUIRKS § 16(d) WF-recursion trick — confirm, no-op.
- [ ] **B3:** `noncomputable def` audit (1 site: `PartialTransversal.encard`
  L781, Submodular). Question: is the keyword forced? `encard` is
  `ℕ∞`-valued via `Set.encard` / a `Finset.card` cast — likely forced
  by the same enumeration driver. Confirm.
- [ ] **B4:** `change` audit (1 site: Submodular L290
  `change (Y : Set α) ⊆ X at hY`). Question per `../CLEANUP.md` §B / the
  *Concrete signals* list: is the `change` covering for an un-fused
  coercion lemma (`Finset.coe_subset` / a `↑`-membership simp lemma)?
  Could a one-line rewrite replace it? Assess (project-side fix is in
  scope here — it's a coercion bridge, not Nelson's argument core).
- [ ] **B5:** Multi-step `rw` (4+ args) audit (5 Submodular sites:
  L179/L297/L375/L381/L403). For each, ask if a missing fused mirror
  lemma under `CombinatorialRigidity/Mathlib/<path>` would collapse the
  chain (per `../CLEANUP.md` §B + `../CombinatorialRigidity/CLAUDE.md`
  *Concrete signals*). Candidates: L179 is a `Nat.cast`/`card_erase`
  numeric chain; L297/L403 share the `card_empty, ← bot_eq_empty,
  hf.zero_at_bot` polymatroid-zero-at-bot pattern (possible 2-site
  fused-lemma candidate); L375 a `Nat.cast`/`card_insert` chain; L381 a
  `biUnion_insert` structural chain. Expected mostly per-step structural
  with no mirror (Phase 9/11-cleanup precedent), but the zero-at-bot
  repeat is worth a look. **Vendored-port bias:** a mirror lemma is a
  project-side addition (in scope); rewriting the chain's *strategy* is
  not.
- [ ] **B6:** `@[nolint]` / `set_option linter` / `backward.privateInPublic`
  / `show … from rfl` audit. Closes **no-op** by survey: zero sites of
  each across both files (recorded for completeness per the §B smell
  table — every column not covered by B1–B5 is zero).

### Bucket C — Long-proof audit (Phase 12 surface)

Top sites by body line span (robust per-decl scan at round open):

| # | Site | LoC | Four-question lean |
|---|---|---|---|
| 1 | `generalized_halls_marriage` (Submodular L476) | 173 | WF-recursive matroidal-Hall core (`termination_by ∑ i, (A i).card`). **Definitional refactor / API extraction** — but it is the vendored sub-tree's root; structural recursion boilerplate. Bias: no-op. |
| 2 | `polymatroid_rank_eq` (Submodular L303) | 173 | Edmonds rank formula; two-direction min argument. **Mathlib lemma we missed?** Re-scan its 5–10 L subblocks. Vendored proof — project-side only. |
| 3 | `polymatroid_of_adjMap` (Union L244) | 149 | The `adjMap`-matroid = `ofPolymatroidFn` bridge; calls `(rado …).mpr`. **API extraction?** Tightly tied to the union construction's locals. |
| 4 | `intro_elimination_nontrivial` (Submodular L98) | 144 | **Private helper reconstructed** in the port (was in never-committed `IsCircuitAxioms`). **Mathlib lemma we missed?** This one is *not* a verbatim Nelson proof — it was reconstructed, so a project-side simplification here does not diverge from upstream content. Worth the closest look in C2. |
| 5 | `sum'_eRk_eq_eRk_sum_on_indep` (Union L393) | 81 | Rank-distribution over `Matroid.sum'`. **Cross-proof unification** with `sum'_rk_eq_rk_sum` / the non-`_on_indep` sibling? |
| 6 | `rado_v2` (Submodular L934) | 68 | Total-transversal form of Rado. **Cross-proof unification** with `rado`? |

Runners-up (just outside): `union_indep_aux'` (Union L168, 46 L);
`PartialTransversal.of_fun_mem_dom` (Submodular L817, 33 L);
`polymatroid_rank_eq_on_indep` (Submodular L276, 27 L).

- [ ] **C1:** Top-6 ranking — **done** (table above). The four-question
  lean for each site is recorded; C2 dispatches.
- [ ] **C2:** Four-question walk over the C1 sites (API extraction,
  mathlib-lemma-we-missed, tactic substitution, definitional refactor,
  cross-proof unification). **Vendored-port bias:** the bar is
  "project-side simplification that doesn't rewrite Nelson's argument";
  `#4 intro_elimination_nontrivial` (a *reconstructed* helper, not
  verbatim upstream) is the exception where a content refactor is in
  scope. Per `../CLEANUP.md` §C *Calibration*, expect mostly no-op
  (ported structural-recursion / case-dispatch bodies), with the gate
  confirming the no-extract finding. Use `lean_loogle` / `lean_leanfinder`
  / `lean_multi_attempt` on any 5–10 L subblock before declaring no-op.
- [ ] **C3:** In-round refactor candidates land each as its own commit
  (per `../CLEANUP.md` *Workflow* rule 3). Populated by C2.

### Bucket D — Project-organization compression

- [ ] **D1:** `notes/Phase12.md` length/compression check. Currently
  434 LoC. Per `../notes/CLAUDE.md` *Soft length budget*, Phase 12 was
  a substantive multi-layer phase (L0/L1/L2a/L2b-union/L2b-rado/
  L2b-partition; ~1670 ported LoC) → adaptive upper band 350–450, so
  434 is **in band but at the top**. Assess whether *Current state*
  (which carries a long reverse-chronological per-layer narrative —
  L2b-partition, L2b-rado, L2b-rado-infra, re-scope, L2b-union, L2a×3,
  L1, L0) duplicates the *Layer plan* section and can collapse to a
  hand-off summary + pointer (the D1/D2 pattern from Phase 11-cleanup).
  If the per-entry ≤8-line rule and the hand-off contract both hold,
  may close no-op-or-light.
- [ ] **D2:** FRICTION re-skim. The `[matroid]` entry (FRICTION L79+) is
  a single large `[resolved]` block with per-layer sub-bullets (L2a /
  L2a-polymatroid / L2a-rank / L2b-union / re-scope / L2b-rado-infra /
  L2b-rado-warnings / L2b-rado-finish / L2b-partition-finish). Now that
  Phase 12 is **closed**, assess per `../CLEANUP.md` §D / `../notes/
  CLAUDE.md`: does the resolved entry (with its resolution fully indexed
  in `notes/Phase12.md` + DESIGN.md) migrate to `FRICTION-archive.md`?
  Or is its port-recipe content (the `Matroid.r → rk` rename chase, the
  Set-lift constructor pattern, the transitive-import gaps) still live
  reference for Phases 13–15 and should stay in active FRICTION?
- [ ] **D3:** Lift-on-promotion check. Have any `notes/Phase12.md`
  decisions been referenced in 2+ files / 2+ phases (the
  `[Finite]→[Fintype]` bridge, the Set-lift constructor pattern, the
  `Matroid.r → rk` port recipe)? If so, promote to `TACTICS-GOLF.md` /
  `TACTICS-QUIRKS.md` / `DESIGN.md` and replace with a one-line pointer.
  Note: TACTICS-QUIRKS § 16(d) already absorbed the WF-recursion
  `termination_by` bridge trick (Phase 12 lifted it during the round) —
  confirm no residual-lift (the phase entry should be pointer-first).
- [ ] **D4:** DESIGN.md *Choices to revisit* drift check. The
  `apnelson1/Matroid dependency` entry and the `Set/Finset and
  rank-flavor boundary at the matroid layer (Phases 13–15)` section
  (added in the last commit `d5d1d8e`) — confirm they reflect Phase 12's
  closed reality and the Phase 13 hand-off. Check the *Local mirror of
  the matroid-union subsystem* section is consistent with what actually
  landed.
- [ ] **D5:** ROADMAP / status-surface consistency spot-check. Phase 12
  is flipped ✓ on the ROADMAP Status table (confirmed at round open);
  confirm the three public surfaces (`README.md`, `home_page/index.md`,
  `blueprint/src/chapter/intro.tex`) also show Phase 12 ✓ — if the
  phase-close commit missed any, fix here (per `../CLAUDE.md` *When this
  commit closes a phase* → status-surface sync, applied retroactively).

## Blockers / open questions

- None at round open. The vendored-port bias (see *Architectural
  choices*) is the main thing that shapes dispositions; if a §C site
  genuinely needs a content reshape to fix a real problem, that's a
  surface-to-the-user moment, not a unilateral rewrite of Nelson's proof.

## Hand-off / next phase

**Smallest concrete next commit:** dispatch **B5** — the multi-step
`rw` (4+ args) audit over the 5 Submodular sites
(L179/L297/L375/L381/L403), the most likely remaining B-bucket fix. The
specific candidate already surfaced: L297/L403 share the `card_empty,
← bot_eq_empty, hf.zero_at_bot` polymatroid-zero-at-bot pattern — assess
whether a 2-site fused mirror lemma under `CombinatorialRigidity/Mathlib/`
collapses both chains (project-side addition, in scope under the
vendored-port bias). The other three (L179 `Nat.cast`/`card_erase`, L375
`Nat.cast`/`card_insert`, L381 `biUnion_insert`) are expected per-step
structural with no mirror (Phase 9/11-cleanup precedent). If B5 surveys
no-op, fall through to **D1** (the `notes/Phase12.md` *Current state*
compression — 434 LoC, top of band) or the A1/A2 statement/proof walks.

A3 landed one fix (the stale forward-mode intro paragraph). The round
already has its non-no-op commit, so the remaining buckets may close
no-op; if B5–D5 all survey no-op, the closing commit flips the ROADMAP
row to ✓ with a "A3 fix + all-else-no-op → close" summary.
