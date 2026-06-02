# Phase 12 cleanup round — work log

**Status:** ✓ complete. **A3 + B5 + D1 fixes landed; all other buckets
(A1/A2, B1–B4/B6, C1/C2, D2–D5) closed no-op** under the vendored-port
bias. A3 removed the stale forward-mode chapter-intro paragraph from
`matroid-union.tex`; B5 added the `PolymatroidFn.zero_at_empty` fused
accessor and applied it at four sites; D1 compressed `notes/Phase12.md`
*Current state* from a 160-line reverse-chronological narrative to a
Phase-11-style summary + pointers, 434 → 304 LoC. The A1/A2
statement/proof walks confirmed all 9 `matroid-union.tex` entries align
with their Lean signatures and no prose carries a gloss the Lean can't
sustain; the remaining code-smell / long-proof / org buckets confirmed
the conventions (`[Finite]`-bridge idiom, vendored structural-recursion
bodies, status surfaces all Phase-12-✓). Build green + warning-clean;
`lake lint` clean.

This is the inter-phase cleanup round covering **Phase 12** (matroid
foundations: submodular functions + matroid union). See `../CLEANUP.md`
for the round-level operating manual: when to run a round, the four
audit categories (A blueprint-divergence, B code-smell, C long-proof,
D project-organization), and the per-round workflow. The task list
below is the round's "lemma checklist" equivalent — populated up front
per CLEANUP.md's *Sweep first, fix later* + *Task list discipline* so a
session that runs out of time can hand off cleanly.

## Current state

**Round complete.** The §A blueprint↔Lean divergence walk over
`matroid-union.tex`'s nine `\lean{...}` entries, the §B code-smell greps
over the two Matroid files, the §C long-proof ranking + four-question
walk, and the §D org-compression checks have all been **run and closed**
(results under *Task checklist* below). Three fixes landed, each its own
commit: **A3** (drop the stale forward-mode chapter-intro paragraph from
`matroid-union.tex`), **B5** (`PolymatroidFn.zero_at_empty` fused accessor
collapsing the `← bot_eq_empty, hf.zero_at_bot` pair at four
`Submodular.lean` sites), **D1** (compress `notes/Phase12.md` *Current
state*, 434 → 304 LoC). Everything else closed **no-op** under the
vendored-port bias: A1/A2 confirmed all 9 entries align in
binders/hypotheses/conclusion and no prose over-glosses the Lean; B1–B4
confirmed the `[Finite]`-signature `classical`/`Fintype.ofFinite` idiom,
the forced `noncomputable` `Set.encard`, and the `change` coercion bridge;
C1/C2 confirmed the long bodies are forced structural-recursion /
two-direction-min / rank-distribution boilerplate (incl. the reconstructed
`intro_elimination_nontrivial`, already tight); D2–D5 confirmed the
FRICTION `[matroid]` port-recipe stays live for Phases 13–15, no residual
lift, no DESIGN.md drift, all status surfaces Phase-12-✓. Build of both
Lean files green, warning-clean; `lake lint` clean.

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

- [x] **A1:** Statement-form walk — **done, closes no-op.** All 9
  entries align in binders / hypotheses / conclusion form. The three
  survey-flagged unknowns resolved clean: (i) `def:ofSubmodular`'s
  three-name group (`ofSubmodular` L122 / `circuit_ofSubmodular_iff`
  L208 / `indep_ofSubmodular_iff` L216) — all present, the prose covers
  both the circuit (`Minimal (X.Nonempty ∧ f X < X.card)`) and indep
  (`∀ I' ⊆ I, I'.Nonempty → I'.card ≤ f I'`) forms; (ii) `lem:rado`'s
  `Finset`-valued family — `rado` (L1103) takes `(A : ι → Finset α)`,
  `[Finite ι]`, conclusion `… ↔ ∀ K : Finset ι, K.card ≤ M.rk (K.biUnion A)`,
  matching the `⋃_{i∈K} A_i` / `K ⊆ ι` prose; (iii) the "two
  namespace-omitted `\lean{}`" concern is **moot** — all 9 pointers
  carry the `Matroid.` prefix (verified by grep), and the declarations
  sit inside `namespace Matroid`, so `checkdecls` (green on the
  per-commit gate) resolves them. The attained-min pair encoding of
  `lem:polymatroid-rank` / `thm:matroid-partition-rank` (∃-half attains,
  ∀-half bounds) is the faithful Lean form of the blueprint `= min`.
- [x] **A2:** Prose-proof scan over the four `\begin{proof}` blocks —
  **done, closes no-op.** None carries a smoothness gloss the Lean
  can't sustain: `lem:polymatroid-rank` (Edmonds two-direction min,
  matches `polymatroid_rank_eq`'s ∃/∀ pair), `lem:union-indep-iff`
  (`adjMap`/`sum'` bipartite-matching, matches the Lean realization),
  `lem:rado` ("submodular generalization of Hall", built on
  `generalized_halls_marriage`), `thm:matroid-partition-rank`
  (rank formula at `f = Σ rk`, matching produced by Rado) all faithful.
  No project-side Lean simplification in scope (vendored-port bias);
  no residual aside needed.
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

- [x] **B1:** `classical` audit (7 Submodular + 5 Union) — **done,
  closes no-op.** Each site sits under a `[Finite]` (not `[Fintype]`)
  signature; the `classical` opens the `DecidableEq` the `Finset` ops
  need (canonical: `rado` L1103-1107, `[Finite ι]` + `classical` +
  `haveI : Fintype ι := Fintype.ofFinite ι`). Standard
  `[Finite]`-signature idiom (ROADMAP *Engineering conventions*),
  confirmed by the Phase 12 port decisions; `[DecidableEq α]` is the
  pre-existing signature boundary, not a candidate to widen.
- [x] **B2:** `Fintype.ofFinite` bridge audit (3 + 7) — **done, closes
  no-op.** The repeated `haveI : Fintype α := Fintype.ofFinite α` is the
  per-lemma re-bridge (the mathlib idiom under a `[Finite]` signature),
  not an extract candidate — each lemma's `Finset.univ`/`Fintype.card`
  step needs its own local `Fintype`. The Submodular WF-recursion
  `termination_by haveI := Fintype.ofFinite ι; …` is TACTICS-QUIRKS
  § 16(d) (already lifted during the phase) — confirmed.
- [x] **B3:** `noncomputable def` audit (`PartialTransversal.encard`
  L788) — **done, closes no-op.** Body is `(T.edges : Set (ι × α)).encard`;
  `Set.encard` is `noncomputable` (choice-built `ℕ∞`), so the keyword is
  forced.
- [x] **B4:** `change` audit (Submodular L297 `change (Y : Set α) ⊆ X
  at hY`) — **done, closes no-op.** It is a `Finset`→`Set` coercion
  bridge: `hY : Y ⊆ X` (Finset) is lifted so `hX_indep.subset hY`
  (Matroid `Indep.subset`, `Set`-valued) typechecks on the next line.
  A project-side `Finset.coe_subset.mpr hY` is a lateral move, not a
  simplification; the `change` reads clearly and stays.
- [x] **B5:** Multi-step `rw` (4+ args) audit (5 Submodular sites:
  L179/L297/L375/L381/L403) — **done, one fix landed.** The zero-at-bot
  repeat the survey flagged at L297/L403 is actually a **four**-site
  pattern (the `← bot_eq_empty, hf.zero_at_bot` pair also at L286 and the
  2-arg L463, both below the 4+ grep threshold). Added
  `PolymatroidFn.zero_at_empty : f ∅ = 0` (the `Finset` specialization of
  `zero_at_bot`, `[DecidableEq α]` for the `Finset` `Lattice`/`Bot`
  instances; lives in `Submodular.lean` beside the structure since it is
  a `PolymatroidFn`-fact, not upstream-eligible) and applied it at all
  four sites, collapsing each `← bot_eq_empty, hf.zero_at_bot` to a single
  `hf.zero_at_empty`. The other three flagged chains close **no-op**: L179
  (`← Nat.cast_one, ← Nat.cast_sub, Nat.cast_inj, card_erase_of_mem`) and
  L375 (`← Int.lt_add_one_iff, ← Nat.cast_one, ← Nat.cast_add, ←
  card_insert_of_notMem`) are per-step `ℤ`/`ℕ`-cast↔card numeric chains
  with no single fused mirror; L381 (`← h, cons_eq_insert, ← hY',
  biUnion_insert, biUnion_insert`) is a per-step structural `cons`/
  `biUnion` chain. **Vendored-port bias:** the accessor is a project-side
  addition (in scope); none of the chains' strategies were rewritten.
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
- [x] **C2:** Four-question walk over the C1 sites — **done, closes
  no-op.** The five vendored sites (#1–3, #5, #6) are structural-recursion
  / two-direction-min / rank-distribution bodies whose length is forced
  at the boilerplate level, not the step level (the §C *Calibration*
  shape): no project-side extraction without reshaping Nelson's argument.
  The C-bucket exception #4 `intro_elimination_nontrivial` (the
  reconstructed helper, where a content refactor *is* in scope) is
  already a tight 20-line `private` helper with a single caller
  (`circuit_elimination` field), a clean `by_contra!` + antichain core,
  and uses only existing mathlib (`singleton_of_mem_card_le_one`,
  `one_lt_card_iff_nontrivial`) — no extraction, mathlib-lemma-we-missed,
  tactic-substitution, or unification opportunity. No refactor surfaced.
- [x] **C3:** No in-round refactor candidates — C2 surfaced none.

### Bucket D — Project-organization compression

- [x] **D1:** `notes/Phase12.md` length/compression check — **done, fix
  landed.** The *Current state* section was ~160 lines of
  reverse-chronological per-layer narrative (L2b-partition, L2b-rado,
  L2b-rado-infra, re-scope, L2b-union, L2a×3, L1, L0) that duplicated three
  other sections of the same file: the *Layer plan* (per-layer what-landed +
  the L2b re-scope rationale), the *Lemma checklist* (every node green), and
  the cross-referenced FRICTION `[matroid]` sub-entries (per-layer port
  hazards). Phase 12 is **closed**, so per `../CLEANUP.md` §D ("compress the
  multi-session plan to a commit-log pointer + a brief summary once the phase
  is closed") this is the D1/D2 pattern from Phase 11-cleanup. Collapsed
  *Current state* to a Phase-11-style ~20-line summary (foundations available
  + where the per-layer detail / port hazards live), dropping nothing not
  preserved elsewhere. **434 → 304 LoC** — mid-band, hand-off contract intact,
  per-entry ≤8-line rule holds.
- [x] **D2:** FRICTION re-skim of the `[matroid]` entry (L79+) —
  **done, closes no-op: keep in active FRICTION.** Phases 13–15 continue
  consuming the *same* `apnelson1/Matroid` package (Phase 13's
  `cycleMatroid` port), so the entry's port-recipe content (`Matroid.r →
  rk` rename chase, Set-lift constructor pattern, transitive-import
  gaps, the aesop-`simp_all only` pruning lesson) is live reference for
  the next porter, not closed design history — does not migrate to
  `FRICTION-archive.md`. The narrow port-specific lesson (aesop
  `simp_all` list pruning) is stated inline and is not yet a
  2+-phase cross-cutting rule, so it stays with the entry.
- [x] **D3:** Lift-on-promotion check — **done, closes no-op.**
  `notes/Phase12.md` is already pointer-first: the WF-recursion
  `termination_by`/`Fintype.ofFinite` trick points to TACTICS-QUIRKS
  § 16(d) (lifted during the phase), and the `Matroid.r → rk` /
  Set-lift port recipes are kept in the FRICTION `[matroid]` entry
  (single source of truth), not duplicated. No decision has crossed the
  2+-phase threshold yet (the port recipes become cross-cutting if
  Phase 13's `cycleMatroid` port re-hits them — promote then).
- [x] **D4:** DESIGN.md drift check — **done, closes no-op.** The
  *Local mirror of the matroid-union subsystem* (L318+) and *Set/Finset
  and rank-flavor boundary at the matroid layer (Phases 13–15)* (L361+,
  added in `d5d1d8e`) sections both reflect Phase 12's closed reality
  and the Phase 13 hand-off — they describe the exact signatures the A1
  walk verified (`matroid_partition'` ℕ/Finset-flavored,
  `matroid_partition_eRk'` ℕ∞/Set-flavored). No drift.
- [x] **D5:** Status-surface spot-check — **done, closes no-op.** All
  three public surfaces show Phase 12 complete/✓: `README.md` (*Project
  status*, "Phases 1–12 complete" + "Phase 12 (complete)"),
  `home_page/index.md` (prose + phase table row 12 = ✓),
  `blueprint/src/chapter/intro.tex` (§*Phase plan*). ROADMAP Status
  table also has Phase 12 ✓ and the post-Phase-12 cleanup-round row
  (flipped to ✓ in this closing commit).

## Blockers / open questions

- None at round open. The vendored-port bias (see *Architectural
  choices*) is the main thing that shapes dispositions; if a §C site
  genuinely needs a content reshape to fix a real problem, that's a
  surface-to-the-user moment, not a unilateral rewrite of Nelson's proof.

## Hand-off / next phase

**Round closed.** All A–D buckets dispatched: A3 + B5 + D1 landed fixes
(each its own commit); A1/A2, B1–B4/B6, C1–C3, D2–D5 closed no-op under
the vendored-port bias (per-bucket results in *Task checklist* above).
ROADMAP Status row flipped to ✓ in the closing commit.

**Next:** Phase 13 (Tutte–Nash-Williams tree-packing, `BodyBar/
TreePacking.lean`) is scoped but not opened — the user opens it when
ready (ROADMAP §13). The next porter consuming the same
`apnelson1/Matroid` package (`cycleMatroid`) should consult the FRICTION
`[matroid]` entry's port recipe (`Matroid.r → rk` renames, Set-lift
constructor pattern, transitive-import gaps) kept live for exactly that
reason; if those recipes re-bite in Phase 13, promote them to a
cross-cutting home then (D3 left them in FRICTION as a single source of
truth, below the 2+-phase promotion threshold).
