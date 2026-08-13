# Pencil doc-set cleanup (ad-hoc round, category D only) (work log)

**Status:** in progress — this commit is the log skeleton + task list only
(`CLEANUP.md` *Workflow* rule 1). Sweep complete; **nothing fixed yet.**

Ad-hoc round, opened mid-Phase-39 (PENCIL stays OPEN throughout; this round
does not close it and does not gate the tenth research direction). Chosen by
the user 2026-08-13, offered a choice after GEXIST landed (`054744a6`)
between a tenth direction, stopping, or paying down doc-debt first — the
user chose the cleanup round. Round manual: `CLEANUP.md`. **Category D only**
(*Project-organization compression*) — no Lean or blueprint work is in
scope, so no `lake build` / `lake lint` / blueprint gates fire on this round;
categories A/B/C are out of scope by construction (nothing here touches
`.lean` or `.tex`).

**No tenth research direction is opened, selected, or named as pending by
this round.** Phase 39 stays OPEN; the Lean hold STANDS; W4 stays PARKED;
`hK`/`hbareSplit` stay pinned; option B stays un-commissioned — see
`notes/Phase39.md` *Current state* for the standing adjudications, unchanged
by this round.

## Scope

The Phase-39 pencil doc set: `notes/Pencil-informal.md`,
`notes/Pencil-W4-informal.md`, `notes/Pencil-labels.md`,
`notes/Pencil-fanout.md`, `notes/Pencil-strategy.md`,
`notes/scripts/README.md`, plus `notes/Phase39.md` itself (length/balance)
and `notes/FRICTION.md` (archive-readiness, project-wide but flagged by the
coordinator alongside this round).

## Task list

### D-1 — `Pencil-informal.md` *Section index* line-range drift

**Coordinator-seeded, extended and corrected here.** Ground truth:
`grep -n '^## ' notes/Pencil-informal.md` (durable anchor); the corrected
table below was computed programmatically (walk forward from each heading
match for the start, and back from the next heading over any run of blank
lines for the end) — not by hand arithmetic, and not by assuming a uniform
per-row offset.

| § | claimed | actual | Δstart | Δend |
|---|---|---|---|---|
| *Shared dictionary* | 100–194 | 109–202 | +9 | +8 |
| *State of (K)* | 195–439 | 204–448 | +9 | +9 |
| §(K-tight) | 440–699 | 450–708 | +10 | +9 |
| §(K-pitch) | 700–1133 | 710–1142 | +10 | +9 |
| §(K-slide) | 1134–1425 | 1144–1434 | +10 | +9 |
| §(K-slide-cl) | 1426–1717 | 1436–1726 | +10 | +9 |
| §(K-slide-comb) | 1718–2069 | 1728–2078 | +10 | +9 |
| §(K-flank) | 2070–2642 | 2080–2651 | +10 | +9 |
| §(K-pure) | 2643–3220 | 2653–3229 | +10 | +9 |
| §(K-Λ) | 3221–4181 | 3231–4190 | +10 | +9 |
| §(K-dom) | 4182–4589 | 4192–4598 | +10 | +9 |
| §(K-σ) | 4590–5323 | 4600–5332 | +10 | +9 |
| §(K-clos) | 5324–5998 | 5334–6009 | +10 | **+11** |
| §(K-ann) | 6001–7509 | 6011–7531 | +10 | **+22** |
| §(K-out) | 7510–8705 | 7534–8728 | +24 | +23 |
| §(K-ind) | 8706–9051 | 8730–9074 | +24 | +23 |
| §(K-Δ) | 9052–9318 | 9076–9341 | +24 | +23 |
| §(K-bare-ext) | 9319–9358 | 9343–9381 | +24 | +23 |
| §(K-grid) | 9383–13277 | 9383–13277 | 0 | 0 |
| §(K-frame) | 13278–14368 | 13279–14368 | +1 | **0** |
| §(K-mech) | 14369–14749 | 14370–14750 | +1 | +1 |

(File total: 14750 lines, `wc -l`, matches §(K-mech)'s actual end.)

Findings beyond the coordinator's seed (the two rows it flagged as
unmeasured, plus a check of every row's end bound, per its instruction):

- *Shared dictionary* and *State of (K)* drift too (+9 start), contrary to
  the phase note's earlier claim that only rows *above* §(K-grid) drift and
  implicitly that these two are exempt — they are not exempt, they drift the
  same as the rest of that block.
- **Drift is not a uniform per-section shift.** Most rows shift by the same
  amount at both ends (Δstart = Δend), but three don't, and a fix that
  applies one offset per block would get these three wrong:
  - **§(K-clos):** Δend +11 vs. Δstart +10 — the section gained one net
    line since the index was last synced.
  - **§(K-ann):** Δend **+22** vs. Δstart +10 — a genuine ~12-line content
    growth on top of the index staleness, *plus* a formatting quirk (two
    consecutive blank lines, not one, before the `§(K-out)` heading at
    7534) that a naive "next-heading-minus-2" patch would miscount.
  - **§(K-frame):** Δend **0** vs. Δstart +1 — one line *shorter* than a
    uniform shift predicts.
- **§(K-grid) is the only row with zero drift at both ends** (exact:
  9383–13277) — it really was correctly resynced at the GEXIST landing, as
  the phase note claimed.
- **Fix instruction:** recompute every row directly (grep the heading starts;
  take each end as the last non-blank line before the next heading) rather
  than porting this table's deltas forward — this snapshot is only valid as
  of this commit, and any other edit to the file before the fix lands could
  move it again.

### D-2 — §(K-grid) *State of (K)* gap-map cell is a changelog, not a status statement

**Coordinator-verified.** `notes/Pencil-informal.md:248` — the *State of (K)*
gap map's single row for gap `(K-grid)` (table starts at line 227) — is one
markdown table cell carrying **eight** directions' narrative in sequence:
the original T material, then one "Since Steps Gxx–Gyy (direction …)" block
each for G, E, TCOL, CFLANK, GCAP, GUNIF and GEXIST (confirmed by direct
read: a single row, several thousand words). This violates the map's own
stated discipline ("this map is the artifact a new pass updates," line
~209-210) and `notes/CLAUDE.md`'s general rule that each section states the
*current* argument, revised in place, not its changelog.

**Scoping constraint for the fix — status-preserving, not narrative-cutting.**
The rewrite may compress *how* the cell says what it says; it must not
change **what** it says is true. No `(GR-1)`–`(GR-35)` label may have its
recorded standing altered by the rewrite, and in particular **(GR-15) must
stay OPEN, unchanged, with no status move**. The target shape: what is
proven, what is open, and the residual *now* — the eight-direction history
belongs in the Steps subsections (already there) and in git, not restated in
the map cell. Whoever picks this up should diff the new cell's status claims
against the old cell's, one label at a time, before committing.

### D-3 — `notes/FRICTION.md`: 8 `[resolved]` entries ready to archive — DONE

Mechanical, per `CLEANUP.md` §D: `grep -n '^### \[resolved\]' notes/FRICTION.md`
→ lines 285, 291, 303, 315, 347, 364, 4810, 4884 (Henneberg row-LI glue
lemmas; `IsKDof` def-opacity accessor; CaseII orientation-agnostic row
lemma; `simp_all` heartbeat multiplier; `neighborFinset` vs. `Set.toFinset`;
two dot-notation/subst traps; `rw [heq]` motive-not-type-correct + term-mode
projection "Unknown constant"; `RingHom.mapMatrix_apply`). Migrated verbatim
to `notes/FRICTION-archive.md` (2656 lines before, 2762 after — a pure
106-line relocation, `git diff` shows only matching `+`/`-` blocks, no
rewording) per `FRICTION.md`'s own filing rule — copy the entries, delete
from `FRICTION.md`, no content change.

**Disposition.** All 8 boundary-checked programmatically (heading line
`### [resolved] …`, trailing blank line) before deletion — no hand-counted
line ranges. Appended in `FRICTION.md`'s original top-to-bottom order (the
mechanical, judgment-free ordering; the archive's own history shows it is a
migration-time append log, not phase-chronological — e.g. its last
pre-existing entry is a Phase-23-cleanup item, while entries from Phases
6–22 sit earlier, each block appended whole by whichever housekeeping pass
migrated it). No "Migrated from `FRICTION.md` in …" note added to the moved
entries — some earlier archive entries carry one, but it is not universal
(the file's last several entries don't), and the coordinator's instruction
for this round was explicit verbatim/no-content-change, so entries landed
byte-identical to their `FRICTION.md` form.

**Cross-reference check.** `grep`ed the tree for each entry's title and
named artifacts (`rigidityRow_none_some_elim`, `oldSpan_le_ker_eval_elim`,
`IsKDof.deficiency_eq`, `annihRow_neg`,
`ofNormals_panelRow_eq_hingeRow_of_ends_or_swap`, …) plus a literal
`FRICTION.md:<line>` line-number-anchor search. Found:
- **3 bare `→ FRICTION [resolved] *title*` pointers** in `notes/Phase38.md`'s
  own *Promoted to …* section (Henneberg row-LI, `IsKDof`/`IsMinimalKDof`,
  CaseII orientation-agnostic row) and **1** in `TACTICS-GOLF.md` §21
  (`simp_all` heartbeat multiplier). **Not repointed** — this convention
  names the friction-log *system* by title, not a file path, and both
  `TACTICS-QUIRKS.md` (line ~25) and `CombinatorialRigidity/CLAUDE.md`
  (line ~40) instruct readers to grep *both* `FRICTION.md` and
  `FRICTION-archive.md`. Confirmed as the established convention, not a
  judgment call: a **live, unedited precedent already exists** —
  `TACTICS-QUIRKS.md` §47 currently reads "See FRICTION [resolved]
  *ℕ-subtraction…*" pointing at an entry that has **already** been
  archived (present in `FRICTION-archive.md`, not `FRICTION.md`), left
  exactly as-is. A `notes/Phase9-cleanup.md` D3 companion-check
  independently reached the same verdict ("all 8 pointer lines still
  resolve to live targets … FRICTION-archive entries … No drift; no
  edit").
- **One stale line-number anchor**, `notes/Phase8-cleanup.md:242`/`:393`
  ("Verified at `notes/FRICTION.md:619`") — pre-existing, unrelated to any
  of these 8 (its cited entry, "Extending a function on a subtype …", was
  already migrated to the archive in an earlier round; the anchor was
  already stale before this commit). Out of scope for D-3: a closed-round
  audit snapshot, not a live pointer, and not one of this round's 8.
- **No Lean doc-comment** references any of the 8 by title (only generic
  `*Mirrored*` / `[mirror-candidate]` pointers unrelated to these entries).

No repoints landed; none were live.

### D-4 — other pencil docs and the wider sweep: swept, nothing found

- **Cross-file references to `Pencil-informal.md`** (`Pencil-fanout.md`,
  `Pencil-labels.md`, `Pencil-strategy.md`, `Pencil-W4-informal.md`): every
  citation uses the `§(K-…)` heading form, never a bare line number
  (`grep -no 'Pencil-informal\.md[^)]*' …` over all four files, checked for
  a trailing `:[0-9]+`, no hits) — so D-1's drift does **not** propagate as
  a stale cross-reference anywhere else in the doc set.
- **`Pencil-labels.md`'s registry** (the (K)-workbook table, from line ~302):
  up to date through `(GR-32)`–`(GR-35)` / GEXIST; every owning section has a
  row, no stale tag, no missing entry.
- **`notes/scripts/README.md`'s driver invocation table**: every `.py` file
  on disk under `notes/scripts/{,w4/,kbare/,m2/}` is documented (33/33 in
  `w4/` cross-checked by script). The four `.m2` names the table mentions
  but that are absent on disk (`cflank.m2`, `gcap.m2`, `gridcol.m2`,
  `patexist.m2`) are each explicitly annotated "reserved and returned
  unused" — intentional, not drift. The *Harness debt* section already
  reads "ALL FOUR CLEARED… the round is CLOSED."
- **`Pencil-strategy.md` / `Pencil-fanout.md`**: neither carries its own
  line-range "Section index" (only `Pencil-informal.md` has one), so there
  is no analogous index to go stale in these files. Section headers read as
  a forward-consistent narrative (fan-out entries added serially, dated,
  never renumbered).
- **`notes/Phase39.md` *Decisions made*** — already fully one-lined with
  canonical-home pointers to the owning workbook section; its own
  "Promoted out of this phase" bullet lists the TACTICS-GOLF / TACTICS-QUIRKS
  / FRICTION lifts already made. No never-lifted cross-cutting lesson found.

### D-5 — `notes/Phase39.md` length/balance: watch, not a fix

484 lines before this round's hand-off update; 490 after (this commit) —
under the ~500 tripwire. Ratio check (`notes/CLAUDE.md` *Forward-weighted
note*): forward sections (*Current state* 140 ll. + *Blockers* 23 ll. +
*Hand-off* 116 ll. = 279 ll.) outweigh finished sections (*Decisions made*
98 ll. + *Citations* 49 ll. = 147 ll.), so the note is **not** finished-heavy
by the ratio rule. It is growing mainly because *Current state*'s
dated-adjudication list adds one bullet per check-in (nine now, 2026-07-24
through 2026-08-13) — each individually justified (a standing constraint
citation), but a candidate for compression once later bullets subsume
earlier ones. **Not actioned now** — flag for whoever's commit next tips the
file past 500 or past a forward/finished ratio flip.

## Judgment call — ROADMAP Status row

**Not adding one.** `CLEANUP.md` *Per-round work log* scopes the ROADMAP
Status-table row to a cleanup round *between phases*; every existing
cleanup-round row in `ROADMAP.md` (`Phase7-cleanup.md` through
`Phase26-cleanup.md`) is exactly that — a between-phases round with its own
"⋮ Cleanup round (post-Phase-N)" line, and none is mid-phase. This round is
mid-phase (Phase 39 stays OPEN with its own active row already), ad-hoc, and
category D only. A separate row here would duplicate the existing Phase 39
row's job under `notes/CLAUDE.md`'s "one canonical home per content type"
(*at-a-glance status* → the ROADMAP cell; *phase working detail* →
`notes/PhaseN.md`). Recorded instead via a pointer from `notes/Phase39.md`'s
*Current state* and *Hand-off* to this log (this commit) — sufficient for
the hand-off contract without a second visibility mechanism CLEANUP.md
doesn't sanction for this shape of round. Either answer was defensible; this
one is chosen because it keeps the round's existence discoverable from the
one place `CLAUDE.md`'s reading order already sends an agent.

## Blockers / open questions

**One hard ordering constraint: D-2 MUST land before D-1.** (Corrected
2026-08-13 by the coordinator; this section previously said the order was
free because the two edits touch disjoint regions. Disjointness is not the
relevant property.) The *State of (K)* gap map occupies lines **204–448** —
i.e. it sits **above every `## §(…)` heading in the file**, the first of
which (§(K-tight)) starts at line 450. D-2 rewrites a cell inside it, and
shrinking eight directions' changelog to a status statement necessarily
changes that cell's length, shifting every subsequent section's start *and*
end. So a D-1 table landed first is re-staled the moment D-2 lands, and the
round would have re-incurred exactly the drift it exists to remove. Land
D-2 first, then recompute D-1 from scratch against the post-D-2 file (per
D-1's own fix instruction: never port this snapshot's deltas forward).

Otherwise no blockers: D-3 is independent of both (different file), and
D-5 is a watch item. Land each fix as its own commit per `CLEANUP.md`
*Workflow* rule 3.

## Hand-off / next phase

**D-3 landed** (the FRICTION.md archive migration). **Next concrete commit:
D-2** (the §(K-grid) gap-map cell rewrite) — forced to precede D-1; see
*Blockers*. D-5 is a watch-item, not a fix, and needs no commit unless it
trips. Once this round's task list is empty, hand back to
`notes/Phase39.md` *Hand-off* for the tenth-direction selection — unblocked
by this round, not gated on it.

## Decisions made during this round

- **Round opened 2026-08-13, sweep-only commit.** Task list above populated
  from a full read of the pencil doc set (`Pencil-informal.md`,
  `Pencil-W4-informal.md`, `Pencil-labels.md`, `Pencil-fanout.md`,
  `Pencil-strategy.md`, `scripts/README.md`, `FRICTION.md`, `Phase39.md`); no
  fixes landed. D-1's drift table was independently recomputed
  programmatically (not copied from the coordinator's seed) and found the
  seed's own two flagged gaps (the unmeasured rows, the unverified end
  bounds) plus two non-uniform-drift exceptions the seed's uniform-offset
  framing would have gotten wrong. D-2 confirmed exactly as seeded. D-3, D-4,
  D-5 and the ROADMAP judgment call are this session's own sweep.
- **D-3 landed** (2026-08-13): the 8 `[resolved]` `FRICTION.md` entries moved
  to `FRICTION-archive.md` verbatim, appended in file order. The 4 bare
  `→ FRICTION [resolved] *title*` pointers found (`Phase38.md` ×3,
  `TACTICS-GOLF.md` §21 ×1) were **not** repointed — confirmed live
  project convention (a same-shaped, currently-unedited pointer in
  `TACTICS-QUIRKS.md` §47 already targets an archived entry; the
  `Phase9-cleanup.md` D3 companion-check reached the same verdict). See the
  D-3 task entry above for the full grep trail.

## Citations

None — no new mathematical or bibliographic claims in this round.
